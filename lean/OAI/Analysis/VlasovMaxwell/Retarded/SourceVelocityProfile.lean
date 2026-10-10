import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SourceJointFlux

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma source_dynamic_spatial_divergence_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (g : Vec → Phase) (n : Sphere) (v : Vec) (r : ℝ),
      ‖v‖≤P → ‖(g (r • n.1)).1‖≤M → ‖(g (r • n.1)).2‖≤M → 0<r →
      DifferentiableAt ℝ g (r • n.1) →
      |divergence (fun z => sourceFixedFlux v (g z).1 (g z).2 e i z) (r • n.1)|≤
        3*C/r^2+(3*C/r)*‖fderiv ℝ g (r • n.1)‖ := by
  obtain ⟨C,hC,hb⟩ := sourceFixedFlux_bounds P M e i
  refine ⟨C,hC,?_⟩
  intro g n v r hv hE hB hr hg
  have hn : n.1≠(0:Vec) := by intro hh; have hh' := sphere_norm n; rw [hh,norm_zero] at hh'; norm_num at hh'
  have hrn : r • (n.1 : Vec)≠0 := smul_ne_zero hr.ne' hn
  let z := r • (n.1 : Vec)
  let F : Vec × Phase → Vec := fun p => sourceFixedFlux v p.2.1 p.2.2 e i p.1
  have hF : DifferentiableAt ℝ F (z,g z) :=
    ((sourceJointFlux_contDiffAt e i (p:=((z,v),g z)) hrn).differentiableAt (by simp)).comp (f:=fun p : Vec × Phase => ((p.1,v),p.2)) (z,g z)
      ((differentiableAt_fst.prodMk (differentiableAt_const v)).prodMk differentiableAt_snd)
  have hchain := divergence_parameter_chain hF hg
  change divergence (fun y => F (y,g y)) z=_ at hchain
  change |divergence (fun y => F (y,g y)) z|≤_
  rw [hchain]
  obtain ⟨hsp,hparam⟩ := hb n v (g z).1 (g z).2 r hv hE hB hr
  have hcor : |∑ j : Fin 3, (fderiv ℝ (fun w : Phase => F (z,w)) (g z) (fderiv ℝ g z (basis j))) j|≤
      (3*C/r)*‖fderiv ℝ g z‖ := by
    calc
      _ ≤ ∑ j : Fin 3,|(fderiv ℝ (fun w : Phase => F (z,w)) (g z) (fderiv ℝ g z (basis j))) j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3,(C/r)*‖fderiv ℝ g z‖ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (norm_coordinate_le _ j).trans
        refine (hparam (fderiv ℝ g z (basis j))).trans ?_
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hC hr.le)
        simpa only [show ‖basis j‖=1 by simp [basis,PiLp.norm_single],mul_one] using
          ContinuousLinearMap.le_opNorm (fderiv ℝ g z) (basis j)
      _ = _ := by simp; ring
  exact (abs_add_le _ _).trans (add_le_add hsp hcor)

lemma retarded_spacetime_lipschitz (t : ℝ) (x : Vec) :
    LipschitzWith 1 (fun z : Vec => (t-coneRadius 0 z,x+z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq,coneRadius,zero_sub,norm_neg]
  apply max_le
  · rw [Real.dist_eq,show (t-‖y‖)-(t-‖z‖)=‖z‖-‖y‖ by ring,abs_sub_comm,dist_eq_norm]
    exact abs_norm_sub_norm_le y z
  · rw [dist_add_left]

lemma norm_fderiv_retarded_fields {s : Solution} {t : ℝ} (x : Vec) {z : Vec}
    (hz : z≠0) (ht : 0<t-coneRadius 0 z)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace) :
    ‖fderiv ℝ (fun y : Vec => (s.E (t-coneRadius 0 y,x+y),s.B (t-coneRadius 0 y,x+y))) z‖≤
      max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖ := by
  let a : Vec → (ℝ × Vec) := fun y => (t-coneRadius 0 y,x+y)
  have ha : DifferentiableAt ℝ a z :=
    ((differentiableAt_const t).sub (differentiableAt_coneRadius hz.symm)).prodMk
      ((differentiableAt_const x).add differentiableAt_id)
  have he := (field_contDiffAt_positive hE ht (x+z)).differentiableAt (by simp)
  have hb := (field_contDiffAt_positive hB ht (x+z)).differentiableAt (by simp)
  have hh := (he.hasFDerivAt.prodMk hb.hasFDerivAt).comp z ha.hasFDerivAt
  change HasFDerivAt (fun y : Vec => (s.E (a y),s.B (a y))) _ z at hh
  rw [hh.fderiv]
  have hn : ‖fderiv ℝ a z‖≤1 := norm_fderiv_le_of_lipschitz ℝ (retarded_spacetime_lipschitz t x)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq
  simp only [mul_one,ContinuousLinearMap.opNorm_prod,Prod.norm_mk]

lemma physical_source_spatial_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t r : ℝ) (x v : Vec) (n : Sphere),
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      0<r → r<t → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 (r • n.1),x+r • n.1)‖≤M →
      ‖s.B (t-coneRadius 0 (r • n.1),x+r • n.1)‖≤M →
      |divergence (fun z => sourceConeCoefficient s t x i (z,v) • coneSpatialLift 0 z v e) (r • n.1)|≤
        3*C/r^2+(3*C/r)*max
          ‖fderiv ℝ s.E (t-coneRadius 0 (r • n.1),x+r • n.1)‖
          ‖fderiv ℝ s.B (t-coneRadius 0 (r • n.1),x+r • n.1)‖ := by
  obtain ⟨C,hC,hb⟩ := source_dynamic_spatial_divergence_bound P M e i
  refine ⟨C,hC,?_⟩
  intro s t r x v n hE hB hr hrt hv he hb'
  have hn : n.1≠(0:Vec) := by intro hh; have hn := sphere_norm n; rw [hh,norm_zero] at hn; norm_num at hn
  have hz : r • (n.1 : Vec)≠0 := smul_ne_zero hr.ne' hn
  have ht : 0<t-coneRadius 0 (r • n.1) := by
    simpa only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr.le,sphere_norm,mul_one] using sub_pos.mpr hrt
  let g : Vec → Phase := fun y => (s.E (t-coneRadius 0 y,x+y),s.B (t-coneRadius 0 y,x+y))
  have ha : DifferentiableAt ℝ (fun y : Vec => (t-coneRadius 0 y,x+y)) (r • n.1) :=
    ((differentiableAt_const t).sub (differentiableAt_coneRadius hz.symm)).prodMk
      ((differentiableAt_const x).add differentiableAt_id)
  have hg : DifferentiableAt ℝ g (r • n.1) :=
    (((field_contDiffAt_positive hE ht (x+r • n.1)).differentiableAt (by simp)).comp (r • n.1) ha).prodMk
      (((field_contDiffAt_positive hB ht (x+r • n.1)).differentiableAt (by simp)).comp (r • n.1) ha)
  exact (hb g n v r hv he hb' hr hg).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (norm_fderiv_retarded_fields x hz ht hE hB)
      (div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hC) hr.le)))

def sourceVelocityProfile (e : Vec) (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : Vec :=
  (sourceAngularProfile i p *
    (dot p.1.1 e/(1-dot p.1.1 (velocity p.2)))) •
      (p.1.2.1+cross (velocity p.2) p.1.2.2)

lemma sourceVelocityProfile_contDiffAt (e : Vec) (i : Fin 3)
    {p : (Vec × Vec × Vec) × Vec} (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (sourceVelocityProfile e i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hi := sourceAngularProfile_contDiffAt i hd
  have hm := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  exact (hi.mul (hm.div (contDiffAt_const.sub hdu) hd)).smul hforce

lemma continuousOn_sourceVelocityDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => sourceVelocityProfile e i (p.1,w)) p.2)
      {p | 1-dot p.1.1 (velocity p.2)≠0} := by
  apply ContinuousOn.congr (f:=fun p : (Vec × Vec × Vec) × Vec =>
    ∑ j : Fin 3,(fderiv ℝ (sourceVelocityProfile e i) p (0,basis j)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((sourceVelocityProfile_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact divergence_parameter_slice ((sourceVelocityProfile_contDiffAt e i hp).differentiableAt (by simp))

lemma sourceVelocityDivergence_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (E B v : Vec), ‖E‖≤M → ‖B‖≤M → ‖v‖≤P →
      |divergence (fun w => sourceVelocityProfile e i ((n.1,E,B),w)) v|≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => sourceVelocityProfile e i (p.1,w)) p.2) K :=
    (continuousOn_sourceVelocityDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
      exact (cone_denom_pos p.2 p.1.1 hn).ne')
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n E B v hE hB hv
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

lemma source_velocity_divergence_rescale (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {z : Vec} (hz : z≠0) (v : Vec) :
    divergence (fun w => sourceConeCoefficient s t x i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v =
      (coneRadius 0 z)⁻¹*
        divergence (fun w => sourceVelocityProfile e i
          ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),w)) v := by
  let a := (coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z))
  have ha : DifferentiableAt ℝ (fun w => sourceVelocityProfile e i (a,w)) v :=
    ((sourceVelocityProfile_contDiffAt e i (p:=(a,v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).comp v
      ((differentiableAt_const a).prodMk differentiableAt_id)
  have he : (fun w => sourceConeCoefficient s t x i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) =
      fun w => (coneRadius 0 z)⁻¹ • sourceVelocityProfile e i (a,w) := by
    funext w
    simp only [sourceConeCoefficient,sourceFixedCoefficient,coneSpatialCoefficient,coneLorentz,sourceVelocityProfile,a,smul_smul,mul_assoc]
  rw [he,divergence_real_const_smul ha]

lemma physical_source_velocity_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |divergence (fun w => sourceConeCoefficient s t x i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v|≤C/(coneRadius 0 z) := by
  obtain ⟨C,hC,hb⟩ := sourceVelocityDivergence_uniform_bound P M e i
  refine ⟨C,hC,?_⟩
  intro s t x z v hz hv hE hB
  rw [source_velocity_divergence_rescale s t x e i hz v,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))]
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  exact (mul_le_mul_of_nonneg_left
    (hb ⟨coneDirection 0 z,hn⟩ _ _ v hE hB hv) (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))).trans_eq (by ring)

end RVM.Magnetic

end

end OAI
