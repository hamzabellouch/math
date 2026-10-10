import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.SourceKernels

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceJointFlux (e : Vec) (i : Fin 3) (p : Phase × Phase) : Vec :=
  sourceFixedFlux p.1.2 p.2.1 p.2.2 e i p.1.1

lemma sourceJointFlux_contDiffAt (e : Vec) (i : Fin 3) {p : Phase × Phase}
    (hp : p.1.1≠0) : ContDiffAt ℝ 1 (sourceJointFlux e i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst.fst
  have hn := (contDiffAt_coneDirection (k:=1) hp.symm).comp p contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase × Phase => velocity z.1.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_fst.snd
  have he := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hd := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hne := (cone_denom_pos p.1.2 _ (coneDirection_norm hp.symm)).ne'
  have hW : ContDiffAt ℝ 1 (fun z : Phase × Phase => coneSpatialLift 0 z.1.1 z.1.2 e) p :=
    contDiffAt_const.add ((he.div (contDiffAt_const.sub hd) hne).smul hu)
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 p.1.1,p.2.1,p.2.2),p.1.2)) hne).comp p
    ((hn.prodMk (contDiffAt_snd.fst.prodMk contDiffAt_snd.snd)).prodMk contDiffAt_fst.snd)
  exact ((hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))).mul hc).smul hW

lemma sourceJointFlux_derivative_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖fderiv ℝ (sourceJointFlux e i) ((n.1,v),(E,B))‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ
    (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)
  have hK : IsCompact K := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : ContinuousOn (fderiv ℝ (sourceJointFlux e i)) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    have hz : p.1.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact ((sourceJointFlux_contDiffAt e i hz).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,v),(E,B)) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_closedBall,dist_zero_right] using hv⟩,
    by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩

lemma sourceFixedFlux_spatial_derivative (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (a : Vec) :
    fderiv ℝ (sourceFixedFlux v E B e i) z a=
      fderiv ℝ (sourceJointFlux e i) ((z,v),(E,B)) ((a,0),(0,0)) := by
  have hm := ((hasFDerivAt_id (𝕜:=ℝ) z).prodMk (hasFDerivAt_const v z)).prodMk
    (hasFDerivAt_const (E,B) z)
  have hh := ((sourceJointFlux_contDiffAt e i (p:=((z,v),(E,B))) hz).differentiableAt (by simp)).hasFDerivAt.comp z hm
  exact congrArg (fun L : Vec →L[ℝ] Vec => L a) hh.fderiv

lemma sourceFixedFlux_field_derivative (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (a : Phase) :
    fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i z) (E,B) a=
      fderiv ℝ (sourceJointFlux e i) ((z,v),(E,B)) ((0,0),a) := by
  have hm := (hasFDerivAt_const (z,v) (E,B)).prodMk (hasFDerivAt_id (𝕜:=ℝ) (E,B))
  have hh := ((sourceJointFlux_contDiffAt e i (p:=((z,v),(E,B))) hz).differentiableAt (by simp)).hasFDerivAt.comp (E,B) hm
  exact congrArg (fun L : Phase →L[ℝ] Vec => L a) hh.fderiv

lemma sourceFixedFlux_field_differentiable (v e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (w : Phase) :
    DifferentiableAt ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i z) w :=
  ((sourceJointFlux_contDiffAt e i (p:=((z,v),w)) hz).differentiableAt (by simp)).comp w
    ((differentiableAt_const (z,v)).prodMk differentiableAt_id)

lemma sourceFixedFlux_field_rescale (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0)
    {r : ℝ} (hr : 0<r) (a : Phase) :
    fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i (r • z)) (E,B) a=
      r⁻¹ • fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i z) (E,B) a := by
  have heq : (fun w : Phase => sourceFixedFlux v w.1 w.2 e i (r • z))=
      fun w : Phase => r⁻¹ • sourceFixedFlux v w.1 w.2 e i z :=
    funext (fun w => sourceFixedFlux_homogeneous v w.1 w.2 e i hr z)
  rw [heq]
  have hh := (sourceFixedFlux_field_differentiable v e i hz (E,B)).hasFDerivAt.const_smul r⁻¹
  change HasFDerivAt (fun w : Phase => r⁻¹ • sourceFixedFlux v w.1 w.2 e i z) _ _ at hh
  exact congrArg (fun L : Phase →L[ℝ] Vec => L a) hh.fderiv

lemma sourceFixedFlux_bounds (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec) (r : ℝ),
      ‖v‖≤P → ‖E‖≤M → ‖B‖≤M → 0<r →
      |divergence (sourceFixedFlux v E B e i) (r • n.1)|≤3*C/r^2 ∧
      ∀ a : Phase, ‖fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i (r • n.1)) (E,B) a‖≤C/r*‖a‖ := by
  obtain ⟨C,hC,hb⟩ := sourceJointFlux_derivative_bound P M e i
  refine ⟨C,hC,?_⟩
  intro n v E B r hv hE hB hr
  have hn : n.1≠(0:Vec) := by intro hh; have hn := sphere_norm n; rw [hh,norm_zero] at hn; norm_num at hn
  have hder := hb n v E B hv hE hB
  have hF (z : Vec) (hz : z≠0) := (sourceFixedFlux_contDiffAt v E B e i hz).differentiableAt (by simp)
  constructor
  · rw [divergence_degree_neg_one (fun r hr z => sourceFixedFlux_homogeneous v E B e i hr z) hF hr hn,
      abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    have hb0 : |divergence (sourceFixedFlux v E B e i) n.1|≤3*C := by
      unfold divergence spatialPartial
      calc
        |∑ j : Fin 3,fderiv ℝ (fun z => sourceFixedFlux v E B e i z j) n.1 (basis j)|
            ≤ ∑ j : Fin 3,|fderiv ℝ (fun z => sourceFixedFlux v E B e i z j) n.1 (basis j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 3,C := by
          apply Finset.sum_le_sum
          intro j hj
          rw [fderiv_vec_component_at (hF n.1 hn) j]
          change |(fderiv ℝ (sourceFixedFlux v E B e i) n.1 (basis j)) j|≤C
          apply (norm_coordinate_le _ j).trans
          rw [sourceFixedFlux_spatial_derivative v E B e i hn]
          have ht := (ContinuousLinearMap.le_opNorm _ ((basis j,0),(0,0))).trans
            (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
          simpa [Prod.norm_mk,basis,PiLp.norm_single] using ht
        _ = 3*C := by simp
    exact (mul_le_mul_of_nonneg_left hb0 (inv_nonneg.mpr (sq_nonneg _))).trans_eq (by ring)
  · intro a
    rw [sourceFixedFlux_field_rescale v E B e i hn hr a,norm_smul,Real.norm_eq_abs,
      abs_inv,abs_of_pos hr,sourceFixedFlux_field_derivative v E B e i hn]
    have ht := (ContinuousLinearMap.le_opNorm _ ((0,0),a)).trans
      (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
    have ht' : ‖fderiv ℝ (sourceJointFlux e i) ((n.1,v),(E,B)) ((0,0),a)‖≤C*‖a‖ := by
      simpa only [Prod.norm_mk,norm_zero,max_self,max_eq_right (norm_nonneg a)] using ht
    exact (mul_le_mul_of_nonneg_left ht' (inv_nonneg.mpr hr.le)).trans_eq (by ring)

lemma divergence_parameter_chain {F : Vec × Phase → Vec} {g : Vec → Phase} {z : Vec}
    (hF : DifferentiableAt ℝ F (z,g z)) (hg : DifferentiableAt ℝ g z) :
    divergence (fun y => F (y,g y)) z=
      divergence (fun y => F (y,g z)) z+
      ∑ j : Fin 3,(fderiv ℝ (fun w : Phase => F (z,w)) (g z) (fderiv ℝ g z (basis j))) j := by
  have hd := hF.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).prodMk hg.hasFDerivAt)
  have hs := hF.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).prodMk (hasFDerivAt_const (g z) z))
  have hp := hF.hasFDerivAt.comp (g z) ((hasFDerivAt_const z (g z)).prodMk (hasFDerivAt_id (𝕜:=ℝ) (g z)))
  change HasFDerivAt (fun y => F (y,g y)) _ z at hd
  change HasFDerivAt (fun y => F (y,g z)) _ z at hs
  change HasFDerivAt (fun w : Phase => F (z,w)) _ (g z) at hp
  unfold divergence spatialPartial
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fderiv_vec_component_at hd.differentiableAt j,fderiv_vec_component_at hs.differentiableAt j,
    hd.fderiv,hs.fderiv,hp.fderiv]
  change (fderiv ℝ F (z,g z) (basis j,fderiv ℝ g z (basis j))) j=
    (fderiv ℝ F (z,g z) (basis j,0)) j+(fderiv ℝ F (z,g z) (0,fderiv ℝ g z (basis j))) j
  rw [show (basis j,fderiv ℝ g z (basis j))=(basis j,0)+(0,fderiv ℝ g z (basis j)) by simp,map_add]
  rfl

end RVM.Magnetic

end

end OAI
