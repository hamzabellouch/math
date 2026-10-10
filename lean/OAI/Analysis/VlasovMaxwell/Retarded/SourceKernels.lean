import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.RetardedDifferentiation
import OAI.Analysis.VlasovMaxwell.Retarded.TransportAngularCore

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffAt_sourceAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u b : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z) (hb : ContDiffAt ℝ k b z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => sourceAngularCore (n w) (u w) (b w)) z := by
  have hnb := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hb)
  have hnu := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hu)
  exact (((contDiffAt_const.sub hnu).pow 2).inv (pow_ne_zero 2 hd)).smul
    ((hnb.smul (hn.sub hu)).sub ((contDiffAt_const.sub hnu).smul hb))

def sourceAngularProfile (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : ℝ :=
  sourceAngularCore p.1.1 (velocity p.2)
    (fderiv ℝ velocity p.2 (p.1.2.1+cross (velocity p.2) p.1.2.2)) i

lemma sourceAngularProfile_contDiffAt (i : Fin 3) {p : (Vec × Vec × Vec) × Vec}
    (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (sourceAngularProfile i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  have hdv : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => fderiv ℝ velocity z.2) p :=
    ((contDiff_velocity (k:=2)).fderiv_right (by norm_num)).contDiffAt.comp p contDiffAt_snd
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p
    (contDiffAt_sourceAngularCore hn hu (hdv.clm_apply hforce) hd)

def sourceFixedCoefficient (v E B : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  (coneRadius 0 z)⁻¹*sourceAngularProfile i ((coneDirection 0 z,E,B),v)

def sourceFixedFlux (v E B e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  sourceFixedCoefficient v E B i z • coneSpatialLift 0 z v e

lemma sourceFixedCoefficient_contDiffAt (v E B : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (sourceFixedCoefficient v E B i) z := by
  have hn := contDiffAt_coneDirection (k:=1) hz.symm
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 z,E,B),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').comp z
      ((hn.prodMk (contDiffAt_const.prodMk contDiffAt_const)).prodMk contDiffAt_const)
  exact ((contDiffAt_coneRadius hz.symm).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hc

lemma sourceFixedFlux_contDiffAt (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (sourceFixedFlux v E B e i) z :=
  (sourceFixedCoefficient_contDiffAt v E B i hz).smul (contDiffAt_coneSpatialLift hz.symm)

lemma sourceFixedFlux_homogeneous (v E B e : Vec) (i : Fin 3) {r : ℝ} (hr : 0<r) (z : Vec) :
    sourceFixedFlux v E B e i (r • z)=r⁻¹ • sourceFixedFlux v E B e i z := by
  simp only [sourceFixedFlux,sourceFixedCoefficient,coneSpatialLift,coneSpatialCoefficient,
    coneRadius_zero_smul hr,coneDirection_zero_smul hr,smul_smul]
  congr 1
  field_simp

lemma fderiv_degree_neg_one {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=r⁻¹ • F z)
    {r : ℝ} (hr : 0<r) {z : Vec}
    (hz : DifferentiableAt ℝ F z) (hrz : DifferentiableAt ℝ F (r • z)) (e : Vec) :
    fderiv ℝ F (r • z) e=(r^2)⁻¹ • fderiv ℝ F z e := by
  have hm : HasFDerivAt (fun y : Vec => r • y) (r • ContinuousLinearMap.id ℝ Vec) z :=
    (hasFDerivAt_id z).const_smul r
  have h₁ := hrz.hasFDerivAt.comp z hm
  have h₂ := hz.hasFDerivAt.const_smul r⁻¹
  have heq : (fun y : Vec => F (r • y))=(fun y : Vec => r⁻¹ • F y) := funext (hh r hr)
  change HasFDerivAt (fun y : Vec => F (r • y)) _ _ at h₁
  rw [heq] at h₁
  have hv := congrArg (fun L : Vec →L[ℝ] Vec => L e) (h₁.unique h₂)
  change fderiv ℝ F (r • z) (r • e)=r⁻¹ • fderiv ℝ F z e at hv
  rw [map_smul] at hv
  have hv' := congrArg (fun a : Vec => r⁻¹ • a) hv
  simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
    show r⁻¹*r⁻¹=(r^2)⁻¹ by ring] using hv'

lemma divergence_degree_neg_one {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=r⁻¹ • F z)
    (hF : ∀ z≠0, DifferentiableAt ℝ F z) {r : ℝ} (hr : 0<r) {z : Vec} (hz : z≠0) :
    divergence F (r • z)=(r^2)⁻¹*divergence F z := by
  have hrz : r • z≠0 := smul_ne_zero hr.ne' hz
  have hc (y : Vec) (hy : y≠0) (i : Fin 3) :
      fderiv ℝ (fun x => F x i) y = (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y) := by
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y (hF y hy).hasFDerivAt).fderiv
  unfold divergence spatialPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc _ hrz i,hc _ hz i]
  change (fderiv ℝ F (r • z) (basis i)) i = (r^2)⁻¹*(fderiv ℝ F z (basis i)) i
  rw [fderiv_degree_neg_one hh hr (hF _ hz) (hF _ hrz)]
  rfl

def sourceConeCoefficient (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (p : Phase) : ℝ :=
  sourceFixedCoefficient p.2 (s.E (t-coneRadius 0 p.1,x+p.1))
    (s.B (t-coneRadius 0 p.1,x+p.1)) i p.1

lemma sourceConeCoefficient_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) (i : Fin 3) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (sourceConeCoefficient s t x i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hp.symm).comp p contDiffAt_fst
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 p.1,
      s.E (t-coneRadius 0 p.1,x+p.1),s.B (t-coneRadius 0 p.1,x+p.1)),p.2))
    (cone_denom_pos p.2 _ (coneDirection_norm hp.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))).mul hc

lemma electric_source_division_annulus {s : Solution} {H t ε R : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (heq : EquationsBefore s H)
    (htH : t≤H) (hε : 0<ε) (hεR : ε≤R) (hRt : R<t) (x e : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, s.f (t-R,x+R • n.1,v) •
        (sourceConeCoefficient s t x i (R • n.1,v) • coneSpatialLift 0 (R • n.1) v e)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, s.f (t-ε,x+ε • n.1,v) •
        (sourceConeCoefficient s t x i (ε • n.1,v) • coneSpatialLift 0 (ε • n.1) v e)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v) := by
  have hk : ContDiffOn ℝ 1 (sourceConeCoefficient s t x i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (sourceConeCoefficient_contDiffAt hE hB x i hp.1.1.symm hp.1.2).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  simpa only [smul_smul] using retarded_spatial_annulus (e:=e) hf hc hε hεR hRt hk hK
    (fun z hz v => coneLorentz_vlasov_before hf heq htH x hz v)

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

lemma sourceFixedFlux_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖sourceFixedFlux v E B e i n.1‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ
    (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)
  have hK : IsCompact K := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : ContinuousOn (sourceJointFlux e i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    have hz : p.1.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact (sourceJointFlux_contDiffAt e i hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,v),(E,B)) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_closedBall,dist_zero_right] using hv⟩,
    by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩

lemma source_sphere_rescale (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {r : ℝ} (hr : 0<r) (n : Sphere) :
    r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) =
    r*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1) := by
  have he : (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1))=
      r⁻¹ • ∫ v in closedBall (0:Vec) P,
        s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
          (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1 := by
    rw [←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only
      rw [sourceFixedFlux_homogeneous v _ _ e i hr]
      simp only [smul_smul,mul_comm])
  rw [he,dot_smul_right]
  field_simp

lemma source_sphere_boundary_bound (P M A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t U r : ℝ) (x : Vec),
      0<r → r≤t → t≤U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      |∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
        s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
          (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) ∂sphereMeasure|≤C*r := by
  obtain ⟨K,hK,hkb⟩ := sourceFixedFlux_uniform_bound P M e i
  let C := volume.real (closedBall (0:Vec) P)*A*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨(4*Real.pi)*C,mul_nonneg (by positivity) hC,?_⟩
  intro s t U r x hr hrt htU hf hEB
  simp_rw [source_sphere_rescale P s t x e i hr]
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith⟩
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (n : Sphere) : ‖r*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1)‖≤r*C := by
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1) (C:=A*K) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hf _ hs _ v)
          (hkb n v _ _ (by simpa only [mem_closedBall,dist_zero_right] using hv)
            (hEB _ hs _).1 (hEB _ hs _).2) (norm_nonneg _) hA)
    have hd := abs_real_inner_le_norm n.1
      (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1)
    rw [sphere_norm,one_mul] at hd
    rw [norm_mul,Real.norm_of_nonneg hr.le,dot_eq_inner,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hd.trans (by
      simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,C,mul_assoc,mul_comm,mul_left_comm] using hh)) hr.le
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_comm,mul_assoc,mul_left_comm] using hh

def sourceDivisionBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P,s.f (t-coneRadius 0 z,x+z,v)*
    (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
      divergence (fun w => sourceConeCoefficient s t x i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)

lemma inverse_source_majorant {a b Q r H : ℝ} (ha : 0≤a) (hb : 0≤b) (hQ : 0≤Q)
    (hr : 0<r) (hrH : r≤H) :
    a/r^2+(a/r)*Q+b/r≤(a+(a*Q+b)*H)/r^2 := by
  calc
    _ = (a+(a*Q+b)*r)/r^2 := by field_simp; ring
    _ ≤ _ := by gcongr

lemma source_division_bulk_annulus_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H Q ε R : ℝ) (x : Vec),
      0≤H → 0≤Q → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z|≤
        C*(H+H^2*(1+Q)) := by
  obtain ⟨Ks,hKs,hks⟩ := physical_source_spatial_bound P M e i
  obtain ⟨Kv,hKv,hkv⟩ := physical_source_velocity_bound P M e i
  let V := volume.real (closedBall (0:Vec) P)*A
  have hV : 0≤V := by dsimp [V]; positivity
  let C := 4*Real.pi*V*(3*Ks+Kv)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s U t H Q ε R x hH hQ hε hεR hRt htU hUH hE hB hf hEB hDF
  let L := V*(3*Ks+(3*Ks*Q+Kv)*H)
  have hL : 0≤L := by dsimp [L]; positivity
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (z : Vec) (hz : z∈ball (0:Vec) R \ ball (0:Vec) ε) :
      ‖sourceDivisionBulk P s t x e i z‖≤L/‖z‖^2 := by
    have hzr : ‖z‖<R ∧ ε≤‖z‖ := by simpa only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hε.trans_le hzr.2)
    have hzpos : 0<‖z‖ := norm_pos_iff.mpr hzn
    have hrad : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
      rw [hrad]
      exact ⟨by linarith,by linarith [norm_nonneg z]⟩
    let n : Sphere := ⟨‖z‖⁻¹ • z,by
      simp only [mem_sphere,dist_zero_right,norm_smul,norm_inv,norm_norm,
        inv_mul_cancel₀ hzpos.ne']⟩
    have hn : ‖z‖ • (n.1 : Vec)=z := by simp only [n,smul_smul,mul_inv_cancel₀ hzpos.ne',one_smul]
    have hs (v : Vec) (hv : ‖v‖≤P) :
        |divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z|≤
        3*Ks/‖z‖^2+(3*Ks/‖z‖)*Q := by
      have hh := hks s t ‖z‖ x v n hE hB hzpos (hzr.1.trans hRt) hv
      rw [hn] at hh
      apply (hh (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2).trans
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (max_le (hDF _ hu _).1 (hDF _ hu _).2) (by positivity))
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v))
      (C:=A*((3*Ks+(3*Ks*Q+Kv)*H)/‖z‖^2)) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        have hvP : ‖v‖≤P := by simpa only [mem_closedBall,dist_zero_right] using hv
        have hvb := hkv s t x z v hzn hvP (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
        rw [hrad] at hvb
        rw [Real.norm_eq_abs,abs_mul]
        apply mul_le_mul (hf _ ⟨hu.1.le,hu.2⟩ _ v) _ (abs_nonneg _) hA
        exact ((abs_add_le _ _).trans (add_le_add (hs v hvP) hvb)).trans
          (inverse_source_majorant (by positivity) hKv hQ hzpos (hzr.1.le.trans (hRt.le.trans (htU.trans hUH)))))
    exact hh.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ,L,V]; ring)
  have hh := norm_integral_annulus_inverse_sq_le hε hεR hL hb
  rw [Real.norm_eq_abs] at hh
  apply hh.trans
  calc
    4*Real.pi*L*R ≤ 4*Real.pi*L*H := by gcongr; exact hRt.le.trans (htU.trans hUH)
    _ ≤ C*(H+H^2*(1+Q)) := by
      dsimp [L,C]
      have hcoef : 3*Ks+(3*Ks*Q+Kv)*H≤(3*Ks+Kv)*(1+H*(1+Q)) := by
        nlinarith [mul_nonneg hKs hH,mul_nonneg (mul_nonneg hKv hH) hQ]
      have hh' := mul_le_mul_of_nonneg_left hcoef (show 0≤4*Real.pi*V*H by positivity)
      nlinarith

lemma source_sphere_support {s : Solution} {t U P r : ℝ} (x e : Vec) (i : Fin 3)
    (hr : 0≤r) (hrt : r≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ n : Sphere,r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) •
      (sourceConeCoefficient s t x i (r • n.1,v) • coneSpatialLift 0 (r • n.1) v e)) ∂sphereMeasure) =
    (∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) •
      sourceFixedFlux v (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) ∂sphereMeasure) := by
  apply integral_congr_ae
  apply ae_of_all
  intro n
  have hrad : coneRadius 0 (r • n.1)=r := by
    simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one]
  simp only [sourceConeCoefficient,hrad]
  change r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
      (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1))=_
  congr 2
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  rw [hP _ ⟨by linarith,by linarith⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_smul]

lemma source_bulk_support {s : Solution} {t U P ε R : ℝ} (x e : Vec) (i : Fin 3)
    (hRt : R≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,∫ v,s.f (t-coneRadius 0 z,x+z,v)*
      (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
        divergence (fun w => sourceConeCoefficient s t x i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)) =
    ∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z := by
  apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
  intro z hz
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    have hzR : ‖z‖<R := by simpa only [mem_ball,dist_zero_right] using hz.1
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  rw [hP _ hu _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_mul]

lemma electric_source_annulus_gradient_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H Q ε R : ℝ) (x : Vec),
      0≤H → 0≤Q → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        C*(H+H^2*(1+Q)) := by
  obtain ⟨C,hC,hb⟩ := source_division_bulk_annulus_bound P A M e i hA
  obtain ⟨B,hB,hbd⟩ := source_sphere_boundary_bound P M A e i hA
  refine ⟨C+2*B,by positivity,?_⟩
  intro s U t H Q ε R x hH hQ hε hεR hRt htU hUH hf hE hB' hc heq hfA hfP hEB hDF
  have hid := electric_source_division_annulus hf hE hB' hc heq htU hε hεR hRt x e i
  rw [hid,source_sphere_support x e i (hε.le.trans hεR) hRt.le htU hfP,
    source_sphere_support x e i hε.le (hεR.trans hRt.le) htU hfP,
    source_bulk_support x e i hRt.le htU hfP]
  have hout := hbd s t U R x (hε.trans_le hεR) hRt.le htU hfA hEB
  have hin := hbd s t U ε x hε (hεR.trans hRt.le) htU hfA hEB
  have hbulk := hb s U t H Q ε R x hH hQ hε hεR hRt htU hUH hE hB' hfA hEB hDF
  apply (abs_sub _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add hout hin)) hbulk).trans
  have hRH : R≤H := hRt.le.trans (htU.trans hUH)
  have heH : ε≤H := hεR.trans hRH
  have hnon : 0≤H^2*(1+Q) := by positivity
  have hBR : B*R≤B*H := mul_le_mul_of_nonneg_left hRH hB
  have hBe : B*ε≤B*H := mul_le_mul_of_nonneg_left heH hB
  have hBN : 0≤B*(H^2*(1+Q)) := mul_nonneg hB hnon
  nlinarith

lemma sourceConeCoefficient_uniform_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |sourceConeCoefficient s t x i (z,v)|≤C/‖z‖ := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (sourceAngularProfile i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact (sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s t x z v hz hv hE hB
  have hb := hC ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v) (by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
    · simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB
    · simpa only [mem_closedBall,dist_zero_right] using hv)
  unfold sourceConeCoefficient sourceFixedCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _))
    (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma source_particle_derivative_integrable {s : Solution} {U t P M N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => sourceConeCoefficient s t x i p*
    fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0)
  let A := ball (0:Vec) t \ ({0} : Set Vec)
  have hzprop {z : Vec} (hz : z∈A) : z≠0 ∧ 0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hzr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact ⟨hz.2,by simpa [coneRadius] using sub_pos.mpr hzr,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-z)]⟩
  have hfc : ContinuousOn F (A ×ˢ univ) := by
    intro p hp
    have hh := hzprop hp.1
    have hr := (contDiffAt_coneRadius (k:=1) hh.1.symm).comp p contDiffAt_fst
    have hm : ContinuousAt (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2)) p :=
      ((contDiffAt_const.sub hr).prodMk ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd)).continuousAt
    have hdf : ContinuousAt (fun q : Phase => fderiv ℝ s.f (t-coneRadius 0 q.1,x+q.1,q.2)) p :=
      ((particle_contDiffAt_positive hf hh.2.1 (x+p.1) p.2).continuousAt_fderiv (by simp)).comp (f:=fun q : Phase => (t-coneRadius 0 q.1,x+q.1,q.2)) hm
    exact ((sourceConeCoefficient_contDiffAt hE hB x i hh.1 hh.2.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := sourceConeCoefficient_uniform_bound P M i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_one]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb s t x z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv)
        (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).1 (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).2)
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma electric_source_particle_gradient_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H Q N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤Q → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤C*(H+H^2*(1+Q)) := by
  obtain ⟨C,hC,hb⟩ := electric_source_annulus_gradient_bound P A M e i hA
  refine ⟨C,hC,?_⟩
  intro s U t H Q N x ht htU hUH hQ hN hf hE hB hc heq hfA hP hEB hDF hfN
  apply norm_integral_ball_of_annulus_bound ht
    (source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN)
  intro ε R hε hεR hRt
  exact hb s U t H Q ε R x (ht.le.trans (htU.trans hUH)) hQ hε hεR hRt htU hUH
    hf hE hB hc heq hfA hP hEB hDF

lemma sourceAngularProfile_derivative_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖fderiv ℝ (sourceAngularProfile i) ((n.1,E,B),v)‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fderiv ℝ (sourceAngularProfile i)) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact ((sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

def sourceReceiverKernel (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceConeCoefficient s t p.1 i p.2

lemma sourceReceiverKernel_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceReceiverKernel s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hn := (contDiffAt_coneDirection (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_fst.add contDiffAt_snd.fst)
  have he := (field_contDiffAt_positive hE ht (p.1+p.2.1)).comp p hm
  have hb := (field_contDiffAt_positive hB ht (p.1+p.2.1)).comp p hm
  have hprof := (sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 p.2.1,s.E (t-coneRadius 0 p.2.1,p.1+p.2.1),s.B (t-coneRadius 0 p.2.1,p.1+p.2.1)),p.2.2))
    (cone_denom_pos p.2.2 _ (coneDirection_norm hz.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd.snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hprof

lemma source_receiver_fderiv_formula {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e =
      (coneRadius 0 z)⁻¹*fderiv ℝ (sourceAngularProfile i)
        ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v)
        ((0,fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),0) := by
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk ((hasFDerivAt_id (𝕜:=ℝ) x).add_const z)
  have he := ((field_contDiffAt_positive hE ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hb := ((field_contDiffAt_positive hB ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hp := ((sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).hasFDerivAt.comp x
      (((hasFDerivAt_const (coneDirection 0 z) x).prodMk (he.prodMk hb)).prodMk (hasFDerivAt_const v x))
  have hh := hp.const_mul ((coneRadius 0 z)⁻¹)
  change HasFDerivAt (fun y => sourceConeCoefficient s t y i (z,v)) _ x at hh
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma physical_source_receiver_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v e : Vec),
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      z≠0 → 0<t-coneRadius 0 z → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e|≤
        C/‖z‖*max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖
          ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖*‖e‖ := by
  obtain ⟨C,hC,hcb⟩ := sourceAngularProfile_derivative_bound P M i
  refine ⟨C,hC,?_⟩
  intro s t x z v e hE hB hz ht hv he hb
  rw [source_receiver_fderiv_formula x z v e i hE hB hz ht,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))]
  let Q := max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖
  have hQ : 0≤Q := (norm_nonneg _).trans (le_max_left _ _)
  have he' : ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_left ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ _) (norm_nonneg ((0:ℝ),e)))
  have hb' : ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_right _ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖) (norm_nonneg ((0:ℝ),e)))
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  have hd := hcb ⟨coneDirection 0 z,hn⟩ v _ _ hv he hb
  have harg : ‖(((0:Vec),fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),
      fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),(0:Vec))‖≤Q*‖e‖ := by
    simp only [Prod.norm_mk,norm_zero]
    exact max_le (max_le (by positivity) (max_le he' hb')) (by positivity)
  have hh := (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hd harg (norm_nonneg _) hC)
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg,Q]
  ring

def sourceWeightedPacket (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceReceiverKernel s t i p*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

lemma sourceWeightedPacket_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p :=
    (contDiffAt_const.sub hr).prodMk ((contDiffAt_fst.add contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  exact (sourceReceiverKernel_contDiffAt i hE hB hz ht).mul
    ((particle_contDiffAt_positive hf ht (p.1+p.2.1) p.2.2).comp p hm)

lemma sourceWeightedPacket_fderiv {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)=
      fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)*s.f (t-coneRadius 0 z,x+z,v)+
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
  have hk := (sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  have hF := (sourceWeightedPacket_contDiffAt i hf hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  rw [←retarded_packet_spatial_fderiv hF e,←retarded_packet_spatial_fderiv hk e]
  have hkp := hk.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk
    (((hasFDerivAt_id (𝕜:=ℝ) x).add_const z).prodMk (hasFDerivAt_const v x))
  have hfp := (particle_differentiableAt_positive hf ht (x+z) v).hasFDerivAt.comp x hm
  have hh := hkp.mul hfp
  change HasFDerivAt (fun y => sourceWeightedPacket s t i (y,z,v)) _ x at hh
  change HasFDerivAt (fun y => sourceReceiverKernel s t i (y,z,v)) _ x at hkp
  rw [hh.fderiv,hkp.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    zero_apply,smul_eq_mul,Function.comp_apply,id_eq,sourceReceiverKernel]
  ring

lemma source_packet_estimates (P A M N Q : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (s : Solution) (U t : ℝ), t≤U →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceWeightedPacket s t i (x,z,v)|≤C/‖z‖ ∧
      |fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)|≤D/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  obtain ⟨L,hL,hlb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*A,L*Q*‖e‖*A+K*N*‖e‖,by positivity,by positivity,?_⟩
  intro s U t htU hf hE hB hfA hEB hDF hfN x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    have hr : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    rw [hr]
    constructor <;> linarith [norm_nonneg z]
  have hc := hkb s t x z v hz hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd := hlb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤L/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  have hfd : |fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤N*‖e‖ := by
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hu.1 _ _) e]
    exact (ContinuousLinearMap.le_opNorm _ e).trans
      (mul_le_mul_of_nonneg_right (hfN _ ⟨hu.1.le,hu.2⟩ _ v) (norm_nonneg e))
  constructor
  · change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul hc (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz hu.1]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact (add_le_add (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity))
      (mul_le_mul hc hfd (abs_nonneg _) (by positivity))).trans_eq (by ring)

lemma hasDerivAt_electric_source_integral {s : Solution} {U t P A M N Q : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ) (htU : t≤U)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hDF : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
      sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ (sourceWeightedPacket s t i) (x+a • e,z,v) (e,0,0)) a := by
  obtain ⟨C,D,hC,hD,hb⟩ := source_packet_estimates P A M N Q e i hA hN hQ
  have hbc := hb s U t htU hf hE hB hfA hEB hDF hfN
  apply hasDerivAt_retarded_packet_integral (F:=sourceWeightedPacket s t i) (P:=P) (C:=C) (D:=D) ?_ ?_
    (fun x z v hz hzt hv => (hbc x z v hz hzt hv).1) x e a (fun x z v hz hzt hv => (hbc x z v hz hzt hv).2)
  · intro p hp ht
    apply sourceWeightedPacket_contDiffAt i hf hE hB hp
    simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  · intro x z v hz hzt hv
    have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
      simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
      constructor <;> linarith [norm_nonneg z]
    simp only [sourceWeightedPacket,hP _ hu _ v hv,mul_zero]

lemma retarded_packet_inner_integrable {F : Vec × Phase → ℝ} {t P : ℝ}
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) : Integrable (fun v => F (x,z,v)) := by
  have hcont : Continuous (fun v => F (x,z,v)) := continuous_iff_continuousAt.mpr (fun v =>
    (hc (x,z,v) hz0 hzt).comp (f:=fun w : Vec => (x,z,w)) (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0:Vec) P)
    (fun v hv => hz x z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)))

lemma norm_integral_ball_inverse_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t C : ℝ} (ht : 0≤t)
    (hb : ∀ z : Vec,z≠0 → ‖z‖<t → ‖F z‖≤C/‖z‖) :
    ‖∫ z in ball (0:Vec) t,F z‖≤2*Real.pi*C*t^2 := by
  have hh := norm_integral_le_of_norm_le ((integrableOn_norm_rpow_neg (R:=t) (show (1:ℝ)<3 by norm_num)).const_mul C) (f:=F) (by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv] using
      hb z hz0 (by simpa only [mem_ball,dist_zero_right] using hz))
  rw [integral_const_mul,integral_ball_norm_rpow_neg (show (1:ℝ)<3 by norm_num) ht] at hh
  norm_num only [show (3:ℝ)-1=2 by norm_num,Real.rpow_two] at hh
  exact hh.trans_eq (by ring)

def sourceReceiverParticlePacket (s : Solution) (t : ℝ) (e : Vec) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  fderiv ℝ (sourceReceiverKernel s t i) p (e,0,0)*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

lemma sourceReceiverParticlePacket_continuousAt {s : Solution} {t : ℝ} (e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : ‖p.2.1‖<t) :
    ContinuousAt (sourceReceiverParticlePacket s t e i) p := by
  have hu : 0<t-coneRadius 0 p.2.1 := by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  have hm : ContinuousAt (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p := (continuousAt_const.sub ((contDiffAt_coneRadius (k:=1) hz.symm).continuousAt.comp (f:=fun q : Vec × Phase => q.2.1) continuousAt_snd.fst)).prodMk
    ((continuousAt_fst.add continuousAt_snd.fst).prodMk continuousAt_snd.snd)
  exact (((sourceReceiverKernel_contDiffAt i hE hB hz hu).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).mul
    ((particle_contDiffAt_positive hf hu (p.1+p.2.1) p.2.2).continuousAt.comp (f:=fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) hm)

lemma source_receiver_packet_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t Q : ℝ),t≤U → 0≤Q →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*Q/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t Q htU hQ hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by ring))

lemma electric_source_receiver_integral_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t Q : ℝ) (x : Vec),0≤t → t≤U → 0≤Q →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      |∫ z in ball (0:Vec) t,∫ v,sourceReceiverParticlePacket s t e i (x,z,v)|≤C*Q*t^2 := by
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨2*Real.pi*volume.real (closedBall (0:Vec) P)*K,by positivity,?_⟩
  intro s U t Q x ht htU hQ hE hB hfA hP hEB hDF
  rw [←Real.norm_eq_abs]
  apply (norm_integral_ball_inverse_le ht (C:=volume.real (closedBall (0:Vec) P)*K*Q) ?_).trans_eq (by ring)
  intro z hz hzt
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  have hh := norm_velocity_integral_bound (P:=P) (g:=fun v => sourceReceiverParticlePacket s t e i (x,z,v))
    (fun v hv => by simp only [sourceReceiverParticlePacket,hP _ hu _ v hv,mul_zero])
    (hkb s U t Q htU hQ hE hB hfA hEB hDF x z · hz hzt)
  exact hh.trans_eq (by ring)

lemma electric_source_deriv_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H Q N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤Q → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
        sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        C*(H+H^2*(1+Q)) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := electric_source_particle_gradient_bound P A M e i hA
  obtain ⟨C₂,hC₂,hb₂⟩ := electric_source_receiver_integral_bound P A M e i hA
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro s U t H Q N x ht htU hUH hQ hN hf hE hB hc heq hfA hP hEB hDF hfN
  have hH : 0≤H := ht.le.trans (htU.trans hUH)
  have hprop (z : Vec) (hz : ‖z‖<t) : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  let R := sourceReceiverParticlePacket s t e i
  let F := fun p : Vec × Phase => fderiv ℝ (sourceWeightedPacket s t i) p (e,0,0)
  have hRc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt R p :=
    fun p hp hpt => sourceReceiverParticlePacket_continuousAt e i hf hE hB hp hpt
  have hRz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → R (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [R,sourceReceiverParticlePacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hweighted : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p :=
    fun p hp hpt => sourceWeightedPacket_contDiffAt i hf hE hB hp (hprop p.2.1 hpt).1
  have hWz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → sourceWeightedPacket s t i (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hFc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p := by
    intro p hp hpt
    exact ((hweighted p hp hpt).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hFz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0 :=
    fun x z v hz hzt hv => retarded_packet_derivative_zero hweighted hWz x z v e hz hzt hv
  have hRi := retarded_packet_integrable x hRc hRz (hkb s U t Q htU hQ hE hB hfA hEB hDF)
  have hPi := source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN
  have hsplit : (∫ z in ball (0:Vec) t,∫ v,F (x,z,v))=
      (∫ z in ball (0:Vec) t,∫ v,R (x,z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) := by
    rw [←integral_add hRi hPi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    have hFi := retarded_packet_inner_integrable hFc hFz x z hz0 hzt
    have hRi' := retarded_packet_inner_integrable hRc hRz x z hz0 hzt
    have hh : (∫ v,F (x,z,v))-(∫ v,R (x,z,v))=
        ∫ v,sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
      rw [←integral_sub hFi hRi']
      apply integral_congr_ae
      exact ae_of_all _ (fun v => by
        dsimp [F,R,sourceReceiverParticlePacket]
        rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz0 (hprop z hzt).1]
        ring)
    linarith
  rw [(hasDerivAt_electric_source_integral x e i 0 htU hf hE hB hA hN hQ hP hfA hEB hDF hfN).deriv]
  simp only [zero_smul,add_zero]
  change |∫ z in ball (0:Vec) t,∫ v,F (x,z,v)|≤_
  rw [hsplit]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hb₂ s U t Q x ht.le htU hQ hE hB hfA hP hEB hDF)
    (hb₁ s U t H Q N x ht htU hUH hQ hN hf hE hB hc heq hfA hP hEB hDF hfN)).trans
  have htH : t^2≤H^2 := by nlinarith [htU.trans hUH]
  have hh : C₂*Q*t^2≤C₂*(H+H^2*(1+Q)) := by
    calc
      _ ≤ C₂*Q*H^2 := mul_le_mul_of_nonneg_left htH (mul_nonneg hC₂ hQ)
      _ ≤ _ := by nlinarith [mul_nonneg hC₂ hH,mul_nonneg hC₂ (sq_nonneg H)]
  nlinarith

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma contDiffAt_sourceAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u b : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z) (hb : ContDiffAt ℝ k b z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => sourceAngularCore (n w) (u w) (b w)) z := by
  exact contDiff_cross.contDiffAt.comp z (hn.prodMk (RVM.contDiffAt_sourceAngularCore hn hu hb hd))

def sourceAngularProfile (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : ℝ :=
  sourceAngularCore p.1.1 (velocity p.2)
    (fderiv ℝ velocity p.2 (p.1.2.1+cross (velocity p.2) p.1.2.2)) i

lemma sourceAngularProfile_contDiffAt (i : Fin 3) {p : (Vec × Vec × Vec) × Vec}
    (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (sourceAngularProfile i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  have hdv : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => fderiv ℝ velocity z.2) p :=
    ((contDiff_velocity (k:=2)).fderiv_right (by norm_num)).contDiffAt.comp p contDiffAt_snd
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p
    (contDiffAt_sourceAngularCore hn hu (hdv.clm_apply hforce) hd)

def sourceFixedCoefficient (v E B : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  (coneRadius 0 z)⁻¹*sourceAngularProfile i ((coneDirection 0 z,E,B),v)

def sourceFixedFlux (v E B e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  sourceFixedCoefficient v E B i z • coneSpatialLift 0 z v e

lemma sourceFixedCoefficient_contDiffAt (v E B : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (sourceFixedCoefficient v E B i) z := by
  have hn := contDiffAt_coneDirection (k:=1) hz.symm
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 z,E,B),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').comp z
      ((hn.prodMk (contDiffAt_const.prodMk contDiffAt_const)).prodMk contDiffAt_const)
  exact ((contDiffAt_coneRadius hz.symm).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hc

lemma sourceFixedFlux_contDiffAt (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (sourceFixedFlux v E B e i) z :=
  (sourceFixedCoefficient_contDiffAt v E B i hz).smul (contDiffAt_coneSpatialLift hz.symm)

lemma sourceFixedFlux_homogeneous (v E B e : Vec) (i : Fin 3) {r : ℝ} (hr : 0<r) (z : Vec) :
    sourceFixedFlux v E B e i (r • z)=r⁻¹ • sourceFixedFlux v E B e i z := by
  simp only [sourceFixedFlux,sourceFixedCoefficient,coneSpatialLift,coneSpatialCoefficient,
    coneRadius_zero_smul hr,coneDirection_zero_smul hr,smul_smul]
  congr 1
  field_simp

lemma fderiv_degree_neg_one {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=r⁻¹ • F z)
    {r : ℝ} (hr : 0<r) {z : Vec}
    (hz : DifferentiableAt ℝ F z) (hrz : DifferentiableAt ℝ F (r • z)) (e : Vec) :
    fderiv ℝ F (r • z) e=(r^2)⁻¹ • fderiv ℝ F z e := by
  have hm : HasFDerivAt (fun y : Vec => r • y) (r • ContinuousLinearMap.id ℝ Vec) z :=
    (hasFDerivAt_id z).const_smul r
  have h₁ := hrz.hasFDerivAt.comp z hm
  have h₂ := hz.hasFDerivAt.const_smul r⁻¹
  have heq : (fun y : Vec => F (r • y))=(fun y : Vec => r⁻¹ • F y) := funext (hh r hr)
  change HasFDerivAt (fun y : Vec => F (r • y)) _ _ at h₁
  rw [heq] at h₁
  have hv := congrArg (fun L : Vec →L[ℝ] Vec => L e) (h₁.unique h₂)
  change fderiv ℝ F (r • z) (r • e)=r⁻¹ • fderiv ℝ F z e at hv
  rw [map_smul] at hv
  have hv' := congrArg (fun a : Vec => r⁻¹ • a) hv
  simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
    show r⁻¹*r⁻¹=(r^2)⁻¹ by ring] using hv'

lemma divergence_degree_neg_one {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=r⁻¹ • F z)
    (hF : ∀ z≠0, DifferentiableAt ℝ F z) {r : ℝ} (hr : 0<r) {z : Vec} (hz : z≠0) :
    divergence F (r • z)=(r^2)⁻¹*divergence F z := by
  have hrz : r • z≠0 := smul_ne_zero hr.ne' hz
  have hc (y : Vec) (hy : y≠0) (i : Fin 3) :
      fderiv ℝ (fun x => F x i) y = (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y) := by
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y (hF y hy).hasFDerivAt).fderiv
  unfold divergence spatialPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc _ hrz i,hc _ hz i]
  change (fderiv ℝ F (r • z) (basis i)) i = (r^2)⁻¹*(fderiv ℝ F z (basis i)) i
  rw [fderiv_degree_neg_one hh hr (hF _ hz) (hF _ hrz)]
  rfl

def sourceConeCoefficient (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (p : Phase) : ℝ :=
  sourceFixedCoefficient p.2 (s.E (t-coneRadius 0 p.1,x+p.1))
    (s.B (t-coneRadius 0 p.1,x+p.1)) i p.1

lemma sourceConeCoefficient_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) (i : Fin 3) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (sourceConeCoefficient s t x i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hp.symm).comp p contDiffAt_fst
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 p.1,
      s.E (t-coneRadius 0 p.1,x+p.1),s.B (t-coneRadius 0 p.1,x+p.1)),p.2))
    (cone_denom_pos p.2 _ (coneDirection_norm hp.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))).mul hc

lemma magnetic_source_division_annulus {s : Solution} {H t ε R : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (heq : EquationsBefore s H)
    (htH : t≤H) (hε : 0<ε) (hεR : ε≤R) (hRt : R<t) (x e : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, s.f (t-R,x+R • n.1,v) •
        (sourceConeCoefficient s t x i (R • n.1,v) • coneSpatialLift 0 (R • n.1) v e)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, s.f (t-ε,x+ε • n.1,v) •
        (sourceConeCoefficient s t x i (ε • n.1,v) • coneSpatialLift 0 (ε • n.1) v e)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v) := by
  have hk : ContDiffOn ℝ 1 (sourceConeCoefficient s t x i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (sourceConeCoefficient_contDiffAt hE hB x i hp.1.1.symm hp.1.2).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  simpa only [smul_smul] using retarded_spatial_annulus (e:=e) hf hc hε hεR hRt hk hK
    (fun z hz v => coneLorentz_vlasov_before hf heq htH x hz v)

end RVM.Magnetic

end

end OAI
