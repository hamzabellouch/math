import Mathlib
import OAI.Analysis.AffineBernstein.SupportGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Homogeneous extension of an actual test function off the affine normal chart. -/
def flatNormalProjection (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (q : S × E) : F :=
  C ((q.1, (ℓ q.2)⁻¹ • q.2)-q₀)

def flatSupportVariation (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (η : F → ℝ) (q : S × E) : ℝ :=
  ℓ q.2 * η (flatNormalProjection ℓ q₀ C q)

def supportGradient (H : S × E → ℝ) (q : S × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fiberGradient H q)

omit [CompleteSpace E] in
lemma contDiffAt_flatNormalProjection (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {q : S × E} (hne : ℓ q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (flatNormalProjection ℓ q₀ C) q := by
  apply C.contDiff.contDiffAt.comp q
  exact (contDiffAt_fst.prodMk
    (((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd).inv hne).smul contDiffAt_snd)).sub contDiffAt_const

omit [CompleteSpace E] in
lemma contDiffAt_flatSupportVariation (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (flatSupportVariation ℓ q₀ C η) q := by
  exact (ℓ.contDiff.contDiffAt.comp q contDiffAt_snd).mul
    (hη.contDiffAt.comp q (contDiffAt_flatNormalProjection ℓ q₀ C hne))

lemma contDiffAt_supportGradient {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) : ContDiffAt ℝ ∞ (supportGradient H) q := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp q
    (contDiffAt_fiberGradient hH)

lemma supportGradient_angular {H : S × E → ℝ} {q : S × E}
    (hH : DifferentiableAt ℝ H q) (v : E) :
    fderiv ℝ H q (0,v) = inner ℝ (supportGradient H q) v := by
  have hd := hH.hasFDerivAt.comp (f := fun y : E => (q.1,y)) q.2
    ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))
  change _ = (InnerProductSpace.toDual ℝ E (supportGradient H q)) v
  simp only [supportGradient, LinearIsometryEquiv.apply_symm_apply]
  change _ = fderiv ℝ (fun y => H (q.1,y)) q.2 v
  exact (congrArg (fun A : E →L[ℝ] ℝ => A v) hd.fderiv).symm

omit [CompleteSpace E] in
lemma flatNormalProjection_smul (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (q : S × E) {t : ℝ} (ht : t ≠ 0) :
    flatNormalProjection ℓ q₀ C (q.1,t • q.2) = flatNormalProjection ℓ q₀ C q := by
  unfold flatNormalProjection
  congr 3
  simp only [map_smul,smul_eq_mul,mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ ht,mul_one]

omit [CompleteSpace E] in
lemma flatSupportVariation_smul (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (η : F → ℝ) (q : S × E) {t : ℝ} (ht : t ≠ 0) :
    flatSupportVariation ℓ q₀ C η (q.1,t • q.2) = t * flatSupportVariation ℓ q₀ C η q := by
  simp only [flatSupportVariation,flatNormalProjection_smul ℓ q₀ C q ht,map_smul,smul_eq_mul]
  ring

lemma flatSupportVariation_euler (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    flatSupportVariation ℓ q₀ C η q = inner ℝ q.2
      (supportGradient (flatSupportVariation ℓ q₀ C η) q) := by
  let G := flatSupportVariation ℓ q₀ C η
  have hG : DifferentiableAt ℝ G q :=
    (contDiffAt_flatSupportVariation ℓ q₀ C hη hne).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => (q.1,t • q.2)) (0,q.2) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) q.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const q.2)
  have hg : HasDerivAt (fun t : ℝ => G (q.1,t • q.2))
      (fderiv ℝ G q (0,q.2)) 1 := by
    have hG' : HasFDerivAt G (fderiv ℝ G q) (q.1, (1 : ℝ) • q.2) := by
      simpa using hG.hasFDerivAt
    exact hG'.comp_hasDerivAt 1 hp
  have he : (fun t : ℝ => G (q.1,t • q.2)) =ᶠ[𝓝 1] (fun t => t * G q) := by
    filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with t ht
    exact flatSupportVariation_smul ℓ q₀ C η q ht
  have hh := (hg.congr_of_eventuallyEq he.symm).unique ((hasDerivAt_id (1 : ℝ)).mul_const (G q))
  have hx := supportGradient_angular hG q.2
  rw [real_inner_comm]
  change G q = _
  simpa using hh.symm.trans hx

omit [CompleteSpace E] in
lemma flatNormalProjection_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (x : F) :
    flatNormalProjection ℓ q₀ C (q₀+J x) = x := by
  have hh : ℓ (q₀+J x).2 = 1 := by simp [hℓ,hJ]
  unfold flatNormalProjection
  rw [hh,inv_one,one_smul]
  change C ((q₀+J x)-q₀) = x
  simpa using hC x

omit [CompleteSpace E] in
lemma flatSupportVariation_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (η : F → ℝ) (x : F) :
    flatSupportVariation ℓ q₀ C η (q₀+J x) = η x := by
  simp [flatSupportVariation,flatNormalProjection_on_chart ℓ q₀ C J hℓ hJ hC,hℓ,hJ]

lemma supportGradient_flatVariation_eq_zero (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (η : F → ℝ) {x : F} (hx : x ∉ tsupport η) :
    supportGradient (flatSupportVariation ℓ q₀ C η) (q₀+J x) = 0 := by
  let q := q₀+J x
  have hq : ℓ q.2 = 1 := by simp [q,hℓ,hJ]
  have hp := (contDiffAt_flatNormalProjection ℓ q₀ C (by rw [hq]; norm_num)).continuousAt
  have heP := flatNormalProjection_on_chart ℓ q₀ C J hℓ hJ hC x
  have ht : Tendsto (flatNormalProjection ℓ q₀ C) (𝓝 q) (𝓝 x) := by
    simpa only [ContinuousAt,q,heP] using hp
  have heη : η =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have heG : flatSupportVariation ℓ q₀ C η =ᶠ[𝓝 q] (fun _ => 0) := by
    filter_upwards [ht.eventually heη] with y hy
    simp [flatSupportVariation,hy]
  have heF : (fun y => flatSupportVariation ℓ q₀ C η (q.1,y)) =ᶠ[𝓝 q.2] (fun _ => 0) :=
    heG.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  change (InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (fun y => flatSupportVariation ℓ q₀ C η (q.1,y)) q.2) = 0
  rw [heF.fderiv_eq]
  simp

lemma tsupport_flatSupportVelocity_subset (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (η : F → ℝ) :
    tsupport (fun x => ((0 : S),supportGradient (flatSupportVariation ℓ q₀ C η) (q₀+J x))) ⊆
      tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  have hh := supportGradient_flatVariation_eq_zero ℓ q₀ C J hℓ hJ hC η hn
  exact hx (by simp [hh])

lemma contDiff_flatSupportVelocity (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    {η : F → ℝ} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (fun x => ((0 : S),supportGradient (flatSupportVariation ℓ q₀ C η) (q₀+J x))) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hq : ℓ (q₀+J x).2 = 1 := by simp [hℓ,hJ]
  have hG := contDiffAt_flatSupportVariation ℓ q₀ C hη (by rw [hq]; norm_num)
  exact contDiffAt_const.prodMk ((contDiffAt_supportGradient hG).comp
    (f := fun x => q₀+J x) x (contDiffAt_const.add J.contDiff.contDiffAt))

end AffineBernstein
end

end OAI
