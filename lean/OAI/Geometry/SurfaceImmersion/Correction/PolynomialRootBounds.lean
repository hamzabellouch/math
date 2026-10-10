import OAI.Geometry.SurfaceImmersion.Atlas.WeightedInverseSqrt
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedRealAlgebra
import OAI.Geometry.Immersion.ClosedSurface.RootMean

namespace OAI

/-! Explicit square-root and square-root-difference bounds from a reciprocal
positivity margin, without a compact-set derivative constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqrtBudget (m : ℕ) (D B : ℝ) : ℝ :=
  2^m*B*((m.factorial : ℝ)*D*B^(m+1)*B^m)

def rootDifferenceBudget (m : ℕ) (D B : ℝ) : ℝ :=
  2^m*((m.factorial : ℝ)^2*B^(m+1)*(1+2*sqrtBudget m D B)^m)

lemma sqrtBudget_nonneg (m : ℕ) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ sqrtBudget m D B := by unfold sqrtBudget; positivity

lemma inverse_sqrt_le {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B) (hi : x⁻¹ ≤ B) :
    (Real.sqrt x)⁻¹ ≤ B := by
  have hh := inverse_half_power_bound hx hB hi (j := 0) (m := 0) (Nat.le_refl 0)
  have he : x^(-1/2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow,show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hx.le]
  simpa only [Nat.cast_zero,Nat.zero_add,sub_zero,pow_one,he] using hh

theorem polynomial_sqrt_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ B →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → WeightedBound U s m B f →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) := by
  obtain ⟨D,hD,hbound⟩ := weighted_inverse_sqrt (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B f hs hB hf hp hi hb
  have hr := hf.sqrt (fun x hx => (hp x hx).ne')
  have hi' := hr.inv (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')
  have hh := hb.mul_real hU hs.le (zero_le_one.trans hB) (by positivity)
    hf hi' (hbound hU hs hB hB hf hp hi hb)
  apply hh.congr
  intro x hx
  change Real.sqrt (f x) = f x*(Real.sqrt (f x))⁻¹
  rw [← div_eq_mul_inv,eq_div_iff (Real.sqrt_pos.mpr (hp x hx)).ne']
  exact Real.mul_self_sqrt (hp x hx).le

theorem polynomial_root_bounds (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B A : ℝ} {f g : E → ℝ}, 0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) ∧
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (g x)) ∧
      WeightedBound U s m (rootDifferenceBudget m D B*A)
        (fun x => Real.sqrt (f x)-Real.sqrt (g x)) := by
  obtain ⟨D,hD,hr⟩ := polynomial_sqrt_bound (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B A f g hs hB hA hf hg hfp hgp hfi hgi hfb hgb hdiff
  have hrf := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hrg := hg.sqrt (fun x hx => (hgp x hx).ne')
  have bF := hr hU hs hB hf hfp hfi hfb
  have bG := hr hU hs hB hg hgp hgi hgb
  have hS : 0 ≤ sqrtBudget m D B := sqrtBudget_nonneg m (zero_le_one.trans hD) (zero_le_one.trans hB)
  have hsum := bF.add hU hs.le hrf hrg bG
  have hsum' : WeightedBound U s m (1+2*sqrtBudget m D B)
      (fun x => Real.sqrt (f x)+Real.sqrt (g x)) := hsum.mono_const (by linarith)
  have hpos (x : E) (hx : x ∈ U) : 0 < Real.sqrt (f x)+Real.sqrt (g x) :=
    add_pos (Real.sqrt_pos.mpr (hfp x hx)) (Real.sqrt_pos.mpr (hgp x hx))
  have hinv (x : E) (hx : x ∈ U) :
      ‖(Real.sqrt (f x)+Real.sqrt (g x))⁻¹‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos x hx))]
    exact ((inv_le_inv₀ (hpos x hx) (Real.sqrt_pos.mpr (hfp x hx))).mpr
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))).trans (inverse_sqrt_le (hfp x hx) hB (hfi x hx))
  have bInv := hsum'.inv_real hU hs (by linarith) hB (hrf.add hrg)
    (fun x hx => (hpos x hx).ne') hinv
  have hsmoothInv := (hrf.add hrg).inv (fun x hx => (hpos x hx).ne')
  have hh := hdiff.mul_real hU hs.le hA (by positivity) (hf.sub hg) hsmoothInv bInv
  refine ⟨bF,bG,?_⟩
  have hh' : WeightedBound U s m (rootDifferenceBudget m D B*A)
      (fun x => (f x-g x)*(Real.sqrt (f x)+Real.sqrt (g x))⁻¹) := by
    convert hh using 1
    unfold rootDifferenceBudget
    ring
  apply hh'.congr
  intro x hx
  exact sqrt_difference (hfp x hx) (hgp x hx)

end ClosedSurfaceR4.RootMean

end

end OAI
