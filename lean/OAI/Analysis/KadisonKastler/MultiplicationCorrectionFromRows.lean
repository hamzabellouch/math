import OAI.Analysis.KadisonKastler.AsymptoticRowCochain
import OAI.Analysis.KadisonKastler.HaagerupSlices
import OAI.Analysis.KadisonKastler.MultiplicationCorrectionFromCochains
import OAI.Analysis.KadisonKastler.PublishedCorrection

namespace OAI

/-! # Multiplication correction from Christensen--Sinclair row averaging

A modular row limit supplies the cochain estimate for multiplication correction.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance correctionRowsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance correctionRowsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem finiteCochainModuleDefect_as_average {A : Type*} [CStarAlgebra A]
    {k : ℕ} (r : Fin k → A) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (a b : A) :
    finiteCochainModuleDefect r f a b =
      finiteRightAverage r (f a) b - finiteRightAverage r (f a) 1 * b := by
  change finiteRightAverage r (f a) b - finiteCochainAverage r f a * b = _
  simp only [finiteCochainAverage_apply, finiteRightAverage_apply, one_mul]

private theorem cochain_module_defect_tendsto (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ)
    (r : (i : ι) → Fin (n i) → Algebra M)
    (f : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M) {c : ℝ}
    (hc : 0 ≤ c) (hf : HaagerupBound f c)
    (hav : ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (c : ℝ), 0 ≤ c → CompletelyBoundedBy F c →
      ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun i => inner ℂ η ((finiteRightAverage (r i) F y : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ))))
    (a b : Algebra M) (ξ η : H) :
    Tendsto (fun i => inner ℂ η ((finiteCochainModuleDefect (r i) f a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 0) := by
  obtain ⟨z, hz⟩ := hav (f a) (c * ‖a‖) (mul_nonneg hc (norm_nonneg a))
    (hf.right_slice hc a)
  have h := (hz b ξ η).sub (hz 1 ((b : H →L[ℂ] H) ξ) η)
  simp_rw [finiteCochainModuleDefect_as_average]
  simpa only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, sub_apply,
    mul_apply_eq_comp, inner_sub_right, mul_one, sub_self] using h

theorem quadraticCochainSolver_of_modular_rows (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ)
    (r : (i : ι) → Fin (n i) → Algebra M)
    (hr : ∀ i, ∑ k, r i k * star (r i k) = 1)
    (hav : ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (c : ℝ), 0 ≤ c → CompletelyBoundedBy F c →
      ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun i => inner ℂ η ((finiteRightAverage (r i) F y : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ)))) :
    QuadraticCochainSolver (Algebra M) := by
  intro c hc _ m
  exact quadratic_cochain_of_asymptotic_rows M m.mul m.assoc m.star_mul hc m.bound ω n r hr
    (cochain_module_defect_tendsto M ω n r (m.mul - LinearMap.mul ℂ (Algebra M)) hc m.bound hav)

/-- A single modular row net suffices for quantitative multiplication correction. -/
theorem publishedMultiplicationCorrection_of_modular_rows (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ)
    (r : (i : ι) → Fin (n i) → Algebra M)
    (hr : ∀ i, ∑ k, r i k * star (r i k) = 1)
    (hav : ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (c : ℝ), 0 ≤ c → CompletelyBoundedBy F c →
      ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun i => inner ℂ η ((finiteRightAverage (r i) F y : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ)))) :
    PublishedMultiplicationCorrection M := by
  intro m hm hs c hc hc1 hf
  obtain ⟨L, hL, hLs, hLb⟩ := multiplication_correction_of_quadratic_cochains
    (quadraticCochainSolver_of_modular_rows M ω n r hr hav) m hm hs hc hc1 hf
  exact ⟨L, hL, hLs, hLb.mono (by linarith)⟩

end

end KadisonKastler

end OAI
