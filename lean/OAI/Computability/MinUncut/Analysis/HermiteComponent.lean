import Mathlib
import OAI.Computability.MinUncut.Analysis.OddAtom
import OAI.Computability.MinUncut.Estimates.IntegralExpect

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
local instance hermiteComponentDualFintype {U : Type*}
    [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [DecidableEq R] [Fintype W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

lemma memLp_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) :
    MemLp (fun x => 𝔼 t, f t x) 2 μ := by
  simp only [Finset.expect_eq_sum_div_card, div_eq_mul_inv]
  exact (memLp_finsetSum _ (fun t _ => hf t)).mul_const _

lemma memLp_rowCoefficient (r : R) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (α : Module.Dual F₂ W) (D : Rest (W := W) r) :
    MemLp (fun c => rowCoefficient r (fun B => u B c) α D) 2 (γpi ι) := by
  exact memLp_expect _ (fun b => (hu (joinRow r b D)).mul_const _)

lemma memLp_oddAtom (r : R) (one : W) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (D : Rest (W := W) r) :
    MemLp (fun c => oddAtom r one (fun B => u B c) D) 2 (γpi ι) := by
  let fs : Module.Dual F₂ W → (ι → ℝ) → ℝ := fun α c =>
    if α one=1 then |rowCoefficient r (fun B => u B c) α D| else 0
  have hfs (α : Module.Dual F₂ W) : MemLp (fs α) 2 (γpi ι) := by
    by_cases h : α one=1
    · simpa [fs, h, ← Real.norm_eq_abs] using (memLp_rowCoefficient r u hu α D).norm
    · simp [fs, h]
  have hh : MemLp (Finset.univ.sup' Finset.univ_nonempty fs) 2 (γpi ι) :=
    Finset.sup'_induction (p := fun f => MemLp f 2 (γpi ι)) Finset.univ_nonempty fs (fun _ hf _ hg => hf.sup hg) (fun α _ => hfs α)
  convert hh using 1
  funext c
  simp only [Finset.sup'_apply, fs, oddAtom]

def hermiteComponent (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) : ℝ := psi I c * GaussianHermite.coeff (u B) I

lemma rowCoefficient_hermiteComponent (r : R) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι))
    (α : Module.Dual F₂ W) (D : Rest (W := W) r) (c : ι → ℝ) :
    rowCoefficient r (fun B => hermiteComponent I u B c) α D =
      psi I c * GaussianHermite.coeff (fun c' => rowCoefficient r (fun B => u B c') α D) I := by
  simp only [rowCoefficient, hermiteComponent, GaussianHermite.coeff, mul_assoc, ← Finset.mul_expect]
  congr 1
  simp_rw [← integral_mul_const]
  rw [← integral_expect]
  · congr 1
    funext c'
    simp only [mul_assoc, ← Finset.mul_expect]
  · intro b
    exact ((memLp_psi I).integrable_mul (hu (joinRow r b D))).mul_const _

lemma oddAtom_hermiteComponent (r : R) (one : W) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι))
    (D : Rest (W := W) r) (c : ι → ℝ) :
    oddAtom r one (fun B => hermiteComponent I u B c) D ≤
      |psi I c| * ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι := by
  apply oddAtom_le
  · exact mul_nonneg (abs_nonneg _) (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (oddAtom_nonneg _ _ _ _)))
  intro α hα
  rw [rowCoefficient_hermiteComponent r I u hu, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ∫ c', |psi I c' * rowCoefficient r (fun B => u B c') α D| ∂γpi ι := abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono
      · exact ((memLp_psi I).integrable_mul (memLp_rowCoefficient r u hu α D)).abs
      · exact (memLp_psi I).norm.integrable_mul (memLp_oddAtom r one u hu D)
      · intro c'
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (rowCoefficient_le_oddAtom _ _ _ α hα _) (abs_nonneg _)

lemma oddAtom_hermiteComponent_mean (r : R) (one : W) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι))
    (D : Rest (W := W) r) :
    (∫ c, oddAtom r one (fun B => hermiteComponent I u B c) D ∂γpi ι) ≤
      Real.sqrt (∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have ha := memLp_oddAtom r one u hu D
  have hh : ∀ B, MemLp (hermiteComponent I u B) 2 (γpi ι) := fun B =>
    (memLp_psi I).mul_const _
  have hc : 0 ≤ ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι :=
    integral_nonneg (fun c' => mul_nonneg (abs_nonneg _) (oddAtom_nonneg _ _ _ _))
  calc
    _ ≤ ∫ c, |psi I c| * ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι ∂γpi ι := by
      exact integral_mono ((memLp_oddAtom r one (hermiteComponent I u) hh D).integrable (by norm_num))
        (((memLp_psi I).integrable (by norm_num)).norm.mul_const _)
        (oddAtom_hermiteComponent r one I u hu D)
    _ = (∫ c, |psi I c| ∂γpi ι) * ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι := integral_mul_const _ _
    _ ≤ ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (psi_l1 I) hc
    _ ≤ _ := by
      have h := integral_norm_mul_le_sqrt (memLp_psi I) ha
      have hn : (∫ c, psi I c^2 ∂γpi ι)=1 := by simpa [sq] using psi_product I I
      simpa only [abs_of_nonneg (oddAtom_nonneg _ _ _ _), hn, Real.sqrt_one, one_mul] using h
end MinUncut.RowNoise

end

end OAI
