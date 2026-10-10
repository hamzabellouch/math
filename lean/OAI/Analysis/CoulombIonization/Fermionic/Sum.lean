import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Restriction

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
section Sum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι α : Type*} [Fintype ι] [Fintype α] {v : ι → E}

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
lemma lineDeriv_sumSquares (p : α → SmoothMultiplier v) (x d : E) :
    lineDeriv ℝ (fun y => ∑ i, (p i).value y ^ 2) x d =
      ∑ i, 2 * (p i).value x * lineDeriv ℝ (p i).value x d := by
  have hd (i : α) := ((p i).regular.differentiable (by simp) x).hasFDerivAt.pow 2
  have hh := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => hd i)).hasLineDerivAt d
  have he := hh.lineDeriv
  simp only [sum_apply, smul_apply, smul_eq_mul, Nat.reduceSub,
    pow_one, nsmul_eq_mul, Nat.cast_ofNat] at he
  convert he using 1
  · congr 1
    funext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl; intro i _
    rw [((p i).regular.differentiable (by simp) x).lineDeriv_eq_fderiv]

def SmoothMultiplier.sumSquares (p : α → SmoothMultiplier v) : SmoothMultiplier v where
  value := fun x => ∑ i, (p i).value x ^ 2
  regular := ContDiff.sum (fun i _ => (p i).regular.pow 2)
  bound := by
    choose C hC using fun i => (p i).bound
    refine ⟨∑ i, C i ^ 2, fun x => ?_⟩
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    apply Finset.sum_le_sum; intro i _
    exact (sq_le_sq₀ (abs_nonneg _) (le_trans (abs_nonneg _) (hC i x))).mpr (hC i x) |>
      fun h => by simpa only [sq_abs] using h
  gradient_bound := by
    intro j
    choose C hC using fun i => (p i).bound
    choose D hD using fun i => (p i).gradient_bound j
    refine ⟨∑ i, 2 * C i * D i, fun x => ?_⟩
    rw [lineDeriv_sumSquares]
    calc
      _ ≤ ∑ i, |2 * (p i).value x * lineDeriv ℝ (p i).value x (v j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i x) (by norm_num))
          (hD i x) (abs_nonneg _) (by linarith [abs_nonneg ((p i).value x), hC i x])

end Sum

def bindingTotalMultiplier {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    FermionMultiplier N where
  toSmoothMultiplier := SmoothMultiplier.sumSquares (bindingMultiplier hR hε)
  symmetric := by
    intro π x
    change (∑ i, bindingRoot R ε ((x ∘ π) i) ^ 2) = ∑ i, bindingRoot R ε (x i) ^ 2
    exact Equiv.sum_comp π (fun i => bindingRoot R ε (x i) ^ 2)

lemma bindingTotalMultiplier_value {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x : Configuration N) : (bindingTotalMultiplier hR hε).value x =
      ∑ i, bindingWeight R ε (x i) := by
  change (∑ i, bindingRoot R ε (x i) ^ 2) = _
  simp only [bindingRoot_sq hR hε]


open MeasureTheory Filter
open scoped Topology BigOperators

lemma l2_coe_finset_sum {X α : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset α) (f : α → Lp ℂ 2 μ) :
    ((∑ i ∈ s, f i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    exact hx
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    rw [hx, hy]

section Sum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι α : Type*} [Fintype ι] [Fintype α] {v : ι → E}

omit [Fintype ι] in
lemma SmoothMultiplier.sumSquares_apply (p : α → SmoothMultiplier v) (F : weakGraph v) :
    (SmoothMultiplier.sumSquares p).apply F = ∑ i, (p i).apply ((p i).apply F) := by
  apply weakGraphValue_injective v
  rw [map_sum]
  apply Lp.ext
  have ha : ∀ᵐ x : E, ∀ i : α,
      ((p i).apply ((p i).apply F)).val none x =
        ((p i).value x : ℂ) * ((p i).value x : ℂ) * F.val none x := by
    apply ae_all_iff.mpr; intro i
    filter_upwards [(p i).apply_value ((p i).apply F), (p i).apply_value F] with x hx hy
    rw [hx, hy, mul_assoc]
  filter_upwards [(SmoothMultiplier.sumSquares p).apply_value F, ha,
    l2_coe_finset_sum volume Finset.univ
      (fun i => weakGraphValue v ((p i).apply ((p i).apply F)))] with x hx hy hz
  change ((SmoothMultiplier.sumSquares p).apply F).val none x = _
  rw [hx, hz]
  change (((∑ i, (p i).value x ^ 2 : ℝ) : ℂ) * F.val none x) = _
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  change ((p i).value x : ℂ) ^ 2 * F.val none x =
    ((p i).apply ((p i).apply F)).val none x
  rw [hy i, pow_two]

omit [Fintype ι] in
lemma weakGraph_sum_component (G : α → weakGraph v) (k : Option ι) :
    (∑ i, G i).val k = ∑ i, (G i).val k := by
  rw [Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]

end Sum

lemma bindingTotalMultiplier_component {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    graphComponent s k ((bindingTotalMultiplier hR hε).apply F) =
      ∑ i, ((bindingMultiplier hR hε i).apply ((bindingMultiplier hR hε i).apply (F.val s))).val k := by
  change ((SmoothMultiplier.sumSquares (bindingMultiplier hR hε)).apply (F.val s)).val k = _
  rw [SmoothMultiplier.sumSquares_apply, weakGraph_sum_component]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
