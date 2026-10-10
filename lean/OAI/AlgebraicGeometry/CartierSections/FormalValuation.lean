import OAI.AlgebraicGeometry.CartierSections.PolynomialValuation
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.PWO

namespace OAI

/-!
# Weighted valuations on formal power series

Dickson finiteness gives an exponent of least weight, even when some weights
vanish. Initial homogeneous series prove multiplicativity without requiring
a unique exponent of least weight.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections.FormalMonomial
section Ring
variable {σ k : Type*} [CommRing k]

/-- Literal coefficient-weight infimum of a formal power series. -/
def value (w : σ → ℝ≥0) (f : MvPowerSeries σ k) : ENNReal :=
  ⨅ (d : σ →₀ ℕ) (_ : MvPowerSeries.coeff d f ≠ 0), (Finsupp.weight w d : ENNReal)

lemma le_value_iff (w : σ → ℝ≥0) {f : MvPowerSeries σ k} {a : ENNReal} :
    a ≤ value w f ↔ ∀ d, MvPowerSeries.coeff d f ≠ 0 →
      a ≤ (Finsupp.weight w d : ENNReal) := by
  simp only [value, le_iInf_iff]

lemma value_le_weight (w : σ → ℝ≥0) {f : MvPowerSeries σ k} {d : σ →₀ ℕ}
    (hd : MvPowerSeries.coeff d f ≠ 0) : value w f ≤ (Finsupp.weight w d : ENNReal) :=
  (le_value_iff w).mp le_rfl d hd

/-- Dickson finiteness gives finitely many minimal exponent vectors. -/
lemma finite_dominated_generators [Fintype σ] (S : Set (σ →₀ ℕ)) :
    ∃ T : Finset (σ →₀ ℕ), (↑T : Set (σ →₀ ℕ)) ⊆ S ∧
      ∀ d ∈ S, ∃ e ∈ T, e ≤ d := by
  classical
  let M : Set (σ →₀ ℕ) := {e | Minimal (fun a => a ∈ S) e}
  have hM : M.Finite := by
    apply WellQuasiOrderedLE.finite_of_isAntichain
    intro a ha b hb hne hab
    exact hne (le_antisymm hab (hb.2 ha.1 hab))
  refine ⟨hM.toFinset, ?_, ?_⟩
  · intro e he
    exact (hM.mem_toFinset.mp he).1
  · intro d hd
    obtain ⟨e, hed, he⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hd
    exact ⟨e, hM.mem_toFinset.mpr he, hed⟩

lemma weight_mono (w : σ → ℝ≥0) : Monotone (Finsupp.weight w : (σ →₀ ℕ) →+ ℝ≥0) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := exists_add_of_le hab
  rw [map_add]
  exact le_add_of_nonneg_right bot_le

lemma exists_initial [Fintype σ] (w : σ → ℝ≥0) {f : MvPowerSeries σ k} (hf : f ≠ 0) :
    ∃ d, MvPowerSeries.coeff d f ≠ 0 ∧
      ∀ e, MvPowerSeries.coeff e f ≠ 0 → Finsupp.weight w d ≤ Finsupp.weight w e := by
  classical
  obtain ⟨e, he⟩ : ∃ e, MvPowerSeries.coeff e f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext d
    simpa using h d
  obtain ⟨T, hTS, hT⟩ := finite_dominated_generators {d | MvPowerSeries.coeff d f ≠ 0}
  obtain ⟨a, ha, hae⟩ := hT e he
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image T (Finsupp.weight w) ⟨a, ha⟩
  refine ⟨d, hTS hd, ?_⟩
  intro b hb
  obtain ⟨c, hc, hcb⟩ := hT b hb
  exact (hmin c hc).trans (weight_mono w hcb)

lemma value_eq_of_initial (w : σ → ℝ≥0) {f : MvPowerSeries σ k} {d : σ →₀ ℕ}
    (hd : MvPowerSeries.coeff d f ≠ 0)
    (hmin : ∀ e, MvPowerSeries.coeff e f ≠ 0 → Finsupp.weight w d ≤ Finsupp.weight w e) :
    value w f = (Finsupp.weight w d : ENNReal) := by
  apply le_antisymm (value_le_weight w hd)
  exact (le_value_iff w).mpr fun e he => ENNReal.coe_le_coe.mpr (hmin e he)

lemma value_attained [Fintype σ] (w : σ → ℝ≥0) {f : MvPowerSeries σ k} (hf : f ≠ 0) :
    ∃ d, MvPowerSeries.coeff d f ≠ 0 ∧ value w f = (Finsupp.weight w d : ENNReal) := by
  obtain ⟨d, hd, hmin⟩ := exists_initial w hf
  exact ⟨d, hd, value_eq_of_initial w hd hmin⟩

@[simp] lemma value_zero (w : σ → ℝ≥0) : value (k := k) w 0 = ⊤ := by
  simp [value]

@[simp] lemma value_one [IsDomain k] (w : σ → ℝ≥0) : value (k := k) w 1 = 0 := by
  have h : value (k := k) w 1 ≤ (Finsupp.weight w 0 : ENNReal) :=
    value_le_weight w (by simp)
  simpa using le_antisymm h bot_le

lemma value_add (w : σ → ℝ≥0) (f g : MvPowerSeries σ k) :
    min (value w f) (value w g) ≤ value w (f+g) := by
  apply (le_value_iff w).mpr
  intro d hd
  by_cases hf : MvPowerSeries.coeff d f = 0
  · have hg : MvPowerSeries.coeff d g ≠ 0 := by
      intro hg
      exact hd (by simp [hf, hg])
    exact (min_le_right _ _).trans (value_le_weight w hg)
  · exact (min_le_left _ _).trans (value_le_weight w hf)

lemma le_value_mul (w : σ → ℝ≥0) (f g : MvPowerSeries σ k) :
    value w f + value w g ≤ value w (f*g) := by
  classical
  apply (le_value_iff w).mpr
  intro d hd
  rw [MvPowerSeries.coeff_mul] at hd
  obtain ⟨⟨a,b⟩, hab, hcoef⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have ha : MvPowerSeries.coeff a f ≠ 0 := left_ne_zero_of_mul hcoef
  have hb : MvPowerSeries.coeff b g ≠ 0 := right_ne_zero_of_mul hcoef
  have hab' : a+b = d := by simpa using hab
  rw [← hab', map_add, ENNReal.coe_add]
  exact add_le_add (value_le_weight w ha) (value_le_weight w hb)

/-- The initial homogeneous series of a given weight. -/
def component (w : σ → ℝ≥0) (a : ℝ≥0) (f : MvPowerSeries σ k) : MvPowerSeries σ k :=
  fun d => if Finsupp.weight w d = a then MvPowerSeries.coeff d f else 0

@[simp] lemma coeff_component (w : σ → ℝ≥0) (a : ℝ≥0)
    (f : MvPowerSeries σ k) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (component w a f) =
      if Finsupp.weight w d = a then MvPowerSeries.coeff d f else 0 := rfl

lemma component_mul_at_lower_bounds (w : σ → ℝ≥0) (f g : MvPowerSeries σ k)
    (a b : ℝ≥0)
    (hf : ∀ d, MvPowerSeries.coeff d f ≠ 0 → a ≤ Finsupp.weight w d)
    (hg : ∀ d, MvPowerSeries.coeff d g ≠ 0 → b ≤ Finsupp.weight w d) :
    component w (a+b) (f*g) = component w a f * component w b g := by
  classical
  ext d
  rw [coeff_component, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  by_cases hd : Finsupp.weight w d = a+b
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [coeff_component, coeff_component]
    by_cases hi : MvPowerSeries.coeff ij.1 f = 0
    · simp [hi]
    by_cases hj : MvPowerSeries.coeff ij.2 g = 0
    · simp [hj]
    have hi' := hf ij.1 hi
    have hj' := hg ij.2 hj
    have hs : Finsupp.weight w ij.1 + Finsupp.weight w ij.2 = a+b := by
      rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hij, hd]
    have hia : Finsupp.weight w ij.1 = a := le_antisymm
      (le_of_add_le_add_right ((add_le_add (le_refl (Finsupp.weight w ij.1)) hj').trans_eq hs)) hi'
    have hjb : Finsupp.weight w ij.2 = b := by
      rw [hia] at hs
      exact add_left_cancel hs
    simp [hia, hjb]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro ij hij
    rw [coeff_component, coeff_component]
    by_cases hi : Finsupp.weight w ij.1 = a
    · have hj : Finsupp.weight w ij.2 ≠ b := by
        intro hj
        apply hd
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, map_add, hi, hj]
      simp [hj]
    · simp [hi]

lemma component_ne_zero (w : σ → ℝ≥0) (f : MvPowerSeries σ k)
    {d : σ →₀ ℕ} (hd : MvPowerSeries.coeff d f ≠ 0) :
    component w (Finsupp.weight w d) f ≠ 0 := by
  intro h
  have hc := congrArg (MvPowerSeries.coeff d) h
  simp only [coeff_component, map_zero] at hc
  exact hd hc

end Ring

section Domain
variable {σ k : Type*} [Fintype σ] [CommRing k] [IsDomain k]

lemma value_mul (w : σ → ℝ≥0) (f g : MvPowerSeries σ k) :
    value w (f*g) = value w f + value w g := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨a, ha, hmin_a⟩ := exists_initial w hf
  obtain ⟨b, hb, hmin_b⟩ := exists_initial w hg
  have hn : component w (Finsupp.weight w a + Finsupp.weight w b) (f*g) ≠ 0 := by
    rw [component_mul_at_lower_bounds w f g _ _ hmin_a hmin_b]
    exact mul_ne_zero (component_ne_zero w f ha) (component_ne_zero w g hb)
  obtain ⟨d, hd⟩ : ∃ d, MvPowerSeries.coeff d
      (component w (Finsupp.weight w a + Finsupp.weight w b) (f*g)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    ext d
    simpa using h d
  rw [coeff_component] at hd
  have heq : Finsupp.weight w d = Finsupp.weight w a + Finsupp.weight w b := by
    by_contra h
    exact hd (ite_eq_right h)
  have hcoef : MvPowerSeries.coeff d (f*g) ≠ 0 := by simpa [heq] using hd
  apply le_antisymm _ (le_value_mul w f g)
  rw [value_eq_of_initial w ha hmin_a, value_eq_of_initial w hb hmin_b,
    ← ENNReal.coe_add, ← heq]
  exact value_le_weight w hcoef

/-- Genuine monomial valuation on the formal regular local ring, including
faces with zero weights. -/
def valuation (w : σ → ℝ≥0) : AddValuation (MvPowerSeries σ k) ENNReal :=
  AddValuation.of (value w) (value_zero w) (value_one w) (value_add w) (value_mul w)

@[simp] lemma valuation_apply (w : σ → ℝ≥0) (f : MvPowerSeries σ k) :
    valuation w f = value w f := rfl

/-- Nonnegative combinations of weights dominate the corresponding values. -/
lemma combine_dominates {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (w : ι → σ → ℝ≥0) (f : MvPowerSeries σ k) :
    ∑ i ∈ s, (c i : ENNReal) * valuation (w i) f ≤
      valuation (Monomial.combine s c w) f := by
  change _ ≤ value _ f
  apply (le_value_iff _).mpr
  intro d hd
  rw [Monomial.weight_combine, ENNReal.ofNNReal_finsetSum]
  simp_rw [ENNReal.coe_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_right (value_le_weight (w i) hd) _

end Domain
end CartierSections.FormalMonomial

end

end OAI
