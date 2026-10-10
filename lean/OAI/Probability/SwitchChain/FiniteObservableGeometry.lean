import OAI.Probability.SwitchChain.FiniteEventVectors
import OAI.Probability.SwitchChain.PairFibers

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.FiniteObservableGeometry
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

def probabilityVector (f : Ω → ℝ) : EuclideanSpace ℝ Ω :=
  (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ • WithLp.toLp 2 f

lemma inner_probabilityVector (f g : Ω → ℝ) :
    ⟪probabilityVector f, probabilityVector g⟫ =
      (∑ x, f x * g x) / (Fintype.card Ω : ℝ) := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card Ω) :
    (0 : ℝ) ≤ Fintype.card Ω)
  have hv : ⟪WithLp.toLp 2 f, WithLp.toLp 2 g⟫ = ∑ x, f x * g x := by
    simp [PiLp.inner_apply, mul_comm]
  simp only [probabilityVector, real_inner_smul_left, real_inner_smul_right, hv]
  rw [← mul_assoc, ← mul_inv, ← pow_two, hsq]
  exact (div_eq_inv_mul _ _).symm

def observable (v : EuclideanSpace ℝ Ω) : Ω → ℝ :=
  fun x => Real.sqrt (Fintype.card Ω : ℝ) * v x

lemma probabilityVector_observable [Nonempty Ω] (v : EuclideanSpace ℝ Ω) :
    probabilityVector (observable v) = v := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  ext x
  change (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ *
    (Real.sqrt (Fintype.card Ω : ℝ) * v x) = v x
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

lemma observable_probabilityVector [Nonempty Ω] (f : Ω → ℝ) :
    observable (probabilityVector f) = f := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  funext x
  change Real.sqrt (Fintype.card Ω : ℝ) *
    ((Real.sqrt (Fintype.card Ω : ℝ))⁻¹ * f x) = f x
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

lemma inner_eq_observable_average [Nonempty Ω] (v w : EuclideanSpace ℝ Ω) :
    ⟪v, w⟫ = (∑ x, observable v x * observable w x) / (Fintype.card Ω : ℝ) := by
  conv_lhs => rw [← probabilityVector_observable v, ← probabilityVector_observable w]
  exact inner_probabilityVector _ _

lemma probabilityVector_add (f g : Ω → ℝ) :
    probabilityVector (fun x => f x + g x) = probabilityVector f + probabilityVector g := by
  ext x
  simp [probabilityVector, mul_add]

lemma probabilityVector_sub (f g : Ω → ℝ) :
    probabilityVector (fun x => f x - g x) = probabilityVector f - probabilityVector g := by
  ext x
  simp [probabilityVector, mul_sub]

lemma probabilityVector_smul (a : ℝ) (f : Ω → ℝ) :
    probabilityVector (fun x => a * f x) = a • probabilityVector f := by
  ext x
  simp [probabilityVector, mul_left_comm]

lemma probabilityVector_mem (R : Setoid Ω) (f : Ω → ℝ)
    (hf : ∀ x y, R.r x y → f x = f y) :
    probabilityVector f ∈ PairFibers.constantSubspace R := by
  intro x y hxy
  change (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ * f x =
    (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ * f y
  rw [hf x y hxy]

lemma expectation_probabilityVector (R : Setoid Ω) (f : Ω → ℝ)
    (hf : ∀ x y, R.r x y → f x = f y) :
    PairFibers.expectation R (probabilityVector f) = probabilityVector f :=
  (PairFibers.expectation_eq_self_iff R _).2 (probabilityVector_mem R f hf)

variable [DecidableEq Ω]
open FiniteEventVectors

lemma probabilityVector_indicator (s : Finset Ω) :
    probabilityVector (fun x => if x ∈ s then 1 else 0) = eventVector s := rfl

lemma probabilityVector_one :
    probabilityVector (fun _ : Ω => 1) = constantVector := by
  ext x
  simp [probabilityVector, constantVector, eventVector, rawIndicator]

lemma normalizedFlag_eq_probabilityVector (s : Finset Ω) :
    DisjointIndicators.normalizedFlag constantVector (eventVector s) (probability s) =
      probabilityVector (fun x =>
        ((if x ∈ s then 1 else 0) - probability s) /
          Real.sqrt (probability s * (1 - probability s))) := by
  unfold DisjointIndicators.normalizedFlag
  rw [← probabilityVector_one, ← probabilityVector_indicator,
    ← probabilityVector_smul, ← probabilityVector_sub, ← probabilityVector_smul]
  congr 1
  funext x
  simp only [mul_one, div_eq_inv_mul]

lemma observable_constantVector [Nonempty Ω] :
    observable (constantVector (Ω := Ω)) = fun _ => 1 := by
  rw [← probabilityVector_one, observable_probabilityVector]

lemma observable_eventVector [Nonempty Ω] (s : Finset Ω) :
    observable (eventVector s) = fun x => if x ∈ s then 1 else 0 :=
  observable_probabilityVector _

lemma observable_normalizedFlag [Nonempty Ω] (s : Finset Ω) :
    observable (DisjointIndicators.normalizedFlag constantVector
      (eventVector s) (probability s)) = fun x =>
        ((if x ∈ s then 1 else 0) - probability s) /
          Real.sqrt (probability s * (1 - probability s)) := by
  rw [normalizedFlag_eq_probabilityVector, observable_probabilityVector]

lemma expectation_constantVector (R : Setoid Ω) :
    PairFibers.expectation R (constantVector (Ω := Ω)) = constantVector := by
  rw [← probabilityVector_one]
  exact expectation_probabilityVector R _ (fun _ _ _ => rfl)

lemma expectation_eventVector (R : Setoid Ω) (s : Finset Ω)
    (hs : ∀ x y, R.r x y → (x ∈ s ↔ y ∈ s)) :
    PairFibers.expectation R (eventVector s) = eventVector s := by
  apply expectation_probabilityVector
  intro x y hxy
  simp only [hs x y hxy]

lemma expectation_normalizedFlag (R : Setoid Ω) (s : Finset Ω)
    (hs : ∀ x y, R.r x y → (x ∈ s ↔ y ∈ s)) :
    PairFibers.expectation R
      (DisjointIndicators.normalizedFlag constantVector (eventVector s) (probability s)) =
      DisjointIndicators.normalizedFlag constantVector (eventVector s) (probability s) :=
  DisjointIndicators.normalizedFlag_fixed (PairFibers.expectation R).toLinearMap
    _ _ _ (expectation_constantVector R) (expectation_eventVector R s hs)

end Problem315.FiniteObservableGeometry

end

end OAI
