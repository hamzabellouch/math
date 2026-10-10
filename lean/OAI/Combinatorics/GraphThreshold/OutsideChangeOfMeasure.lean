import OAI.Combinatorics.GraphThreshold.BernoulliCoupling
import OAI.Combinatorics.GraphThreshold.Resampling
import OAI.Combinatorics.GraphThreshold.ProbabilityTree
import OAI.Combinatorics.GraphThreshold.SpreadCounting
import OAI.Combinatorics.GraphThreshold.LocalFailureNumerics
import Mathlib.Tactic

namespace OAI

/-!
# Outside-coordinate change of measure for the actual resampling transition

The observable may depend on the same Bernoulli set used at every other tree
node.  The only locality required here is that it ignores the fixed target's
incoming label.  No independence between different tree nodes is assumed.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- Actual target marginal restricted to the event that the density is at least `δ`. -/
def cutoffTargetMass (ν : FiniteLaw B) (A : B → Finset X) (p δ : ℝ)
    (W : Finset X) (b : B) : ℝ :=
  ∑ c, if δ ≤ resamplingZ ν A p (resamplingY A W c)
    then resamplingWeight ν A p W (c, b) else 0

theorem cutoffTargetMass_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {p : ℝ} (hp : 0 ≤ p) (δ : ℝ) (W : Finset X) (b : B) :
    0 ≤ cutoffTargetMass ν A p δ W b := by
  unfold cutoffTargetMass
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact resamplingWeight_nonneg ν A hp W (c, b)
  · exact le_rfl

/-- This marginal is the literal conditional expectation of the target-and-density event. -/
theorem cutoffTargetMass_mul_eq_expectation (ν : FiniteLaw B) (A : B → Finset X)
    {p : ℝ} (hν : ν.IsPositive) (hp : 0 < p) (δ : ℝ)
    (W : Finset X) (b : B) (f : Finset X → ℝ) :
    cutoffTargetMass ν A p δ W b * f W =
      (resamplingLaw ν A p W hν hp).expectation
        (fun cb => if cb.2 = b ∧ δ ≤ resamplingZ ν A p (resamplingY A W cb.1)
          then f W else 0) := by
  classical
  simp only [cutoffTargetMass, FiniteLaw.expectation, resamplingLaw_weight,
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : δ ≤ resamplingZ ν A p (resamplingY A W c)
  · simp [hc, mul_ite]
  · simp [hc]

theorem subset_union_iff_sdiff_subset (S T W : Finset X) :
    S ⊆ W ∪ T ↔ S \ T ⊆ W := by
  constructor
  · intro h x hx
    obtain ⟨hxS, hxT⟩ := Finset.mem_sdiff.mp hx
    exact (Finset.mem_union.mp (h hxS)).resolve_right hxT
  · intro h x hxS
    by_cases hxT : x ∈ T
    · exact Finset.mem_union.mpr (Or.inr hxT)
    · exact Finset.mem_union.mpr (Or.inl (h (Finset.mem_sdiff.mpr ⟨hxS, hxT⟩)))

/-- Modifying only coordinates inside the ignored label leaves the observable unchanged. -/
theorem dependsOutside_union {β : Type*} (A S : Finset X) (f : Finset X → β)
    (hf : DependsOutside A f) (hSA : S ⊆ A) (W : Finset X) :
    f (W ∪ S) = f W := by
  apply hf
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact ⟨hx, hn⟩
    · exact (hn (hSA hx)).elim
  · rintro ⟨hx, hn⟩
    exact ⟨Or.inl hx, hn⟩

theorem inv_pow_card_mul_pow_sdiff (p : ℝ) (hp : p ≠ 0) (S T : Finset X) :
    (p⁻¹) ^ S.card * p ^ (S \ T).card = (p⁻¹) ^ (T ∩ S).card := by
  have hc : (S \ T).card + (T ∩ S).card = S.card := by
    simpa only [Finset.inter_comm] using Finset.card_sdiff_add_card_inter S T
  rw [← hc, pow_add]
  calc
    (p⁻¹) ^ (S \ T).card * (p⁻¹) ^ (T ∩ S).card * p ^ (S \ T).card =
        ((p⁻¹) ^ (S \ T).card * p ^ (S \ T).card) * (p⁻¹) ^ (T ∩ S).card := by ring
    _ = (p⁻¹) ^ (T ∩ S).card := by rw [← mul_pow, inv_mul_cancel₀ hp, one_pow, one_mul]

/-- The only pointwise change of density is the reciprocal cutoff.
The remaining event uses coordinates inside the fixed target label. -/
theorem cutoff_source_weight_le (ν : FiniteLaw B) (A : B → Finset X)
    {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ) (W : Finset X) (c b : B) :
    (if δ ≤ resamplingZ ν A p (resamplingY A W c)
      then resamplingWeight ν A p W (c, b) else 0) ≤
      if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
      else 0 := by
  have hnum : 0 ≤ ν.weight b * (p⁻¹) ^ (A b).card :=
    mul_nonneg (ν.nonneg b) (pow_nonneg (inv_nonneg.mpr hp) _)
  by_cases he : A b \ A c ⊆ W
  · have he' : A b ⊆ resamplingY A W c :=
      (subset_union_iff_sdiff_subset (A b) (A c) W).mpr he
    rw [ite_eq_left he]
    by_cases hz : δ ≤ resamplingZ ν A p (resamplingY A W c)
    · rw [ite_eq_left hz]
      simp only [resamplingWeight, resamplingTargetWeight, resamplingNumerator, ite_eq_left he']
      calc
        ν.weight c * (ν.weight b * (p⁻¹) ^ (A b).card /
            resamplingZ ν A p (resamplingY A W c)) ≤
            ν.weight c * (ν.weight b * (p⁻¹) ^ (A b).card / δ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum hδ hz) (ν.nonneg c)
        _ = _ := by ring
    · rw [ite_eq_right hz]
      exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le) (ν.nonneg c))
        (ν.nonneg b)) (pow_nonneg (inv_nonneg.mpr hp) _)
  · have he' : ¬ A b ⊆ resamplingY A W c :=
      fun h => he ((subset_union_iff_sdiff_subset (A b) (A c) W).mp h)
    simp [he, resamplingWeight, resamplingTargetWeight, resamplingNumerator, he']

variable [Fintype X]

/-- A containment event on ignored coordinates is independent of the observable.
This is derived from the fixed-union formula for the actual Bernoulli product weights. -/
theorem bernoulli_subset_expectation_of_dependsOutside
    {p : ℝ} (hp : p ≠ 0) (A S : Finset X) (f : Finset X → ℝ)
    (hf : DependsOutside A f) (hSA : S ⊆ A) :
    bernoulliExpectation p (fun W => if S ⊆ W then f W else 0) =
      p ^ S.card * bernoulliExpectation p f := by
  have hu : bernoulliExpectation p (fun W => f (W ∪ S)) =
      bernoulliExpectation p f := by
    congr 1
    funext W
    exact dependsOutside_union A S f hf hSA W
  have hd : bernoulliExpectation p (fun W => if S ⊆ W then f W / p ^ S.card else 0) =
      bernoulliExpectation p (fun W => if S ⊆ W then f W else 0) / p ^ S.card := by
    unfold bernoulliExpectation
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro W _
    by_cases hW : S ⊆ W <;> simp [hW, mul_div_assoc]
  have h := bernoulliExpectation_union_fixed (p := p) hp S f
  rw [hu, hd] at h
  have he := (eq_div_iff (pow_ne_zero _ hp)).mp h
  simpa only [mul_comm] using he.symm

/-- Change of measure before applying spread: the exact loss is the intersection moment. -/
theorem outside_change_of_measure_moment (ν : FiniteLaw B) (A : B → Finset X)
    {p δ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (b : B) (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W)
    (hloc : DependsOutside (A b) f) :
    bernoulliExpectation p (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
      δ⁻¹ * ν.weight b * bernoulliExpectation p f *
        ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) := by
  let μ := bernoulliLaw (X := X) p hp.le hp1
  change μ.expectation (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
    δ⁻¹ * ν.weight b * μ.expectation f *
      ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card)
  calc
    μ.expectation (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
        μ.expectation (fun W => ∑ c,
          (if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
            else 0) * f W) := by
      apply μ.expectation_mono
      intro W
      unfold cutoffTargetMass
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_right (cutoff_source_weight_le ν A hp.le hδ W c b) (hf W)
    _ = ∑ c, μ.expectation (fun W =>
          (if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
            else 0) * f W) := μ.expectation_sum _
    _ = ∑ c, δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A c ∩ A b).card *
        μ.expectation f := by
      apply Finset.sum_congr rfl
      intro c _
      have hi : μ.expectation (fun W => if A b \ A c ⊆ W then f W else 0) =
          p ^ (A b \ A c).card * μ.expectation f :=
        bernoulli_subset_expectation_of_dependsOutside hp.ne' (A b) (A b \ A c) f
          hloc Finset.sdiff_subset
      have he : μ.expectation (fun W =>
            (if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
              else 0) * f W) =
          (δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card) *
            μ.expectation (fun W => if A b \ A c ⊆ W then f W else 0) := by
        rw [← μ.expectation_smul]
        congr 1
        funext W
        split_ifs <;> simp
      rw [he, hi]
      calc
        δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card *
            (p ^ (A b \ A c).card * μ.expectation f) =
            δ⁻¹ * ν.weight c * ν.weight b *
              ((p⁻¹) ^ (A b).card * p ^ (A b \ A c).card) * μ.expectation f := by ring
        _ = _ := by rw [inv_pow_card_mul_pow_sdiff p hp.ne']
    _ = δ⁻¹ * ν.weight b * μ.expectation f *
        ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) := by
      change (∑ c, δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A c ∩ A b).card *
        μ.expectation f) =
        (δ⁻¹ * ν.weight b * μ.expectation f) *
          (∑ c, ν.weight c * (p⁻¹) ^ (A c ∩ A b).card)
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem outside_change_of_measure (ν : FiniteLaw B) (A : B → Finset X)
    {p a : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a)
    (hs : IsSpread ν A a) (m : ℕ) (b : B) (hAb : (A b).card ≤ m)
    (hsmall : a / p ≤ Real.exp (-50))
    (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W) (hloc : DependsOutside (A b) f) :
    bernoulliExpectation p (fun W =>
      cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b * f W) ≤
      Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p f := by
  have hEf : 0 ≤ bernoulliExpectation p f :=
    (bernoulliLaw (X := X) p hp.le hp1).expectation_nonneg hf
  have hmoment : ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) ≤
      Real.exp (m : ℝ) :=
    (intersection_inverse_moment_le hs ha hAb hp).trans
      (one_add_pow_le_exp_nat (div_nonneg ha hp.le) hsmall m)
  have hcoef : 0 ≤ (Real.exp (-10 * (m : ℝ)))⁻¹ * ν.weight b *
      bernoulliExpectation p f :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.exp_pos _).le) (ν.nonneg b)) hEf
  have he : (Real.exp (-10 * (m : ℝ)))⁻¹ * Real.exp (m : ℝ) =
      Real.exp (11 * (m : ℝ)) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  calc
    bernoulliExpectation p (fun W =>
        cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b * f W) ≤
        (Real.exp (-10 * (m : ℝ)))⁻¹ * ν.weight b * bernoulliExpectation p f *
          ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) :=
      outside_change_of_measure_moment ν A hp hp1 (Real.exp_pos _) b f hf hloc
    _ ≤ (Real.exp (-10 * (m : ℝ)))⁻¹ * ν.weight b * bernoulliExpectation p f *
        Real.exp (m : ℝ) := mul_le_mul_of_nonneg_left hmoment hcoef
    _ = ((Real.exp (-10 * (m : ℝ)))⁻¹ * Real.exp (m : ℝ)) * ν.weight b *
        bernoulliExpectation p f := by ring
    _ = _ := by rw [he]

/-- Any smaller target mass, including local non-failure, obeys the same bound. -/
theorem outside_change_of_measure_of_le (ν : FiniteLaw B) (A : B → Finset X)
    {p a : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a)
    (hs : IsSpread ν A a) (m : ℕ) (b : B) (hAb : (A b).card ≤ m)
    (hsmall : a / p ≤ Real.exp (-50))
    (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W) (hloc : DependsOutside (A b) f)
    (t : Finset X → ℝ)
    (ht : ∀ W, t W ≤ cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b) :
    bernoulliExpectation p (fun W => t W * f W) ≤
      Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p f := by
  have hm : bernoulliExpectation p (fun W => t W * f W) ≤
      bernoulliExpectation p (fun W =>
        cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b * f W) :=
    (bernoulliLaw (X := X) p hp.le hp1).expectation_mono
      (fun W => mul_le_mul_of_nonneg_right (ht W) (hf W))
  exact hm.trans (outside_change_of_measure ν A hp hp1 ha hs m b hAb hsmall f hf hloc)

/-- The same inequality stated as the expectation of the actual transition event. -/
theorem outside_change_of_measure_law (ν : FiniteLaw B) (A : B → Finset X)
    (hν : ν.IsPositive) {p a : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a)
    (hs : IsSpread ν A a) (m : ℕ) (b : B) (hAb : (A b).card ≤ m)
    (hsmall : a / p ≤ Real.exp (-50))
    (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W) (hloc : DependsOutside (A b) f) :
    bernoulliExpectation p (fun W =>
      (resamplingLaw ν A p W hν hp).expectation
        (fun cb => if cb.2 = b ∧ Real.exp (-10 * (m : ℝ)) ≤
            resamplingZ ν A p (resamplingY A W cb.1) then f W else 0)) ≤
      Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p f := by
  classical
  simp_rw [← cutoffTargetMass_mul_eq_expectation ν A hν hp _ _ b f]
  exact outside_change_of_measure ν A hp hp1 ha hs m b hAb hsmall f hf hloc

end LeanBlast.SecondKahnKalai

end

end OAI
