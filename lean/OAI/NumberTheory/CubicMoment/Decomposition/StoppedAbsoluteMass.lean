import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedRoughness
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! The absolute, uncollected complementary factorization mass used
after a free prime is cancelled. No cancellation inside beta is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairAbsolute (R D : Finset Eisenstein) (v f : Eisenstein → ℂ)
    (b : Eisenstein) : ℝ :=
  ∑ p ∈ primaryPairFiber R D b, ‖v p.1‖*‖f p.2‖

lemma pairAbsolute_filter_nonzero (R D : Finset Eisenstein) (v f : Eisenstein → ℂ)
    (b : Eisenstein) : pairAbsolute (R.filter (fun r => v r ≠ 0)) D v f b =
      pairAbsolute R D v f b := by
  unfold pairAbsolute
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpr,hpd⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hpr).1,hpd⟩,he⟩
  · intro p hp hn
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpr,hpd⟩ := Finset.mem_product.mp hp
    have hz : v p.1 = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpr,h⟩,hpd⟩,he⟩)
    rw [hz,norm_zero,zero_mul]

lemma rough_pairAbsolute_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (v f : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    (hf : ∀ d ∈ D, ‖f d‖ ≤ 1) {b : Eisenstein}
    (hb : primary b) (hs : Squarefree b) {w : ℝ} (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) : pairAbsolute R D v f b ≤ (2^k:ℕ)*M := by
  calc
    _ ≤ ∑ _p ∈ primaryPairFiber R D b, M := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact (mul_le_mul_of_nonneg_left (hf p.2 hmem.2) (_root_.norm_nonneg _)).trans
        ((mul_one _).le.trans (hv p.1 hmem.1))
    _ = ((primaryPairFiber R D b).card:ℝ)*M := by simp
    _ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le R D hR b)) hM
    _ ≤ (2^k:ℕ)*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM

theorem distinguished_pairAbsolute_bound
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1)
    (R D : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ}
    (hsize : norm b < w^k) :
    pairAbsolute R D (distinguishedTupleCoefficient S W ψ w z) (cutoffMoebius ψ w) b ≤
      (2^k:ℕ)*(‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  rw [←pairAbsolute_filter_nonzero]
  apply rough_pairAbsolute_bound _ D
    (fun r hr => hR r (Finset.mem_filter.mp hr).1) _ _ (by positivity)
    (fun r _ => distinguishedTupleCoefficient_norm S hS W hW hψ w z r)
    (fun d _ => cutoffMoebius_norm_le_one hψ w d) hb hs hw
  · intro r hr p hp
    have hp' := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
    exact (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hp'.1 hp'.2).1.le
  · exact hsize

/-- Summing the absolute complementary weights costs only their linear
norm range. In particular no cancellation inside the collected coefficient
and no ordering of the selected bin primes is used. -/
theorem distinguished_pairAbsolute_mass
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1)
    (R D : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z Y : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z) (hY : 0 ≤ Y)
    {k : ℕ} (hsize : Y < w^k) :
    (∑ b ∈ (primaryElementBall Y).filter Squarefree,
      pairAbsolute R D (distinguishedTupleCoefficient S W ψ w z)
        (cutoffMoebius ψ w) b) ≤
      18*Y*((2^k:ℕ)*(‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ))) := by
  let M : ℝ := (2^k:ℕ)*(‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
    ((Fintype.card ι)^(Fintype.card ι):ℕ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  calc
    _ ≤ ∑ _b ∈ (primaryElementBall Y).filter Squarefree, M := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hb,hs⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb,hbY⟩ := mem_primaryElementBall.mp hb
      exact distinguished_pairAbsolute_bound S hS W hW R D hR hψ hψone hψzero
        hw hwz hb hs (hbY.trans_lt hsize)
    _ = (((primaryElementBall Y).filter Squarefree).card:ℝ)*M := by simp
    _ ≤ 18*Y*M := mul_le_mul_of_nonneg_right
      ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
        (primaryElementBall_card_le hY)) hM


end CubicFirstMoment

end

end OAI
