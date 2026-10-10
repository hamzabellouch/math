import OAI.NumberTheory.CubicMoment.Estimates.RoughProductPairs
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingSupportCollection

namespace OAI

/-! Exact product slices for the original finite support. Divisibility
supplies the norm bound needed by the stopping construction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryProductSlice (S : Finset Eisenstein) (X : ℝ) (a : Eisenstein) :
    Finset Eisenstein :=
  (primaryElementBall X).filter (fun m => a*m ∈ S)

lemma mem_primaryProductSlice_iff (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (a : Eisenstein) {m : Eisenstein} (hm : primary m) :
    m ∈ primaryProductSlice S X a ↔ a*m ∈ S := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨mem_primaryElementBall.mpr ⟨hm,?_⟩,h⟩
    exact (norm_le_of_dvd (primary_ne_zero (hS _ h).1)
      (dvd_mul_left m a)).trans (hS _ h).2.2

lemma primaryProductSlice_support (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (a : Eisenstein) :
    ∀ m ∈ primaryProductSlice S X a, primary m ∧ Squarefree m ∧ norm m ≤ X := by
  intro m hm
  obtain ⟨hmb,hprod⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmp,hmX⟩ := mem_primaryElementBall.mp hmb
  exact ⟨hmp,(hS _ hprod).2.1.of_mul_right,hmX⟩

/-- Reindex the literal rough-product divisor expansion with the
complementary factor first. No condition is imposed on the kernel. -/
theorem roughProduct_slice_pairs (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (r : Eisenstein) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n)) =
      ∑ u ∈ primaryElementBall X, ∑ m ∈ primaryProductSlice S X (r*u),
        cutoffMoebius ψ w m*K (r*(m*u)) := by
  rw [roughProduct_finite_factor_pairs (primaryProductSlice S X r) X
    (primaryProductSlice_support S X hS r) ψ w (fun n => K (r*n)),
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  conv_rhs => rw [primaryProductSlice,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hp := primary_mul (mem_primaryElementBall.mp hm).1
    (mem_primaryElementBall.mp hu).1
  have heq : r*(m*u) = (r*u)*m := by ring
  simp only [mem_primaryProductSlice_iff S X hS r hp,heq]

/-- A fixed complementary-factor row has an exact no-stop and stopped
split. The only support predicate on the collected pair is the original
total product membership. -/
theorem stopping_product_slice_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) (u : Eisenstein)
    {Z : ℝ} (hstart : norm r < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ m ∈ primaryProductSlice S X (r*u), cutoffMoebius ψ w m*K (r*(m*u))) =
      (∑ m ∈ primaryProductSlice S X (r*u) with
          norm r*primeSurrogate (primaryPrimeFactors m)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w m*K (r*(m*u))) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then
            (if stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 Z r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
          else 0 := by
  rw [finite_stopping_pair_split (primaryProductSlice S X (r*u)) hρ hρ₂ hX
    (primaryProductSlice_support S X hS (r*u)) hr hstart ψ w
    (fun m => K (r*(m*u)))]
  congr 1
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have heq : (r*u)*(d*e) = r*(d*e)*u := by ring
  have heq' : r*((d*e)*u) = r*(d*e)*u := by ring
  simp only [mem_primaryProductSlice_iff S X hS (r*u)
    (primary_mul (mem_primaryElementBall.mp hd).1 (mem_primaryElementBall.mp he).1),heq,heq']

/-- The genuine rough product on one distinguished row, with the
un-stopped term retained explicitly. -/
theorem roughProduct_slice_stopping (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) {Z : ℝ} (hstart : norm r < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n)) =
      (∑ u ∈ primaryElementBall X,
        ∑ m ∈ primaryProductSlice S X (r*u) with
          norm r*primeSurrogate (primaryPrimeFactors m)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
          cutoffMoebius ψ w m*K (r*(m*u))) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ u ∈ primaryElementBall X, ∑ d ∈ primaryElementBall X,
          ∑ e ∈ primaryElementBall X,
            if r*(d*e)*u ∈ S then
              (if stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 Z r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
            else 0 := by
  rw [roughProduct_slice_pairs S X hS r ψ w K]
  simp_rw [stopping_product_slice_split S hρ hρ₂ hX hS hr _ hstart ψ w K]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.mul_sum]

end CubicFirstMoment

end

end OAI
