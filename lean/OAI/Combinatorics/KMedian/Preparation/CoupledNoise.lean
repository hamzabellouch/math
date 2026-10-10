import Mathlib
import OAI.Combinatorics.KMedian.Preparation.CoupledPreparation
import OAI.Combinatorics.KMedian.Preparation.ShortfallByDeviation
import OAI.Combinatorics.KMedian.Preparation.PreparationOldCost

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem nominal_extension (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hy : ∀ i, 0 ≤ y i)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ) :
    let U := fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i
    (∀ i, L.ν.expect (fun ω => U ω i)=y i) ∧
    (∀ i, L.ν.variance (fun ω => U ω i) ≤ g*y i) ∧
    (∀ i j, i ≠ j → L.ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j) := by
  classical
  dsimp only
  have hm : ∀ i, i ∈ outside P → L.ν.expect (fun ω => L.N ω (.inl i))=y i := by
    intro i hi
    simpa only [weight,ite_eq_left hi] using L.nominal_mean (.inl i)
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ outside P
    · simp only [ite_eq_left hi,hm i hi]
    · simp only [ite_eq_right hi,FiniteLaw.expect_const]
  · intro i
    by_cases hi : i ∈ outside P
    · simp only [ite_eq_left hi]
      simpa only [weight,ite_eq_left hi] using L.nominal_variance (.inl i)
    · simp only [ite_eq_right hi,FiniteLaw.variance_const]
      exact mul_nonneg hg (hy i)
  · intro i j hij
    by_cases hi : i ∈ outside P <;> by_cases hj : j ∈ outside P
    · simp only [ite_eq_left hi,ite_eq_left hj]
      simpa only [weight,ite_eq_left hi,ite_eq_left hj] using L.nominal_pair (.inl i) (.inl j)
        (fun h => hij (Sum.inl.inj h))
    · simp only [ite_eq_left hi,ite_eq_right hj,FiniteLaw.expect_mul_right,hm i hi,le_refl]
    · simp only [ite_eq_right hi,ite_eq_left hj,FiniteLaw.expect_mul,hm j hj,le_refl]
    · simp only [ite_eq_right hi,ite_eq_right hj,FiniteLaw.expect_const,le_refl]

theorem coupled_old_estimates (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (_hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    let μ := L.ν.joint L.κ
    let U := fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i
    let Y := fun ω ξ ti => g*(L.C ω ξ ti:ℝ)
    μ.expect (fun z => max
      (1-(∑ i ∈ F ∩ outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    μ.expect (fun z => (∑ i ∈ F ∩ outside P, U z.1 i*d i)+
      (∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i)*d i)) ≤ (∑ i ∈ F, y i*d i)/p₀ := by
  classical
  dsimp only
  obtain ⟨hUm,hUv,hUp⟩ := nominal_extension P A y p c hg hy L
  have hcap : ∀ ω t, g*(L.K ω t:ℝ) ≤ 1 := fun ω t =>
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.total_cap ω t)) hg).trans_eq hunit
  have hdev : ∀ t, L.ν.expect (fun ω => |g*(L.K ω t:ℝ)-p t|) ≤ γ+Real.sqrt (g*(1+γ)) := by
    intro t
    apply (L.total_deviation t).trans
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left (hc1 t) hγ).trans_eq (mul_one _)
    · exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left (hc1 t)
        (mul_nonneg hg (by linarith only [hγ]))).trans_eq (mul_one _))
  constructor
  · exact shortfall_from_deviation L.ν L.κ P y p
      (fun ω t => g*(L.K ω t:ℝ))
      (fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i)
      (fun ω ξ ti => g*(L.C ω ξ ti:ℝ)) F hg hγ hp₀ hy hF hP hp hcap hdev
      hUm hUv hUp L.piece_mean L.piece_variance L.piece_pair
  · exact preparation_old_cost L.ν L.κ P y d p
      (fun ω t => g*(L.K ω t:ℝ))
      (fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i)
      (fun ω ξ ti => g*(L.C ω ξ ti:ℝ)) F hy hd hp₀ hp₀1 hP hp hcap hUm L.piece_mean

end MetricKMedian.Preparation
end
end

end OAI
