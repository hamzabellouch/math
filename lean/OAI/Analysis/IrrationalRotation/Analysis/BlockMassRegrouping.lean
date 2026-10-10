import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233
namespace CircleParameterData

def normalizedBlockMass (p : CircleParameterData) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)

private def budgetBlocks (p : CircleParameterData) (j : ℕ) : Finset ℕ :=
  if j = 0 then {0} else p.block j

private theorem budgetBlocks_partition (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) :
    ∀ i : ℕ, ∃! j : ℕ, i ∈ budgetBlocks p j := by
  intro i
  by_cases hi : i = 0
  · subst i
    refine ⟨0, by simp [budgetBlocks], ?_⟩
    intro j hj
    by_contra h
    have hb : 0 ∈ p.block j := by simpa [budgetBlocks, h] using hj
    have hb' := (p.mem_block_iff j 0).mp hb
    omega
  · obtain ⟨j, hj, hij⟩ := p.exists_mem_block hm i (by omega)
    have hj0 : j ≠ 0 := by omega
    refine ⟨j, by simpa [budgetBlocks, hj0] using hij, ?_⟩
    intro k hik
    have hk0 : k ≠ 0 := by
      intro hk
      subst k
      simp [budgetBlocks, hi] at hik
    have hk : i ∈ p.block k := by simpa [budgetBlocks, hk0] using hik
    exact p.block_index_unique hm hk hij

theorem sum_normalizedBlockMass (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (a : ℕ → ℝ)
    (j : ℕ) (hj : 1 ≤ j) :
    (∑ i ∈ p.block j, p.normalizedBlockMass a i) = a j := by
  have hm0 : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hm j hj).ne'
  calc
    (∑ i ∈ p.block j, p.normalizedBlockMass a i) =
        ∑ _i ∈ p.block j, a j / (p.m j : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : i ≠ 0 := by
        have hu := (p.mem_block_iff j i).mp hi
        omega
      simp only [normalizedBlockMass, ite_eq_right hi0, p.blockIndex_eq_of_mem hm hi]
    _ = a j := by
      simp only [Finset.sum_const, nsmul_eq_mul, p.card_block j hj]
      field_simp

private theorem tsum_budgetBlock (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (j : ℕ) :
    (∑' i : (budgetBlocks p j : Set ℕ), p.normalizedBlockMass a i) = a j := by
  classical
  by_cases hj : j = 0
  · subst j
    simp [budgetBlocks, normalizedBlockMass, ha0]
  · rw [tsum_fintype]
    change (∑ i ∈ (budgetBlocks p j).attach, p.normalizedBlockMass a i) = a j
    rw [Finset.sum_attach]
    simpa only [budgetBlocks, ite_eq_right hj] using
      p.sum_normalizedBlockMass hm a j (by omega)

theorem summable_normalizedBlockMass (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (ha0 : a 0 = 0) (hs : Summable a) :
    Summable (p.normalizedBlockMass a) := by
  classical
  have hnonneg : 0 ≤ p.normalizedBlockMass a := by
    intro i
    simp only [normalizedBlockMass]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ha _) (Nat.cast_nonneg _)
  apply (summable_partition hnonneg (p.budgetBlocks_partition hm)).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · simpa only [p.tsum_budgetBlock hm a ha0] using hs

theorem tsum_normalizedBlockMass (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (ha0 : a 0 = 0) (hs : Summable a) :
    (∑' i, p.normalizedBlockMass a i) = ∑' j, a j := by
  classical
  let e := Set.sigmaEquiv (fun j => (budgetBlocks p j : Set ℕ))
    (p.budgetBlocks_partition hm)
  have hsum := p.summable_normalizedBlockMass hm a ha ha0 hs
  have he : ∀ z, e z = z.2.val := fun _ => rfl
  have hsig : Summable (fun z : (j : ℕ) × (budgetBlocks p j : Set ℕ) =>
      p.normalizedBlockMass a z.2.val) := by
    apply (e.summable_iff.mpr hsum).congr
    intro z
    exact congrArg (p.normalizedBlockMass a) (he z)
  calc
    (∑' i, p.normalizedBlockMass a i) =
        ∑' z, p.normalizedBlockMass a (e z) := (e.tsum_eq _).symm
    _ = ∑' z : (j : ℕ) × (budgetBlocks p j : Set ℕ),
        p.normalizedBlockMass a z.2.val := tsum_congr (fun z => congrArg _ (he z))
    _ = ∑' j, ∑' i : (budgetBlocks p j : Set ℕ), p.normalizedBlockMass a i :=
      hsig.tsum_sigma
    _ = ∑' j, a j := tsum_congr (p.tsum_budgetBlock hm a ha0)

theorem summable_kappa_sq : Summable (fun j : ℕ => kappa j ^ 2) := by
  have h : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (h.mul_left ((1 / 100 : ℝ) ^ 2)).congr
  intro j
  simp only [kappa, one_div, mul_inv_rev, mul_pow]
  ring

end CircleParameterData
end Invariant233

end

end OAI
