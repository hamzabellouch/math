import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233
namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

private def budgetBlocks (p : CircleParameterData) (s : ℕ) : Finset ℕ :=
  if s = 0 then {0} else p.block s

private theorem budgetBlocks_partition :
    ∀ i : ℕ, ∃! s : ℕ, i ∈ budgetBlocks p s := by
  intro i
  by_cases hi : i = 0
  · subst i
    refine ⟨0, by simp [budgetBlocks], ?_⟩
    intro s hs
    by_contra h
    have hb : 0 ∈ p.block s := by simpa [budgetBlocks, h] using hs
    have hb' := (p.mem_block_iff s 0).mp hb
    omega
  · obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
    have hs0 : s ≠ 0 := by omega
    refine ⟨s, by simpa [budgetBlocks, hs0] using his, ?_⟩
    intro t hit
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      simp [budgetBlocks, hi] at hit
    have ht : i ∈ p.block t := by simpa [budgetBlocks, ht0] using hit
    exact p.block_index_unique hp.m_pos ht his

theorem normalized_block_budget (a : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s)
    (has : Summable a) :
    Summable (fun i : ℕ => if i = 0 then 0 else
      a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) ∧
    (∑' i : ℕ, if i = 0 then 0 else
      a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) ≤ ∑' s, a s := by
  classical
  let f : ℕ → ℝ := fun i => if i = 0 then 0 else
    a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)
  have hfnonneg : ∀ i, 0 ≤ f i := by
    intro i
    simp only [f]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ha _) (Nat.cast_nonneg _)
  have hblock (s : ℕ) :
      (∑' i : budgetBlocks p s, f i) = if s = 0 then 0 else a s := by
    rw [Finset.tsum_subtype]
    by_cases hs : s = 0
    · subst s
      simp [budgetBlocks, f]
    · have hspos : 1 ≤ s := by omega
      rw [ite_eq_right hs]
      simp only [budgetBlocks, ite_eq_right hs]
      have hm : (p.m s : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos s hspos).ne'
      calc
        (∑ i ∈ p.block s, f i) = ∑ _i ∈ p.block s, a s / (p.m s : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi0 : i ≠ 0 := by
            have := (p.mem_block_iff s i).mp hi
            omega
          simp only [f, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
        _ = a s := by
          simp only [Finset.sum_const, nsmul_eq_mul, p.card_block s hspos]
          field_simp
  have hgnonneg : ∀ s, 0 ≤ (if s = 0 then 0 else a s) := by
    intro s
    split_ifs
    · exact le_rfl
    · exact ha s
  have hgle : ∀ s, (if s = 0 then 0 else a s) ≤ a s := by
    intro s
    split_ifs
    · exact ha s
    · exact le_rfl
  have hgs : Summable (fun s : ℕ => if s = 0 then 0 else a s) :=
    Summable.of_nonneg_of_le hgnonneg hgle has
  have hfs : Summable f := by
    apply (summable_partition hfnonneg hp.budgetBlocks_partition).mpr
    constructor
    · intro s
      exact (hasSum_fintype _).summable
    · apply hgs.congr
      intro s
      exact (hblock s).symm
  refine ⟨hfs, ?_⟩
  let e := Set.sigmaEquiv (fun s => (budgetBlocks p s : Set ℕ)) hp.budgetBlocks_partition
  have he (z : Σ s, (budgetBlocks p s : Set ℕ)) : e z = z.2 := rfl
  have hsig : Summable (fun z : Σ s, (budgetBlocks p s : Set ℕ) => f z.2) := by
    apply (e.summable_iff.mpr hfs).congr
    intro z
    change f (e z) = f z.2
    rw [he]
  calc
    (∑' i, f i) = ∑' z : Σ s, (budgetBlocks p s : Set ℕ), f z.2 :=
      by simpa only [he] using (e.tsum_eq f).symm
    _ = ∑' s, ∑' i : budgetBlocks p s, f i := hsig.tsum_sigma
    _ = ∑' s, if s = 0 then 0 else a s := tsum_congr hblock
    _ ≤ ∑' s, a s := hgs.tsum_le_tsum hgle has

end CircleParameterLaws

namespace CircleParameterData

theorem summable_kappa_sq : Summable (fun s : ℕ => kappa s ^ 2) := by
  have h : Summable (fun s : ℕ => 1 / (s : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (h.mul_left ((1 / 100 : ℝ) ^ 2)).congr
  intro s
  simp only [kappa, div_pow, mul_pow]
  ring

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem circle_marginal_budget (j : ℕ) :
    Summable (fun i : ℕ => if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) ∧
    (∑' i : ℕ, if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) ≤
      50 * ((∑' s : ℕ, CircleParameterData.kappa s ^ 2) + 1) := by
  let a : ℕ → ℝ := fun s => 50 *
    (CircleParameterData.kappa s ^ 2 + if s = j then 1 else 0)
  have ha : ∀ s, 0 ≤ a s := by
    intro s
    dsimp [a]
    positivity
  have hs : Summable a :=
    (CircleParameterData.summable_kappa_sq.add (hasSum_ite_eq j (1 : ℝ)).summable).mul_left 50
  have heq : (fun i : ℕ => if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) =
      (fun i : ℕ => if i = 0 then 0 else
        a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) := by
    funext i
    dsimp [a]
    split_ifs <;> ring
  rw [heq]
  obtain ⟨hsum, hle⟩ := hp.normalized_block_budget a ha hs
  refine ⟨hsum, hle.trans_eq ?_⟩
  simp only [a, tsum_mul_left, Summable.tsum_add CircleParameterData.summable_kappa_sq
    (hasSum_ite_eq j (1 : ℝ)).summable, tsum_ite_eq]

end CircleParameterLaws
end Invariant233

end

end OAI
