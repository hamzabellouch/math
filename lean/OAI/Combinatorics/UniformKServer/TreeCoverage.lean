import Mathlib
import OAI.Combinatorics.UniformKServer.TreeAllocator

namespace OAI

                                   
section

/-! The allocation serves every request and is dominated by true posterior
counts. Positive parks therefore have validity witnesses; no impossible
history is used in either conclusion. -/
noncomputable section
namespace UniformKServer.TreeCoverage
open Finset TreeRounding TreeRankData
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def mean (d : Data Ω S k) (t : ℕ) (ω : Ω) (v : Vertex n) : ℝ :=
  ConditionalLaw.posterior d.weight (d.filtration t) (fun x => (d.count t x v : ℝ)) ω

theorem mean_nonneg (d : Data Ω S k) (t : ℕ) (ω : Ω) (v : Vertex n) : 0 ≤ mean d t ω v :=
  ConditionalLaw.posterior_nonneg (fun x => (d.positive x).le) (fun _ => Nat.cast_nonneg _) _ _

theorem child_size_bound (d : Data Ω S k) (v : Vertex n) (i : Children S v) (t : ℕ) (ω : Ω) :
    StarRanks.held (star d v) t ω i ≤ (11/10)*mean d t ω i.val := by
  apply (CoarseBridge.held_bound _ t ω).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ConditionalRanks.size_le_mean d.weight (fun x => (d.positive x).le) (d.filtration t) ω
    (ne_of_gt (StarRanks.mass_pos (star d v) t ω)) (fun x => d.count t x i.val) k
    (fun x => d.bound t x i.val)

theorem nonroot_domination (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n)
    (hv : v ≠ 0) : TreeAllocator.amount d hk t ω v ≤ 132*mean d t ω v := by
  let i : Children S (S.parent v) := ⟨v,hv,rfl⟩
  have hu := (StarAllocator.feasible (star d (S.parent v)) hk t ω
    (TreeAllocator.parent_le d hk t ω (S.parent v))).2.1 i
  have hc := StarCaps.cap_bound (star d (S.parent v)) hk t ω i
  have hs := child_size_bound d (S.parent v) i t ω
  rw [←TreeAllocator.child d hk t ω (S.parent v) i] at hu
  change TreeAllocator.amount d hk t ω v ≤ _ at hu
  change StarRanks.held (star d (S.parent v)) t ω i ≤ (11/10)*mean d t ω v at hs
  linarith

theorem root_mean (d : Data Ω S k) (hroot : ∀ t x, d.count t x 0=k) (t : ℕ) (ω : Ω) :
    mean d t ω 0=k := by
  unfold mean ConditionalLaw.posterior
  simp only [hroot,←sum_mul]
  have hn : ∑ x, ConditionalLaw.kernel d.weight (d.filtration t) ω x=1 :=
    ConditionalRanks.normalized_kernel d.weight (d.filtration t) ω (ne_of_gt (StarRanks.mass_pos (single d 0) t ω))
  rw [hn,one_mul]

theorem domination (d : Data Ω S k) (hk : 1 ≤ k) (hroot : ∀ t x, d.count t x 0=k)
    (t : ℕ) (ω : Ω) (v : Vertex n) : TreeAllocator.amount d hk t ω v ≤ 132*mean d t ω v := by
  by_cases hv : v=0
  · subst v
    rw [TreeAllocator.root,root_mean d hroot]
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  · exact nonroot_domination d hk t ω v hv

theorem required (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n)
    (hcount : ∀ x, (d.filtration t).r ω x → 1 ≤ d.count t x v) :
    1 ≤ TreeAllocator.amount d hk t ω v := by
  apply le_trans _ (TreeAllocator.lower_le d hk t ω v)
  exact ConditionalRanks.required_rank_lower d.weight (d.filtration t) ω (fun x => d.count t x v)
    (fun x hx _ => hcount x hx) k (by omega) (beta d v t ω) (allowed d hk v t ω)

theorem positive_witness (d : Data Ω S k) (t : ℕ) (ω : Ω) (v : Vertex n)
    (hp : 0 < mean d t ω v) : ∃ x, (d.filtration t).r ω x ∧ 0 < d.count t x v := by
  by_contra hn
  push Not at hn
  have hz : mean d t ω v=0 := by
    unfold mean ConditionalLaw.posterior
    apply sum_eq_zero
    intro x _
    by_cases hx : (d.filtration t).r ω x
    · have hc : d.count t x v=0 := by simpa only [Nat.le_zero] using hn x hx
      simp only [hc,Nat.cast_zero,mul_zero]
    · simp only [ConditionalLaw.kernel,ite_eq_right hx,zero_mul]
  linarith

theorem allocation_witness (d : Data Ω S k) (hk : 1 ≤ k) (hroot : ∀ t x, d.count t x 0=k)
    (t : ℕ) (ω : Ω) (v : Vertex n) (hp : 0 < TreeAllocator.amount d hk t ω v) :
    ∃ x, (d.filtration t).r ω x ∧ 0 < d.count t x v := by
  apply positive_witness d t ω v
  have h := domination d hk hroot t ω v
  linarith

end UniformKServer.TreeCoverage

end


end

end OAI
