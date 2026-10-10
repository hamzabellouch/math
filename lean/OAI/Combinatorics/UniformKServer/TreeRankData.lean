import Mathlib
import OAI.Combinatorics.UniformKServer.RoundingChain
import OAI.Combinatorics.UniformKServer.StarLower

namespace OAI

                                   
section

/-! Fixed-tree finite count laws. Internal counts are exactly sums of child
counts; leaves keep their own counts. All operations depend on the observed
finite filtration only. -/
noncomputable section
namespace UniformKServer.TreeRankData
open Finset TreeRounding RankTracking RankData RankFunctions
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

structure Data (Ω : Type*) [Fintype Ω] {n : ℕ} (S : Shape n) (k : ℕ) where
  weight : Ω → ℝ
  positive : ∀ ω, 0 < weight ω
  total : ∑ ω, weight ω=1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  count : ℕ → Ω → Vertex n → ℕ
  bound : ∀ t ω v, count t ω v ≤ k
  conserves : ∀ t ω v, Nonempty (Children S v) → (∑ i : Children S v, count t ω i.val)=count t ω v

def single (d : Data Ω S k) (v : Vertex n) : StarRanks.Data Ω Unit k where
  weight := d.weight
  positive := d.positive
  total := d.total
  filtration := d.filtration
  refines := d.refines
  count := fun t ω _ => d.count t ω v
  bound := by intro t ω; simpa using d.bound t ω v

def star (d : Data Ω S k) (v : Vertex n) : StarRanks.Data Ω (Children S v) k where
  weight := d.weight
  positive := d.positive
  total := d.total
  filtration := d.filtration
  refines := d.refines
  count := fun t ω i => d.count t ω i.val
  bound := by
    intro t ω
    by_cases h : Nonempty (Children S v)
    · rw [d.conserves t ω v h]
      exact d.bound t ω v
    · have : IsEmpty (Children S v) := not_nonempty_iff.mp h
      simp

def input (d : Data Ω S k) (v : Vertex n) : Fin k → Input Ω := StarRanks.input (single d v) ()
def beta (d : Data Ω S k) (v : Vertex n) (t : ℕ) (ω : Ω) : ℝ := ParentBeta.trueParam (input d v) k t ω
def lower (d : Data Ω S k) (v : Vertex n) (t : ℕ) (ω : Ω) : ℝ :=
  totalRank (beta d v t ω) (fun j => (input d v j).posterior t ω)

theorem child_input (d : Data Ω S k) (v : Vertex n) (i : Children S v) :
    StarRanks.input (star d v) i=input d i.val := rfl

theorem child_lower (d : Data Ω S k) (v : Vertex n) (i : Children S v) (t : ℕ) (ω : Ω) :
    StarLower.lower (star d v) (StarLower.childBeta (star d v) t ω i) t ω i=lower d i.val t ω := rfl

theorem parent_input (d : Data Ω S k) (v : Vertex n) (hv : Nonempty (Children S v)) :
    StarRanks.parentInput (star d v)=input d v := by
  have he : (fun t ω => ∑ i : Children S v, d.count t ω i.val)=(fun t ω => d.count t ω v) :=
    funext fun t => funext fun ω => d.conserves t ω v hv
  unfold StarRanks.parentInput input StarRanks.input
  simp only [star,single,he]

theorem parent_lower (d : Data Ω S k) (v : Vertex n) (hv : Nonempty (Children S v)) (t : ℕ) (ω : Ω) :
    StarLower.parentLower (star d v) t ω=lower d v t ω := by
  simp only [StarLower.parentLower,StarLower.parentBeta,parent_input d v hv,lower,beta]

theorem allowed (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    RankFunctions.allowed (beta d v t ω) := StarLower.child_allowed (single d v) hk t ω ()

theorem lower_nonneg (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    0 ≤ lower d v t ω := by
  unfold lower totalRank
  exact sum_nonneg fun j _ => rank_nonneg (allowed d hk v t ω)

theorem lower_bound (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    lower d v t ω ≤ k := by
  calc
    _ ≤ ∑ _ : Fin k, (1:ℝ) := sum_le_sum fun j _ =>
      rank_le_one (allowed d hk v t ω) ((input d v j).posterior_range t ω).1
    _ = _ := by simp

theorem empty_parent (d : Data Ω S k) (v : Vertex n) [IsEmpty (Children S v)] (t : ℕ) (ω : Ω) :
    StarLower.parentLower (star d v) t ω=0 := by
  have hp (j : Fin k) : (StarRanks.parentInput (star d v) j).posterior t ω=1 := by
    change ConditionalLaw.posterior d.weight (d.filtration t)
      (fun x => ConditionalRank.indicator (∑ i : Children S v, d.count t x i.val) j) ω=1
    simp only [sum_of_isEmpty,ConditionalRank.indicator,Nat.zero_le,ite_true,ConditionalLaw.posterior,mul_one]
    exact ConditionalRanks.normalized_kernel _ _ _ (ne_of_gt (StarRanks.mass_pos (star d v) t ω))
  unfold StarLower.parentLower totalRank
  simp only [hp]
  apply sum_eq_zero
  intro j _
  exact rank_beyond (by norm_num [sstar])

theorem parent_le_lower (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    StarLower.parentLower (star d v) t ω ≤ lower d v t ω := by
  by_cases h : Nonempty (Children S v)
  · exact (parent_lower d v h t ω).le
  · have : IsEmpty (Children S v) := not_nonempty_iff.mp h
    rw [empty_parent]
    exact lower_nonneg d hk v t ω

end UniformKServer.TreeRankData

end


end

end OAI
