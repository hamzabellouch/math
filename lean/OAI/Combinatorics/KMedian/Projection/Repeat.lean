import Mathlib
import OAI.Combinatorics.KMedian.Projection.Bound
import OAI.Combinatorics.KMedian.Projection.Tensor

namespace OAI

section Inline_PCPProjectionRepeat

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

def Nested (A : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => A × Nested A n
namespace Nested
instance fintype (A : Type) [Fintype A] : (n : ℕ) → Fintype (Nested A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := fintype A n; inferInstanceAs (Fintype (A × Nested A n))
instance nonempty (A : Type) [Nonempty A] : (n : ℕ) → Nonempty (Nested A n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => letI := nonempty A n; inferInstanceAs (Nonempty (A × Nested A n))
lemma card (A : Type) [Fintype A] (n : ℕ) : Fintype.card (Nested A n)=Fintype.card A^n := by
  induction n with
  | zero => change Fintype.card Unit=Fintype.card A^0; rw [Fintype.card_unique,pow_zero]
  | succ n ih => change Fintype.card (A × Nested A n)=_; rw [Fintype.card_prod,ih,pow_succ]; exact Nat.mul_comm _ _
end Nested

namespace BiProjection
variable {U V D S A B : Type}
def trivial : BiProjection Unit Unit Unit Unit Unit Unit where
  edge := Equiv.refl _
  project _ _ := ()
def power (G : BiProjection U V D S A B) : (n : ℕ) →
    BiProjection (Nested U n) (Nested V n) (Nested D n) (Nested S n) (Nested A n) (Nested B n)
  | 0 => trivial
  | n+1 => G.prod (power G n)

variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty D]
  [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionBound_power (r : ℝ) (hr0 : 0 ≤ r) (hr : G.CollisionBound r) (n : ℕ) :
    (G.power n).CollisionBound (r^n) := by
  induction n with
  | zero => exact trivial.collisionBound_one
  | succ n ih =>
    rw [pow_succ']
    change (G.prod (G.power n)).CollisionBound (r*r^n)
    exact G.collisionBound_prod (G.power n) r (r^n) hr0 (pow_nonneg hr0 _) hr ih

omit [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
theorem arbitrarily_small (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r<1) (hr : G.CollisionBound r)
    (ε : ℝ) (hε : 0<ε) : ∃ n : ℕ, (G.power n).Sound ε := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sq_pos_of_pos hε) hr1
  exact ⟨n,(G.power n).sound_of_collisionBound (r^n) ε (G.collisionBound_power r hr0 hr n) hε.le hn.le⟩

def Perfect (G : BiProjection U V D S A B) : Prop :=
  ∃ a : U → A, ∃ b : V → B, ∀ u d, G.project (u,d) (a u)=b (G.edge (u,d)).1
def Consistent (G : BiProjection U V D S A B) : Prop :=
  ∀ u d e, (G.edge (u,d)).1=(G.edge (u,e)).1 → ∀ a, G.project (u,d) a=G.project (u,e) a

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRepeat

end OAI
