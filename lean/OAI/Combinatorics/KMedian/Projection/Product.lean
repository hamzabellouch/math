import Mathlib
import OAI.Combinatorics.KMedian.Projection.Operator

namespace OAI

section Inline_PCPProjectionProduct

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace ProjectionMass
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
omit [Fintype B] in
lemma push_sum (π : A → B) (f : I → A → ℝ) (b : B) :
    push π (fun a => ∑ i, f i a) b=∑ i, push π (f i) b := by
  unfold push
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp
end ProjectionMass

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' T I : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Fintype T] [Fintype I]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')

omit [Fintype U] [Fintype V] [Fintype D] [Fintype B] [Fintype T]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_sum (f : I → U → A → T → ℝ) (v : V) (b : B) (t : T) :
    G.push (fun u a t => ∑ i, f i u a t) v b t=∑ i, G.push (f i) v b t := by
  simp only [push,ProjectionMass.push_sum,expect_sum_comm]

def prod : BiProjection (U × U') (V × V') (D × D') (S × S') (A × A') (B × B') where
  edge := {
    toFun p := (((G.edge (p.1.1,p.2.1)).1,(H.edge (p.1.2,p.2.2)).1),
      ((G.edge (p.1.1,p.2.1)).2,(H.edge (p.1.2,p.2.2)).2))
    invFun p := (((G.edge.symm (p.1.1,p.2.1)).1,(H.edge.symm (p.1.2,p.2.2)).1),
      ((G.edge.symm (p.1.1,p.2.1)).2,(H.edge.symm (p.1.2,p.2.2)).2))
    left_inv p := by simp
    right_inv p := by simp }
  project p a := (G.project (p.1.1,p.2.1) a.1,H.project (p.1.2,p.2.2) a.2)

omit [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
@[simp] lemma prod_source (v : V × V') (s : S × S') :
    (G.prod H).source v s = (((G.source v.1 s.1).1,(H.source v.2 s.2).1),
      ((G.source v.1 s.1).2,(H.source v.2 s.2).2)) := rfl

omit [Fintype U] [Fintype V] [Fintype D] [Fintype B]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype B'] [Fintype T]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
lemma prod_push (f : (U × U') → (A × A') → T → ℝ)
    (v : V) (v' : V') (b : B) (b' : B') (t : T) :
    (G.prod H).push f (v,v') (b,b') t =
      G.push (fun u a (_ : Unit) => H.push (fun u' a' t => f (u,u') (a,a') t) v' b' t) v b () := by
  unfold push ProjectionMass.push
  simp only [source,prod,Prod.mk.injEq,Fintype.sum_prod_type,expect_prod]
  dsimp only [Equiv.symm]
  apply expect_congr rfl
  intro s _
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : G.project (G.edge.symm (v,s)) a=b
  · simp [h]
    rfl
  · simp [h]

noncomputable def partialPush (f : (U × U') → (A × A') → T → ℝ) :
    U → A → (V' × (B' × T)) → ℝ := fun u a z =>
  H.push (fun u' a' t => f (u,u') (a,a') t) z.1 z.2.1 z.2.2

omit [Fintype U] [Fintype A] [Fintype U'] [Fintype V'] [Fintype D'] [Fintype B']
  [Fintype T] [Nonempty U] [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
lemma partialPush_nonneg (f : (U × U') → (A × A') → T → ℝ)
    (hf : ∀ u a t, 0 ≤ f u a t) : ∀ u a z, 0 ≤ H.partialPush f u a z := by
  intro u a z
  exact H.push_nonneg _ (fun u' a' t => hf _ _ _) _ _ _

omit [Fintype U] [Fintype U'] [Fintype V'] [Fintype D'] [Fintype B'] [Fintype T]
  [Nonempty U] [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
lemma partialPush_total (f : (U × U') → (A × A') → T → ℝ) (u : U) (z : V' × (B' × T)) :
    (∑ a, H.partialPush f u a z)=
      H.push (fun u' a' t => ∑ a, f (u,u') (a,a') t) z.1 z.2.1 z.2.2 := by
  exact (H.push_sum (fun a u' a' t => f (u,u') (a,a') t) _ _ _).symm

omit [Fintype U] [Fintype D] [Fintype U'] [Fintype D']
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty U'] [Nonempty D'] [Nonempty S'] in
lemma prod_collision (f : (U × U') → (A × A') → T → ℝ) :
    (G.prod H).collision f * Fintype.card V'=G.collision (H.partialPush f) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type,expect_prod]
  simp_rw [G.prod_push H]
  rw [expect_mul]
  apply expect_congr rfl
  intro v _
  rw [Fintype.expect_eq_sum_div_card,div_mul_cancel₀ _ (show (Fintype.card V' : ℝ) ≠ 0 by positivity)]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro v' _
  apply sum_congr rfl
  intro b' _
  apply sum_congr rfl
  intro t _
  rfl

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionProduct

end OAI
