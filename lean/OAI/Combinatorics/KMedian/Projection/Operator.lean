import Mathlib
import OAI.Combinatorics.KMedian.Expanders.L2
import OAI.Combinatorics.KMedian.Projection.Norm

namespace OAI

section Inline_PCPProjectionOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

structure BiProjection (U V D S A B : Type) where
  edge : U × D ≃ V × S
  project : U × D → A → B

namespace ProjectionMass
variable {A B : Type} [Fintype A] [Fintype B]
noncomputable def push (π : A → B) (f : A → ℝ) (b : B) : ℝ := ∑ a, if π a=b then f a else 0

lemma push_total (π : A → B) (f : A → ℝ) : ∑ b, push π f b=∑ a, f a := by
  unfold push
  rw [sum_comm]
  simp

omit [Fintype B] in
lemma push_nonneg (π : A → B) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (b : B) :
    0 ≤ push π f b := sum_nonneg (fun a _ => by split_ifs; exact hf a; exact le_rfl)

omit [Fintype B] in
lemma push_sub (π : A → B) (f g : A → ℝ) (b : B) :
    push π (fun a => f a-g a) b=push π f b-push π g b := by
  unfold push
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

omit [Fintype B] in
lemma push_abs (π : A → B) (f : A → ℝ) (b : B) :
    |push π f b| ≤ push π (fun a => |f a|) b := by
  unfold push
  calc
    _ ≤ ∑ a, |if π a=b then f a else 0| := abs_sum_le_sum_abs _ _
    _ = _ := by apply sum_congr rfl; intro a _; split_ifs <;> simp

lemma push_sq_sum (π : A → B) (f : A → ℝ) :
    ∑ b, push π f b^2 ≤ (∑ a, |f a|)^2 := by
  calc
    _ ≤ ∑ b, push π (fun a => |f a|) b^2 := by
      apply sum_le_sum
      intro b _
      have h := push_abs π f b
      have hn := push_nonneg π (fun a => |f a|) (fun _ => abs_nonneg _) b
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (push π f b)) hn).mpr h
    _ ≤ (∑ b, push π (fun a => |f a|) b)^2 :=
      sum_sq_le_sq_sum_of_nonneg (fun b _ => push_nonneg π _ (fun _ => abs_nonneg _) b)
    _ = _ := by rw [push_total]
end ProjectionMass

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

def source (v : V) (s : S) : U × D := G.edge.symm (v,s)
noncomputable def average (h : U → ℝ) (v : V) := 𝔼 s, h (G.source v s).1
noncomputable def push (f : U → A → T → ℝ) (v : V) (b : B) (t : T) : ℝ :=
  𝔼 s, ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b
noncomputable def collision (f : U → A → T → ℝ) : ℝ :=
  MixedNorm.sq (fun v (p : B × T) => G.push f v p.1 p.2)

omit [Fintype A] [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma source_expect (f : U × D → ℝ) :
    (𝔼 v, 𝔼 s, f (G.source v s))=𝔼 u, 𝔼 d, f (u,d) := by
  rw [← expect_prod (fun p : V × S => f (G.source p.1 p.2)),← expect_prod f]
  exact Fintype.expect_equiv G.edge.symm _ _ (fun _ => rfl)

omit [Fintype A] [Fintype B] [Nonempty U] [Nonempty V] [Nonempty S] in
lemma average_mean (f : U → ℝ) : (𝔼 v, G.average f v)=𝔼 u, f u := by
  unfold average
  rw [G.source_expect (fun p : U × D => f p.1)]
  simp only [Fintype.expect_const]

omit [Fintype U] [Fintype V] [Fintype D] [Fintype T] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_nonneg (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) :
    ∀ v b t, 0 ≤ G.push f v b t := by
  intro v b t
  exact expect_nonneg (fun s _ => ProjectionMass.push_nonneg _ _ (fun a => hf _ a _) _)

omit [Fintype U] [Fintype V] [Fintype D] [Fintype T] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_sub (f g : U → A → T → ℝ) :
    G.push (fun u a t => f u a t-g u a t)=fun v b t => G.push f v b t-G.push g v b t := by
  funext v b t
  simp only [push,ProjectionMass.push_sub,expect_sub_distrib]

omit [Fintype U] [Fintype V] [Fintype D] [Fintype T]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_total (f : U → A → T → ℝ) (v : V) (t : T) :
    (∑ b, G.push f v b t)=G.average (fun u => ∑ a, f u a t) v := by
  unfold push average
  rw [← expect_sum_comm]
  simp only [ProjectionMass.push_total]

omit [Nonempty U] [Nonempty V] in
lemma collision_le_abs_total (f : U → A → T → ℝ) :
    G.collision f ≤ MixedNorm.sq (fun u t => ∑ a, |f u a t|) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ 𝔼 v, ∑ b, ∑ t, 𝔼 s,
        (ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b)^2 := by
      apply expect_le_expect
      intro v _
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro t _
      exact mean_sq_le_energy _
    _ = 𝔼 v, 𝔼 s, ∑ t, ∑ b,
        (ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b)^2 := by
      simp_rw [← expect_sum_comm]
      apply expect_congr rfl
      intro v _
      apply expect_congr rfl
      intro s _
      exact sum_comm
    _ ≤ 𝔼 v, 𝔼 s, ∑ t, (∑ a, |f (G.source v s).1 a t|)^2 := by
      apply expect_le_expect
      intro v _
      apply expect_le_expect
      intro s _
      exact sum_le_sum (fun t _ => ProjectionMass.push_sq_sum _ _)
    _ = _ := by
      rw [G.source_expect (fun p : U × D => ∑ t, (∑ a, |f p.1 a t|)^2)]
      simp only [Fintype.expect_const]

omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma collision_nonneg (f : U → A → T → ℝ) : 0 ≤ G.collision f := MixedNorm.sq_nonneg _

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionOperator

end OAI
