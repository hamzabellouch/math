import Mathlib
import OAI.Computability.MaxCut.Estimates.Clip

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic

noncomputable def cubePerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Cube (Fin n)) where
  toFun x := fun i => x (π i)
  invFun x := fun i => x (π.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] theorem cubePerm_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Cube (Fin n)) (i : Fin n) :
    cubePerm π x i = x (π i) := rfl

 theorem degree_cubePerm {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Cube (Fin n)) :
    degree (cubePerm π s) = degree s := by
  unfold degree
  simp only [card_eq_sum_ones, sum_filter]
  exact Fintype.sum_equiv π _ _ (fun _ => rfl)

 theorem walsh_cubePerm {n : ℕ} (π : Equiv.Perm (Fin n)) (s x : Cube (Fin n)) :
    walsh (cubePerm π s) (cubePerm π x) = walsh s x := by
  unfold walsh
  exact Fintype.prod_equiv π _ _ (fun _ => rfl)

noncomputable def reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ)
    (x : Cube (Fin n)) : ℝ := f (cubePerm π x)

 theorem coefficient_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ)
    (s : Cube (Fin n)) : coefficient (reindex π f) s = coefficient f (cubePerm π s) := by
  unfold coefficient reindex
  apply Fintype.expect_equiv (cubePerm π)
  intro x
  rw [walsh_cubePerm]

 theorem mean_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ) :
    (𝔼 x, reindex π f x) = 𝔼 x, f x :=
  Fintype.expect_equiv (cubePerm π) _ _ (fun _ => rfl)

 theorem cutoffInfluence_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ)
    (K : ℕ) (i : Fin n) :
    cutoffInfluence K i (reindex π f) = cutoffInfluence K (π.symm i) f := by
  classical
  unfold cutoffInfluence
  simp only [sum_filter, coefficient_reindex]
  apply Fintype.sum_equiv (cubePerm π)
  intro s
  simp [degree_cubePerm]

 theorem cutoffInfluence_nonneg {n : ℕ} (K : ℕ) (i : Fin n) (f : Cube (Fin n) → ℝ) :
    0 ≤ cutoffInfluence K i f :=
  sum_nonneg (fun _ _ => sq_nonneg _)

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

/-- A real weighted averaging of all pulled-back odd long codes at a right
question. The graph/test itself uses only rational probabilities. -/
noncomputable def averageCode (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (y : Y) (z : Cube (Fin q)) : ℝ :=
  (G.edgeLaw y).avg (fun e => reindex (G.permutation e) (f (G.source e)) z)

 theorem averageCode_bounded (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (hf : ∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1) (y : Y) (z : Cube (Fin q)) :
    G.averageCode f y z ∈ Set.Icc (-1 : ℝ) 1 :=
  (G.edgeLaw y).avg_mem (fun e => hf (G.source e) _)

 theorem averageCode_mean (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (hf : ∀ x, (𝔼 z, f x z) = 0) (y : Y) : (𝔼 z, G.averageCode f y z) = 0 := by
  unfold averageCode
  rw [Law.avg_expect]
  simp_rw [mean_reindex, hf]
  exact Law.avg_const _ _

 theorem averageCode_influence (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (K : ℕ) (y : Y) (i : Fin q) :
    cutoffInfluence K i (G.averageCode f y) ≤ (G.edgeLaw y).avg (fun e =>
      cutoffInfluence K ((G.permutation e).symm i) (f (G.source e))) := by
  apply (Law.cutoffInfluence_avg (G.edgeLaw y) _ K i).trans_eq
  simp_rw [cutoffInfluence_reindex]

/-- Low-degree Fourier influence decodes an actual labeling. There is no
assumed decoder or hardness assertion in this inequality. -/
 theorem decoding_bound (G : Game X Y E q) (hq : 0 < q) (K : ℕ)
    (f : X → Cube (Fin q) → ℝ) (hf : ∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1)
    (δ : ℝ) (hsound : G.Sound δ) (ly : Y → Fin q) :
    G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
      cutoffInfluence K ((G.permutation e).symm (ly y)) (f (G.source e)))) ≤ (K : ℝ) * δ := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let P (x : X) (i : Fin q) : ℝ := cutoffInfluence K i (f x)
  let score (x : X) (i : Fin q) : ℝ := G.rightLaw.avg (fun y =>
    (G.edgeLaw y).avg (fun e => if G.source e = x then
      (if G.permutation e i = ly y then 1 else 0) else 0))
  have hP (x : X) (i : Fin q) : 0 ≤ P x i := cutoffInfluence_nonneg _ _ _
  have hPsum (x : X) : (∑ i, P x i) ≤ (K : ℝ) := sum_cutoffInfluences K (f x) (hf x)
  have hscore (x : X) (i : Fin q) : 0 ≤ score x i := by
    apply Law.avg_nonneg
    intro y
    apply Law.avg_nonneg
    intro e
    split_ifs <;> norm_num
  have hmax (x : X) : ∃ i : Fin q, ∀ j, score x j ≤ score x i := by
    obtain ⟨i, _, hi⟩ := exists_max_image univ (score x) univ_nonempty
    exact ⟨i, fun j => hi j (mem_univ _)⟩
  choose lx hlx using hmax
  have hweighted (x : X) : (∑ i, P x i * score x i) ≤ (K : ℝ) * score x (lx x) := by
    calc
      _ ≤ ∑ i, P x i * score x (lx x) :=
        sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlx x i) (hP x i))
      _ = (∑ i, P x i) * score x (lx x) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hPsum x) (hscore x (lx x))
  have htotal : (∑ x, score x (lx x)) = G.satisfied lx ly := by
    dsimp [score, satisfied]
    simp_rw [← Law.avg_sum]
    congr 1
    funext y
    congr 1
    funext e
    simp
  have hinfluence : (∑ x, ∑ i, P x i * score x i) =
      G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
        P (G.source e) ((G.permutation e).symm (ly y)))) := by
    calc
      _ = ∑ x, ∑ i, G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
          P x i * (if G.source e = x then (if G.permutation e i = ly y then 1 else 0) else 0))) := by
        simp only [Law.avg_smul, score]
      _ = G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
          ∑ x, ∑ i, P x i * (if G.source e = x then (if G.permutation e i = ly y then 1 else 0) else 0))) := by
        simp_rw [Law.avg_sum]
      _ = _ := by
        congr 1
        funext y
        congr 1
        funext e
        simp only [← Equiv.eq_symm_apply, mul_ite, mul_one, mul_zero]
        simp
  change G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
    P (G.source e) ((G.permutation e).symm (ly y)))) ≤ _
  rw [← hinfluence]
  calc
    _ ≤ ∑ x, (K : ℝ) * score x (lx x) := sum_le_sum (fun x _ => hweighted x)
    _ = (K : ℝ) * G.satisfied lx ly := by rw [← mul_sum, htotal]
    _ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_left (hsound lx ly) (Nat.cast_nonneg _)

end Game
end OptimalMaxCut.LongCode

end

end OAI
