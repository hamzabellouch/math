import OAI.Dynamics.ConditionalShuffle.ColorLayer

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Color
open Thorp Thorp.Conditional Revealed.Disintegration

def matrixSwap {I X : Type} (M : I → X → Bool) :
    Equiv.Perm ((I → X → Bool) × (I → X → Bool)) :=
  Function.Involutive.toPerm
    (fun p => ((fun i => maskedCoin (M i) (p.1 i) (p.2 i)),
      (fun i => maskedCoin (M i) (p.2 i) (p.1 i)))) (by
        intro p; apply Prod.ext <;> funext i x <;>
          cases hx : M i x <;> simp [maskedCoin, hx])

lemma mean_maskedMatrix {I X : Type} [Fintype (I → X → Bool)]
    (M : I → X → Bool) (f : (I → X → Bool) → ℝ) :
    mean (fun a : I → X → Bool => mean (fun b : I → X → Bool => f (fun i => maskedCoin (M i) (a i) (b i)))) = mean f := by
  have he := mean_equiv (matrixSwap M) (fun p => f p.1)
  change mean (fun p : (I → X → Bool) × (I → X → Bool) =>
    f (fun i => maskedCoin (M i) (p.1 i) (p.2 i))) = _ at he
  rw [mean_prod, mean_prod] at he
  simpa only [mean_const] using he

def mergeHistory (d : ℕ) (h : Coloring d) (t : ℕ) (c a b : History (d+1) t) : History (d+1) t :=
  fun i => maskedCoin (fun x => occupancy d h t c i.castSucc (Fin.cons false x)) (b i) (a i)

lemma merge_succ (d : ℕ) (h : Coloring d) (t : ℕ) (c a b : History (d+1) (t+1)) :
    mergeHistory d h (t+1) c a b = Fin.snoc (mergeHistory d h t (Fin.init c) (Fin.init a) (Fin.init b))
      (maskedCoin (fun x => occupied d h t (Fin.init c) (Fin.cons false x)) (b (Fin.last t)) (a (Fin.last t))) := by
  funext i x
  refine Fin.lastCases ?_ (fun j => ?_) i
  · erw [Fin.snoc_last]
    simp only [mergeHistory, occupancy, Fin.snoc_castSucc, occupied]
  · erw [Fin.snoc_castSucc]
    simp only [mergeHistory, occupancy, Fin.snoc_castSucc, Fin.init_def]

lemma mean_merge (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t)
    (f : History (d+1) t → ℝ) :
    mean (fun a => mean (fun b => f (mergeHistory d h t c a b))) = mean f := by
  rw [mean_comm]
  exact @mean_maskedMatrix (Fin t) (Position d) (inferInstanceAs (Fintype (History (d+1) t)))
    (fun i x => occupancy d h t c i.castSucc (Fin.cons false x)) f

def resampleTwo (d : ℕ) (h : Coloring d) (t : ℕ) (c a b : History (d+1) t) : History (d+1) t :=
  resample d h t c (mergeHistory d h t c a b)

def splitCoin (d : ℕ) (h : Coloring d) (c a b : Coins (d+1)) : Coins (d+1) :=
  maskedCoin (sameMask d h) c (maskedCoin (fun x => h (Fin.cons false x)) b a)

lemma resampleTwo_succ (d : ℕ) (h : Coloring d) (t : ℕ) (c a b : History (d+1) (t+1)) :
    resampleTwo d h (t+1) c a b = Fin.snoc (resampleTwo d h t (Fin.init c) (Fin.init a) (Fin.init b))
      (splitCoin d (occupied d h t (Fin.init c)) (c (Fin.last t)) (a (Fin.last t)) (b (Fin.last t))) := by
  unfold resampleTwo
  rw [merge_succ, resample_succ]
  erw [Fin.init_snoc, Fin.snoc_last]
  rfl

lemma splitCoin_A (d : ℕ) (h : Coloring d) (c a b b' : Coins (d+1))
    (x : Position (d+1)) (hx : h x = true) :
    step (d+1) (splitCoin d h c a b) x = step (d+1) (splitCoin d h c a b') x := by
  obtain ⟨⟨u,y⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).surjective x
  change h (Fin.cons u y) = true at hx
  apply (step_same_at_iff d _ _ _).mpr
  change splitCoin d h c a b y = splitCoin d h c a b' y
  cases u <;> cases hf : h (Fin.cons false y) <;> cases ht : h (Fin.cons true y) <;>
    simp_all [splitCoin, sameMask, maskedCoin]

lemma splitCoin_C (d : ℕ) (h : Coloring d) (c a a' b : Coins (d+1))
    (x : Position (d+1)) (hx : h x = false) :
    step (d+1) (splitCoin d h c a b) x = step (d+1) (splitCoin d h c a' b) x := by
  obtain ⟨⟨u,y⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).surjective x
  change h (Fin.cons u y) = false at hx
  apply (step_same_at_iff d _ _ _).mpr
  change splitCoin d h c a b y = splitCoin d h c a' b y
  cases u <;> cases hf : h (Fin.cons false y) <;> cases ht : h (Fin.cons true y) <;>
    simp_all [splitCoin, sameMask, maskedCoin]

lemma resampleTwo_occupancy (d : ℕ) (h : Coloring d) (t : ℕ) (c a b : History (d+1) t) :
    occupancy d h t (resampleTwo d h t c a b) = occupancy d h t c := resample_observation d h t c _

lemma resampleTwo_tag_color (d : ℕ) (h : Coloring d) (t : ℕ) (c a b : History (d+1) t)
    (x : Position (d+1)) :
    occupied d h t c (run (d+1) t (resampleTwo d h t c a b) x) = h x := by
  have hh := congrFun (resampleTwo_occupancy d h t c a b) (Fin.last t)
  change occupied d h t (resampleTwo d h t c a b) = occupied d h t c at hh
  rw [← hh]
  exact occupied_image d h t _ x

lemma resampleTwo_A (d : ℕ) (h : Coloring d) (t : ℕ) (c a b b' : History (d+1) t)
    (x : Position (d+1)) (hx : h x = true) :
    run (d+1) t (resampleTwo d h t c a b) x = run (d+1) t (resampleTwo d h t c a b') x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [resampleTwo_succ, resampleTwo_succ, run_succ, run_succ]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Equiv.Perm.mul_apply]
      rw [ih]
      apply splitCoin_A
      exact (resampleTwo_tag_color d h t (Fin.init c) (Fin.init a) (Fin.init b') x).trans hx

lemma resampleTwo_C (d : ℕ) (h : Coloring d) (t : ℕ) (c a a' b : History (d+1) t)
    (x : Position (d+1)) (hx : h x = false) :
    run (d+1) t (resampleTwo d h t c a b) x = run (d+1) t (resampleTwo d h t c a' b) x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [resampleTwo_succ, resampleTwo_succ, run_succ, run_succ]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Equiv.Perm.mul_apply]
      rw [ih]
      apply splitCoin_C
      exact (resampleTwo_tag_color d h t (Fin.init c) (Fin.init a') (Fin.init b) x).trans hx

lemma conditional_two_arrays (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t)
    {G : Type} [Fintype G] [Nonempty G] (f : History (d+1) t → G) :
    fairMass (fun p : History (d+1) t × History (d+1) t => f (resampleTwo d h t c p.1 p.2)) =
      conditional (fairMass (fun a => (occupancy d h t a,f a))) (occupancy d h t c) := by
  rw [← conditional_resampling d h t c f]
  funext g
  rw [fairMass_eq_mean, fairMass_eq_mean, mean_prod]
  exact mean_merge d h t c (fun r => if f (resample d h t c r) = g then (1:ℝ) else 0)

end Revealed.Color

end

end OAI
