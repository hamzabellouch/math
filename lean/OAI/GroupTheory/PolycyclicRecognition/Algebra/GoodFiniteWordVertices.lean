import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulSampleBlockPaths

namespace OAI

/-! # The actual good vertices of a successful finite block -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G]

theorem WordSheetsGood.take_prod_mem {A : Set G} {x : G} {u : List G}
    (hg : WordSheetsGood A x u) (j : ℕ) : x * (u.take j).prod ∈ A := by
  induction u generalizing x j with
  | nil => simpa only [List.take_nil, List.prod_nil, mul_one] using hg.start
  | cons a u ih =>
    cases j with
    | zero => simpa only [List.take_zero, List.prod_nil, mul_one] using hg.1
    | succ j =>
      simpa only [List.take_succ_cons, List.prod_cons, ← mul_assoc] using ih hg.2 j

def finiteWordVertex {m : ℕ} (x : G) (u : Fin m → G) (j : Fin (m + 1)) : G :=
  x * ((List.ofFn u).take j.val).prod

@[simp] theorem finiteWordVertex_zero {m : ℕ} (x : G) (u : Fin m → G) :
    finiteWordVertex x u 0 = x := by
  simp only [finiteWordVertex, Fin.val_zero, List.take_zero, List.prod_nil, mul_one]

@[simp] theorem finiteWordVertex_last {m : ℕ} (x : G) (u : Fin m → G) :
    finiteWordVertex x u (Fin.last m) = x * (List.ofFn u).prod := by
  simp only [finiteWordVertex, Fin.val_last, List.take_of_length_le (by simp :
    (List.ofFn u).length ≤ m)]

theorem finiteWordVertex_step {m : ℕ} (x : G) (u : Fin m → G) (j : Fin m) :
    finiteWordVertex x u j.succ = finiteWordVertex x u j.castSucc * u j := by
  simp only [finiteWordVertex, Fin.val_succ, Fin.val_castSucc]
  rw [List.take_succ_eq_append_getElem (by simp), List.prod_append,
    List.prod_singleton, List.getElem_ofFn]
  exact (mul_assoc _ _ _).symm

theorem WordSheetsGood.finite_vertices {A : Set G} {x : G} {m : ℕ} {u : Fin m → G}
    (hg : WordSheetsGood A x (List.ofFn u)) (j : Fin (m + 1)) :
    finiteWordVertex x u j ∈ A := hg.take_prod_mem j.val

/-- A globally successful sample gives the genuine intermediate states of
each block, starting after the product of all preceding blocks. -/
theorem successful_sample_block_vertices {h m : ℕ}
    (A : Set G) (sample : ℕ → ℝ → G)
    (hsub : ∀ j s t, sample j s * (sample j t)⁻¹ = sample j (s - t))
    (x : G) (hx : x ∈ A) (t : Fin (h * m + h * m) → ℝ)
    (hs : SwitchSuccessful (fun _ => A) 0 (h * m) x
      (sampledSwitchParameters sample (h * m) t)) (i : Fin h) :
    let start := x * wordPrefix (sampledBlockProducts sample t) i.val
    let u := fun j : Fin m => sample (finProdFinEquiv (i, j)).val
      (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
        t (Fin.natAdd (h * m) (finProdFinEquiv (i, j))))
    ∀ j : Fin (m + 1), finiteWordVertex start u j ∈ A := by
  dsimp only
  let w : ℕ → List G := fun j =>
    if hj : j < h then sampledBlockWord sample t ⟨j, hj⟩ else []
  have hw : (fun j => (w j).prod) = sampledBlockProducts sample t := by
    funext j
    dsimp only [w, sampledBlockProducts]
    split_ifs <;> rfl
  have hg := wordSheetsGood_sampled A sample hsub (h * m) t x hx hs
  rw [ofFn_eq_flatten_bundles] at hg
  have hg' : WordSheetsGood A x (List.ofFn (fun j : Fin h => w j.val)).flatten := by
    simpa only [w, sampledBlockWord, dite_eq_left (Fin.isLt _)] using hg
  have hb := hg'.ofFn_block w i
  rw [hw] at hb
  have hwi : w i.val = sampledBlockWord sample t i := by
    simp only [w, dite_eq_left i.isLt]
  rw [hwi] at hb
  exact hb.finite_vertices

end PolycyclicRecognition

end

end OAI
