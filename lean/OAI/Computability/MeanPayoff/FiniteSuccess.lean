import OAI.Computability.MeanPayoff.Online

namespace OAI

section

namespace MeanPayoff

@[simp] theorem SolveBox.online_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Counted (BoxVector I)) (J : ℕ) :
    (I.repeatedCounted t J).online = I.repeatedOnline t.online J := by
  simp [SolveBox.repeatedCounted, SolveBox.repeatedOnline]

namespace CountedAlgorithm

def onlineLower {n Bmax : ℕ} {P : Budgets n} (lower : LowerSolver (Bmax := Bmax) P) :
    OnlineAlgorithm.LowerSolver (Bmax := Bmax) P := fun Q h I => (lower Q h I).online

@[simp] theorem online_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).online =
    OnlineAlgorithm.centerUpdate P hR (onlineLower lower) I hB q := by
  simp [centerUpdate, OnlineAlgorithm.centerUpdate, onlineLower]

@[simp] theorem online_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).online =
    OnlineAlgorithm.centerSteps P hR (onlineLower lower) I hB t q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih => simp only [centerSteps, OnlineAlgorithm.centerSteps, Counted.online_bind,
      online_centerUpdate, Counted.online_map, ih]

@[simp] theorem online_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) :
    (orientationTail G P I qs child).online =
    OnlineAlgorithm.orientationTail G P I qs (fun q => (child q).online) := by
  unfold orientationTail OnlineAlgorithm.orientationTail
  dsimp only
  split_ifs <;> simp

@[simp] theorem online_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).online = OnlineAlgorithm.orient G P hR (onlineLower lower) I := by
  rw [orient, OnlineAlgorithm.orient]
  split_ifs with h
  · rfl
  · simp only [Counted.online_bind, online_centerSteps, online_orientationTail]
    apply congrArg (Online.bind _)
    funext qs
    apply congrArg (OnlineAlgorithm.orientationTail G P I qs)
    funext q
    exact online_orient G P hR lower (I.wideCentered (lt_of_not_ge h) q.val)
termination_by I.width
 decreasing_by exact I.E_smaller

@[simp] theorem online_orientPlus {n : ℕ} {P : Budgets n}
    (t : Counted (Orientation P)) (J : ℕ) :
    (orientPlus t J).online = OnlineAlgorithm.orientPlus t.online J := by
  simp [orientPlus, OnlineAlgorithm.orientPlus]

@[simp] theorem online_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).online = OnlineAlgorithm.tighten P hR (onlineLower lower) I hB := by
  rw [tighten, OnlineAlgorithm.tighten]
  simp only [Counted.online_bind, SolveBox.online_repeated]
  congr 1
  funext r₁
  split_ifs with h₁
  · simp only [Counted.online_map, online_tighten P hR lower (I.withFloor r₁) hB]
  · simp only [Counted.online_bind, SolveBox.online_repeated]
    congr 1
    funext r₂
    split_ifs with h₂
    · simp only [Counted.online_map, online_tighten P hR lower (I.withCeiling r₂) hB]
    · rfl
termination_by volume I.b I.a
 decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

@[simp] theorem online_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    (finishChoice G P hR lower I hB O up lo).online =
    OnlineAlgorithm.finishChoice G P hR (onlineLower lower) I hB O up.online lo.online := by
  unfold finishChoice OnlineAlgorithm.finishChoice
  split_ifs <;> simp [onlineLower]

@[simp] theorem online_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).online = OnlineAlgorithm.solveWidth G P hR (onlineLower lower) I := by
  rw [solveWidth, OnlineAlgorithm.solveWidth, Counted.online_charge]
  apply congrArg (Online.charge 1)
  split_ifs with hB
  · rfl
  · simp only [Counted.online_bind, online_tighten]
    congr 1
    funext T
    simp only [online_orientPlus, online_orient]
    congr 1
    funext O
    simp only [Counted.online_map, online_finishChoice]
    congr 2
    · exact online_solveWidth G P hR lower _
    · exact online_solveWidth G P hR lower _
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller (by rw [T.width_eq]; omega)

@[simp] theorem online_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).online = OnlineAlgorithm.solve G P I := by
  rw [solve, OnlineAlgorithm.solve]
  split_ifs with hR
  · rfl
  · rw [online_solveWidth]
    congr 1
    funext Q h K
    exact online_solve G Q K
termination_by parameterRank P.parameter

end CountedAlgorithm


@[simp] theorem RandomTree.read_map {α β : Type} (t : RandomTree α) (f : α → β)
    (bits : ℕ → Bool) : (t.map f).read bits = f (t.read bits) := by
  induction t generalizing bits with
  | leaf a => rfl
  | coin l r il ir => simp only [RandomTree.map, RandomTree.bind, RandomTree.read]; split <;> simp_all [RandomTree.map]

theorem Counted.online_value {α : Type} (t : Counted α) (bits : ℕ → Bool) (pos : ℕ) :
    (t.online bits pos).1.1 = t.erase.read (fun j => bits (pos + j)) := by
  rw [Counted.erase, RandomTree.read_map, ← RandomTree.consume_read]
  rfl

theorem Counted.online_count {α : Type} (t : Counted α) {N : ℕ} (h : t.Bounded N)
    (bits : ℕ → Bool) (pos : ℕ) : (t.online bits pos).1.2 ≤ N := by
  exact (RandomTree.consume_path t.tree bits pos).2.all h

theorem Counted.online_coins {α : Type} (t : Counted α) {K E : ℕ} (h : t.Resource K E)
    (bits : ℕ → Bool) (pos : ℕ) :
    pos ≤ (t.online bits pos).2 ∧
    (t.online bits pos).2 ≤ pos + K * (t.online bits pos).1.2 + E := by
  obtain ⟨hp, hh⟩ := RandomTree.consume_path t.tree bits pos
  have hb := h _ _ hh
  exact ⟨hp, by unfold Counted.online; omega⟩

def onlineGame (G : Game) : Online (Fin G.n → Bool) :=
  (OnlineAlgorithm.solve G (rootBudgets G) (rootBox G)).map
    (fun p v => decide (topWidth G / 2 < p.val v))

theorem onlineGame_counted (G : Game) : onlineGame G =
    ((CountedAlgorithm.solve G (rootBudgets G) (rootBox G)).map
      (fun p v => decide (topWidth G / 2 < p.val v))).online := by
  simp only [onlineGame, Counted.online_map, CountedAlgorithm.online_solve]

theorem onlineGame_value (G : Game) (bits : ℕ → Bool) (pos : ℕ) :
    (onlineGame G bits pos).1.1 = (gameSolve G).read (fun j => bits (pos + j)) := by
  rw [onlineGame_counted, Counted.online_value]
  simp only [Counted.erase_map, CountedAlgorithm.erase_solve, gameSolve]

theorem onlineGame_count (G : Game) (bits : ℕ → Bool) (pos : ℕ) :
    (onlineGame G bits pos).1.2 ≤ rootInvocationBound G := by
  rw [onlineGame_counted]
  exact Counted.online_count _
    (Counted.bounded_map _ (CountedAlgorithm.bounded_solve G (rootBudgets G) (rootBox G))) bits pos

theorem onlineGame_coins (G : Game) (bits : ℕ → Bool) (pos : ℕ) :
    pos ≤ (onlineGame G bits pos).2 ∧
    (onlineGame G bits pos).2 ≤ pos + rootRandomBound G := by
  have h := Counted.online_coins
    ((CountedAlgorithm.solve G (rootBudgets G) (rootBox G)).map
      (fun p v => decide (topWidth G / 2 < p.val v)))
    (Counted.resource_map _ (CountedAlgorithm.resource_solve G (rootBudgets G) (rootBox G))) bits pos
  rw [← onlineGame_counted G] at h
  have hc := Nat.mul_le_mul_left (nodeRandomBound G.n (topWidth G).toNat) (onlineGame_count G bits pos)
  exact ⟨h.1, by unfold rootRandomBound; omega⟩

namespace BinaryInput

def onlineProgram (code : List Bool) : Online (List Bool) :=
  match decodeGame code with
  | none => Online.pure []
  | some G => (onlineGame G).map List.ofFn

@[simp] theorem onlineProgram_input (G : Game) :
    onlineProgram (input G) = (onlineGame G).map List.ofFn := by
  simp only [onlineProgram, decodeGame_input]

theorem onlineProgram_value (G : Game) (bits : ℕ → Bool) (pos : ℕ) :
    (onlineProgram (input G) bits pos).1.1 =
      List.ofFn ((gameSolve G).read (fun j => bits (pos + j))) := by
  simp only [onlineProgram_input, Online.map, onlineGame_value]

def CorrectList (G : Game) (out : List Bool) : Prop :=
  out.length = G.n ∧ ∀ v : Fin G.n, out[v.val]? = some true ↔ Winning G v

@[simp] theorem correctList_ofFn (G : Game) (out : Fin G.n → Bool) :
    CorrectList G (List.ofFn out) ↔ CorrectSet G out := by
  simp only [CorrectList, List.length_ofFn, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte,
    Option.some.injEq, true_and, CorrectSet]

theorem onlineProgram_coins (G : Game) (bits : ℕ → Bool) :
    (onlineProgram (input G) bits 0).2 ≤ rootRandomBound G := by
  simpa only [onlineProgram_input, Online.map, Nat.zero_add] using (onlineGame_coins G bits 0).2

open scoped Classical

theorem onlineProgram_success (G : Game) :
    (∀ bits : ℕ → Bool, (onlineProgram (input G) bits 0).2 ≤ rootRandomBound G) ∧
    7 * 2 ^ rootRandomBound G ≤ 8 * (Finset.univ.filter
      (fun bits : Fin (rootRandomBound G) → Bool =>
        CorrectList G (onlineProgram (input G) (padBits bits) 0).1.1)).card := by
  refine ⟨onlineProgram_coins G, ?_⟩
  have h := RandomTree.game_prefix_success G (rootRandomBound G) (game_bitDepth G)
  simp only [onlineProgram_value, Nat.zero_add, correctList_ofFn, RandomTree.readPrefix] at ⊢ h
  convert h using 1
  congr 1

end BinaryInput
end MeanPayoff

namespace MeanPayoff
namespace TwoPhase

def even {t : ℕ} (bits : Fin (2 * t) → Bool) (j : Fin t) : Bool :=
  bits ⟨2 * j.val, by omega⟩

def odd {t : ℕ} (bits : Fin (2 * t) → Bool) (j : Fin t) : Bool :=
  bits ⟨2 * j.val + 1, by omega⟩

def interleave {t : ℕ} (bits : (Fin t → Bool) × (Fin t → Bool))
    (j : Fin (2 * t)) : Bool :=
  if j.val % 2 = 0 then bits.1 ⟨j.val / 2, by omega⟩
  else bits.2 ⟨j.val / 2, by omega⟩

@[simp] theorem even_interleave {t : ℕ} (bits : (Fin t → Bool) × (Fin t → Bool)) :
    even (interleave bits) = bits.1 := by
  funext j
  simp [even, interleave]

@[simp] theorem odd_interleave {t : ℕ} (bits : (Fin t → Bool) × (Fin t → Bool)) :
    odd (interleave bits) = bits.2 := by
  funext j
  simp [odd, interleave, Nat.add_div]

def equiv (t : ℕ) : ((Fin t → Bool) × (Fin t → Bool)) ≃ (Fin (2 * t) → Bool) where
  toFun := interleave
  invFun := fun bits => (even bits, odd bits)
  left_inv bits := by simp only [even_interleave, odd_interleave]
  right_inv bits := by
    funext j
    simp only [interleave, even, odd]
    split <;> rename_i hj
    · congr 1
      apply Fin.ext
      dsimp only
      have hm := Nat.mod_add_div j.val 2
      omega
    · congr 1
      apply Fin.ext
      dsimp only
      have hm := Nat.mod_add_div j.val 2
      have hb := Nat.mod_lt j.val (by omega : 0 < 2)
      omega

theorem pad_even {t : ℕ} (bits : Fin (2 * t) → Bool) :
    (fun j => padBits bits (2 * j)) = padBits (even bits) := by
  funext j
  by_cases hj : j < t
  · simp only [padBits, show 2 * j < 2 * t by omega, hj, ↓reduceDIte, even]
  · simp only [padBits, show ¬2 * j < 2 * t by omega, hj, ↓reduceDIte]

open scoped Classical

theorem successful_count (t : ℕ) (Q : (Fin t → Bool) → Prop) :
    (Finset.univ.filter (fun bits : Fin (2 * t) → Bool => Q (even bits))).card =
      2 ^ t * (Finset.univ.filter Q).card := by
  have h := Equiv.sum_comp (equiv t) (fun bits => if Q (even bits) then (1 : ℕ) else 0)
  rw [Fintype.sum_prod_type] at h
  simp only [equiv, Equiv.coe_fn_mk, even_interleave] at h
  calc
    _ = ∑ x : Fin t → Bool, if Q x then 2 ^ t else 0 := by
      simpa [Finset.sum_boole, Fintype.card_fun] using h.symm
    _ = _ := by simp [Finset.sum_ite, Nat.mul_comm]

theorem success_transfer (t : ℕ) (Q : (Fin t → Bool) → Prop)
    (h : 7 * 2 ^ t ≤ 8 * (Finset.univ.filter Q).card) :
    7 * 2 ^ (2 * t) ≤ 8 * (Finset.univ.filter
      (fun bits : Fin (2 * t) → Bool => Q (even bits))).card := by
  rw [successful_count]
  have hh := Nat.mul_le_mul_left (2 ^ t) h
  rw [show 2 * t = t + t by omega, pow_add]
  nlinarith only [hh]

end TwoPhase
end MeanPayoff
end

end OAI
