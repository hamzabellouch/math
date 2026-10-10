import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedCut

namespace OAI

/-! Every sublist of the assigned segments is realized by deleting its omitted segments. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

inductive SystemAssignedAmounts (Q : Finset V) : List (List V) → List ℕ → Prop
  | nil : SystemAssignedAmounts Q [] []
  | cons {l : List V} {C : List (List V)} {w W : List ℕ}
      (head : AssignedAmounts Q l w) (tail : SystemAssignedAmounts Q C W) :
      SystemAssignedAmounts Q (l :: C) (w ++ W)

namespace SystemAssignedAmounts

theorem exists_of_raw (S : RawPathSystem G Q) : ∃ w, SystemAssignedAmounts Q S.chains w := by
  have hex : ∀ C : List (List V), (∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)) →
      (∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) →
      ∃ w, SystemAssignedAmounts Q C w := by
    intro C
    induction C with
    | nil => intros; exact ⟨[], .nil⟩
    | cons l C ih =>
      intro hends hsteps
      obtain ⟨w, hw⟩ := exists_assignedAmounts (hends l (by simp)) (hsteps l (by simp))
      obtain ⟨W, hW⟩ := ih (fun l hl => hends l (by simp [hl])) (fun l hl => hsteps l (by simp [hl]))
      exact ⟨w ++ W, .cons hw hW⟩
  exact hex S.chains S.endpoints S.no_clique_steps

theorem append {C D : List (List V)} {w W : List ℕ}
    (hC : SystemAssignedAmounts Q C w) (hD : SystemAssignedAmounts Q D W) :
    SystemAssignedAmounts Q (C ++ D) (w ++ W) := by
  induction hC with
  | nil => simpa using hD
  | cons h ht ih => simpa only [List.cons_append, List.append_assoc] using SystemAssignedAmounts.cons h ih

theorem sum_eq {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w) :
    w.sum = chainOutsideCount Q C.flatten := by
  induction h with
  | nil => rfl
  | cons hh ht ih =>
    simp only [List.sum_append, List.flatten_cons, hh.sum_eq, ih,
      chainOutsideCount, List.filter_append, List.length_append]

theorem length_eq {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w) :
    w.length = rawAssignedCount Q C := by
  induction h with
  | nil => rfl
  | cons hh ht ih =>
    simp only [List.length_append, hh.length_eq, ih, rawAssignedCount, List.map_cons, List.sum_cons]

theorem positive {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w) :
    ∀ a ∈ w, 0 < a := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hh.positive a ha
    · exact ih a ha


theorem cut {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w)
    {A B : List ℕ} {a : ℕ} (heq : w = A ++ a :: B) :
    ∃ P R l A' B' U W,
      C = P ++ l :: R ∧ SystemAssignedAmounts Q P U ∧
      AssignedAmounts Q l (A' ++ a :: B') ∧ SystemAssignedAmounts Q R W ∧
      A = U ++ A' ∧ B = B' ++ W := by
  induction h generalizing A B a with
  | nil => cases A <;> simp at heq
  | @cons l C w W hh ht ih =>
    have htail (D : List ℕ) (hA : A = w ++ D) (hW : W = D ++ a :: B) :
        ∃ P R l' A' B' U W',
          l :: C = P ++ l' :: R ∧ SystemAssignedAmounts Q P U ∧
          AssignedAmounts Q l' (A' ++ a :: B') ∧ SystemAssignedAmounts Q R W' ∧
          A = U ++ A' ∧ B = B' ++ W' := by
      obtain ⟨P, R, l', A', B', U, W', hC, hP, hl, hR, hD, hB⟩ := ih hW
      refine ⟨l :: P, R, l', A', B', w ++ U, W', ?_, .cons hh hP, hl, hR, ?_, hB⟩
      · simp only [List.cons_append, hC]
      · rw [hA, hD, List.append_assoc]
    rcases List.append_eq_append_iff.mp heq with ⟨D, hA, hW⟩ | ⟨D, hw, hB⟩
    · exact htail D hA hW
    · cases D with
      | nil =>
        exact htail [] (by simpa using hw.symm) (by simpa using hB.symm)
      | cons b D =>
        have hb : a = b ∧ B = D ++ W := List.cons.inj hB
        obtain ⟨rfl, hB'⟩ := hb
        exact ⟨[], C, l, A, D, [], W, rfl, .nil, by simpa using hw ▸ hh, ht, rfl, hB'⟩

theorem delete_one (S : RawPathSystem G Q) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w)
    {A B : List ℕ} {a : ℕ} (heq : w = A ++ a :: B) :
    ∃ T : RawPathSystem G Q,
      SystemAssignedAmounts Q T.chains (A ++ B) ∧ T.vertices ⊆ S.vertices := by
  obtain ⟨P, R, l, A', B', U, W, hsys, hP, hl, hR, hA, hB⟩ := h.cut heq
  obtain ⟨D, J, E, x, y, hl, hx, hy, hJ, _, hpre, hsuf⟩ := hl.cut rfl
  obtain ⟨T, hT, _, _, hsub⟩ := S.delete_assigned_path (hsys.trans (by rw [hl])) hx hy hJ
  refine ⟨T, ?_, hsub⟩
  rw [hT, hA, hB]
  simpa only [List.append_assoc] using hP.append (.cons hpre (.cons hsuf hR))

theorem realize_sublist_aux {B C : List ℕ} (hBC : B.Sublist C) :
    ∀ (A : List ℕ) (S : RawPathSystem G Q),
      SystemAssignedAmounts Q S.chains (A ++ C) →
      ∃ T : RawPathSystem G Q,
        SystemAssignedAmounts Q T.chains (A ++ B) ∧ T.vertices ⊆ S.vertices := by
  induction hBC with
  | slnil => intro A S h; exact ⟨S, h, fun _ hv => hv⟩
  | @cons B C a hBC ih =>
    intro A S h
    obtain ⟨T, hT, hsub⟩ := delete_one S h rfl
    obtain ⟨U, hU, husub⟩ := ih A T hT
    exact ⟨U, hU, fun v hv => hsub (husub hv)⟩
  | @cons_cons B C a hBC ih =>
    intro A S h
    obtain ⟨T, hT, hsub⟩ := ih (A ++ [a]) S (by simpa only [List.append_assoc, List.singleton_append] using h)
    exact ⟨T, by simpa only [List.append_assoc, List.singleton_append] using hT, hsub⟩

theorem realize_sublist (S : RawPathSystem G Q) {w w' : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hsub : w'.Sublist w) :
    ∃ T : ExpandedPathSystem G Q, T.amount = w'.sum ∧ T.assignedCount = w'.length := by
  obtain ⟨T, hT, _⟩ := realize_sublist_aux hsub [] S (by simpa using h)
  refine ⟨T.normalize, ?_, ?_⟩
  · rw [RawPathSystem.normalize_amount, T.amount_eq_outside_count]
    exact hT.sum_eq.symm
  · rw [RawPathSystem.normalize_assignedCount]
    exact hT.length_eq.symm

end SystemAssignedAmounts

end CycleClique.Construction

end OAI
