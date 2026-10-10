import OAI.Analysis.BoundedHochschild.FiniteGroupBarOperators
import OAI.Analysis.BoundedHochschild.UnitInsertionFaces
import OAI.Analysis.BoundedHochschild.UnitaryPrefixDeletion

namespace OAI

/-! The elementary Hochschild-face formulas for bounded bar insertions.
The finite signed averaging identity is proved separately from these
pointwise operator identities. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma barInsertion_leftCoboundary_zero {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) : barInsertion u 0 (leftCoboundary f) = f := by
  unfold barInsertion
  rw [cochainUnitaryTransport_leftCoboundary, unitaryPrefix_tail]
  simp only [Fin.val_zero]
  have hp : unitaryPrefix (Fin.tail u) 0 = (fun _ => 1) := by
    funext j
    simp [unitaryPrefix]
  rw [hp, cochainUnitaryTransport_one, curryMid_leftCoboundary_zero]

lemma barInsertion_leftCoboundary_succ {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.succ (leftCoboundary f) =
      leftCoboundary (barInsertion (Fin.tail u) i f) := by
  unfold barInsertion
  rw [cochainUnitaryTransport_leftCoboundary, unitaryPrefix_tail,
    curryMid_leftCoboundary_succ]
  simp only [Fin.val_succ]

lemma barInsertion_rightCoboundary_last {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) :
    barInsertion u (Fin.last (n + 1)) (rightCoboundary f) =
      cochainUnitaryTransport (Fin.init u) f := by
  unfold barInsertion
  rw [cochainUnitaryTransport_rightCoboundary]
  change (rightCoboundary (cochainUnitaryTransport
    (Fin.init (unitaryPrefix u (n + 2))) f)).curryMid (Fin.last (n + 1)) 1 = _
  rw [unitaryPrefix_init, curryMid_rightCoboundary_last]
  have hp : unitaryPrefix (Fin.init u) (n + 2) = Fin.init u := by
    funext j
    simp only [unitaryPrefix, j.isLt, ite_true]
  rw [hp]

lemma barInsertion_rightCoboundary_castSucc {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.castSucc (rightCoboundary f) =
      rightCoboundary (barInsertion (Fin.init u) i f) := by
  unfold barInsertion
  rw [cochainUnitaryTransport_rightCoboundary]
  change (rightCoboundary (cochainUnitaryTransport
    (Fin.init (unitaryPrefix u (i.val + 1))) f)).curryMid i.castSucc 1 = _
  rw [unitaryPrefix_init, curryMid_rightCoboundary_castSucc]

lemma barInsertion_middleCoboundary_castSucc {n : ℕ}
    (u : Fin (n + 3) → unitary M) (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.castSucc (middleCoboundary f i) =
      cochainUnitaryTransport (unitaryPrefix (i.castSucc.succ.removeNth u) (i.val + 1)) f := by
  unfold barInsertion
  simp only [Fin.val_castSucc]
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_after u i.castSucc.succ (i.val + 1) (by simp),
    curryMid_middleCoboundary_castSucc]

lemma barInsertion_middleCoboundary_succ {n : ℕ}
    (u : Fin (n + 3) → unitary M) (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.succ (middleCoboundary f i) =
      cochainUnitaryTransport (unitaryPrefix (i.castSucc.succ.removeNth u) (i.val + 1)) f := by
  unfold barInsertion
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_before u i.castSucc.succ (i.succ.val + 1) (by simp),
    curryMid_middleCoboundary_succ]
  rfl

lemma barInsertion_middleCoboundary_after {n : ℕ}
    (u : Fin (n + 4) → unitary M) (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i.val ≤ j.val) :
    barInsertion u i.castSucc (middleCoboundary f j.succ) =
      middleCoboundary (barInsertion (j.succ.castSucc.succ.removeNth u) i f) j := by
  unfold barInsertion
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_after u j.succ.castSucc.succ (i.castSucc.val + 1)
      (by simp only [Fin.val_castSucc, Fin.val_succ]; omega),
    curryMid_middleCoboundary_after _ i j hij]
  simp only [Fin.val_castSucc]

lemma barInsertion_middleCoboundary_before {n : ℕ}
    (u : Fin (n + 4) → unitary M) (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.val < i.val) :
    barInsertion u i.succ (middleCoboundary f j.castSucc) =
      middleCoboundary (barInsertion (j.castSucc.castSucc.succ.removeNth u) i f) j := by
  unfold barInsertion
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_before u j.castSucc.castSucc.succ (i.succ.val + 1)
      (by simp only [Fin.val_castSucc, Fin.val_succ]; omega),
    curryMid_middleCoboundary_before _ i j hji]
  simp only [Fin.val_succ, Nat.add_sub_cancel]

end BoundedHochschild.KadisonRingrose

end

end OAI
