import OAI.Analysis.BoundedHochschild.FiniteGroupBarOperators

namespace OAI

/-! An explicit input formula for the bounded bar-insertion operators. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

def barPrefixTuple {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (x : Fin n → M) : Fin n → M :=
  fun j => if j.castSucc < i then
    (u j.castSucc.castSucc : M) * x j * star (u j.castSucc.succ : M) else x j

lemma cochainUnitaryTuple_prefix_insert {n : ℕ} (u : Fin (n + 2) → unitary M)
    (i : Fin (n + 1)) (x : Fin n → M) :
    cochainUnitaryTuple (unitaryPrefix u (i.val + 1)) (i.insertNth 1 x) =
      i.insertNth (u i.castSucc : M) (barPrefixTuple u i x) := by
  symm
  apply (Fin.insertNth_eq_iff).mpr
  constructor
  · simp [cochainUnitaryTuple, unitaryPrefix]
  · ext j
    change barPrefixTuple u i x j =
      cochainUnitaryTuple (unitaryPrefix u (i.val + 1)) (i.insertNth 1 x) (i.succAbove j)
    rw [show cochainUnitaryTuple (unitaryPrefix u (i.val + 1)) (i.insertNth 1 x) (i.succAbove j) =
        (unitaryPrefix u (i.val + 1) (i.succAbove j).castSucc : M) * x j *
          star (unitaryPrefix u (i.val + 1) (i.succAbove j).succ : M) by
      simp only [cochainUnitaryTuple, Fin.insertNth_apply_succAbove]]
    by_cases hji : j.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt i j hji]
      have ha : j.val < i.val + 1 := by have h := hji; simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
      have hb : j.val + 1 < i.val + 1 := by have h := hji; simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
      simp only [barPrefixTuple, hji, ite_true, unitaryPrefix, Fin.val_castSucc, Fin.val_succ, ha, hb]
    · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
      have ha : ¬j.val + 1 < i.val + 1 := by
        have h := hji
        simp only [Fin.lt_def, Fin.val_castSucc] at h
        omega
      have hb : ¬j.val + 1 + 1 < i.val + 1 := by omega
      simp only [barPrefixTuple, hji, ite_false, unitaryPrefix, Fin.val_castSucc, Fin.val_succ,
        ha, hb, OneMemClass.coe_one, star_one, one_mul, mul_one]

lemma barInsertion_prefix_value {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) (x : Fin n → M) :
    barInsertion u i f x = star (u 0 : M) *
      f (i.insertNth (u i.castSucc : M) (barPrefixTuple u i x)) := by
  rw [barInsertion_value, cochainUnitaryTuple_prefix_insert]

end BoundedHochschild.KadisonRingrose

end

end OAI
