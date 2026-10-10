import OAI.Analysis.BoundedHochschild.FiniteGroupMultimodularity

namespace OAI

/-! A multimodular cochain is fixed by independent boundary transports
from its subalgebra, hence by finite-group averaging in that subalgebra. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma cochainUnitaryTransport_one {n : ℕ} (f : Cochain M n) :
    cochainUnitaryTransport (fun _ => 1) f = f := by
  ext x
  simp only [cochainUnitaryTransport_apply, OneMemClass.coe_one, star_one, one_mul, mul_one]
  congr 1
  funext i
  simp only [cochainUnitaryTuple, OneMemClass.coe_one, star_one, one_mul, mul_one]

def unitaryPrefix {n : ℕ} (u : Fin (n + 1) → unitary M) (k : ℕ) : Fin (n + 1) → unitary M :=
  fun i => if i.val < k then u i else 1

lemma unitaryPrefix_step {n : ℕ} (u : Fin (n + 1) → unitary M) (k : ℕ) (hk : k < n + 1) :
    unitaryPrefix u (k + 1) =
      unitaryPrefix u k * Function.update (fun _ => 1) ⟨k, hk⟩ (u ⟨k, hk⟩) := by
  funext i
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp [unitaryPrefix]
  · have hv : i.val ≠ k := fun h => hi (Fin.ext h)
    by_cases hlt : i.val < k
    · simp [unitaryPrefix, hlt, Nat.lt_succ_of_lt hlt, hi]
    · have hn : ¬i.val < k + 1 := by omega
      simp [unitaryPrefix, hlt, hn, hi]

lemma cochainUnitaryTransport_fixed_of_coordinates {n : ℕ}
    (u : Fin (n + 1) → unitary M) (f : Cochain M n)
    (hf : ∀ i, cochainUnitaryTransport (Function.update (fun _ => 1) i (u i)) f = f) :
    cochainUnitaryTransport u f = f := by
  have hp : ∀ k, k ≤ n + 1 → cochainUnitaryTransport (unitaryPrefix u k) f = f := by
    intro k
    induction k with
    | zero =>
        intro _
        have hzero : unitaryPrefix u 0 = (fun _ => 1) := by
          funext i
          simp [unitaryPrefix]
        rw [hzero]
        exact cochainUnitaryTransport_one f
    | succ k ih =>
        intro hk
        rw [unitaryPrefix_step u k (by omega), ← cochainUnitaryTransport_comp, ih (by omega)]
        exact hf _
  have hu : unitaryPrefix u (n + 1) = u := by
    funext i
    simp only [unitaryPrefix, i.isLt, ite_true]
  rw [← hu]
  exact hp _ le_rfl

lemma cochainUnitaryTransport_coordinate_fixed {n : ℕ}
    (R : StarSubalgebra ℂ M) (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (i : Fin (n + 2)) (u : unitary M) (hu : (u : M) ∈ R) :
    cochainUnitaryTransport (Function.update (fun _ => 1) i u) f = f := by
  have hcancel (a : M) : star (u : M) * ((u : M) * a) = a := by
    rw [← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]
  ext x
  by_cases hi : i = 0
  · subst i
    rw [cochainUnitaryTransport_apply, cochainUnitaryTuple_left, hf.left (u : M) hu x]
    simp only [Function.update_self, Function.update_of_ne (by simp : Fin.last (n + 1) ≠ 0),
      OneMemClass.coe_one, mul_one]
    exact hcancel _
  · by_cases hl : i = Fin.last (n + 1)
    · subst i
      rw [cochainUnitaryTransport_apply, cochainUnitaryTuple_right, hf.right _ (star_mem hu) x]
      simp only [Function.update_self, Function.update_of_ne (by simp : (0 : Fin (n + 2)) ≠ Fin.last (n + 1)),
        OneMemClass.coe_one, star_one, one_mul, mul_assoc,
        Unitary.star_mul_self_of_mem u.property, mul_one]
    · let j : Fin n := ⟨i.val - 1, by
        have h0 : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
        have hlast : i.val < n + 1 := lt_of_le_of_ne i.is_le (fun h => hl (Fin.ext h))
        omega⟩
      have hij : i = j.castSucc.succ := by
        apply Fin.ext
        dsimp [j]
        have h0 : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
        omega
      rw [hij, cochainUnitaryTransport_apply, cochainUnitaryTuple_internal]
      have hzero : (0 : Fin (n + 2)) ≠ j.castSucc.succ := Ne.symm (Fin.succ_ne_zero _)
      have hlast : Fin.last (n + 1) ≠ j.castSucc.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hv
        omega
      simp only [Function.update_of_ne hzero, Function.update_of_ne hlast,
        OneMemClass.coe_one, star_one, one_mul, mul_one]
      let y := Function.update x j.succ ((u : M) * x j.succ)
      have hleft : Function.update y j.castSucc (y j.castSucc * star (u : M)) =
          Function.update (Function.update x j.castSucc (x j.castSucc * star (u : M)))
            j.succ ((u : M) * x j.succ) := by
        ext k
        by_cases hk : k = j.castSucc
        · subst k
          simp [y, ne_of_lt (Fin.castSucc_lt_succ (i := j))]
        · by_cases hk' : k = j.succ
          · subst k
            simp [y, ne_of_gt (Fin.castSucc_lt_succ (i := j))]
          · simp [y, hk, hk']
      have hright : Function.update y j.succ (star (u : M) * y j.succ) = x := by
        simp only [y, Function.update_self, hcancel, Function.update_idem, Function.update_eq_self]
      have h := hf.balance _ (star_mem hu) y j
      rw [hleft, hright] at h
      exact h

lemma cochainUnitaryTransport_fixed_of_multimodular {n : ℕ}
    (R : StarSubalgebra ℂ M) (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (u : Fin (n + 2) → unitary M) (hu : ∀ i, (u i : M) ∈ R) :
    cochainUnitaryTransport u f = f :=
  cochainUnitaryTransport_fixed_of_coordinates u f
    (fun i => cochainUnitaryTransport_coordinate_fixed R f hf i (u i) (hu i))

lemma finiteGroupCochainAverage_fixes {G : Type*} [Group G] [Fintype G]
    (ρ : G →* unitary M) {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 1))
    (hf : MultimodularOver R f) (hρ : ∀ g, (ρ g : M) ∈ R) : finiteGroupCochainAverage ρ f = f := by
  unfold finiteGroupCochainAverage
  have h (g : Fin (n + 2) → G) : cochainUnitaryTransport (fun i => ρ (g i)) f = f :=
    cochainUnitaryTransport_fixed_of_multimodular R f hf _ (fun i => hρ (g i))
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)), one_smul]

end BoundedHochschild.KadisonRingrose

end

end OAI
