import Mathlib

namespace OAI

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace EdgeCoordinates

def shear {n : ℕ} (j : Option (Fin n)) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun z := fun i => if i=0 then z 0 - j.elim 0 (fun k => z k.succ) else z i
  invFun z := fun i => if i=0 then z 0 + j.elim 0 (fun k => z k.succ) else z i
  left_inv z := by
    ext i
    cases j with
    | none => by_cases hi : i=0 <;> simp [hi]
    | some k => by_cases hi : i=0 <;> simp [hi]
  right_inv z := by
    ext i
    cases j with
    | none => by_cases hi : i=0 <;> simp [hi]
    | some k => by_cases hi : i=0 <;> simp [hi]
  map_add' z w := by
    ext i
    cases j with
    | none => by_cases hi : i=0 <;> simp [hi]
    | some k =>
      by_cases hi : i=0 <;> simp [hi]
      ring
  map_smul' c z := by
    ext i
    cases j with
    | none => by_cases hi : i=0 <;> simp [hi]
    | some k => by_cases hi : i=0 <;> simp [hi, mul_sub]

@[simp] lemma shear_zero {n : ℕ} (j : Option (Fin n)) (z : Fin (n+1) → ℝ) :
    shear j z 0 = z 0 - j.elim 0 (fun k => z k.succ) := by simp [shear]

@[simp] lemma shear_succ {n : ℕ} (j : Option (Fin n)) (z : Fin (n+1) → ℝ) (i : Fin n) :
    shear j z i.succ = z i.succ := by simp [shear]

@[simp] lemma shear_symm_zero {n : ℕ} (j : Option (Fin n)) (z : Fin (n+1) → ℝ) :
    (shear j).symm z 0 = z 0 + j.elim 0 (fun k => z k.succ) := by simp [shear]

@[simp] lemma shear_symm_succ {n : ℕ} (j : Option (Fin n)) (z : Fin (n+1) → ℝ) (i : Fin n) :
    (shear j).symm z i.succ = z i.succ := by simp [shear]

lemma shear_measurePreserving {n : ℕ} (j : Option (Fin n)) :
    MeasurePreserving (shear j) := by
  cases j with
  | none =>
    have he : (shear (none : Option (Fin n))) = (id : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ)) := by
      funext z i
      by_cases hi : i=0 <;> simp [shear, hi]
    rw [he]
    exact MeasurePreserving.id volume
  | some k =>
    let t : Matrix.TransvectionStruct (Fin (n+1)) ℝ := ⟨0,k.succ,Fin.succ_ne_zero k |>.symm,-1⟩
    have ht := Real.volume_preserving_transvectionStruct t
    convert ht using 1
    ext z i
    simp [shear, t, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
      Matrix.toLin'_apply, Matrix.single_mulVec]
    by_cases hi : i=0
    · simp [hi, sub_eq_add_neg]
    · simp [hi]

lemma norm_shear_le {n : ℕ} (j : Option (Fin n)) (z : Fin (n+1) → ℝ) :
    ‖shear j z‖ ≤ 2*‖z‖ := by
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  by_cases hi : i=0
  · subst i
    rw [shear_zero]
    cases j with
    | none => simpa using (norm_le_pi_norm z 0).trans (by nlinarith [norm_nonneg z])
    | some k =>
      exact (norm_sub_le _ _).trans (by
        simpa [two_mul] using add_le_add (norm_le_pi_norm z 0) (norm_le_pi_norm z k.succ))
  · simp only [shear, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false]
    exact (norm_le_pi_norm z i).trans (by nlinarith [norm_nonneg z])

lemma norm_shear_symm_le {n : ℕ} (j : Option (Fin n)) (z : Fin (n+1) → ℝ) :
    ‖(shear j).symm z‖ ≤ 2*‖z‖ := by
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  cases i using Fin.cases with
  | zero =>
    rw [shear_symm_zero]
    cases j with
    | none => simpa using (norm_le_pi_norm z 0).trans (by nlinarith [norm_nonneg z])
    | some k =>
      exact (norm_add_le _ _).trans (by
        simpa [two_mul] using add_le_add (norm_le_pi_norm z 0) (norm_le_pi_norm z k.succ))
  | succ i =>
    rw [shear_symm_succ]
    exact (norm_le_pi_norm z i.succ).trans (by nlinarith [norm_nonneg z])

def signedShear {n : ℕ} (j : Option (Fin n)) (negate : Bool) :
    (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) :=
  if negate then (shear j).trans (LinearEquiv.neg ℝ) else shear j

lemma signedShear_measurePreserving {n : ℕ} (j : Option (Fin n)) (b : Bool) :
    MeasurePreserving (signedShear j b) := by
  cases b
  · simpa [signedShear] using shear_measurePreserving j
  · change MeasurePreserving (Neg.neg ∘ (shear j))
    exact (Measure.measurePreserving_neg (volume : Measure (Fin (n+1) → ℝ))).comp
      (shear_measurePreserving j)

lemma norm_signedShear_le {n : ℕ} (j : Option (Fin n)) (b : Bool) (z : Fin (n+1) → ℝ) :
    ‖signedShear j b z‖ ≤ 2*‖z‖ := by
  cases b <;> simpa [signedShear] using norm_shear_le j z

lemma norm_signedShear_symm_le {n : ℕ} (j : Option (Fin n)) (b : Bool) (z : Fin (n+1) → ℝ) :
    ‖(signedShear j b).symm z‖ ≤ 2*‖z‖ := by
  cases b
  · simpa [signedShear] using norm_shear_symm_le j z
  · simpa [signedShear] using norm_shear_symm_le j (-z)

end EdgeCoordinates

namespace EdgeCoordinates

lemma exists_indexEquiv {ι : Type*} [Fintype ι] (y : ι) :
    ∃ n : ℕ, ∃ e : ι ≃ Fin (n+1), e y=0 := by
  classical
  have hc : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨y⟩
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  let e₀ : ι ≃ Fin (n+1) := (Fintype.equivFin ι).trans (finCongr hn)
  exact ⟨n,e₀.trans (Equiv.swap (e₀ y) 0), by simp⟩

def reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1)) :
    (ι → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) := LinearEquiv.piCongrLeft ℝ (fun _ => ℝ) e

@[simp] lemma reindex_apply {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1))
    (a : ι → ℝ) (i : Fin (n+1)) : reindex e a i = a (e.symm i) := by simp [reindex, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

@[simp] lemma norm_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1)) (a : ι → ℝ) :
    ‖reindex e a‖ = ‖a‖ := by
  apply le_antisymm
  · apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr
    intro i
    simpa only [reindex_apply] using norm_le_pi_norm a (e.symm i)
  · apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr
    intro i
    simpa using norm_le_pi_norm (reindex e a) (e i)

lemma norm_reindex_symm {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1)) (z : Fin (n+1) → ℝ) :
    ‖(reindex e).symm z‖ = ‖z‖ := by
  simpa using (norm_reindex e ((reindex e).symm z)).symm

lemma reindex_measurePreserving {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1)) :
    MeasurePreserving (reindex e) := by
  exact volume_measurePreserving_piCongrLeft (fun _ : Fin (n+1) => ℝ) e

def edgeMap {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1))
    (j : Option (Fin n)) (b : Bool) : (ι → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) :=
  (reindex e).trans (signedShear j b)

lemma edgeMap_measurePreserving {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin (n+1)) (j : Option (Fin n)) (b : Bool) :
    MeasurePreserving (edgeMap e j b) :=
  (signedShear_measurePreserving j b).comp (reindex_measurePreserving e)

lemma norm_edgeMap_symm_le {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin (n+1)) (j : Option (Fin n)) (b : Bool) (z : Fin (n+1) → ℝ) :
    ‖(edgeMap e j b).symm z‖ ≤ 2*‖z‖ := by
  simpa only [edgeMap, LinearEquiv.trans_symm, LinearEquiv.trans_apply, norm_reindex_symm]
    using norm_signedShear_symm_le j b z

end EdgeCoordinates

namespace EdgeCoordinates

lemma edgeMap_zero {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n+1))
    (j : Option (Fin n)) (b : Bool) (a : ι → ℝ) :
    edgeMap e j b a 0 = (if b then -1 else 1)*
      (a (e.symm 0)-j.elim 0 (fun k => a (e.symm k.succ))) := by
  cases b <;> simp [edgeMap, signedShear, LinearEquiv.trans_apply, reindex_apply]

lemma exists_edge_coordinates {ι : Type*} [Fintype ι] {n : ℕ}
    (e₀ : ι ≃ Fin (n+1)) (y : ι) (x : Option ι) (τ : ℝ)
    (hτ : |τ|=1) (hxy : ∀ i, x=some i → i≠y) :
    ∃ E : (ι → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ),
      MeasurePreserving E ∧ (∀ z, ‖E.symm z‖ ≤ 2*‖z‖) ∧
      ∀ a, E a 0 = τ*(a y-x.elim 0 a) := by
  classical
  let e := e₀.trans (Equiv.swap (e₀ y) 0)
  have hey : e y=0 := by simp [e]
  have hey' : e.symm 0=y := by rw [Equiv.symm_apply_eq]; exact hey.symm
  have hsign : ∃ b : Bool, (if b then (-1:ℝ) else 1)=τ := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hτ with ht | ht
    · exact ⟨false,ht.symm⟩
    · exact ⟨true,ht.symm⟩
  obtain ⟨b,hb⟩ := hsign
  cases x with
  | none =>
    refine ⟨edgeMap e none b,edgeMap_measurePreserving _ _ _,norm_edgeMap_symm_le _ _ _,?_⟩
    intro a
    simp [edgeMap_zero,hb,hey']
  | some i =>
    have hne : e i ≠ 0 := by
      intro hi
      exact hxy i rfl (e.injective (hi.trans hey.symm))
    obtain ⟨k,hk⟩ := Fin.eq_zero_or_eq_succ (e i) |>.resolve_left hne
    have hk' : e.symm k.succ=i := by rw [Equiv.symm_apply_eq]; exact hk.symm
    refine ⟨edgeMap e (some k) b,edgeMap_measurePreserving _ _ _,norm_edgeMap_symm_le _ _ _,?_⟩
    intro a
    simp [edgeMap_zero,hb,hey',hk']

end EdgeCoordinates

end

end OAI
