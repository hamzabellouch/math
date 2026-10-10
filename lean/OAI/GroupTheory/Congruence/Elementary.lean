import Mathlib

namespace OAI

noncomputable section

/-!
Elementary matrices, Euclidean generation, block matrices, and residue-field pivot arguments.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

abbrev E {i j : Fin n} (h : i ≠ j) (c : A) :=
  Matrix.SpecialLinearGroup.transvection h c

theorem E_mul_apply {i j : Fin n} (h : i ≠ j) (c : A)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (E h c * g : Matrix.SpecialLinearGroup (Fin n) A) a b =
      g a b + if a = i then c * g j b else 0 := by
  change ((Matrix.transvection i j c) * g.val) a b = _
  by_cases ha : a = i
  · subst a
    simp
  · simp [ha]

def Upper (g : Matrix.SpecialLinearGroup (Fin n) A) : Prop :=
  ∀ i j, j ≤ i → g i j = (1 : Matrix (Fin n) (Fin n) A) i j

theorem upper_E_mul {i j : Fin n} (hij : i < j) (c : A)
    {g : Matrix.SpecialLinearGroup (Fin n) A} (hg : Upper g) :
    Upper (E hij.ne c * g) := by
  intro a b hba
  rw [E_mul_apply, hg a b hba]
  by_cases ha : a = i
  · subst a
    rw [ite_eq_left rfl, hg j b (hba.trans hij.le), Matrix.one_apply_ne (ne_of_gt (lt_of_le_of_lt hba hij))]
    simp
  · simp [ha]

def Cleared (g : Matrix.SpecialLinearGroup (Fin n) A) (k : ℕ) : Prop :=
  ∀ i j, i.val * n + j.val < k → g i j = (1 : Matrix (Fin n) (Fin n) A) i j

theorem clear_step (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i < j) c, E h.ne c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : Upper g)
    (k : ℕ) (hk : k < n * n) (hc : Cleared g k) :
    ∃ e ∈ H, Upper (e * g) ∧ Cleared (e * g) (k + 1) := by
  have hn : 0 < n := by nlinarith
  let i : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let j : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
  have hkij : i.val * n + j.val = k := by
    dsimp [i, j]
    simpa [Nat.mul_comm] using Nat.div_add_mod k n
  by_cases hij : i < j
  · refine ⟨E hij.ne (-g i j), hE i j hij _, upper_E_mul hij _ hg, ?_⟩
    intro a b hab
    rw [E_mul_apply]
    by_cases ha : a = i
    · subst a
      rw [ite_eq_left rfl]
      have hbj : b ≤ j := by change b.val ≤ j.val; omega
      rcases hbj.eq_or_lt with rfl | hbj
      · rw [hg j j le_rfl]
        simp [hij.ne]
      · rw [hg j b hbj.le, Matrix.one_apply_ne hbj.ne.symm, mul_zero, add_zero]
        exact hc i b (by omega)
    · rw [ite_eq_right ha, add_zero]
      apply hc a b
      have hne : a.val * n + b.val ≠ k := by
        intro he
        have := congrArg (fun r => r / n) he
        have hab' : b.val < n := b.isLt
        rw [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt hab', add_zero] at this
        exact ha (Fin.ext this)
      omega
  · refine ⟨1, H.one_mem, by simpa using hg, ?_⟩
    rw [one_mul]
    intro a b hab
    by_cases hk' : a.val * n + b.val < k
    · exact hc a b hk'
    · have he : a.val * n + b.val = k := by omega
      have hai : a = i := by
        apply Fin.ext
        have := congrArg (fun r => r / n) he
        dsimp [i]
        simpa only [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero] using this
      have hbj : b = j := by
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt b.isLt] using this
      subst a; subst b
      exact hg i j (le_of_not_gt hij)

theorem upper_mem_of_transvections (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i < j) c, E h.ne c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : Upper g) : g ∈ H := by
  have hsteps : ∀ k, k ≤ n * n → ∃ h ∈ H, Upper (h * g) ∧ Cleared (h * g) k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hg, by intro i j h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hu, hc⟩ := ih (by omega)
      obtain ⟨e, he, hu', hc'⟩ := clear_step H hE (h * g) hu k (by omega) hc
      exact ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using hu',
        by simpa only [mul_assoc] using hc'⟩
  obtain ⟨h, hh, _, hc⟩ := hsteps (n * n) le_rfl
  have he : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply hc
    have hi := i.isLt
    have hj := j.isLt
    nlinarith
  have hginv : g = h⁻¹ := (eq_inv_of_mul_eq_one_right he)
  rw [hginv]
  exact H.inv_mem hh

theorem E_commutator {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : A) : E hij a * E hjk b * (E hij a)⁻¹ * (E hjk b)⁻¹ = E hik (a * b) := by
  rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
    (1 + Matrix.single i j (-a)) * (1 + Matrix.single j k (-b)) =
      1 + Matrix.single i k (a * b)
  simp [mul_add, add_mul,
    hij.symm, hjk.symm, hik.symm, ← Matrix.single_neg]
  abel

end CoboundaryExpanders.Elementary

namespace CoboundaryExpanders.Blocks
variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def reindexSL (e : ι ≃ κ) : Matrix.SpecialLinearGroup ι A ≃* Matrix.SpecialLinearGroup κ A where
  toFun g := ⟨Matrix.reindex e e g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  left_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  right_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  map_mul' g h := by apply Subtype.ext; exact (Matrix.reindexRingEquiv A e).map_mul _ _

@[simp] theorem reindexSL_apply (e : ι ≃ κ) (g : Matrix.SpecialLinearGroup ι A) (i j : ι) :
    reindexSL e g (e i) (e j) = g i j := by
  change g.val (e.symm (e i)) (e.symm (e j)) = _
  simp

theorem reindexSL_map (e : ι ≃ κ) (f : A →+* B) (g : Matrix.SpecialLinearGroup ι A) :
    Matrix.SpecialLinearGroup.map f (reindexSL e g) = reindexSL e (Matrix.SpecialLinearGroup.map f g) := by
  ext i j; rfl

def blockSL (a b : ℕ) : Matrix.SpecialLinearGroup (Fin a) A →*
    Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A where
  toFun g := ⟨Matrix.fromBlocks g.val 0 0 1, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact g.property⟩
  map_one' := by apply Subtype.ext; exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.fromBlocks (g.val * h.val) 0 0 (1 : Matrix (Fin b) (Fin b) A) =
      Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks h.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

@[simp] theorem blockSL_map (a b : ℕ) (f : A →+* B) (g : Matrix.SpecialLinearGroup (Fin a) A) :
    Matrix.SpecialLinearGroup.map f (blockSL a b g) = blockSL a b (Matrix.SpecialLinearGroup.map f g) := by
  ext i j
  change f (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin b) (Fin b) A) i j) =
    Matrix.fromBlocks (g.val.map f) 0 0 (1 : Matrix (Fin b) (Fin b) B) i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

def stabilizeSL (a b : ℕ) : Matrix.SpecialLinearGroup (Fin a) A →*
      Matrix.SpecialLinearGroup (Fin (a + b)) A :=
  (reindexSL (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).toMonoidHom.comp (blockSL a b)

theorem stabilizeSL_map (a b : ℕ) (f : A →+* B) (g : Matrix.SpecialLinearGroup (Fin a) A) :
    Matrix.SpecialLinearGroup.map f (stabilizeSL a b g) = stabilizeSL a b (Matrix.SpecialLinearGroup.map f g) := by
  change Matrix.SpecialLinearGroup.map f (reindexSL finSumFinEquiv (blockSL a b g)) = _
  rw [reindexSL_map, blockSL_map]; rfl

@[simp] theorem stabilizeSL_right_row (a b : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A)
    (i : Fin b) (j : Fin (a + b)) :
    stabilizeSL a b g (Fin.natAdd a i) j = (1 : Matrix (Fin (a + b)) (Fin (a + b)) A) (Fin.natAdd a i) j := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective j
  change reindexSL finSumFinEquiv (blockSL a b g) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv j) = _
  rw [reindexSL_apply, Matrix.one_apply]
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin b) (Fin b) A) (Sum.inr i) j = _
  simp only [← finSumFinEquiv_apply_right, finSumFinEquiv.injective.eq_iff]
  cases j <;> simp [Matrix.one_apply]

@[simp] theorem stabilizeSL_right_col (a b : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A)
    (i : Fin (a + b)) (j : Fin b) :
    stabilizeSL a b g i (Fin.natAdd a j) = (1 : Matrix (Fin (a + b)) (Fin (a + b)) A) i (Fin.natAdd a j) := by
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective i
  change reindexSL finSumFinEquiv (blockSL a b g) (finSumFinEquiv i) (finSumFinEquiv (Sum.inr j)) = _
  rw [reindexSL_apply, Matrix.one_apply]
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin b) (Fin b) A) i (Sum.inr j) = _
  simp only [← finSumFinEquiv_apply_right, finSumFinEquiv.injective.eq_iff]
  cases i <;> simp [Matrix.one_apply]

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

theorem E_path_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {a b : A} (ha : E hij a ∈ H) (hb : E hjk b ∈ H) : E hik (a * b) ∈ H := by
  rw [← E_commutator hij hjk hik]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem E_natCast_mul {i j : Fin n} (hij : i ≠ j) (a : A) (r : ℕ) :
    E hij ((r : A) * a) = E hij a ^ r := by
  induction r with
  | zero => simp [E]
  | succ r ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    change Matrix.SpecialLinearGroup.transvection hij (↑r * a + a) = _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    change E hij (↑r * a) * E hij a = _
    rw [ih, pow_succ]

theorem E_upper_one_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i.val + 1 = j.val), E (show i ≠ j by intro he; subst j; omega) (1 : A) ∈ H)
    {i j : Fin n} (hij : i < j) : E hij.ne (1 : A) ∈ H := by
  generalize hdiff : j.val - i.val = r
  induction r using Nat.strong_induction_on generalizing i j with
  | h r ih =>
    by_cases hadj : i.val + 1 = j.val
    · exact hE i j hadj
    · let k : Fin n := ⟨j.val - 1, by omega⟩
      have hik : i < k := by dsimp [k]; change i.val < j.val - 1; omega
      have hkj : k.val + 1 = j.val := by dsimp [k]; omega
      have hkj' : k < j := by change k.val < j.val; omega
      have hk := ih (k.val - i.val) (by omega) hik rfl
      simpa only [mul_one] using E_path_mem H hik.ne hkj'.ne hij.ne hk (hE k j hkj)

theorem clear_step_relative (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : Upper g)
    (hE : ∀ i j (h : i < j), E h.ne (-g i j) ∈ H)
    (k : ℕ) (hk : k < n * n) (hc : Cleared g k) :
    ∃ e ∈ H, Upper (e * g) ∧ Cleared (e * g) (k + 1) := by
  have hn : 0 < n := by nlinarith
  let i : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let j : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
  have hkij : i.val * n + j.val = k := by
    dsimp [i, j]
    simpa [Nat.mul_comm] using Nat.div_add_mod k n
  by_cases hij : i < j
  · refine ⟨E hij.ne (-g i j), hE i j hij, upper_E_mul hij _ hg, ?_⟩
    intro a b hab
    rw [E_mul_apply]
    by_cases ha : a = i
    · subst a
      rw [ite_eq_left rfl]
      have hbj : b ≤ j := by change b.val ≤ j.val; omega
      rcases hbj.eq_or_lt with rfl | hbj
      · rw [hg j j le_rfl]
        simp [hij.ne]
      · rw [hg j b hbj.le, Matrix.one_apply_ne hbj.ne.symm, mul_zero, add_zero]
        exact hc i b (by omega)
    · rw [ite_eq_right ha, add_zero]
      apply hc a b
      have hne : a.val * n + b.val ≠ k := by
        intro he
        have := congrArg (fun r => r / n) he
        have hab' : b.val < n := b.isLt
        rw [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt hab', add_zero] at this
        exact ha (Fin.ext this)
      omega
  · refine ⟨1, H.one_mem, by simpa using hg, ?_⟩
    rw [one_mul]
    intro a b hab
    by_cases hk' : a.val * n + b.val < k
    · exact hc a b hk'
    · have he : a.val * n + b.val = k := by omega
      have hai : a = i := by
        apply Fin.ext
        have := congrArg (fun r => r / n) he
        dsimp [i]
        simpa only [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero] using this
      have hbj : b = j := by
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt b.isLt] using this
      subst a; subst b
      exact hg i j (le_of_not_gt hij)

theorem upper_subgroup_le (P H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hHP : H ≤ P) (hP : ∀ g ∈ P, Upper g)
    (hE : ∀ g ∈ P, ∀ i j (h : i < j), E h.ne (g i j) ∈ H) : P ≤ H := by
  intro g hg
  have hsteps : ∀ k, k ≤ n * n → ∃ h ∈ H, Upper (h * g) ∧ Cleared (h * g) k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hP g hg, by intro i j h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hu, hc⟩ := ih (by omega)
      have hhg := P.mul_mem (hHP hh) hg
      have hE' : ∀ i j (hij : i < j), E hij.ne (-((h * g) i j)) ∈ H := by
        intro i j hij
        simpa only [E, Matrix.SpecialLinearGroup.transvection_inv] using
          H.inv_mem (hE (h * g) hhg i j hij)
      obtain ⟨e, he, hu', hc'⟩ := clear_step_relative H (h * g) hu hE' k (by omega) hc
      exact ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using hu',
        by simpa only [mul_assoc] using hc'⟩
  obtain ⟨h, hh, _, hc⟩ := hsteps (n * n) le_rfl
  have he : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply hc
    have hi := i.isLt
    have hj := j.isLt
    nlinarith
  rw [eq_inv_of_mul_eq_one_right he]
  exact H.inv_mem hh

end CoboundaryExpanders.Elementary

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [CommRing F] {n : ℕ}

def OffCleared (g : Matrix.SpecialLinearGroup (Fin n) A) (k : ℕ) : Prop :=
  ∀ i j, i ≠ j → j.val * n + i.val < k → g i j = 0

theorem off_clear_step (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : g ∈ B)
    (k : ℕ) (hk : k < n * n) (hc : OffCleared g k) :
    ∃ e ∈ H, e * g ∈ B ∧ OffCleared (e * g) (k + 1) := by
  have hn : 0 < n := by nlinarith
  let j : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let i : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
  have hkij : j.val * n + i.val = k := by
    dsimp [i, j]
    simpa [Nat.mul_comm] using Nat.div_add_mod k n
  by_cases hij : i = j
  · refine ⟨1, H.one_mem, by simpa using hg, ?_⟩
    rw [one_mul]
    intro a b hab hkey
    apply hc a b hab
    have hne : b.val * n + a.val ≠ k := by
      intro he
      have hai : a = i := by
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt] using this
      have hbj : b = j := by
        apply Fin.ext
        have := congrArg (fun r => r / n) he
        simpa only [Nat.mul_comm b.val n, Nat.mul_add_div hn,
          Nat.div_eq_of_lt a.isLt, add_zero] using this
      exact hab (hai.trans (hij.trans hbj.symm))
    omega
  · obtain ⟨u, hu⟩ := hunit (g j j) (by simpa using hB g hg j j le_rfl)
    let c : A := -g i j * (↑(u⁻¹) : A)
    have he : E hij c ∈ H := by
      apply hE
      intro hji
      simp [c, hB g hg i j hji.le, hij]
    refine ⟨E hij c, he, B.mul_mem (hHB he) hg, ?_⟩
    intro a b hab hkey
    rw [E_mul_apply]
    by_cases ha : a = i
    · subst a
      rw [ite_eq_left rfl]
      by_cases hb : b = j
      · subst b
        rw [← hu]
        dsimp [c]
        rw [mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]
      · have hbj : b.val < j.val := by
          have hbval : b.val ≠ j.val := Fin.val_ne_of_ne hb
          have hb_le : b.val ≤ j.val := by
            by_contra hnot
            have hlt : j.val + 1 ≤ b.val := by omega
            have hmul := Nat.mul_le_mul_right n hlt
            nlinarith
          omega
        rw [hc j b (ne_of_gt (show b < j from hbj)) (by
          have hmul := Nat.mul_le_mul_right n (by omega : b.val + 1 ≤ j.val)
          have hjlt := j.isLt
          nlinarith), mul_zero, add_zero]
        apply hc i b hab
        have hmul := Nat.mul_le_mul_right n (by omega : b.val + 1 ≤ j.val)
        nlinarith
    · rw [ite_eq_right ha, add_zero]
      apply hc a b hab
      have hne : b.val * n + a.val ≠ k := by
        intro he
        apply ha
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt] using this
      omega

theorem diagonalize_iwahori (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : g ∈ B) :
    ∃ h ∈ H, h * g ∈ B ∧ ∀ i j, i ≠ j → (h * g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n * n → ∃ h ∈ H, h * g ∈ B ∧ OffCleared (h * g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, H.one_mem, by simpa using hg, by intro i j h h'; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hb, hc⟩ := ih (by omega)
      obtain ⟨e, he, hb', hc'⟩ := off_clear_step π B H hHB hB hunit hE
        (h * g) hb k (by omega) hc
      exact ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using hb',
        by simpa only [mul_assoc] using hc'⟩
  obtain ⟨h, hh, hb, hc⟩ := hsteps _ le_rfl
  refine ⟨h, hh, hb, fun i j hij => hc i j hij ?_⟩
  have hi := i.isLt
  have hj := j.isLt
  nlinarith

def D {i j : Fin n} (hij : i ≠ j) (u : Aˣ) :
    Matrix.SpecialLinearGroup (Fin n) A :=
  E hij (1 : A) * E hij.symm ((u : A) - 1) * E hij (-(↑(u⁻¹) : A)) *
    E hij.symm (-(((u : A) - 1) * (u : A)))

theorem D_mul_apply {i j : Fin n} (hij : i ≠ j) (u : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (D hij u * g) a b =
      (if a = i then ↑u else if a = j then ↑(u⁻¹) else (1 : A)) * g a b := by
  simp only [D, mul_assoc, E_mul_apply]
  by_cases hai : a = i
  · subst a
    simp only [ite_true, ite_eq_right hij, ite_eq_right hij.symm, one_mul, add_zero]
    have hu : (↑u : A) * ↑(u⁻¹) = 1 := Units.mul_inv u
    linear_combination (g i b * ((u : A)^2 - (u : A)) - g j b) * hu
  · by_cases haj : a = j
    · subst a
      simp only [ite_eq_right hij.symm, ite_eq_right hij, ite_true, one_mul, add_zero]
      have hu : (↑u : A) * ↑(u⁻¹) = 1 := Units.mul_inv u
      linear_combination (g i b * ((u : A) - 1)^2 - g j b) * hu
    · simp [hai, haj]

theorem D_mem (π : A →+* F) (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    {i j : Fin n} (hij : i < j) (u : Aˣ) (hu : π (↑u : A) = 1) : D hij.ne u ∈ H := by
  unfold D
  apply H.mul_mem
  · apply H.mul_mem
    · apply H.mul_mem
      · exact hE _ _ _ _ (by intro h; exact False.elim ((lt_asymm hij h)))
      · exact hE _ _ _ _ (by intro _; simp [hu])
    · exact hE _ _ _ _ (by intro h; exact False.elim ((lt_asymm hij h)))
  · exact hE _ _ _ _ (by intro _; simp [hu])

theorem diagonal_iwahori_mem (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A) (hg : g ∈ B)
    (hdiag : ∀ i j, i ≠ j → g i j = 0) : g ∈ H := by
  have hsteps : ∀ k, k ≤ n → ∃ h ∈ H, h * g ∈ B ∧
      (∀ i j, i ≠ j → (h * g) i j = 0) ∧
      (∀ i : Fin (n + 1), i.val < k → (h * g) i i = 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hg, by simpa using hdiag,
        by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hb, hd, hc⟩ := ih (by omega)
      let i : Fin (n + 1) := ⟨k, by omega⟩
      have hilast : i < Fin.last n := by change k < n; omega
      obtain ⟨u, hu⟩ := hunit ((h * g) i i) (by simpa using hB (h * g) hb i i le_rfl)
      have hπu : π (u : A) = 1 := by rw [hu]; simpa using hB (h * g) hb i i le_rfl
      have hπinv : π (↑(u⁻¹) : A) = 1 := by
        have := congrArg π (Units.mul_inv u)
        simpa only [map_mul, map_one, hπu, one_mul] using this
      let e := D hilast.ne u⁻¹
      have he : e ∈ H := D_mem π H hE hilast u⁻¹ hπinv
      refine ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using B.mul_mem (hHB he) hb,
        ?_, ?_⟩
      · intro a b hab
        rw [mul_assoc, D_mul_apply, hd a b hab, mul_zero]
      · intro a ha
        rw [mul_assoc, D_mul_apply]
        by_cases hai : a = i
        · subst a
          rw [ite_eq_left rfl, ← hu]
          exact Units.inv_mul u
        · have halast : a ≠ Fin.last n := by intro heq; subst a; simp only [Fin.val_last] at ha; omega
          rw [ite_eq_right hai, ite_eq_right halast, one_mul]
          apply hc
          have hne : a.val ≠ k := fun h => hai (Fin.ext h)
          omega
  obtain ⟨h, hh, hb, hd, hc⟩ := hsteps n le_rfl
  have hmatrix : (h * g).val = Matrix.diagonal (fun i => (h * g) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [hd i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (h * g) i i = (1 : A) := by
    rw [← Matrix.det_diagonal, ← hmatrix]
    exact (h * g).property
  have hfirst : ∀ i : Fin n, (h * g) i.castSucc i.castSucc = 1 := fun i => hc _ i.isLt
  have hlast : (h * g) (Fin.last n) (Fin.last n) = 1 := by
    simpa only [Fin.prod_univ_castSucc, hfirst, Finset.prod_const_one, one_mul] using hdet
  have heq : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (h * g) i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      by_cases hilast : i = Fin.last n
      · subst i; exact hlast
      · apply hc
        have := i.isLt
        have := Fin.val_ne_of_ne hilast
        simp only [Fin.val_last] at this
        omega
    · rw [hd i j hij, Matrix.one_apply_ne hij]
  rw [eq_inv_of_mul_eq_one_right heq]
  exact H.inv_mem hh

theorem iwahori_mem_of_roots (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H) : B ≤ H := by
  intro g hg
  obtain ⟨h, hh, hb, hd⟩ := diagonalize_iwahori π B H hHB hB hunit hE g hg
  have hm := diagonal_iwahori_mem π B H hHB hB hunit hE (h * g) hb hd
  simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hh) hm

end CoboundaryExpanders.Elementary

end

section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary

section
variable {A : Type*} [CommRing A] {n : ℕ}

def ColumnPrefix (g : Matrix.SpecialLinearGroup (Fin n) A) (k : ℕ) : Prop :=
  ∀ a b, b.val < k → a ≠ b → g a b = 0

theorem inverse_column_sum (g : Matrix.SpecialLinearGroup (Fin n) A) (i j : Fin n) :
    ∑ a, g⁻¹ i a * g a j = if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) A => M i j) (inv_mul_cancel g)
  change (g⁻¹.val * g.val) i j = (1 : Matrix (Fin n) (Fin n) A) i j at h
  simpa only [Matrix.mul_apply, Matrix.one_apply] using h

theorem column_diagonal_unit (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n)
    (hcol : ∀ i, i ≠ j → g i j = 0) : IsUnit (g j j) := by
  have hs := inverse_column_sum g j j
  rw [ite_eq_left rfl, Finset.sum_eq_single j] at hs
  · exact isUnit_of_dvd_one ⟨g⁻¹ j j, by rw [mul_comm]; exact hs.symm⟩
  · intro b hb hbj; rw [hcol b hbj, mul_zero]
  · simp

theorem inverse_prefix_zero (g : Matrix.SpecialLinearGroup (Fin n) A)
    {k : ℕ} (hg : ColumnPrefix g k) {i j : Fin n} (hj : j.val < k) (hij : i ≠ j) :
    g⁻¹ i j = 0 := by
  have hu : IsUnit (g j j) := column_diagonal_unit g j (fun a ha => hg a j hj ha)
  have hs := inverse_column_sum g i j
  rw [ite_eq_right hij, Finset.sum_eq_single j] at hs
  · exact (hu.mul_left_eq_zero).mp hs
  · intro b hb hbj; rw [hg b j hj hbj, mul_zero]
  · simp

theorem columnPrefix_E_mul {g : Matrix.SpecialLinearGroup (Fin n) A}
    {k : ℕ} (hg : ColumnPrefix g k) {i j : Fin n} (hij : i ≠ j)
    (hj : k ≤ j.val) (c : A) : ColumnPrefix (E hij c * g) k := by
  intro a b hb hab
  rw [E_mul_apply, hg a b hb hab, hg j b hb (by intro he; subst b; omega)]
  simp

def W {i j : Fin n} (hij : i ≠ j) : Matrix.SpecialLinearGroup (Fin n) A :=
  E hij (1 : A) * E hij.symm (-1) * E hij 1

theorem W_mul_apply {i j : Fin n} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (W hij * g : Matrix.SpecialLinearGroup (Fin n) A) a b = if a = i then g j b else if a = j then -g i b else g a b := by
  simp only [W, mul_assoc, E_mul_apply]
  by_cases ha : a = i
  · subst a; simp [hij, hij.symm]
  · by_cases hb : a = j
    · subst a; simp [hij.symm]
    · simp [ha, hb]

theorem W_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H) {i j : Fin n} (hij : i ≠ j) :
    W hij ∈ H := H.mul_mem (H.mul_mem (hE _ _ _ _) (hE _ _ _ _)) (hE _ _ _ _)

theorem columnPrefix_W_mul {g : Matrix.SpecialLinearGroup (Fin n) A}
    {k : ℕ} (hg : ColumnPrefix g k) {i j : Fin n} (hij : i ≠ j)
    (hi : k ≤ i.val) (hj : k ≤ j.val) : ColumnPrefix (W hij * g) k := by
  unfold W
  rw [mul_assoc, mul_assoc]
  exact columnPrefix_E_mul (columnPrefix_E_mul (columnPrefix_E_mul hg hij hj 1)
    hij.symm hi (-1)) hij hj 1

end

section
variable {F : Type*} [Field F] {n : ℕ}

theorem lower_column_nonzero (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F))
    (j : Fin n) (hg : ColumnPrefix g j.val) :
    ∃ a : Fin n, j ≤ a ∧ g a j ≠ 0 := by
  classical
  by_contra! h
  have hs := inverse_column_sum g j j
  rw [ite_eq_left rfl] at hs
  have hz : (∑ a, g⁻¹ j a * g a j) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hja : j ≤ a
    · rw [h a hja, mul_zero]
    · rw [inverse_prefix_zero g hg (show a.val < j.val from lt_of_not_ge hja)
        (ne_of_gt (lt_of_not_ge hja)), zero_mul]
  exact zero_ne_one (hz.symm.trans hs)

theorem exists_unit_pivot
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (j : Fin n)
    (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ IsUnit ((e * g) j j) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧
    (e * g) j j ≠ 0 ∧ ((e * g) j j).natDegree = r
  have hex : ∃ r, P r := by
    obtain ⟨a, hja, ha⟩ := lower_column_nonzero g j hg
    by_cases haj : a = j
    · subst a
      exact ⟨(g j j).natDegree, 1, H.one_mem, by simpa using hg, by simpa using ha,
        by simp⟩
    · refine ⟨(g a j).natDegree, W (Ne.symm haj), W_mem H hE (Ne.symm haj),
        columnPrefix_W_mul hg (Ne.symm haj) le_rfl hja, ?_, ?_⟩
      · simpa [W_mul_apply] using ha
      · simp [W_mul_apply]
  obtain ⟨e, he, hpref, hp, hdegree⟩ := Nat.find_spec hex
  have hdiv : ∀ a : Fin n, j ≤ a → (e * g) j j ∣ (e * g) a j := by
    intro a hja
    by_cases haj : a = j
    · subst a; exact dvd_refl _
    · apply (EuclideanDomain.mod_eq_zero).mp
      by_contra hmod
      let c : (Polynomial F) := -((e * g) a j / (e * g) j j)
      let e' := W (Ne.symm haj) * E haj c * e
      have he' : e' ∈ H := H.mul_mem (H.mul_mem (W_mem H hE (Ne.symm haj)) (hE _ _ _ _)) he
      have hpre' : ColumnPrefix (e' * g) j.val := by
        dsimp only [e']
        rw [mul_assoc, mul_assoc]
        exact columnPrefix_W_mul (columnPrefix_E_mul hpref haj le_rfl c)
          (Ne.symm haj) le_rfl hja
      have hpiv : (e' * g) j j = (e * g) a j % (e * g) j j := by
        dsimp only [e']
        rw [mul_assoc, mul_assoc, W_mul_apply, ite_eq_left rfl, E_mul_apply, ite_eq_left rfl]
        rw [EuclideanDomain.mod_eq_sub_mul_div]
        dsimp [c]
        ring
      have hnew : P (((e * g) a j % (e * g) j j).natDegree) :=
        ⟨e', he', hpre', by rw [hpiv]; exact hmod, by rw [hpiv]⟩
      have hlt : (((e * g) a j % (e * g) j j).natDegree) < Nat.find hex := by
        rw [← hdegree]
        exact Polynomial.natDegree_lt_natDegree hmod (Polynomial.degree_mod_lt _ hp)
      exact Nat.find_min hex hlt hnew
  refine ⟨e, he, hpref, isUnit_of_dvd_one ?_⟩
  have hs := inverse_column_sum (e * g) j j
  rw [ite_eq_left rfl] at hs
  apply (show (e * g) j j ∣ ∑ a, (e * g)⁻¹ j a * (e * g) a j from ?_).trans
    (dvd_of_eq hs)
  apply Finset.dvd_sum
  intro a ha
  by_cases hja : j ≤ a
  · exact dvd_mul_of_dvd_right (hdiv a hja) _
  · rw [inverse_prefix_zero (e * g) hpref (show a.val < j.val from lt_of_not_ge hja)
      (ne_of_gt (lt_of_not_ge hja)), zero_mul]
    exact dvd_zero _

end

section
variable {A : Type*} [CommRing A] {n : ℕ}

theorem clear_column (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n)
    (hg : ColumnPrefix g j.val) (hu : IsUnit (g j j)) :
    ∃ e ∈ H, ColumnPrefix (e * g) (j.val + 1) := by
  classical
  obtain ⟨u, hu⟩ := hu
  have hclear : ∀ s : Finset (Fin n), (∀ a ∈ s, a ≠ j) →
      ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ (e * g) j j = (u : A) ∧
        ∀ a ∈ s, (e * g) a j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hg, by simpa using hu.symm, by simp⟩
    | @insert a s has ih =>
      intro hs
      obtain ⟨e, he, hpref, hpiv, hz⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      have haj : a ≠ j := hs a (Finset.mem_insert_self _ _)
      let c : A := -((e * g) a j) * (↑(u⁻¹) : A)
      refine ⟨E haj c * e, H.mul_mem (hE _ _ _ _) he, ?_, ?_, ?_⟩
      · rw [mul_assoc]
        exact columnPrefix_E_mul hpref haj le_rfl c
      · rw [mul_assoc, E_mul_apply, ite_eq_right haj.symm, add_zero, hpiv]
      · intro b hb
        rw [mul_assoc, E_mul_apply]
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [ite_eq_left rfl, hpiv]
          dsimp [c]
          rw [mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]
        · rw [ite_eq_right (by intro h; subst b; exact has hb), add_zero]
          exact hz b hb
  obtain ⟨e, he, hpref, _, hz⟩ := hclear (Finset.univ.erase j) (by simp)
  refine ⟨e, he, ?_⟩
  intro a b hb hab
  by_cases hbj : b.val < j.val
  · exact hpref a b hbj hab
  · have hbe : b = j := Fin.ext (by omega)
    subst b
    exact hz a (by simp [hab])

end

section
variable {F : Type*} [Field F] {n : ℕ}

theorem diagonalize_polynomial
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e * g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e * g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, H.one_mem, by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e, he, hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨h, hh, hpref', hpiv⟩ := exists_unit_pivot H hE (e * g) j hpref
      obtain ⟨r, hr, hcol⟩ := clear_column H hE (h * (e * g)) j hpref' hpiv
      exact ⟨r * h * e, H.mul_mem (H.mul_mem hr hh) he, by simpa [mul_assoc, j] using hcol⟩
  obtain ⟨e, he, hpref⟩ := hsteps n le_rfl
  exact ⟨e, he, fun i j hij => hpref i j j.isLt hij⟩

end

section
variable {A : Type*} [CommRing A] {n : ℕ}

theorem diagonal_mem_of_roots
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A)
    (hdiag : ∀ i j, i ≠ j → g i j = 0) : g ∈ H := by
  have hsteps : ∀ k, k ≤ n → ∃ h ∈ H,
      (∀ i j, i ≠ j → (h * g) i j = 0) ∧
      (∀ i : Fin (n + 1), i.val < k → (h * g) i i = 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hdiag,
        by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hd, hc⟩ := ih (by omega)
      let i : Fin (n + 1) := ⟨k, by omega⟩
      have hilast : i < Fin.last n := by change k < n; omega
      obtain ⟨u, hu⟩ := column_diagonal_unit (h * g) i (fun a ha => hd a i ha)
      let e := D hilast.ne u⁻¹
      have he : e ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (hE _ _ _ _) (hE _ _ _ _))
        (hE _ _ _ _)) (hE _ _ _ _)
      refine ⟨e * h, H.mul_mem he hh, ?_, ?_⟩
      · intro a b hab
        rw [mul_assoc, D_mul_apply, hd a b hab, mul_zero]
      · intro a ha
        rw [mul_assoc, D_mul_apply]
        by_cases hai : a = i
        · subst a
          rw [ite_eq_left rfl, ← hu]
          exact Units.inv_mul u
        · have halast : a ≠ Fin.last n := by intro heq; subst a; simp only [Fin.val_last] at ha; omega
          rw [ite_eq_right hai, ite_eq_right halast, one_mul]
          apply hc
          have hne : a.val ≠ k := fun h => hai (Fin.ext h)
          omega
  obtain ⟨h, hh, hd, hc⟩ := hsteps n le_rfl
  have hmatrix : (h * g).val = Matrix.diagonal (fun i => (h * g) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [hd i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (h * g) i i = (1 : A) := by
    rw [← Matrix.det_diagonal, ← hmatrix]
    exact (h * g).property
  have hfirst : ∀ i : Fin n, (h * g) i.castSucc i.castSucc = 1 := fun i => hc _ i.isLt
  have hlast : (h * g) (Fin.last n) (Fin.last n) = 1 := by
    simpa only [Fin.prod_univ_castSucc, hfirst, Finset.prod_const_one, one_mul] using hdet
  have heq : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (h * g) i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      by_cases hilast : i = Fin.last n
      · subst i; exact hlast
      · apply hc
        have := i.isLt
        have := Fin.val_ne_of_ne hilast
        simp only [Fin.val_last] at this
        omega
    · rw [hd i j hij, Matrix.one_apply_ne hij]
  rw [eq_inv_of_mul_eq_one_right heq]
  exact H.inv_mem hh

end

section
variable {F : Type*} [Field F]

theorem polynomial_SL_mem_of_roots (n : ℕ)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) : g ∈ H := by
  cases n with
  | zero =>
    have hg : g = 1 := by ext i; exact Fin.elim0 i
    rw [hg]; exact H.one_mem
  | succ n =>
    obtain ⟨e, he, hd⟩ := diagonalize_polynomial H hE g
    have hm := diagonal_mem_of_roots H hE (e * g) hd
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem he) hm

end

variable {A : Type*} [CommRing A] {n : ℕ}

theorem mul_E_apply {i j : Fin n} (h : i ≠ j) (c : A)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (g * E h c : Matrix.SpecialLinearGroup (Fin n) A) a b =
      g a b + if b = j then g a i * c else 0 := by
  change (g.val * Matrix.transvection i j c) a b = _
  by_cases hb : b = j
  · subst b; simp [mul_comm]
  · simp [hb]

theorem elementary_commutes_of_complement {i j : Fin n} (hij : i ≠ j) (c : A)
    (g : Matrix.SpecialLinearGroup (Fin n) A)
    (hrow : ∀ b, g j b = (1 : Matrix (Fin n) (Fin n) A) j b)
    (hcol : ∀ a, g a i = (1 : Matrix (Fin n) (Fin n) A) a i) :
    Commute (E hij c) g := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  rw [E_mul_apply, mul_E_apply, hrow, hcol]
  by_cases ha : a = i
  · subst a; by_cases hb : b = j
    · subst b; simp
    · simp [hb, Ne.symm hb]
  · by_cases hb : b = j
    · subst b; simp [ha]
    · simp [ha, hb]

end CoboundaryExpanders.Elementary

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Elementary
open Polynomial
variable {F : Type*} [Field F] {n : ℕ}

theorem restricted_euclidean_descent (a b : Polynomial F)
    (ha : a.constantCoeff = 1) (hb : b.constantCoeff = 0)
    (hmod : b % a ≠ 0) :
    ∃ c d : Polynomial F, c.constantCoeff = 0 ∧
      (a + d * (b + c*a)).natDegree < a.natDegree := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let q := b / a
  let r := b % a
  have hr : r ≠ 0 := hmod
  have hdeg : r.natDegree < a.natDegree :=
    Polynomial.natDegree_lt_natDegree hmod (Polynomial.degree_mod_lt b ha0)
  have heq : b + (-q)*a = r := by
    dsimp [q,r]
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    ring
  by_cases hq : q.constantCoeff = 0
  · refine ⟨-q, -(a/r), by simpa using hq, ?_⟩
    rw [heq]
    have heq' : a + (-(a/r))*r = a % r := by
      rw [EuclideanDomain.mod_eq_sub_mul_div]
      ring
    rw [heq']
    have hr0 : r.constantCoeff = 0 := by
      rw [← heq]
      simp only [map_add,map_mul,map_neg,hb,hq,zero_mul,neg_zero,add_zero]
    have hrem : a % r ≠ 0 := by
      intro h
      have hc := congrArg Polynomial.constantCoeff h
      rw [EuclideanDomain.mod_eq_sub_mul_div] at hc
      simp only [map_sub,map_mul,ha,hr0,zero_mul,sub_zero,map_zero] at hc
      exact one_ne_zero hc
    exact (Polynomial.natDegree_lt_natDegree hrem (Polynomial.degree_mod_lt a hr)).trans hdeg
  · let c := -q + C q.constantCoeff
    let d := C (-q.constantCoeff⁻¹)
    refine ⟨c,d,by simp [c],?_⟩
    have heq' : a + d*(b+c*a) = d*r := by
      have hc : b+c*a = r + C q.constantCoeff * a := by
        dsimp [c]
        rw [← heq]
        ring
      rw [hc]
      have hd : d * C q.constantCoeff = -1 := by
        dsimp only [d]
        rw [← map_mul, neg_mul, inv_mul_cancel₀ hq]
        simp
      calc
        a + d*(r+C q.constantCoeff*a) = a + (d*C q.constantCoeff)*a + d*r := by ring
        _ = d*r := by rw [hd]; ring
    rw [heq']
    apply lt_of_le_of_lt (Polynomial.natDegree_mul_le) _
    simpa [d] using hdeg

theorem exists_unit_pivot_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hgB : g ∈ B)
    (j : Fin n) (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ IsUnit ((e*g) j j) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ ((e*g) j j).natDegree = r
  have hex : ∃ r, P r := ⟨(g j j).natDegree,1,H.one_mem,by simpa using hg,by simp⟩
  obtain ⟨e,he,hpref,hdegree⟩ := Nat.find_spec hex
  have hegB : e*g ∈ B := B.mul_mem (hHB he) hgB
  have hconst : ((e*g) j j).constantCoeff = 1 := by simpa using hB (e*g) hegB j j le_rfl
  have hdiv : ∀ a : Fin n, j ≤ a → (e*g) j j ∣ (e*g) a j := by
    intro a hja
    by_cases haj : a=j
    · subst a; exact dvd_refl _
    · apply (EuclideanDomain.mod_eq_zero).mp
      by_contra hmod
      have hja' : j < a := lt_of_le_of_ne hja (Ne.symm haj)
      have hb : ((e*g) a j).constantCoeff = 0 := by simpa [haj] using hB (e*g) hegB a j hja
      obtain ⟨c,d,hc,hlt⟩ := restricted_euclidean_descent ((e*g) j j) ((e*g) a j) hconst hb hmod
      let e' := E (Ne.symm haj) d * E haj c * e
      have he' : e' ∈ H := H.mul_mem (H.mul_mem
        (hE j a (Ne.symm haj) d (by intro h; exact False.elim (not_lt_of_ge hja h)))
        (hE a j haj c (by intro _; exact hc))) he
      have hpre' : ColumnPrefix (e'*g) j.val := by
        dsimp only [e']
        rw [mul_assoc,mul_assoc]
        exact columnPrefix_E_mul (columnPrefix_E_mul hpref haj le_rfl c) (Ne.symm haj) hja d
      have hpiv : (e'*g) j j = (e*g) j j + d*((e*g) a j + c*(e*g) j j) := by
        dsimp only [e']
        simp only [mul_assoc,E_mul_apply,ite_eq_right (Ne.symm haj),add_zero,ite_true]
      have hnew : P (((e*g) j j + d*((e*g) a j+c*(e*g) j j)).natDegree) :=
        ⟨e',he',hpre',by rw [hpiv]⟩
      apply Nat.find_min hex _ hnew
      simpa only [← hdegree] using hlt
  refine ⟨e,he,hpref,isUnit_of_dvd_one ?_⟩
  have hs := inverse_column_sum (e*g) j j
  rw [ite_eq_left rfl] at hs
  apply (show (e*g) j j ∣ ∑ a, (e*g)⁻¹ j a * (e*g) a j from ?_).trans (dvd_of_eq hs)
  apply Finset.dvd_sum
  intro a _
  by_cases hja : j ≤ a
  · exact dvd_mul_of_dvd_right (hdiv a hja) _
  · rw [inverse_prefix_zero (e*g) hpref (show a.val < j.val from lt_of_not_ge hja)
      (ne_of_gt (lt_of_not_ge hja)),zero_mul]
    exact dvd_zero _

theorem clear_column_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hgB : g ∈ B)
    (j : Fin n) (hg : ColumnPrefix g j.val) (hu : IsUnit (g j j)) :
    ∃ e ∈ H, ColumnPrefix (e*g) (j.val+1) := by
  classical
  obtain ⟨u,hu⟩ := hu
  have hclear : ∀ s : Finset (Fin n), (∀ a ∈ s, a ≠ j) →
      ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ (e*g) j j = (u : Polynomial F) ∧
        ∀ a ∈ s, (e*g) a j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1,H.one_mem,by simpa using hg,by simpa using hu.symm,by simp⟩
    | @insert a s has ih =>
      intro hs
      obtain ⟨e,he,hpref,hpiv,hz⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      have haj : a ≠ j := hs a (Finset.mem_insert_self _ _)
      let c : Polynomial F := -((e*g) a j) * (↑(u⁻¹) : Polynomial F)
      have hc : E haj c ∈ H := by
        apply hE
        intro hja
        dsimp only [c]
        rw [map_mul,map_neg,hB (e*g) (B.mul_mem (hHB he) hgB) a j hja.le,ite_eq_right haj]
        simp
      refine ⟨E haj c * e,H.mul_mem hc he,?_,?_,?_⟩
      · rw [mul_assoc]
        exact columnPrefix_E_mul hpref haj le_rfl c
      · rw [mul_assoc,E_mul_apply,ite_eq_right (Ne.symm haj),add_zero,hpiv]
      · intro b hb
        rw [mul_assoc,E_mul_apply]
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [ite_eq_left rfl,hpiv]
          dsimp [c]
          rw [mul_assoc,Units.inv_mul,mul_one,add_neg_cancel]
        · rw [ite_eq_right (by intro h; subst b; exact has hb),add_zero]
          exact hz b hb
  obtain ⟨e,he,hpref,_,hz⟩ := hclear (Finset.univ.erase j) (by simp)
  refine ⟨e,he,?_⟩
  intro a b hb hab
  by_cases hbj : b.val < j.val
  · exact hpref a b hbj hab
  · have hbe : b=j := Fin.ext (by omega)
    subst b
    exact hz a (by simp [hab])

theorem diagonalize_polynomial_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hg : g ∈ B) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e*g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e*g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1,H.one_mem,by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e,he,hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k,by omega⟩
      have heg := B.mul_mem (hHB he) hg
      obtain ⟨h,hh,hpref',hpiv⟩ := exists_unit_pivot_iwahori B H hHB hB hE (e*g) heg j hpref
      obtain ⟨r,hr,hcol⟩ := clear_column_iwahori B H hHB hB hE (h*(e*g))
        (B.mul_mem (hHB hh) heg) j hpref' hpiv
      exact ⟨r*h*e,H.mul_mem (H.mul_mem hr hh) he,by simpa [mul_assoc,j] using hcol⟩
  obtain ⟨e,he,hpref⟩ := hsteps n le_rfl
  exact ⟨e,he,fun i j hij => hpref i j j.isLt hij⟩

theorem polynomial_iwahori_mem_of_roots
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hg : g ∈ B) : g ∈ H := by
  obtain ⟨e,he,hdiag⟩ := diagonalize_polynomial_iwahori B H hHB hB hE g hg
  have heg : e*g = 1 := by
    ext i j
    by_cases hij : i=j
    · subst j
      have hunit := column_diagonal_unit (e*g) i (fun a ha => hdiag a i ha)
      obtain ⟨c,hc,hc'⟩ := Polynomial.isUnit_iff.mp hunit
      have hconst := hB (e*g) (B.mul_mem (hHB he) hg) i i le_rfl
      rw [← hc'] at hconst
      have hc1 : c=1 := by simpa using hconst
      simp [← hc',hc1]
    · simp [hdiag i j hij, hij]
  rw [eq_inv_of_mul_eq_one_right heg]
  exact H.inv_mem he

end CoboundaryExpanders.Elementary

end

section
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [Field F] {n : ℕ}

lemma exists_unit_pivot_residue (π : A →+* F)
    (hu : ∀ a, π a ≠ 0 → IsUnit a)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n)
    (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ IsUnit ((e * g) j j) := by
  classical
  have ha : ∃ a : Fin n, j ≤ a ∧ π (g a j) ≠ 0 := by
    by_contra! h
    have hs := congrArg π (inverse_column_sum g j j)
    simp only [ite_true, map_sum, map_mul, map_one] at hs
    have hz : (∑ a, π (g⁻¹ j a) * π (g a j)) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hja : j ≤ a
      · rw [h a hja, mul_zero]
      · rw [inverse_prefix_zero g hg (show a.val < j.val from lt_of_not_ge hja)
          (ne_of_gt (lt_of_not_ge hja)), map_zero, zero_mul]
    exact zero_ne_one (hz.symm.trans hs)
  obtain ⟨a,hja,ha⟩ := ha
  by_cases haj : a = j
  · subst a
    exact ⟨1,H.one_mem,by simpa using hg,by simpa using hu (g j j) ha⟩
  · refine ⟨W (Ne.symm haj), W_mem H hE (Ne.symm haj),
      columnPrefix_W_mul hg (Ne.symm haj) le_rfl hja, ?_⟩
    rw [W_mul_apply]
    simpa [haj] using hu (g a j) ha

lemma diagonalize_residue (π : A →+* F) (hu : ∀ a, π a ≠ 0 → IsUnit a)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e*g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e*g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1,H.one_mem,by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e,he,hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k,by omega⟩
      obtain ⟨h,hh,hpref',hpiv⟩ := exists_unit_pivot_residue π hu H hE (e*g) j hpref
      obtain ⟨r,hr,hcol⟩ := clear_column H hE (h*(e*g)) j hpref' hpiv
      exact ⟨r*h*e,H.mul_mem (H.mul_mem hr hh) he,by simpa [mul_assoc,j] using hcol⟩
  obtain ⟨e,he,hpref⟩ := hsteps n le_rfl
  exact ⟨e,he,fun i j hij => hpref i j j.isLt hij⟩

theorem SL_mem_of_residue_units (π : A →+* F) (hu : ∀ a, π a ≠ 0 → IsUnit a)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) : g ∈ H := by
  cases n with
  | zero =>
    have hg : g = 1 := by ext i; exact Fin.elim0 i
    rw [hg]; exact H.one_mem
  | succ n =>
    obtain ⟨e,he,hd⟩ := diagonalize_residue π hu H hE g
    have hm := diagonal_mem_of_roots H hE (e*g) hd
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem he) hm

theorem SL_map_surjective {B : Type*} [CommRing B] (f : B →+* A)
    (hf : Function.Surjective f) (π : A →+* F) (hu : ∀ a, π a ≠ 0 → IsUnit a) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin n) f) := by
  intro g
  apply SL_mem_of_residue_units π hu (Matrix.SpecialLinearGroup.map f).range _ g
  intro i j hij c
  obtain ⟨c,rfl⟩ := hf c
  refine ⟨E hij c,?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  change f ((Matrix.transvection i j c) a b) = (Matrix.transvection i j (f c)) a b
  simp only [Matrix.transvection, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp
end CoboundaryExpanders.Elementary

end

open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.Elementary
variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*}
    [Fintype ι] [DecidableEq ι]

lemma SL_map_surjective_reindex (f : A →+* B)
    (hf : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin (Fintype.card ι)) f)) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := ι) f) := by
  intro g
  let e := Fintype.equivFin ι
  obtain ⟨h,hh⟩ := hf (Blocks.reindexSL e g)
  refine ⟨Blocks.reindexSL e.symm h, ?_⟩
  rw [Blocks.reindexSL_map, hh]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change g (e.symm (e i)) (e.symm (e j)) = g i j
  simp
end CoboundaryExpanders.Elementary

end

end OAI
