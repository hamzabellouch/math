import OAI.Probability.SwitchChain.FixedBlockPartitions

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BinaryColumnPartitions

abbrev Column (q : ℕ) := {c : Fin 3 → Fin 2 // ∑ i, (c i : ℕ) = q}

def unitColumn (i : Fin 3) : Column 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [Fin.sum_univ_three]
    fin_cases i <;> decide⟩

def complementColumn (c : Fin 3 → Fin 2) : Fin 3 → Fin 2 :=
  fun i => if c i = 0 then 1 else 0

lemma column_one_surjective : Function.Surjective unitColumn := by
  decide

lemma column_one_injective : Function.Injective unitColumn := by
  decide

noncomputable def oneColumnEquiv : Fin 3 ≃ Column 1 :=
  Equiv.ofBijective unitColumn ⟨column_one_injective, column_one_surjective⟩

noncomputable def complementEquiv : Column 1 ≃ Column 2 where
  toFun c := ⟨complementColumn c.val, by
    have h : ∀ c : Column 1, ∑ i, (complementColumn c.val i : ℕ) = 2 := by decide
    exact h c⟩
  invFun c := ⟨complementColumn c.val, by
    have h : ∀ c : Column 2, ∑ i, (complementColumn c.val i : ℕ) = 1 := by decide
    exact h c⟩
  left_inv := by decide
  right_inv := by decide

def twoColumnEquiv : Fin 3 ≃ Column 2 := oneColumnEquiv.trans complementEquiv

variable (U W : Type*)

abbrev MatrixSpace :=
  {M : Fin 3 → U ⊕ W → Fin 2 //
    (∀ u, ∑ i, (M i (Sum.inl u) : ℕ) = 1) ∧
    (∀ w, ∑ i, (M i (Sum.inr w) : ℕ) = 2)}

def matrixEquiv : ((U → Fin 3) × (W → Fin 3)) ≃ MatrixSpace U W where
  toFun c := ⟨fun i j => Sum.elim
    (fun u => (oneColumnEquiv (c.1 u)).val i)
    (fun w => (twoColumnEquiv (c.2 w)).val i) j,
    ⟨fun u => (oneColumnEquiv (c.1 u)).property,
     fun w => (twoColumnEquiv (c.2 w)).property⟩⟩
  invFun M :=
    (fun u => oneColumnEquiv.symm ⟨fun i => M.val i (Sum.inl u), M.property.1 u⟩,
     fun w => twoColumnEquiv.symm ⟨fun i => M.val i (Sum.inr w), M.property.2 w⟩)
  left_inv c := by
    apply Prod.ext
    · funext u
      exact oneColumnEquiv.symm_apply_apply (c.1 u)
    · funext w
      exact twoColumnEquiv.symm_apply_apply (c.2 w)
  right_inv M := by
    apply Subtype.ext
    funext i j
    cases j with
    | inl u =>
      exact congrArg (fun c : Column 1 => c.val i)
        (oneColumnEquiv.apply_symm_apply ⟨fun k => M.val k (Sum.inl u), M.property.1 u⟩)
    | inr w =>
      exact congrArg (fun c : Column 2 => c.val i)
        (twoColumnEquiv.apply_symm_apply ⟨fun k => M.val k (Sum.inr w), M.property.2 w⟩)

@[simp] theorem matrixEquiv_inl (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) (u : U) :
    (matrixEquiv U W c).val i (Sum.inl u) = if i = c.1 u then 1 else 0 := rfl

@[simp] theorem matrixEquiv_inr (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) (w : W) :
    (matrixEquiv U W c).val i (Sum.inr w) = if i = c.2 w then 0 else 1 := by
  change (if (if i = c.2 w then (1 : Fin 2) else 0) = 0 then 1 else 0) = _
  split_ifs <;> simp_all

variable [Fintype U] [Fintype W]

theorem row_sum_add (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) :
    (∑ j, ((matrixEquiv U W c).val i j : ℕ)) + (FixedBlock.row c.2 i).card =
      (FixedBlock.row c.1 i).card + Fintype.card W := by
  classical
  have hU : (∑ u : U, ((matrixEquiv U W c).val i (Sum.inl u) : ℕ)) =
      (FixedBlock.row c.1 i).card := by
    have hu (u : U) : ((matrixEquiv U W c).val i (Sum.inl u) : ℕ) =
        if c.1 u = i then 1 else 0 := by
      rw [matrixEquiv_inl]
      by_cases h : i = c.1 u
      · simp [h]
      · simp [h, Ne.symm h]
    simp_rw [hu]
    simp [FixedBlock.row]
  have hW : (∑ w : W, ((matrixEquiv U W c).val i (Sum.inr w) : ℕ)) +
      (FixedBlock.row c.2 i).card = Fintype.card W := by
    have hh (w : W) : ((matrixEquiv U W c).val i (Sum.inr w) : ℕ) +
        (if c.2 w = i then 1 else 0) = 1 := by
      rw [matrixEquiv_inr]
      by_cases h : i = c.2 w
      · simp [h]
      · simp [h, Ne.symm h]
    have hs := congrArg (fun f : W → ℕ => ∑ w, f w) (funext hh)
    simpa [Finset.sum_add_distrib, FixedBlock.row] using hs
  rw [Fintype.sum_sum_type, hU]
  omega

def fixedMarginsEquiv (r : Fin 3 → ℕ) :
    {c : (U → Fin 3) × (W → Fin 3) // ∀ i,
      (FixedBlock.row c.1 i).card + Fintype.card W = r i + (FixedBlock.row c.2 i).card} ≃
    {M : MatrixSpace U W // ∀ i, ∑ j, (M.val i j : ℕ) = r i} :=
  (matrixEquiv U W).subtypeEquiv (fun c => by
    constructor
    · intro h i
      have hh := row_sum_add U W c i
      have hi := h i
      omega
    · intro h i
      have hh := row_sum_add U W c i
      rw [h i] at hh
      exact hh.symm)

theorem row_eq_iff (c d : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) :
    (matrixEquiv U W c).val i = (matrixEquiv U W d).val i ↔
      FixedBlock.row c.1 i = FixedBlock.row d.1 i ∧
      FixedBlock.row c.2 i = FixedBlock.row d.2 i := by
  classical
  have h1 : ∀ a b i : Fin 3,
      (if i = a then (1 : Fin 2) else 0) = (if i = b then 1 else 0) ↔
        (a = i ↔ b = i) := by decide
  have h2 : ∀ a b i : Fin 3,
      (if i = a then (0 : Fin 2) else 1) = (if i = b then 0 else 1) ↔
        (a = i ↔ b = i) := by decide
  constructor
  · intro h
    constructor
    · ext u
      have he := congrFun h (Sum.inl u)
      simpa only [FixedBlock.mem_row, matrixEquiv_inl, h1] using he
    · ext w
      have he := congrFun h (Sum.inr w)
      simpa only [FixedBlock.mem_row, matrixEquiv_inr, h2] using he
  · rintro ⟨hu, hw⟩
    funext j
    cases j with
    | inl u =>
      rw [matrixEquiv_inl, matrixEquiv_inl, h1]
      simpa only [FixedBlock.mem_row] using (Finset.ext_iff.mp hu u)
    | inr w =>
      rw [matrixEquiv_inr, matrixEquiv_inr, h2]
      simpa only [FixedBlock.mem_row] using (Finset.ext_iff.mp hw w)

end Problem315.BinaryColumnPartitions

end

end OAI
