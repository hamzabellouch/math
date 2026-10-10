import OAI.Probability.InvariantIsing.Cavity.CavitySelectedGroupFrames

namespace OAI

/-! Grouping retained and exceptional base axes by the same spectral
labels. Their dimensions are the retained counts plus the finite extras. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityBaseGroupSumEquiv {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m) :
    ((a : Fin m) × (Fin (k a) ⊕ {j : Fin d // g j=a})) ≃
      (((a : Fin m) × Fin (k a)) ⊕ Fin d) where
  toFun x := match x with
    | ⟨a,Sum.inl i⟩ => Sum.inl ⟨a,i⟩
    | ⟨_,Sum.inr j⟩ => Sum.inr j.1
  invFun x := match x with
    | Sum.inl ⟨a,i⟩ => ⟨a,Sum.inl i⟩
    | Sum.inr j => ⟨g j,Sum.inr ⟨j,rfl⟩⟩
  left_inv x := by
    rcases x with ⟨a,i | ⟨j,hj⟩⟩
    · rfl
    · cases hj
      rfl
  right_inv x := by
    rcases x with ⟨a,i⟩ | j <;> rfl

lemma cavityBaseGroupSumEquiv_label {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (x : (a : Fin m) × (Fin (k a) ⊕ {j : Fin d // g j=a})) :
    Sum.elim (fun w => w.1) g (cavityBaseGroupSumEquiv k g x)=x.1 := by
  rcases x with ⟨a,i | j⟩
  · rfl
  · exact j.2

def cavityBaseGroupDimension {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (a : Fin m) : ℕ := k a+Fintype.card {j : Fin d // g j=a}

def cavityBaseGroupEquiv {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m) :
    ((a : Fin m) × Fin (cavityBaseGroupDimension k g a)) ≃ Fin N :=
  (Equiv.sigmaCongrRight (fun a => finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin {j : Fin d // g j=a}).symm))).trans
      ((cavityBaseGroupSumEquiv k g).trans e)

lemma cavityBaseGroupEquiv_label {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (i : Fin N) :
    ((cavityBaseGroupEquiv k e g).symm i).1 = Sum.elim (fun w => w.1) g (e.symm i) := by
  let E := cavityBaseGroupEquiv k e g
  have h (x : (a : Fin m) × Fin (cavityBaseGroupDimension k g a)) :
      Sum.elim (fun w => w.1) g (e.symm (E x))=x.1 := by
    change Sum.elim (fun w => w.1) g (e.symm (e (cavityBaseGroupSumEquiv k g _)))=x.1
    rw [e.symm_apply_apply, cavityBaseGroupSumEquiv_label]
    rfl
  simpa only [E, Equiv.apply_symm_apply] using (h (E.symm i)).symm

lemma cavityBaseGroupDimension_ge {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (a : Fin m) : k a ≤ cavityBaseGroupDimension k g a := Nat.le_add_right _ _

theorem cavity_canonical_group_frames {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    ∃ A : (a : Fin m) → Matrix (Fin (cavityBaseGroupDimension k g a)) (Fin d) ℝ,
      (∀ a, (A a).transpose*A a=1) ∧
      cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
        (fun j => (g j,j)) A = cavityCanonicalSpecial e := by
  have hlabel j : ((cavityBaseGroupEquiv k e g).symm (e (Sum.inr j))).1=g j := by
    rw [cavityBaseGroupEquiv_label, e.symm_apply_apply]
    rfl
  obtain ⟨f,hf⟩ := cavity_group_selected_embedding (cavityBaseGroupDimension k g)
    (cavityBaseGroupEquiv k e g) (fun j => e (Sum.inr j))
    (e.injective.comp Sum.inr_injective) g hlabel
    (fun a => (hk a).trans (cavityBaseGroupDimension_ge k g a))
  refine ⟨cavitySelectedGroupFrame (cavityBaseGroupDimension k g) f,
    cavitySelectedGroupFrame_gram _ f, ?_⟩
  rw [cavitySelectedGroupFrame_columns]
  ext i j
  rw [hf]
  rfl

end InvariantIsing

end

end OAI
