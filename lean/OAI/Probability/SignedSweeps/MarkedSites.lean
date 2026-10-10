import OAI.Probability.SignedSweeps.TensorMultiplicity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev MarkedAssignment (l n : ℕ) := Fin l ↪ Fin n

def moveMarks {l n : ℕ} (g : SymmetricGroup n) (z : MarkedAssignment l n) :
    MarkedAssignment l n := z.trans g.toEmbedding

@[simp] lemma moveMarks_apply {l n : ℕ} (g : SymmetricGroup n)
    (z : MarkedAssignment l n) (a : Fin l) : moveMarks g z a = g (z a) := rfl

@[simp] lemma moveMarks_one {l n : ℕ} (z : MarkedAssignment l n) : moveMarks 1 z = z := by
  ext a; rfl

@[simp] lemma moveMarks_mul {l n : ℕ} (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) : moveMarks (g*t) z = moveMarks g (moveMarks t z) := by
  ext a; rfl

abbrev MarkedComplement {l n : ℕ} (z : MarkedAssignment l n) :=
  {x : Fin n // x ∉ Set.range z}

lemma markedComplement_card {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fintype.card (MarkedComplement z) = p := by
  rw [Fintype.card_subtype_compl (fun x => x ∈ Set.range z)]
  have hr : Fintype.card (Set.range z) = l := by
    simpa using Fintype.card_congr (Equiv.ofInjective z z.injective).symm
  rw [hr, Fintype.card_fin]
  omega

def markedSites {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ≃ MarkedComplement z :=
  (Fintype.equivFinOfCardEq (markedComplement_card h z)).symm

def markedInjection {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ↪ Fin n := (markedSites h z).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] lemma markedInjection_apply {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h z i = (markedSites h z i).1 := rfl

lemma markedInjection_avoids {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) : markedInjection h z i ∉ Set.range z :=
  (markedSites h z i).2

def moveComplement {l n : ℕ} (g : SymmetricGroup n) (z : MarkedAssignment l n) :
    MarkedComplement z ≃ MarkedComplement (moveMarks g z) where
  toFun x := ⟨g x.1, by
    rintro ⟨a,ha⟩
    exact x.2 ⟨a,g.injective ha⟩⟩
  invFun x := ⟨g.symm x.1, by
    rintro ⟨a,ha⟩
    apply x.2
    exact ⟨a,by simp only [moveMarks_apply, ha, Equiv.apply_symm_apply]⟩⟩
  left_inv x := by apply Subtype.ext; exact g.symm_apply_apply _
  right_inv x := by apply Subtype.ext; exact g.apply_symm_apply _

def markedSpinTransport {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : SymmetricGroup p :=
  (markedSites h z).trans ((moveComplement g z).trans (markedSites h (moveMarks g z)).symm)

lemma markedSpinTransport_sites {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h (moveMarks g z) (markedSpinTransport h g z i) =
      g (markedInjection h z i) := by
  change ((markedSites h (moveMarks g z))
    ((markedSites h (moveMarks g z)).symm (moveComplement g z (markedSites h z i)))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] lemma markedSpinTransport_one {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    markedSpinTransport h 1 z = 1 := by
  apply Equiv.ext
  intro i
  apply (markedInjection h z).injective
  simpa using markedSpinTransport_sites h 1 z i

lemma markedSpinTransport_mul {p l n : ℕ} (h : p+l=n) (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedSpinTransport h (g*t) z = markedSpinTransport h g (moveMarks t z) *
      markedSpinTransport h t z := by
  apply Equiv.ext
  intro i
  apply (markedInjection h (moveMarks (g*t) z)).injective
  rw [markedSpinTransport_sites, moveMarks_mul]
  change (g*t) (markedInjection h z i) =
    markedInjection h (moveMarks g (moveMarks t z))
      (markedSpinTransport h g (moveMarks t z) (markedSpinTransport h t z i))
  rw [markedSpinTransport_sites, markedSpinTransport_sites]
  rfl

def moveMarksEquiv {l n : ℕ} (g : SymmetricGroup n) :
    MarkedAssignment l n ≃ MarkedAssignment l n where
  toFun := moveMarks g
  invFun := moveMarks g⁻¹
  left_inv z := by rw [← moveMarks_mul, inv_mul_cancel, moveMarks_one]
  right_inv z := by rw [← moveMarks_mul, mul_inv_cancel, moveMarks_one]

@[simp] lemma moveMarksEquiv_apply {l n : ℕ} (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : moveMarksEquiv g z = moveMarks g z := rfl

def markedAllSites {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ⊕ Fin l ≃ Fin n :=
  (Equiv.sumCongr (markedSites h z) (Equiv.ofInjective z z.injective)).trans
    ((Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (Set.range z)))

@[simp] lemma markedAllSites_left {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (i : Fin p) : markedAllSites h z (Sum.inl i) = markedInjection h z i := rfl

@[simp] lemma markedAllSites_right {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (i : Fin l) : markedAllSites h z (Sum.inr i) = z i := rfl

lemma moveMarks_viaEmbedding {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (g : SymmetricGroup p) : moveMarks (g.viaEmbedding (markedInjection h z)) z = z := by
  apply Function.Embedding.ext
  intro a
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,hi⟩
  exact markedInjection_avoids h z i ⟨a,hi.symm⟩

lemma markedSpinTransport_viaEmbedding {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (g : SymmetricGroup p) : markedSpinTransport h (g.viaEmbedding (markedInjection h z)) z = g := by
  apply Equiv.ext
  intro i
  apply (markedInjection h z).injective
  have he := markedSpinTransport_sites h (g.viaEmbedding (markedInjection h z)) z i
  rw [moveMarks_viaEmbedding, Equiv.Perm.viaEmbedding_apply] at he
  exact he

end SignedSweeps
end

end OAI
