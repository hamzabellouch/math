import OAI.Probability.InvariantIsing.Cavity.CavityOrderedGroups
import OAI.Probability.InvariantIsing.Cavity.CavityBaseGroups

namespace OAI

/-! The retained and special axes can be identified with the same ordered
spectral basis used for the scalar pressure sequence. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityBaseGroupEquiv_trans {N M m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (f : Fin N ≃ Fin M) :
    cavityBaseGroupEquiv k (e.trans f) g=(cavityBaseGroupEquiv k e g).trans f := rfl

def cavityOrderedBase {N m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (hsum : ∑ a, cavityBaseGroupDimension k g a=N) :
    (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N :=
  let e := Fintype.equivFin (((a : Fin m) × Fin (k a)) ⊕ Fin d)
  e.trans ((cavityBaseGroupEquiv k e g).symm.trans
    (cavityOrderedEquiv (cavityBaseGroupDimension k g) hsum))

lemma cavityOrderedBase_group {N m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (hsum : ∑ a, cavityBaseGroupDimension k g a=N) :
    cavityBaseGroupEquiv k (cavityOrderedBase k g hsum) g=
      cavityOrderedEquiv (cavityBaseGroupDimension k g) hsum := by
  unfold cavityOrderedBase
  rw [cavityBaseGroupEquiv_trans]
  simp only [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

lemma cavityOrderedBase_label {N m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (hsum : ∑ a, cavityBaseGroupDimension k g a=N) (i : Fin N) :
    Sum.elim (fun w => w.1) g ((cavityOrderedBase k g hsum).symm i)=
      cavityOrderedGroup (cavityBaseGroupDimension k g) hsum i := by
  rw [← cavityBaseGroupEquiv_label, cavityOrderedBase_group]
  rfl

lemma cavity_special_labels_exists {m n d : ℕ} (s : Fin m → ℕ)
    (hdim : ∑ a, (n-s a)=d) :
    ∃ g : Fin d → Fin m, ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a := by
  refine ⟨cavityOrderedGroup (fun a => n-s a) hdim,?_⟩
  intro a
  exact cavityOrderedGroup_card (fun a => n-s a) hdim a

end InvariantIsing

end

end OAI
