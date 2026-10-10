import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEntryParity

namespace OAI

/-! Extending a Pauli word by identities is exactly the local tensor lift. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliExtend (S : Finset ι) (w : {i // i ∈ S} → Fin 4) : ι → Fin 4 :=
  fun i => if hi : i ∈ S then w ⟨i,hi⟩ else 0

theorem qmaPauliExtend_support (S : Finset ι) (w : {i // i ∈ S} → Fin 4) :
    qmaPauliSupport (qmaPauliExtend S w) ⊆ S := by
  intro i hi
  by_contra h
  simp [qmaPauliSupport,qmaPauliExtend,h] at hi

theorem qmaPauliExtend_lift (S : Finset ι) (w : {i // i ∈ S} → Fin 4) :
    qmaPauliWord (qmaPauliExtend S w) = qmaLocalLift S (qmaPauliWord w) := by
  ext s t
  rw [qmaLocalLift_apply]
  change (∏ i, qmaPauli (qmaPauliExtend S w i) (s i) (t i)) =
    (∏ i : {i // i ∈ S}, qmaPauli (w i) (s i.val) (t i.val))*
      (if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0)
  by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
  · rw [ite_eq_left hr,mul_one]
    have he (i : ι) (_hi : i ∈ Finset.univ) (hi : i ∉ S) :
        qmaPauli (qmaPauliExtend S w i) (s i) (t i) = 1 := by
      simp only [qmaPauliExtend,hi,dite_false,qmaPauli_zero,Matrix.one_apply]
      exact ite_eq_left (congrFun hr ⟨i,hi⟩)
    have hp := Finset.prod_subset (Finset.subset_univ S) he
    have hs := Finset.prod_subtype (F := inferInstance) S
      (by simp : ∀ i, i ∈ S ↔ i ∈ S) (fun i => qmaPauli (qmaPauliExtend S w i) (s i) (t i))
    have hex := hp.symm.trans hs
    have hw (i : {i // i ∈ S}) : qmaPauliExtend S w i.val = w i := by
      simp [qmaPauliExtend,i.property]
    simpa only [hw] using hex
  · rw [ite_eq_right hr,mul_zero]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    simp only [qmaPauliExtend,i.property,dite_false,qmaPauli_zero,Matrix.one_apply]
    exact ite_eq_right hi

theorem qmaPauliExtend_yCount (S : Finset ι) (w : {i // i ∈ S} → Fin 4) :
    qmaPauliYCount (qmaPauliExtend S w) = qmaPauliYCount w := by
  unfold qmaPauliYCount
  have he : Finset.univ.filter (fun i => qmaPauliExtend S w i = 2) =
      (Finset.univ.filter (fun i : {i // i ∈ S} => w i = 2)).map
        ⟨Subtype.val,Subtype.val_injective⟩ := by
    ext i
    constructor
    · intro hi
      have he := (Finset.mem_filter.mp hi).2
      by_cases hS : i ∈ S
      · exact Finset.mem_map.mpr ⟨⟨i,hS⟩,by simpa [qmaPauliExtend,hS] using he,rfl⟩
      · simp [qmaPauliExtend,hS] at he
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change qmaPauliExtend S w j.val = 2
      simpa [qmaPauliExtend,j.property] using (Finset.mem_filter.mp hj).2
  rw [he,Finset.card_map]

end ContinuumCoulomb

end

end OAI
