import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSupportFactors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSplit

namespace OAI

/-! Literal XZ/ZX factors for the only possible real two-site Y term. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedYY
open Matrix
open scoped Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def factor (xs : List ι) (w : ι → Fin 4) : (ι → Fin 4) × (ι → Fin 4) :=
  match xs with
  | [a,b] => if w a = 2 then (qmaTwoPauliWord a b 1 3,qmaTwoPauliWord a b 3 1)
      else (w,fun _ => 0)
  | _ => (w,fun _ => 0)

private theorem classify (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 2)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) :
    (∀ i, w i ≠ 2) ∨ ∃ a b, xs = [a,b] ∧ a ≠ b ∧ w = qmaTwoPauliWord a b 2 2 := by
  have hs : (qmaPauliSupport w).card ≤ 2 :=
    (Finset.card_le_card hcover).trans ((List.toFinset_card_le _).trans hlen)
  rcases qmaTwoLocalEvenY_cases w hs he with h | ⟨i,j,hij,rfl⟩
  · exact Or.inl h
  · right
    rw [qmaTwoPauliYY_support_eq] at hcover
    have htwo : 2 ≤ xs.length := calc
      2 = ({i,j} : Finset ι).card := by simp [hij]
      _ ≤ xs.toFinset.card := Finset.card_le_card hcover
      _ ≤ xs.length := List.toFinset_card_le _
    have hshape : ∃ a b, xs = [a,b] := by
      cases xs with
      | nil => simp at htwo
      | cons a ys =>
        cases ys with
        | nil => simp at htwo
        | cons b zs =>
          cases zs with
          | nil => exact ⟨a,b,rfl⟩
          | cons c zs => simp at hlen
    obtain ⟨a,b,rfl⟩ := hshape
    have hab : a ≠ b := by simpa using hx
    have heq : ({i,j} : Finset ι) = [a,b].toFinset :=
      Finset.eq_of_subset_of_card_le hcover (by simp [hij,hab])
    have ha : a = i ∨ a = j := by
      have : a ∈ ({i,j} : Finset ι) := by rw [heq]; simp
      simpa using this
    have hb : b = i ∨ b = j := by
      have : b ∈ ({i,j} : Finset ι) := by rw [heq]; simp
      simpa using this
    refine ⟨a,b,rfl,hab,?_⟩
    funext k
    by_cases hka : k = a
    · subst k
      rcases ha with rfl | rfl <;> simp [qmaTwoPauliWord]
    · by_cases hkb : k = b
      · subst k
        rcases hb with rfl | rfl <;> simp [qmaTwoPauliWord,hka]
      · have hki : k ≠ i := by
          intro hki
          have : k ∈ [a,b].toFinset := hcover (by simp [hki])
          simp [hka,hkb] at this
        have hkj : k ≠ j := by
          intro hkj
          have : k ∈ [a,b].toFinset := hcover (by simp [hkj])
          simp [hka,hkb] at this
        simp [qmaTwoPauliWord,hka,hkb,hki,hkj]

omit [Fintype ι] in
private theorem factor_noY (xs : List ι) (w : ι → Fin 4) (h : ∀ i, w i ≠ 2) :
    factor xs w = (w,fun _ => 0) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => simp [factor,h]
      | cons c xs => rfl

theorem factors (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 2)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) :
    (∀ i, (factor xs w).1 i ≠ 2) ∧ (∀ i, (factor xs w).2 i ≠ 2) ∧
    qmaPauliSupport (factor xs w).1 ⊆ xs.toFinset ∧
    qmaPauliSupport (factor xs w).2 ⊆ xs.toFinset ∧
    qmaPauliWord (factor xs w).1*qmaPauliWord (factor xs w).2 = qmaPauliWord w ∧
    qmaPauliWord (factor xs w).1*qmaPauliWord (factor xs w).2 =
      qmaPauliWord (factor xs w).2*qmaPauliWord (factor xs w).1 := by
  rcases classify xs w hlen hx hcover he with h | ⟨a,b,rfl,hab,rfl⟩
  · rw [factor_noY xs w h]
    refine ⟨h,by simp,hcover,by simp [qmaPauliSupport],?_,?_⟩
    · simp only [qmaPauliWord_zero,Matrix.mul_one]
    · simp only [qmaPauliWord_zero,Matrix.mul_one,Matrix.one_mul]
  · simp only [factor,qmaTwoPauliWord,ite_true]
    change (∀ i, qmaTwoPauliWord a b 1 3 i ≠ 2) ∧
      (∀ i, qmaTwoPauliWord a b 3 1 i ≠ 2) ∧ _
    refine ⟨?_,?_,?_,?_,qmaYY_factor a b hab,qmaYY_factor_commute a b hab⟩
    · intro i; simp only [qmaTwoPauliWord]; split_ifs <;> decide
    · intro i; simp only [qmaTwoPauliWord]; split_ifs <;> decide
    · simpa using qmaTwoPauliWord_support a b 1 3
    · simpa using qmaTwoPauliWord_support a b 3 1

end ContinuumCoulomb.QuantumOrderedYY

end

end OAI
