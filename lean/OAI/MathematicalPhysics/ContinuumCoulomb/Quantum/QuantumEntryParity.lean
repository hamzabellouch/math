import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliSplit
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitPhaseLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumThirdCounterterm

namespace OAI

/-! Real and purely imaginary entry parities determine the mediator phase. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ : Type*}

def QMAEntryParity (p : Bool) (M : Matrix σ σ ℂ) : Prop :=
  if p = true then ∀ s t, (M s t).re = 0 else ∀ s t, (M s t).im = 0

theorem QMAEntryParity.add {p : Bool} {M N : Matrix σ σ ℂ}
    (hM : QMAEntryParity p M) (hN : QMAEntryParity p N) : QMAEntryParity p (M+N) := by
  cases p <;> simp only [QMAEntryParity,Bool.false_eq_true,ite_false,ite_true] at *
  · intro s t
    simp [hM s t,hN s t]
  · intro s t
    simp [hM s t,hN s t]

theorem QMAEntryParity.real_smul {p : Bool} {M : Matrix σ σ ℂ}
    (hM : QMAEntryParity p M) (r : ℝ) : QMAEntryParity p (r • M) := by
  cases p <;> simp only [QMAEntryParity,Bool.false_eq_true,ite_false,ite_true] at *
  · intro s t
    simp [hM s t]
  · intro s t
    simp [hM s t]

theorem QMAEntryParity.pair {p : Bool} {M N : Matrix σ σ ℂ}
    (hM : QMAEntryParity p M) (hN : QMAEntryParity p N) (j : ℝ) :
    QMAEntryParity p (qmaThirdSeriesPair M N j) := by
  have he : qmaThirdSeriesPair M N j = M+(j/2:ℝ) • N := by
    change M+((j:ℂ)/2) • N = M+((j/2:ℝ):ℂ) • N
    push_cast
    rfl
  rw [he]
  exact hM.add (hN.real_smul (j/2))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qmaPauliWord_real_of_even (w : ι → Fin 4) (h : Even (qmaPauliYCount w)) :
    QMAEntryParity false (qmaPauliWord w) := by
  intro s t
  have hc := congrArg Complex.im (qmaPauliWord_conjugate w s t)
  rw [h.neg_one_pow] at hc
  simp only [Complex.star_def,Complex.conj_im,one_mul] at hc
  linarith

omit [DecidableEq ι] in
theorem qmaPauliWord_imaginary_of_odd (w : ι → Fin 4) (h : Odd (qmaPauliYCount w)) :
    QMAEntryParity true (qmaPauliWord w) := by
  intro s t
  have hc := congrArg Complex.re (qmaPauliWord_conjugate w s t)
  rw [h.neg_one_pow] at hc
  simp only [Complex.star_def,Complex.conj_re,neg_one_mul,Complex.neg_re] at hc
  linarith

omit [DecidableEq ι] in
theorem qmaPauliWord_entryParity (w : ι → Fin 4) :
    QMAEntryParity (decide (Odd (qmaPauliYCount w))) (qmaPauliWord w) := by
  by_cases h : Odd (qmaPauliYCount w)
  · simpa only [h,decide_true] using qmaPauliWord_imaginary_of_odd w h
  · have he : Even (qmaPauliYCount w) := (Nat.even_or_odd _).resolve_right h
    simpa only [h,decide_false] using qmaPauliWord_real_of_even w he

theorem qmaPauliYCount_restrict (S : Finset ι) (w : ι → Fin 4) :
    qmaPauliYCount (qmaPauliRestrict S w) = (S.filter (fun i => w i = 2)).card := by
  unfold qmaPauliYCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : i ∈ S <;> simp [qmaPauliRestrict,hi]

theorem qmaPauliYCount_split (S T : Finset ι) (w : ι → Fin 4)
    (hST : Disjoint S T) (hcover : qmaPauliSupport w ⊆ S ∪ T) :
    qmaPauliYCount (qmaPauliRestrict S w)+qmaPauliYCount (qmaPauliRestrict T w) =
      qmaPauliYCount w := by
  rw [qmaPauliYCount_restrict,qmaPauliYCount_restrict]
  have hd : Disjoint (S.filter (fun i => w i = 2)) (T.filter (fun i => w i = 2)) :=
    hST.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← Finset.card_union_of_disjoint hd]
  unfold qmaPauliYCount
  congr 1
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi <;> simpa using (Finset.mem_filter.mp hi).2
  · intro hi
    have hw := (Finset.mem_filter.mp hi).2
    have hs : i ∈ qmaPauliSupport w := by simp [qmaPauliSupport,hw]
    rcases Finset.mem_union.mp (hcover hs) with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,hw⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hw⟩)

theorem qmaPauliRestrict_same_parity (S T : Finset ι) (w : ι → Fin 4)
    (hST : Disjoint S T) (hcover : qmaPauliSupport w ⊆ S ∪ T)
    (hw : Even (qmaPauliYCount w)) :
    decide (Odd (qmaPauliYCount (qmaPauliRestrict S w))) =
      decide (Odd (qmaPauliYCount (qmaPauliRestrict T w))) := by
  have hsum := qmaPauliYCount_split S T w hST hcover
  simp only [Nat.even_iff] at hw
  have he : Odd (qmaPauliYCount (qmaPauliRestrict S w)) ↔
      Odd (qmaPauliYCount (qmaPauliRestrict T w)) := by
    simp only [Nat.odd_iff]
    omega
  simp only [he]

end ContinuumCoulomb

end

end OAI
