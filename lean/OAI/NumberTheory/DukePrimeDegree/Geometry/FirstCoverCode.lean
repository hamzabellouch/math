import OAI.NumberTheory.DukePrimeDegree.Geometry.CutFamilyCode

namespace OAI

/-! # One covering label instead of the full vector of cut tests

A point is labeled by one cut containing it. There are N+1 labels for N
cuts. Equality of labels still puts covered points in the same small
set, while constancy of all cut tests implies constancy of this label.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

private def firstTrue {N : ℕ} (w : Fin N → Bool) : Fin (N+1) :=
  if h : ∃ i, w i=true then ⟨h.choose.val+1,Nat.succ_lt_succ h.choose.isLt⟩ else 0

private lemma firstTrue_common {N : ℕ} (v w : Fin N → Bool)
    (hw : ∃ i, w i=true) (h : firstTrue v=firstTrue w) :
    ∃ i, v i=true ∧ w i=true := by
  classical
  have hv : ∃ i, v i=true := by
    by_contra hn
    have hh := congrArg Fin.val h
    simp only [firstTrue,dite_eq_right hn,dite_eq_left hw,Fin.val_zero] at hh
    omega
  have hi : hv.choose=hw.choose := by
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [firstTrue,dite_eq_left hv,dite_eq_left hw] at hh
    omega
  exact ⟨hw.choose,hi ▸ hv.choose_spec,hw.choose_spec⟩

def firstCoverCode {Y : Type*} {N : ℕ} (f : Fin N → Y → ℝ)
    (c : Fin N → ℝ) (x : Y) : Fin (N+1) :=
  firstTrue (fun i => decide (f i x<c i))

lemma firstCoverCode_measurable {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    {f : Fin N → Y → ℝ} (hf : ∀ i, Measurable (f i)) (c : Fin N → ℝ) :
    Measurable (firstCoverCode f c) := by
  have h := (measurable_of_finite
    (fun u : Fin (Fintype.card (Fin N → Bool)) =>
      firstTrue ((Fintype.equivFin (Fin N → Bool)).symm u))).comp
        (finiteCutCode_measurable hf c)
  change Measurable (fun x => firstTrue (fun i => decide (f i x<c i)))
  simpa only [Function.comp_def,finiteCutCode,Equiv.symm_apply_apply] using h

lemma firstCoverCode_eq_of_cutCode_eq {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (h : finiteCutCode f c y=finiteCutCode f c x) :
    firstCoverCode f c y=firstCoverCode f c x :=
  congrArg firstTrue ((Fintype.equivFin (Fin N → Bool)).injective h)


lemma firstCoverCode_selected {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) (x : Y)
    (hx : ∃ i, f i x<c i) :
    ∃ i : Fin N, (firstCoverCode f c x).val=i.val+1 ∧ f i x<c i := by
  have hw : ∃ i, decide (f i x<c i)=true := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,decide_eq_true hi⟩
  refine ⟨hw.choose,?_,of_decide_eq_true hw.choose_spec⟩
  simp only [firstCoverCode,firstTrue,dite_eq_left hw]

lemma firstCoverCode_common {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (hx : ∃ i, f i x<c i) (h : firstCoverCode f c y=firstCoverCode f c x) :
    ∃ i, f i y<c i ∧ f i x<c i := by
  have hw : ∃ i, decide (f i x<c i)=true := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,decide_eq_true hi⟩
  obtain ⟨i,hi,hj⟩ := firstTrue_common (fun i => decide (f i y<c i))
    (fun i => decide (f i x<c i)) hw h
  exact ⟨i,of_decide_eq_true hi,of_decide_eq_true hj⟩

lemma layered_firstCover_eq_of_cutCode_eq {Y : Type*} {N : ℕ → ℕ}
    (H : Y → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ) (c : ∀ m, Fin (N m) → ℝ)
    {x y : Y}
    (h : layeredObservation H (fun m => finiteCutCode (f m) (c m)) y =
      layeredObservation H (fun m => finiteCutCode (f m) (c m)) x) :
    layeredObservation H (fun m => firstCoverCode (f m) (c m)) y =
      layeredObservation H (fun m => firstCoverCode (f m) (c m)) x := by
  obtain ⟨hH,hP⟩ := layeredObservation_eq H _ h
  unfold layeredObservation
  rw [hH]
  dsimp only
  rw [firstCoverCode_eq_of_cutCode_eq _ _ hP]

end DukePrimeDegree

end

end OAI
