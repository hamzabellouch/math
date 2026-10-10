import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Geometry.CapCompact
import OAI.Probability.LatticeSurface.Geometry.CapContract
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

def bulkIndex (pins : Set V) (W : Finset V) (hwp : ∀ w ∈ W, w ∉ pins) :
    Free pins ≃ (Free (pins ∪ (W : Set V))) ⊕ W where
  toFun x := if hx : (x : V) ∈ W then .inr ⟨x,hx⟩ else .inl ⟨x,by simpa using ⟨x.2,hx⟩⟩
  invFun x := x.elim (fun (x : Free (pins ∪ (W : Set V))) => ⟨x, fun hp => x.2 (Or.inl hp)⟩)
    (fun (x : W) => ⟨x,hwp x x.2⟩)
  left_inv := by
    intro x
    by_cases hx : (x : V) ∈ W
    · simp only [dite_eq_left hx, Sum.elim_inr]
    · simp only [dite_eq_right hx, Sum.elim_inl]
  right_inv := by
    intro x
    cases x with
    | inl x =>
      have hx : (x : V) ∉ W := fun h => x.2 (Or.inr h)
      simp [hx]
    | inr x => simp [x.2]

def splitBulk (pins : Set V) (W : Finset V) (hwp : ∀ w ∈ W, w ∉ pins) :
    (Free pins → ℝ) ≃ᵐ ((Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Free (pins ∪ (W : Set V)) ⊕ W => ℝ)
    (bulkIndex pins W hwp)).trans (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

lemma preserving_splitBulk [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) : MeasurePreserving (splitBulk pins W hwp) := by
  exact (volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ)).comp
    (volume_measurePreserving_piCongrLeft _ (bulkIndex pins W hwp))

@[simp] lemma splitBulk_fst (pins : Set V) (W : Finset V) (hwp : ∀ w ∈ W, w ∉ pins)
    (h : Free pins → ℝ) (x : Free (pins ∪ (W : Set V))) :
    (splitBulk pins W hwp h).1 x = h ⟨x, fun hp => x.2 (Or.inl hp)⟩ := by
  simp [splitBulk, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, bulkIndex]

@[simp] lemma splitBulk_snd (pins : Set V) (W : Finset V) (hwp : ∀ w ∈ W, w ∉ pins)
    (h : Free pins → ℝ) (x : W) :
    (splitBulk pins W hwp h).2 x = h ⟨x,hwp x x.2⟩ := by
  simp [splitBulk, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, bulkIndex]

lemma continuous_splitBulk [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) : Continuous (splitBulk pins W hwp) := by
  change Continuous (fun h => ((splitBulk pins W hwp h).1, (splitBulk pins W hwp h).2))
  apply Continuous.prodMk
  · apply continuous_pi; intro x
    simpa only [splitBulk_fst] using (continuous_apply (⟨x,fun hp => x.2 (Or.inl hp)⟩ : Free pins))
  · apply continuous_pi; intro x
    simpa only [splitBulk_snd] using (continuous_apply (⟨x,hwp x x.2⟩ : Free pins))

lemma splitBulk_restore (pins : Set V) (W : Finset V) (hwp : ∀ w ∈ W, w ∉ pins)
    (p : (Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) (x : V) :
    restore pins (fun _ => 0) ((splitBulk pins W hwp).symm p) x =
      if hx : x ∈ W then p.2 ⟨x,hx⟩ else restore (pins ∪ (W : Set V)) (fun _ => 0) p.1 x := by
  by_cases hx : x ∈ W
  · have hxp := hwp x hx
    simp [restore, hx, hxp, splitBulk, MeasurableEquiv.piCongrLeft, bulkIndex,
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  · by_cases hxp : x ∈ pins
    · simp [restore, hx, hxp]
    · simp [restore, hx, hxp, splitBulk, MeasurableEquiv.piCongrLeft, bulkIndex,
        MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]

def targetHeight (pins : Set V) (W : Finset V) (r : V → V)
    (h : Free (pins ∪ (W : Set V)) → ℝ) (w : W) : ℝ :=
  restore (pins ∪ (W : Set V)) (fun _ => 0) h (r w)

lemma continuous_targetHeight [Fintype V] (pins : Set V) (W : Finset V) (r : V → V) :
    Continuous (targetHeight pins W r) :=
  continuous_pi fun _ => continuous_restore _ _ _

def gradientShift [Fintype V] (pins : Set V) (W : Finset V) (r : V → V) :
    ((Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) ≃ᵐ
      ((Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) where
  toFun p := (p.1, p.2-targetHeight pins W r p.1)
  invFun p := (p.1, p.2+targetHeight pins W r p.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp
  measurable_toFun := measurable_fst.prodMk
    (measurable_snd.sub ((continuous_targetHeight pins W r).measurable.comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk
    (measurable_snd.add ((continuous_targetHeight pins W r).measurable.comp measurable_fst))

lemma preserving_gradientShift [Fintype V] (pins : Set V) (W : Finset V) (r : V → V) :
    MeasurePreserving (gradientShift pins W r) := by
  exact (MeasurePreserving.id volume).skew_product
    (measurable_snd.sub ((continuous_targetHeight pins W r).measurable.comp measurable_fst))
    (Filter.Eventually.of_forall fun h =>
      (measurePreserving_add_right (volume : Measure (W → ℝ)) (-targetHeight pins W r h)).map_eq)

def gradientCoords [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V) :
    (Free pins → ℝ) ≃ᵐ ((Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) :=
  (splitBulk pins W hwp).trans (gradientShift pins W r)

lemma preserving_gradientCoords [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V) :
    MeasurePreserving (gradientCoords pins W hwp r) :=
  (preserving_gradientShift pins W r).comp (preserving_splitBulk pins W hwp)

lemma continuous_gradientCoords [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V) :
    Continuous (gradientCoords pins W hwp r) :=
  (continuous_fst.prodMk
    (continuous_snd.sub ((continuous_targetHeight pins W r).comp continuous_fst))).comp
      (continuous_splitBulk pins W hwp)

def fromGradients (pins : Set V) (W : Finset V) (r : V → V)
    (p : (Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) (x : V) : ℝ :=
  if hx : x ∈ W then p.2 ⟨x,hx⟩ + restore (pins ∪ (W : Set V)) (fun _ => 0) p.1 (r x)
  else restore (pins ∪ (W : Set V)) (fun _ => 0) p.1 x

lemma gradient_restore [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V)
    (p : (Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) (x : V) :
    restore pins (fun _ => 0) ((gradientCoords pins W hwp r).symm p) x =
      fromGradients pins W r p x := by
  change restore pins (fun _ => 0) ((splitBulk pins W hwp).symm
    (p.1,p.2+targetHeight pins W r p.1)) x = _
  rw [splitBulk_restore]
  rfl

lemma fromGradients_zero (pins : Set V) (W : Finset V) (r : V → V)
    (h : Free (pins ∪ (W : Set V)) → ℝ) (x : V) :
    fromGradients pins W r (h,0) x =
      restore (pins ∪ (W : Set V)) (fun _ => 0) h (collapse W r x) := by
  by_cases hx : x ∈ W <;> simp [fromGradients, collapse, hx]

lemma fromGradients_comb (pins : Set V) (W : Finset V) (r : V → V)
    (p q : (Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) (s t : ℝ) (x : V) :
    fromGradients pins W r (s • p+t • q) x =
      s*fromGradients pins W r p x+t*fromGradients pins W r q x := by
  by_cases hx : x ∈ W <;>
    simp [fromGradients, hx, restore_zero_add, restore_zero_smul]
  ring

lemma fromGradients_neg (pins : Set V) (W : Finset V) (r : V → V)
    (p : (Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) (x : V) :
    fromGradients pins W r (-p) x = -fromGradients pins W r p x := by
  have hh := fromGradients_comb pins W r p p (-1) 0 x
  simpa using hh

lemma gradientCoords_difference [Fintype V] (pins : Set V) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V) (hr : ∀ w ∈ W, r w ∉ W)
    (h : Free pins → ℝ) (w : W) :
    (gradientCoords pins W hwp r h).2 w =
      restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w) := by
  have hrel (x : V) (hx : x ∉ W) :
      restore (pins ∪ (W : Set V)) (fun _ => 0) (splitBulk pins W hwp h).1 x =
        restore pins (fun _ => 0) h x := by
    by_cases hp : x ∈ pins
    · simp [restore, hp]
    · simp [restore, hx, hp]
  change (splitBulk pins W hwp h).2 w-restore (pins ∪ (W : Set V)) (fun _ => 0)
    (splitBulk pins W hwp h).1 (r w) = _
  rw [splitBulk_snd, hrel _ (hr w w.2)]
  simp [restore, hwp w w.2]

end ExtremalEdges

end

end OAI
