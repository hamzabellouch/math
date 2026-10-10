import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodQuantities
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledVariationSplit
import OAI.Analysis.LipschitzHilbert.Trees.SourceBadEventUnion

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

def physicalReferenceEvent (i : Fin 3) : Set (ℝ×ℝ) :=
  if i = 0 then {z | L^e ≤ P.physicalAngularError t a b v g z}
  else if i = 1 then {z | L^s ≤ P.physicalMainSquareOnPlane t a b v g z}
  else {z | L^r ≤ P.physicalMaskedVariation alt hAlt t b v g T L A (z.2-t*z.1) z.1}

def physicalReferenceBad : Set (ℝ×ℝ) :=
  ⋃ i : Fin 3, P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i

theorem physicalReferenceEvent_measurable (i : Fin 3) :
    MeasurableSet (P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i) := by
  unfold physicalReferenceEvent
  split_ifs
  · exact measurableSet_le measurable_const (P.physicalAngularError_measurable t a b v g)
  · exact measurableSet_le measurable_const (P.physicalMainSquareOnPlane_continuous t a b v g).measurable
  · exact measurableSet_le measurable_const
      (P.physicalMaskedVariation_physical_continuous alt hAlt t b v g T L A).measurable

theorem physicalReferenceBad_measurable :
    MeasurableSet (P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :=
  MeasurableSet.iUnion (P.physicalReferenceEvent_measurable alt hAlt t a b v g T L A e s r)

theorem physicalReferenceBad_compl_bounds (z : ℝ×ℝ)
    (hz : z ∉ P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :
    P.physicalAngularError t a b v g z < L^e ∧
    P.physicalMainSquareOnPlane t a b v g z < L^s ∧
    P.physicalMaskedVariation alt hAlt t b v g T L A (z.2-t*z.1) z.1 < L^r := by
  have h (i : Fin 3) : z ∉ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i :=
    fun hi => hz (mem_iUnion.mpr ⟨i,hi⟩)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [physicalReferenceEvent,ite_true,Set.mem_ofPred_eq] at h0
  simp only [physicalReferenceEvent,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,
    Set.mem_ofPred_eq] at h1
  simp only [physicalReferenceEvent,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false,Set.mem_ofPred_eq] at h2
  exact ⟨lt_of_not_ge h0,lt_of_not_ge h1,lt_of_not_ge h2⟩

theorem physicalReferenceEvent_line_zero (y : ℝ) :
    {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 0} =
      {x | L^e ≤ P.physicalAngularError t a b v g (x,y+t*x)} := by
  ext x
  simp only [physicalReferenceEvent,ite_true,Set.mem_ofPred_eq]

theorem physicalReferenceEvent_line_one (y : ℝ) :
    {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 1} =
      {x | L^s ≤ P.physicalMainSquare t a b v g y x} := by
  ext x
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalReferenceEvent,show (1 : Fin 3) ≠ 0 by decide,ite_false,
    ite_true,Set.mem_ofPred_eq,physicalMainSquareOnPlane,hy]

theorem physicalReferenceEvent_line_two (y : ℝ) :
    {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 2} =
      {x | L^r ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} := by
  ext x
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalReferenceEvent,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false,Set.mem_ofPred_eq,hy]

/-- The three actual reference tails lose one unit of exponential rate.
There is no dependence on the number of packets or angular depth. -/
theorem eventually_physicalReferenceBad_tail (rate : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
      (A e s r y u W : ℝ), 0 < W →
      (volume.restrict (Ico u (u+W)))
        {x | L^e ≤ P.physicalAngularError t a b v g (x,y+t*x)} ≤
          ENNReal.ofReal (Real.exp (-(rate+1)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^s ≤ P.physicalMainSquare t a b v g y x} ≤
          ENNReal.ofReal (Real.exp (-(rate+1)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^r ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} ≤
          ENNReal.ofReal (Real.exp (-(rate+1)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t a b v g T L A e s r} ≤
          ENNReal.ofReal (Real.exp (-rate*L))*ENNReal.ofReal W := by
  filter_upwards [eventually_source_bad_event_tail 1 rate,eventually_ge_atTop (3:ℝ)]
    with L htail hL
  intro N κ Label Item _ _ P alt hAlt t a b v g T A e s r y u W _hW he hs hr
  let μ := volume.restrict (Ico u (u+W))
  have hlen : μ univ = ENNReal.ofReal W := by
    simp only [μ,Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  let event := fun i : Fin 3 => {x | (x,y+t*x) ∈
    P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i}
  have he' : μ (event 0) ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L))*μ univ := by
    rw [hlen]
    change μ {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 0} ≤ _
    rw [P.physicalReferenceEvent_line_zero alt hAlt t a b v g T L A e s r y]
    exact he
  have hs' : μ (event 1) ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L))*μ univ := by
    rw [hlen]
    change μ {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 1} ≤ _
    rw [P.physicalReferenceEvent_line_one alt hAlt t a b v g T L A e s r y]
    exact hs
  have hr' : μ (event 2) ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L))*μ univ := by
    rw [hlen]
    change μ {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 2} ≤ _
    rw [P.physicalReferenceEvent_line_two alt hAlt t a b v g T L A e s r y]
    exact hr
  have ht := htail (Fin 3) ℝ μ Finset.univ event
    (by simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,Real.rpow_one] using hL) (by
      intro i _
      fin_cases i
      · exact he'
      · exact hs'
      · exact hr')
  have hset : {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t a b v g T L A e s r} =
      ⋃ i ∈ (Finset.univ : Finset (Fin 3)),
        {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i} := by
    ext x
    simp only [physicalReferenceBad,mem_ofPred_eq,mem_iUnion,Finset.mem_univ,exists_prop,true_and]
  rwa [← hset,hlen] at ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
