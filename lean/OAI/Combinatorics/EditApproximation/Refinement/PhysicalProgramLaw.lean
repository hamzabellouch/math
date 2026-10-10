import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSelectionResampling
import OAI.Combinatorics.EditApproximation.Probability.FiniteResampling

namespace OAI

/-!
# The global finite product of actual selection streams

Online slots and whole-cell slots form a finite disjoint union. Each slot
contains its complete finite time array with the prescribed product law.
Mapping the flattened product produces
the actual online/group stream pair without independence hypotheses.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section GlobalLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau : ℚ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

abbrev PhysicalOnlineKey := Σ node : PhysicalInternalNode M J,
  Fin (stageRepresentatives source target U N P F A node.1).length

abbrev PhysicalGroupKey := Σ node : PhysicalInternalNode M J,
  Σ scale : Fin (dyadicScales N).length,
    Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length

abbrev PhysicalProgramKey := Sum (PhysicalOnlineKey source target U N P F A)
  (PhysicalGroupKey source target U N P F A thetaExponent)

abbrev PhysicalOnlineArray (key : PhysicalOnlineKey source target U N P F A) :=
  Fin R → Fin (optimizerTriangularMass
    (physicalProgramBandK source target U N P F A T thetaExponent H tau key.1 key.2))

abbrev PhysicalGroupArray (key : PhysicalGroupKey source target U N P F A thetaExponent) :=
  Fin R → ParentGroupDraw M (groupDyadicScales M ((dyadicScales N).get key.2.1) F).length
    (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
      (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h))

abbrev PhysicalProgramCoordinate (key : PhysicalProgramKey source target U N P F A thetaExponent) : Type :=
  match key with
  | .inl online => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau online
  | .inr group => PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q group

instance physicalProgramCoordinateFintype (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    Fintype (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalProgramCoordinate] <;> infer_instance

instance physicalProgramCoordinateMeasurableSpace
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    MeasurableSpace (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalProgramCoordinate] <;> infer_instance

instance physicalProgramCoordinateMeasurableSingleton
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    MeasurableSingletonClass
      (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalProgramCoordinate, physicalProgramCoordinateMeasurableSpace] <;> infer_instance

abbrev PhysicalProgramDraw := ∀ key : PhysicalProgramKey source target U N P F A thetaExponent,
  PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key

instance physicalProgramBandMass_nezero (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length) :
    NeZero (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative)) :=
  ⟨Nat.ne_of_gt (optimizerTriangularMass_positive _
    (physicalProgramBandK_positive source target U N P F A T thetaExponent H tau node representative))⟩


noncomputable def physicalProgramCoordinateLaw
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    Measure (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) :=
  match key with
  | .inl online =>
    let : NeZero (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau online.1 online.2)) :=
      ⟨Nat.ne_of_gt (optimizerTriangularMass_positive _
        (physicalProgramBandK_positive source target U N P F A T thetaExponent H tau online.1 online.2))⟩
    Measure.pi fun _ : Fin R => (PMF.uniformOfFintype (Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau online.1 online.2)))).toMeasure
  | .inr group => Measure.pi fun _ : Fin R => groupSharedDrawLaw (M := M)
      (fun h => groupSampleCount M Q ((dyadicScales N).get group.2.1)
        (groupDyadicScaleAt M ((dyadicScales N).get group.2.1) F h))

instance physicalProgramCoordinateLaw_probability
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    IsProbabilityMeasure
      (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [physicalProgramCoordinateLaw, physicalProgramCoordinateMeasurableSpace,
    PhysicalProgramCoordinate] <;> infer_instance

noncomputable def physicalProgramDrawLaw :
    Measure (PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau) :=
  Measure.pi (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau)

instance physicalProgramDrawLaw_probability :
    IsProbabilityMeasure (physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau) := by
  unfold physicalProgramDrawLaw
  infer_instance

def physicalProgramDrawStreams
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau) :
    PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R ×
      PhysicalGroupStreams source target U N P F A thetaExponent Q R :=
  (fun node representative => draw (.inl ⟨node, representative⟩),
    fun node scale cell => draw (.inr ⟨node, scale, cell⟩))

noncomputable def physicalProgramStreamLaw :
    Measure (PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R ×
      PhysicalGroupStreams source target U N P F A thetaExponent Q R) :=
  (physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau).map
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau)

instance physicalProgramStreamLaw_probability :
    IsProbabilityMeasure (physicalProgramStreamLaw (R := R) source target U N P F A T thetaExponent H Q tau) := by
  unfold physicalProgramStreamLaw
  infer_instance

/-- The transported law is the law of the complete literal stream pair. -/
theorem physicalProgramStreamLaw_integral
    (payoff : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R ×
      PhysicalGroupStreams source target U N P F A thetaExponent Q R → ℝ) :
    (∫ streams, payoff streams ∂physicalProgramStreamLaw (R := R) source target U N P F A T thetaExponent H Q tau) =
      ∫ draw, payoff (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw)
        ∂physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau := by
  exact integral_map_of_stronglyMeasurable (measurable_of_finite _)
    (measurable_of_finite payoff).stronglyMeasurable

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- Refresh exactly one online band and one shared whole-cell coordinate. -/
noncomputable def physicalProgramRefresh
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent)
    (fresh : PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau online ×
      PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q group) :
    PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau := by
  classical
  exact Function.update (Function.update draw (.inl online) fresh.1) (.inr group) fresh.2

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_online
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).1
        online.1 online.2 = fresh.1 := by
  classical
  rcases online with ⟨node, representative⟩
  rcases group with ⟨groupNode, scale, cell⟩
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne (show (Sum.inl ⟨node, representative⟩ :
    PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inr ⟨groupNode, scale, cell⟩ from Sum.inl_ne_inr)]
  exact Function.update_self _ _ _

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_group
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).2
        group.1 group.2.1 group.2.2 = fresh.2 := by
  classical
  rcases group with ⟨node, scale, cell⟩
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  exact Function.update_self _ _ _

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_online_other
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalInternalNode M J) (hne : label ≠ online.1) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).1 label =
      (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw).1 label := by
  classical
  funext representative
  have hkey : (Sum.inl ⟨label, representative⟩ : PhysicalProgramKey source target U N P F A thetaExponent) ≠
      Sum.inl online := by
    intro heq
    exact hne (congrArg Sigma.fst (Sum.inl.inj heq))
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne (show (Sum.inl ⟨label, representative⟩ :
    PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inr group from Sum.inl_ne_inr),
    Function.update_of_ne hkey]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_group_other
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalInternalNode M J) (hne : label ≠ group.1) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).2 label =
      (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw).2 label := by
  classical
  funext scale cell
  have hkey : (Sum.inr ⟨label, scale, cell⟩ : PhysicalProgramKey source target U N P F A thetaExponent) ≠
      Sum.inr group := by
    intro heq
    exact hne (congrArg Sigma.fst (Sum.inr.inj heq))
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne hkey,
    Function.update_of_ne (show (Sum.inr ⟨label, scale, cell⟩ :
      PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inl online from Sum.inr_ne_inl)]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- The actual complete selection program evaluated on its global array. -/
def physicalProgramDrawSelections [NeZero R] (η κ : ℚ)
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau) :
    PhysicalSelections M J source.length target.length P (stageRepresentatives source target U N P F A) :=
  let streams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw
  physicalProgramSelections source target U N P F A T thetaExponent H Q tau η κ streams.1 streams.2

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- Refreshing a parent's chosen band/cell coordinates leaves every
strictly deeper raw selection function unchanged. -/
theorem physicalProgramDrawSelections_refresh_deeper [NeZero R] (η κ : ℚ)
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalNode M J)
    (honline : online.1.1.1.val < label.1.val) (hgroup : group.1.1.1.val < label.1.val) :
    (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).groups label =
        (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ draw).groups label ∧
    (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).online label =
        (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ draw).online label := by
  have hneOnline (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ online.1 := by
    intro heq
    have hdepth := congrArg (fun node : PhysicalInternalNode M J => node.1.1.val) heq
    change label.1.val = online.1.1.1.val at hdepth
    omega
  have hneGroup (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ group.1 := by
    intro heq
    have hdepth := congrArg (fun node : PhysicalInternalNode M J => node.1.1.val) heq
    change label.1.val = group.1.1.1.val at hdepth
    omega
  let oldStreams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw
  let nextStreams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)
  constructor
  · exact physicalProgramSelections_groups_congr_at source target U N P F A T thetaExponent H Q tau η κ
      oldStreams.1 nextStreams.2 oldStreams.2 label (fun hbelow => physicalProgramRefresh_group_other source target U N P F A T thetaExponent H Q tau
        draw online group fresh ⟨label, hbelow⟩ (hneGroup hbelow))
  · exact physicalProgramSelections_online_congr_at source target U N P F A T thetaExponent H Q tau η κ
      nextStreams.1 oldStreams.1 oldStreams.2 label (fun hbelow => physicalProgramRefresh_online_other source target U N P F A T thetaExponent H Q tau
        draw online group fresh ⟨label, hbelow⟩ (hneOnline hbelow))


/-- Exact finite-product disintegration into an original global array and
fresh local parent arrays. The unused old values are integrated out. -/
theorem physicalProgramDrawLaw_refresh_integral
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent)
    (payoff : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau → ℝ) :
    (∫ draw, ∫ fresh,
      payoff (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)
      ∂(physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (.inl online)).prod
        (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (.inr group))
      ∂physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau) =
      ∫ draw, payoff draw ∂physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau := by
  classical
  exact finite_pi_integral_update_pair
    (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau)
    (.inl online) (.inr group) payoff


end GlobalLaw

end EditApproximation

end OAI
