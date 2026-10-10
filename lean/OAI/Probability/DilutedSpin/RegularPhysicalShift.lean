import OAI.Probability.DilutedSpin.JointGridSelection
import OAI.Probability.DilutedSpin.RootShiftIntegrability
import OAI.Probability.DilutedSpin.ScheduledRootMultileaf

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
noncomputable local instance (β : Type) : DecidableEq β := Classical.decEq β

def childBranchCoordinates {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) (v : (C j).Vertex) :
    {x : Option (ReducedTopology.node k hk C).Vertex // x≠some none} :=
  ⟨some (some ⟨j,v⟩),by simp⟩

lemma childBranchCoordinates_injective {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) : Function.Injective (childBranchCoordinates (hk := hk) (C := C) j) := by
  intro x y h
  have hh := congrArg Subtype.val h
  simpa only [childBranchCoordinates,Option.some.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh

lemma regular_child_branches {L : ℕ} [NeZero L] {η : ℝ}
    {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) {Q : Option (ReducedTopology.node k hk C).Vertex → Fin L}
    (hQ : DepthAverage.Regular η Q) :
    DepthAverage.Regular η (fun v => Q ((childBranchCoordinates (hk := hk) (C := C) j v).val)) := by
  constructor
  · intro v
    exact hQ.1 _
  · intro v w hvw
    exact hQ.2 _ _ (fun h => hvw (childBranchCoordinates_injective j (Subtype.ext h)))

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance (β : Type) : DecidableEq β := Classical.decEq β
variable {p : ℕ}
attribute [local irreducible] projectionShiftError

/-- The uniform h_N bound on the FULL actual regular/admissible parent domain,
with the literal physical root and exactly its proper-child embeddings. This
has no geometry or ordinary-integrability hypothesis left to discharge. -/
theorem regular_physical_shift_average (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (η : ℝ) (hlarge : 1<η*(L+1:ℕ)) :
    let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)
    let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
      (I := Labels L (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (fun Q => ∫ z, projectionShiftError (some none) C
        (fun j => childBranchCoordinates (hk := hk) j) (K z) (f z) Q ∂μ) ≤
      Real.sqrt (8*((k:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(k:ℝ)^2)/(L+1:ℕ)) := by
  dsimp only
  have hh := physical_root_shift_average (some none) C
    (fun j => childBranchCoordinates (hk := hk) j)
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
    (measurable_physicalBase M θB hB N)
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (readVector_bound _) (fun j => childBranchCoordinates_injective j)
    η hlarge (regularShapeDomain (.node k hk C) (L+1) η) (by
      intro Q hQ j
      exact ⟨hQ.2.2.2 j, regular_child_branches j hQ.1⟩)
  simpa only [Fintype.card_fin] using hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
