import OAI.Combinatorics.Progressions.Estimates.DiagramNativeExternalNetMonotone

namespace OAI

section

universe u uO uR uIO uX uσ

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem DiagramNativeExternalNetConclusion.exists_physical_niltest_family (s t k : ℕ)
{H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) (p cost : ℝ) (q : ℕ)
    (h : DiagramNativeExternalNetConclusion.{u, uO, uR, uIO} s t k E D Q F φ ψ₀ ψ p cost q) :
      let Z₀ := pi F
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := realification_moduleTopology_t2 Z₀.basis
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∃ Z : RationalFilteredNilmanifold (∀ i, L i) t (Fintype.card (Σ i, Fin (d i))),
          Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
          Z.GeometryComplexityLE cost ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp cost ∧
          letI := Q'.metricSpace
          letI := Z.metricSpace
          let diagram := fun x : E.RealGroup =>
            ((QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x) : Q'.Space),
              (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Z.filtration.lowerCentralSeries_eq_bot) (liePiMap ψ) x) : Z.Space))
          ∀ {O : Type uO} {R : Type uR} {IO : Type uIO} [Fintype R] [Fintype IO]
            (S : O → D.Space → ℂ) (oc : IO → O) (r : R → D.RealGroup)
            (ℓ B : ℝ≥0) {ε : ℝ},
            (ℓ : ℝ) ≤ Real.exp p → 1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ k) →
            0 < ε → 1 / ε ≤ Real.exp p →
            (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
            (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
            (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
            (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
            (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid q) →
            let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
              (D.basis.baseChange ℝ) B
            let frozen := fun o (a : A) j (x : E.RealGroup) =>
              S o (QuotientGroup.mk (a.val * realificationMap
                (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r j))
            ∃ n : ℕ, (n : ℝ) ≤ Real.exp cost ∧
              ∃ centers : Fin n → Q'.Space → ℂ,
                (∀ i, LipschitzWith K (centers i)) ∧
                (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
                (∀ i y, ‖centers i y‖ ≤ 1) ∧
                (∀ o a j x, positiveImageSlice diagram K (frozen o a j)
                  (diagram x).2 (diagram x).1 = frozen o a j x) ∧
                (∀ o a j z, ∃ i, ∀ y,
                  ‖positiveImageSlice diagram K (frozen o a j) z y - centers i y‖ ≤ ε) ∧
                ∀ {X : Type uX} [Nonempty X]
                  (observableAt : X → O) (leftAt : X → A) (rightAt : X → R)
                  (externalAt : X → Z.Space),
                  let physicalFunction := fun x y => positiveImageSlice diagram K
                    (frozen (observableAt x) (leftAt x) (rightAt x)) (externalAt x) y
                  (∀ x, LipschitzWith K (physicalFunction x)) ∧
                  (∀ x y, (physicalFunction x y).im = 0 ∧
                    0 ≤ (physicalFunction x y).re ∧ (physicalFunction x y).re ≤ 1) ∧
                  (∀ x y, ‖physicalFunction x y‖ ≤ 1) ∧
                  (∀ x, ∃ i, ∀ y, ‖physicalFunction x y - centers i y‖ ≤ ε) ∧
                  (∀ x (source : E.RealGroup), externalAt x = (diagram source).2 →
                    physicalFunction x (diagram source).1 =
                      frozen (observableAt x) (leftAt x) (rightAt x) source) ∧
                  ∀ {σ : Type uσ} (w : σ → ℕ),
                    ∃ (tests : X → Q'.Niltest w) (centerTests : Fin n → Q'.Niltest w),
                      (∀ x, (tests x).orbit = 1 ∧ (tests x).observable = physicalFunction x ∧
                        (tests x).normBound = 1 ∧ (tests x).lipBound = K ∧
                        (tests x).UnitIntervalValued ∧ (tests x).ComplexityLE (cost + 3)) ∧
                      (∀ i, (centerTests i).orbit = 1 ∧ (centerTests i).observable = centers i ∧
                        (centerTests i).normBound = 1 ∧ (centerTests i).lipBound = K ∧
                        (centerTests i).UnitIntervalValued ∧ (centerTests i).ComplexityLE (cost + 3)) ∧
                      (∀ x, ∃ i, ∀ y,
                        ‖(tests x).observable y - (centerTests i).observable y‖ ≤ ε) ∧
                      ∀ x (source : E.RealGroup), externalAt x = (diagram source).2 →
                        (tests x).observable (diagram source).1 =
                          frozen (observableAt x) (leftAt x) (rightAt x) source := by
  let Z₀ := pi F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom,
    K, hK, hnet⟩ :=
    DiagramNativeExternalNetConclusion.exists_physical_family s t k E D Q F φ ψ₀ ψ p cost q h
  refine ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom, K, hK, ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  intro diagram O J IO _ _ S oc r ℓ Bbox ε hℓ hB hBbound hε hεinv hIO hJ hS hpositive hO hr
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover, hphysical⟩ :=
    hnet (O := O) (R := J) (IO := IO) S oc r ℓ Bbox hℓ hB hBbound hε hεinv hIO hJ
      hS hpositive hO hr
  refine ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover, ?_⟩
  intro X _ observableAt leftAt rightAt externalAt physicalFunction
  obtain ⟨hfLip, hfunit, hfcap, hfnet, hrecon⟩ :=
    hphysical observableAt leftAt rightAt externalAt
  refine ⟨hfLip, hfunit, hfcap, hfnet, hrecon, ?_⟩
  intro σ w
  have hcost : 0 ≤ cost := (Nat.cast_nonneg d₀).trans hQgeom.1
  let tests : X → Q'.Niltest w := fun x =>
    Q'.externalNetNiltest (physicalFunction x) K (hfcap x) (hfLip x) 1
  let centerTests : Fin n → Q'.Niltest w := fun i =>
    Q'.externalNetNiltest (centers i) K (hcap i) (hLip i) 1
  refine ⟨tests, centerTests, ?_, ?_, hfnet, hrecon⟩
  · intro x
    exact ⟨rfl, rfl, rfl, rfl, hfunit x,
      Q'.externalNetNiltest_complexity (physicalFunction x) K (hfcap x) (hfLip x) 1
        hcost hQgeom hK⟩
  · intro i
    exact ⟨rfl, rfl, rfl, rfl, hunit i,
      Q'.externalNetNiltest_complexity (centers i) K (hcap i) (hLip i) 1
        hcost hQgeom hK⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
