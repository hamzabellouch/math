import OAI.Combinatorics.Progressions.Dynamics.AllocatedCandidateBudgetedTreeTerminal

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_forward_tree_terminal_of_stage_data
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (aControl aLocal : ℕ)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (pControl : ℕ → ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x) s pTree)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hphaseExponent : ∀ r < s, allocatedCandidateTerminalPhaseConstant s m aControl r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hpControl : ∀ r ≤ s, 0 ≤ pControl r)
    (hκControl : ∀ r ≤ s, (Fintype.card κ : ℝ) ≤ pControl r)
    (hTagsControl : ∀ r ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl r)
    (hHbrExp : ∀ r ≤ s, (Hbr : ℝ) ≤ Real.exp (pControl r))
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hden : ∀ r ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) *
      preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤ Real.exp (pControl r))
    (hcost : ∀ r ≤ s, (Fintype.card η : ℝ) * Bbound *
      Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤
        Real.exp ((pControl r + 2) ^ aControl))
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ) (P := P) (keep := keep) (hkeep := hkeep)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r aLocal
        (preparedFiniteForwardCumulative scheduleExponent countConstants r x)
        ((pControl r + allocatedCandidateTerminalControlConstant s m aControl) ^
          allocatedCandidateTerminalControlConstant s m aControl)
        (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
          preparedFiniteForwardWork scheduleExponent countConstants r x)
        Rrank (allocatedCandidateTerminalPhaseConstant s m aControl r))) :
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        ((pControl s + allocatedCandidateTerminalControlConstant s m aControl) ^
          allocatedCandidateTerminalControlConstant s m aControl) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  apply P.exists_budgeted_tree_terminal_of_stage_data keep hkeep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection aControl aLocal Bphase Bbound pTree Rrank Hbr qS
    (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x)
    (fun r => preparedFiniteForwardCumulative scheduleExponent countConstants r x)
    pControl
    (fun r => preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent countConstants r x)
    T hHbr hqS hpControl
    (fun r _ => (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.1)
    ?_ ?_ ?_ ?_ hκControl hTagsControl hHbrExp hstructure hden hcost hentry hgrid hdata
  · intro r hr
    exact preparedFiniteForwardCumulative_monotone scheduleExponent countConstants hx (Nat.le_succ r)
  · intro r hr
    exact preparedFiniteForwardCap_le_cumulative_succ scheduleExponent countConstants r hx
  · intro r hr j hj
    exact preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hj
  · intro r hr
    exact preparedFiniteForward_phase_cap scheduleExponent countConstants r
      (allocatedCandidateTerminalPhaseConstant s m aControl r) hx hgain hstage (hphaseExponent r hr)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_forward_controlled_tree_terminal
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (aLocal : ℕ)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x) s pTree)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hphaseExponent : ∀ r < s, allocatedCandidateTerminalPhaseConstant s m 1 r ≤ scheduleExponent)
    (hSchedule : 2 ≤ scheduleExponent) (hsSchedule : s + 3 ≤ scheduleExponent)
    (hControlSchedule : 4 * allocatedCandidateTerminalControlConstant s m 1 ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ) (P := P) (keep := keep) (hkeep := hkeep)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r aLocal
        (preparedFiniteForwardCumulative scheduleExponent countConstants r x)
        ((allocatedCandidateForwardControlInput s (Fintype.card η)
          (preparedFiniteForwardParameter scheduleExponent countConstants r x) +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
          preparedFiniteForwardWork scheduleExponent countConstants r x)
        Rrank (allocatedCandidateTerminalPhaseConstant s m 1 r))) :
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  let pControl : ℕ → ℝ := fun r => allocatedCandidateForwardControlInput s (Fintype.card η)
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  have hinput (r : ℕ) := allocatedCandidateForwardControlInput_bounds s (Fintype.card η)
    (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
  have hbase (r : ℕ) : x ≤ pControl r :=
    (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx).trans (hinput r).2.1
  have hwork (r : ℕ) :
      (pControl r + allocatedCandidateTerminalControlConstant s m 1) ^
        allocatedCandidateTerminalControlConstant s m 1 ≤
      preparedFiniteForwardWork scheduleExponent countConstants r x := by
    rw [preparedFiniteForwardWork_eq]
    exact allocatedCandidateForwardControlInput_power_bound s (Fintype.card η)
      (allocatedCandidateTerminalControlConstant s m 1) scheduleExponent
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
      (hηBase.trans (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx))
      hSchedule hsSchedule hControlSchedule
  have hden : ∀ r ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) *
      preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤ Real.exp (pControl r) := by
    intro r hr
    exact allocatedCandidateForwardControlInput_denominator_bound s (Fintype.card η) qS
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
      (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2 hqSBase
  have hcost : ∀ r ≤ s, (Fintype.card η : ℝ) * Bbound *
      Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤
        Real.exp ((pControl r + 2) ^ (1 : ℕ)) := by
    intro r hr
    simpa only [pow_one] using allocatedCandidateForwardControlInput_cost_bound s (Fintype.card η)
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
      (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2 hηBase hBboundBase
  obtain ⟨history, hmem, hcontrol, hcertificate, hterminal⟩ :=
    P.exists_forward_tree_terminal_of_stage_data keep hkeep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection 1 aLocal Bphase Bbound pTree Rrank Hbr qS scheduleExponent
    x gainLog stageLog pControl T hx hgain hstage hphaseExponent hHbr hqS
    (fun r _ => (hinput r).1)
    (fun r _ => hκBase.trans (hbase r))
    (fun r _ => hTagsBase.trans (hbase r))
    (fun r _ => hHbrBase.trans (Real.exp_le_exp.mpr (hbase r))) hstructure
    hden hcost hentry hgrid hdata
  exact ⟨history, hmem, FullChartControlledFactors.mono Fmark bF ν hF J poly N history.outer.1 history.outer.2 hcontrol (hwork s), hcertificate, hterminal⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
