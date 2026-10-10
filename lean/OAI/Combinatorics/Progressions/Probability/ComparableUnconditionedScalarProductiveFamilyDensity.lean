import OAI.Combinatorics.Progressions.Estimates.ComparableUnconditionedScalarFamily

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w

noncomputable local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def ComparableUnconditionedScalarProductiveFamilyDensityStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} {Λ : Type w} [Fintype I] [Fintype Λ] [Nonempty Λ]
      [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ : ℝ} (level : Λ → ℝ), 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p →
      (∀ c, Real.exp (-p) ≤ level c) → (∀ c, level c ≤ 2) →
    ∀ g : Λ → nilmanifold.Niltest (fun _ : I => 1), (∀ c, (g c).ComplexityLE p) →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ) [∀ j, NeZero (parameters j)],
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ c z, z ∈ translatedIntegerBox (0 : I → ℤ) N →
        ((g c).eval z).im = 0 ∧ 0 ≤ ((g c).eval z).re ∧ ((g c).eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < parameters j),
    budget ≤ (p + F) ^ F ∧
    (∀ i, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound parameters) τ
      (unconditionedCollisionWidth parameters σ) ≤ (N i : ℝ)) ∧
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ h : Λ → (I → ℤ) → ℂ,
      (∀ c z, z ∈ translatedIntegerBox (0 : I → ℤ) N →
        0 ≤ (h c z).re ∧ (h c z).re ≤ 1) →
    ∀ productive : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card Λ : ℝ) ≤ Real.exp p →
      Real.exp (-p) ≤ outer.eventProbability productive →
      (∀ z, productive z → ∃ c, Real.exp (-target) <
        rectangularScalarDiscrepancy 0 N (h c) (g c).eval epsilon (level c) 1
          0 0 (fun j => (parameters j : ℤ)) hparam
          (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)) →
    ∃ (c : Λ) (lo : I → ℤ) (H : I → ℕ) (M : ℕ) (a : I → ℤ),
      0 < M ∧ PhysicalSubbox 0 N lo H ∧
      ResidueSliceLogCostLE N lo H M a budget ∧
      Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a) ∧
      (∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i)) ∧
      Real.exp (-budget) < (physicalResidueMean (h c) lo H M a).re -
        level c * (physicalResidueMean (g c).eval lo H M a).re

theorem exists_comparable_unconditioned_scalar_productive_family_density
    (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarProductiveFamilyDensityStatement.{u,v,w} s d r epsilon := by
  unfold ComparableUnconditionedScalarProductiveFamilyDensityStatement
  obtain ⟨A, C, F, hA, hC, hF, hfamily⟩ :=
    exists_comparable_unconditioned_scalar_productive_family.{u,v,w} s d r hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V Λ _ _ _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv
    hlevel hlevel2 g hg target budget L parameters _ hlo hhi N hN hunit τ Wsite width margin
  obtain ⟨hwidth, hmargin, hZ, hparam, hbudget, hcutoff, hselect⟩ :=
    hfamily (I := I) (V := V) (Λ := Λ) nilmanifold level hp hn hσ hσ1 hσinv
      hlevel hlevel2 g hg parameters hlo hhi N hN hunit
  refine ⟨hwidth, hmargin, hZ, hparam, hbudget, hcutoff, ?_⟩
  intro outer h hh productive hcard hmass hproductive
  exact hselect h hh productive
    (canonicalScalarFamilyMass (r * d) (Fintype.card Λ) (by linarith) hcard hmass)
    hproductive

theorem exists_dyadic_unconditioned_scalar_productive_family_density (s d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarProductiveFamilyDensityStatement.{u,v,w} s d (2 ^ (d + 1)) epsilon := by
  apply exists_comparable_unconditioned_scalar_productive_family_density s d (2 ^ (d + 1)) hd _
    hepsilon hepsilon1
  simpa only [pow_one] using
    (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ d + 1))

end Erdos3

end

end OAI
