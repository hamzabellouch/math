import OAI.Combinatorics.Progressions.Estimates.ComparableUnconditionedScalarTransfer
import OAI.Combinatorics.Progressions.Geometry.CanonicalScalarFullBoxDiscrepancy

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical

theorem canonicalScalarFamily_apply {I J Λ : Type*}
    [Fintype I] [Fintype J] [DecidableEq J] [Fintype Λ] [Nonempty Λ]
    (N margin : I → ℕ) (width : Option J × I → ℝ) (parameters : J → ℕ)
    (g : Λ → (I → ℤ) → ℂ) (epsilon target budget : ℝ) (level : Λ → ℝ)
    (hsingle : ∀ c : Λ,
      ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
        (hparam : ∀ j : J, (0 : ℤ) < parameters j),
      ∀ h : (I → ℤ) → ℂ,
        (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
        ResidueSliceUpperComparison h (g c) 0 N budget (level c) (Real.exp (-budget)) →
        (selectedJointReference (trimmedIntegerBox N margin)
          (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0}
          width hwidth hZ).eventProbability (fun z => Real.exp (-target) <
            (integerBoxUniformWeights (fun _ : J => (0 : ℤ))
              (fun j => (parameters j : ℤ)) hparam).mean
              (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (h x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)) -
                (1 + epsilon) * level c *
                  realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (g c x).re)
                    (smoothAffineSample (fun j => (t j).val)
                      (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)))) ≤ Real.exp (-target)) :
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : J, (0 : ℤ) < parameters j),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ h : Λ → (I → ℤ) → ℂ,
      (∀ c z, z ∈ translatedIntegerBox (0 : I → ℤ) N → 0 ≤ (h c z).re ∧ (h c z).re ≤ 1) →
    ∀ productive : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card Λ : ℝ) * Real.exp (-target) < outer.eventProbability productive →
      (∀ z, productive z → ∃ c, Real.exp (-target) <
        rectangularScalarDiscrepancy 0 N (h c) (g c) epsilon (level c) 1
          0 0 (fun j => (parameters j : ℤ)) hparam
          (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)) →
    ∃ (c : Λ) (lo : I → ℤ) (H : I → ℕ) (M : ℕ) (a : I → ℤ),
      0 < M ∧ PhysicalSubbox 0 N lo H ∧
      ResidueSliceLogCostLE N lo H M a budget ∧
      Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a) ∧
      (∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i)) ∧
      Real.exp (-budget) < (physicalResidueMean (h c) lo H M a).re -
        level c * (physicalResidueMean (g c) lo H M a).re := by
  obtain ⟨hwidth, hmargin, hZ, hparam, _⟩ := hsingle (Classical.arbitrary Λ)
  refine ⟨hwidth, hmargin, hZ, hparam, ?_⟩
  intro outer h hh productive hmass hproductive
  apply exists_residue_slice_of_rectangular_scalar_family outer
    (fun z i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2) 0 N
    h g (fun _ => epsilon) level (fun _ => budget)
    (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ j => (parameters j : ℤ))
    (fun _ => hparam) target ?_ productive hmass hproductive
  intro c hupper
  obtain ⟨_, _, _, _, htail⟩ := hsingle c
  exact canonicalScalarFullBox_transfer outer
    (fun z i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2) 0 N
    (h c) (g c) epsilon (level c) parameters hparam target (htail (h c) (hh c) hupper)

theorem canonicalScalarFamily_apply_with {I J Λ : Type*}
    [Fintype I] [Fintype J] [DecidableEq J] [Fintype Λ] [Nonempty Λ]
    (N margin : I → ℕ) (width : Option J × I → ℝ) (parameters : J → ℕ)
    (g : Λ → (I → ℤ) → ℂ) (epsilon target budget : ℝ) (level : Λ → ℝ) (P : Prop)
    (hsingle : ∀ c : Λ,
      ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
        (hparam : ∀ j : J, (0 : ℤ) < parameters j),
      P ∧ ∀ h : (I → ℤ) → ℂ,
        (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
        ResidueSliceUpperComparison h (g c) 0 N budget (level c) (Real.exp (-budget)) →
        (selectedJointReference (trimmedIntegerBox N margin)
          (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0}
          width hwidth hZ).eventProbability (fun z => Real.exp (-target) <
            (integerBoxUniformWeights (fun _ : J => (0 : ℤ))
              (fun j => (parameters j : ℤ)) hparam).mean
              (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (h x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)) -
                (1 + epsilon) * level c *
                  realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (g c x).re)
                    (smoothAffineSample (fun j => (t j).val)
                      (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)))) ≤ Real.exp (-target)) :
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : J, (0 : ℤ) < parameters j),
    P ∧
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ h : Λ → (I → ℤ) → ℂ,
      (∀ c z, z ∈ translatedIntegerBox (0 : I → ℤ) N → 0 ≤ (h c z).re ∧ (h c z).re ≤ 1) →
    ∀ productive : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card Λ : ℝ) * Real.exp (-target) < outer.eventProbability productive →
      (∀ z, productive z → ∃ c, Real.exp (-target) <
        rectangularScalarDiscrepancy 0 N (h c) (g c) epsilon (level c) 1
          0 0 (fun j => (parameters j : ℤ)) hparam
          (fun i => jointIntegerFrame (z.1.val, z.2.val) i.1 i.2)) →
    ∃ (c : Λ) (lo : I → ℤ) (H : I → ℕ) (M : ℕ) (a : I → ℤ),
      0 < M ∧ PhysicalSubbox 0 N lo H ∧
      ResidueSliceLogCostLE N lo H M a budget ∧
      Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a) ∧
      (∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i)) ∧
      Real.exp (-budget) < (physicalResidueMean (h c) lo H M a).re -
        level c * (physicalResidueMean (g c) lo H M a).re := by
  obtain ⟨_, _, _, _, hP, _⟩ := hsingle (Classical.arbitrary Λ)
  obtain ⟨hwidth, hmargin, hZ, hparam, hfamily⟩ :=
    canonicalScalarFamily_apply N margin width parameters g epsilon target budget level (by
      intro c
      obtain ⟨hw, hm, hz, hp, _, htail⟩ := hsingle c
      exact ⟨hw, hm, hz, hp, htail⟩)
  exact ⟨hwidth, hmargin, hZ, hparam, hP, hfamily⟩

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w

noncomputable local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def CanonicalUnconditionedScalarFamilyStatement (s d : ℕ) (epsilon : ℝ) : Prop :=
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
    let target := 8 * ((d : ℝ) + 1) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ 2 * L) →
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
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ h : Λ → (I → ℤ) → ℂ,
      (∀ c z, z ∈ translatedIntegerBox (0 : I → ℤ) N →
        0 ≤ (h c z).re ∧ (h c z).re ≤ 1) →
    ∀ productive : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card Λ : ℝ) * Real.exp (-target) < outer.eventProbability productive →
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

theorem exists_canonical_unconditioned_scalar_family (s d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    CanonicalUnconditionedScalarFamilyStatement.{u,v,w} s d epsilon := by
  unfold CanonicalUnconditionedScalarFamilyStatement
  obtain ⟨A, C, F, hA, hC, hF, htransfer⟩ :=
    exists_canonical_unconditioned_scalar_transfer.{u,v} s d hd hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V Λ _ _ _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv
    hlevel hlevel2 g hg target budget L parameters hlo hhi N hN hunit τ Wsite width margin
  apply canonicalScalarFamily_apply_with N margin width parameters
    (fun c => (g c).eval) epsilon target budget level (budget ≤ (p + F) ^ F)
  intro c
  exact htransfer nilmanifold hp hn hσ hσ1 hσinv (hlevel c) (hlevel2 c)
    (g c) (hg c) parameters hlo hhi N hN (hunit c)

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w

noncomputable local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def ComparableUnconditionedScalarProductiveFamilyStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
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
      (Fintype.card Λ : ℝ) * Real.exp (-target) < outer.eventProbability productive →
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

theorem exists_comparable_unconditioned_scalar_productive_family (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarProductiveFamilyStatement.{u,v,w} s d r epsilon := by
  unfold ComparableUnconditionedScalarProductiveFamilyStatement
  obtain ⟨A, C, F, hA, hC, hF, htransfer⟩ :=
    exists_comparable_unconditioned_scalar_productive_transfer.{u,v} s d r hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V Λ _ _ _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv
    hlevel hlevel2 g hg target budget L parameters _ hlo hhi N hN hunit τ Wsite width margin
  have hfamily := canonicalScalarFamily_apply_with N margin width parameters
    (fun c => (g c).eval) epsilon target budget level
    (budget ≤ (p + F) ^ F ∧
      ∀ i, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound parameters) τ
        (unconditionedCollisionWidth parameters σ) ≤ (N i : ℝ))
  have hsingle := fun c => htransfer (I := I) (V := V) nilmanifold hp hn hσ hσ1 hσinv
    (hlevel c) (hlevel2 c) (g c) (hg c) parameters hlo hhi N hN (hunit c)
  obtain ⟨hwidth, hmargin, hZ, hparam, hnumeric, hselect⟩ := hfamily (fun c => by
    obtain ⟨hw, hm, hz, hpar, hbudget, hcutoff, htail⟩ := hsingle c
    exact ⟨hw, hm, hz, hpar, ⟨hbudget, hcutoff⟩, htail⟩)
  exact ⟨hwidth, hmargin, hZ, hparam, hnumeric.1, hnumeric.2, hselect⟩

theorem exists_dyadic_unconditioned_scalar_productive_family (s d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarProductiveFamilyStatement.{u,v,w} s d (2 ^ (d + 1)) epsilon := by
  apply exists_comparable_unconditioned_scalar_productive_family s d (2 ^ (d + 1)) hd _ hepsilon hepsilon1
  simpa only [pow_one] using
    (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ d + 1))

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w

noncomputable local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def ComparableUnconditionedScalarFamilyStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
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
    ∀ (parameters : Fin d → ℕ),
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
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ h : Λ → (I → ℤ) → ℂ,
      (∀ c z, z ∈ translatedIntegerBox (0 : I → ℤ) N →
        0 ≤ (h c z).re ∧ (h c z).re ≤ 1) →
    ∀ productive : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card Λ : ℝ) * Real.exp (-target) < outer.eventProbability productive →
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

theorem exists_comparable_unconditioned_scalar_family (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarFamilyStatement.{u,v,w} s d r epsilon := by
  unfold ComparableUnconditionedScalarFamilyStatement
  obtain ⟨A, C, F, hA, hC, hF, htransfer⟩ :=
    exists_comparable_unconditioned_scalar_transfer.{u,v} s d r hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V Λ _ _ _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv
    hlevel hlevel2 g hg target budget L parameters hlo hhi N hN hunit τ Wsite width margin
  apply canonicalScalarFamily_apply_with N margin width parameters
    (fun c => (g c).eval) epsilon target budget level (budget ≤ (p + F) ^ F)
  intro c
  exact htransfer nilmanifold hp hn hσ hσ1 hσinv (hlevel c) (hlevel2 c)
    (g c) (hg c) parameters hlo hhi N hN (hunit c)

theorem exists_dyadic_unconditioned_scalar_family (s d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarFamilyStatement.{u,v,w} s d (2 ^ (d + 1)) epsilon := by
  apply exists_comparable_unconditioned_scalar_family s d (2 ^ (d + 1)) hd _ hepsilon hepsilon1
  simpa only [pow_one] using
    (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ d + 1))

end Erdos3

end

end OAI
