import OAI.Combinatorics.Progressions.Dynamics.UnconditionedCollisionWidthLogBudget
import OAI.Combinatorics.Progressions.Estimates.CanonicalUnconditionedScalarTransfer

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem comparableScalarProductivityCutoff_le_exp
    {X : Type*} [Fintype X] (d r : ℕ) (_hd : 2 ≤ d) (hr : 2 ≤ r)
    {P0 budget σ : ℝ} (hP0 : 0 ≤ P0) (hbudget : 0 ≤ budget)
    (hdP0 : (d : ℝ) ≤ Real.exp P0) (hrP0 : (r : ℝ) ≤ Real.exp P0)
    (hσ : 0 < σ) (hσP0 : σ⁻¹ ≤ Real.exp P0)
    (hτP0 : (unconditionedSpatialTrimFraction (Fintype.card X) σ)⁻¹ ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (parameters : Fin d → ℕ) [∀ j, NeZero (parameters j)]
    (hhi : ∀ j, (parameters j : ℝ) ≤ (r : ℝ) * Real.exp budget) :
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound parameters)
      (unconditionedSpatialTrimFraction (Fintype.card X) σ)
      (unconditionedCollisionWidth parameters σ) ≤
      Real.exp ((((r*d : ℕ) : ℝ)+4) * (budget+P0+20)) := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := unconditionedResidueSiteBound parameters
  let Q := budget + 2*P0
  let R := 2*(d : ℝ)*(budget+P0)+P0+8
  have hτ : 0 < τ := by dsimp [τ, unconditionedSpatialTrimFraction]; positivity
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hparam (j) : (parameters j : ℝ) ≤ Real.exp (budget+P0) := by
    calc
      _ ≤ (r : ℝ) * Real.exp budget := hhi j
      _ ≤ Real.exp P0 * Real.exp budget :=
        mul_le_mul_of_nonneg_right hrP0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hcard : (Fintype.card (∀ j, ZMod (parameters j)) : ℝ) ≤
      Real.exp ((d : ℝ)*(budget+P0)) := by
    calc
      _ = ∏ j, (parameters j : ℝ) := by simp [Fintype.card_pi]
      _ ≤ ∏ _j : Fin d, Real.exp (budget+P0) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hparam j)
      _ = _ := by simp [Real.exp_nat_mul]
  have hW : W ≤ Real.exp Q := by
    calc
      _ ≤ ∑ _j : Fin d, (r : ℝ)*Real.exp budget :=
        Finset.sum_le_sum (fun j _ => hhi j)
      _ = (d : ℝ)*(r : ℝ)*Real.exp budget := by simp [mul_assoc]
      _ ≤ Real.exp P0 * Real.exp P0 * Real.exp budget := by gcongr
      _ = _ := by dsimp [Q]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have honeW : 1+W ≤ Real.exp (Q+1) := by
    have heQ : 1 ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ 2*Real.exp Q := by linarith
      _ ≤ Real.exp 1 * Real.exp Q :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hcollision := unconditionedCollisionWidth_le_exp parameters hσ hσP0 hcard
  have hmax : max (8*(probabilityProfileLipschitz : ℝ))
      (unconditionedCollisionWidth parameters σ) ≤ Real.exp R := by
    apply max_le
    · calc
        _ ≤ Real.exp 8 * Real.exp P0 := by
          apply mul_le_mul _ hprofile (by positivity) (Real.exp_nonneg _)
          linarith [Real.add_one_le_exp (8 : ℝ)]
        _ = Real.exp (8+P0) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by
          have hh : 0 ≤ 2*(d : ℝ)*(budget+P0) := by positivity
          dsimp [R]
          linarith)
    · apply hcollision.trans
      apply Real.exp_le_exp.mpr
      dsimp [R]
      ring_nf
      linarith
  have hD : 2*(d : ℝ) ≤ ((r*d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right d hr
  have hD0 : (0 : ℝ) ≤ (r*d : ℕ) := Nat.cast_nonneg _
  have hlog : Q+1+8+R+P0 ≤ (((r*d : ℕ) : ℝ)+4)*(budget+P0+20) := by
    have hb := mul_le_mul_of_nonneg_right hD hbudget
    have hP := mul_le_mul_of_nonneg_right hD hP0
    dsimp [Q, R]
    nlinarith
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      _ = 4*τ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4 * Real.exp P0 := by
        apply mul_le_mul _ hτP0 (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = Real.exp (4+P0) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ = 8*(1+W)*max (8*(probabilityProfileLipschitz : ℝ))
          (unconditionedCollisionWidth parameters σ)*τ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 8 * Real.exp (Q+1) * Real.exp R * Real.exp P0 := by
        apply mul_le_mul _ hτP0 (inv_nonneg.mpr hτ.le) (by positivity)
        apply mul_le_mul _ hmax (le_trans (by positivity) (le_max_left _ _)) (by positivity)
        apply mul_le_mul _ honeW (by positivity) (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (8 : ℝ)]
      _ = Real.exp (Q+1+8+R+P0) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem comparableScalarProductivitySize
    {X : Type*} [Fintype X] (d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {P0 budget σ : ℝ} (hP0 : 0 ≤ P0) (hbudget : 0 ≤ budget)
    (hdP0 : (d : ℝ) ≤ Real.exp P0) (hrP0 : (r : ℝ) ≤ Real.exp P0)
    (hσ : 0 < σ) (hσP0 : σ⁻¹ ≤ Real.exp P0)
    (hτP0 : (unconditionedSpatialTrimFraction (Fintype.card X) σ)⁻¹ ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (parameters : Fin d → ℕ) [∀ j, NeZero (parameters j)]
    (hhi : ∀ j, (parameters j : ℝ) ≤ (r : ℝ)*Real.exp budget)
    (N : X → ℕ)
    (hN : ∀ i, Real.exp ((((r*d : ℕ) : ℝ)+4)*(budget+P0+20)) ≤ (N i : ℝ)) :
    ∀ i, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound parameters)
      (unconditionedSpatialTrimFraction (Fintype.card X) σ)
      (unconditionedCollisionWidth parameters σ) ≤ (N i : ℝ) := by
  intro i
  exact (comparableScalarProductivityCutoff_le_exp d r hd hr hP0 hbudget hdP0 hrP0
    hσ hσP0 hτP0 hprofile parameters hhi).trans (hN i)

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance comparableScalarGeometryTransferFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem exists_comparableScalarGeometryTransfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    ((r*d : ℕ) : ℝ) ≤ Real.exp P0 → ((r : ℝ) + 1) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant (r*d) τ ≤ Real.exp P0 →
    4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < parameters j),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, happly⟩ := exists_comparableScalarTailApplication.{u,v} s d r hd hr
  refine ⟨E, hE, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hDP0 hrPlusOneP0 hprofile
    hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget g hg L parameters hlo hhi
    N hN hunit Wsite width margin
  have data := comparableScalarGeometryData d r hd hr hP0 hbudget0 hDP0 hprofile hσ hσ1 hτP0
    parameters hlo hhi N hN
  refine ⟨data.hwidth, data.hmargin, data.hZ, data.hparam, ?_⟩
  exact happly nilmanifold p epsilon P0 level budget σ hp hepsilon hepsilon1 hP0
    htargetP0 hepsP0 hlevel hlevel2 hnTarget hDP0 hrPlusOneP0 hprofile hσ hσ1 hτP0 hKP0
    hframeDim hbudget0 hbudget g hg parameters hlo hhi N hunit data

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section

local instance comparableUnconditionedScalarProductiveFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def ComparableUnconditionedScalarProductiveTransferStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ) [∀ j, NeZero (parameters j)],
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
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
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_comparable_unconditioned_scalar_productive_transfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarProductiveTransferStatement.{u,v} s d r epsilon := by
  unfold ComparableUnconditionedScalarProductiveTransferStatement
  obtain ⟨E, hE, hgeom⟩ := exists_comparableScalarGeometryTransfer.{u,v} s d r hd hr
  obtain ⟨A, C, F, hA, hC, hF, hselect⟩ :=
    exists_comparableScalarSelectedBudget E d r hE hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv hlevel hlevel2
    g hg target budget L parameters _ hlo hhi N hN hunit τ Wsite width margin
  let P0 := (A : ℝ) * (target + 1)
  have hsel := hselect (Fintype.card I) hp hn hσ hσinv
  have hpTarget := hsel.1
  have htarget := hsel.2.1
  have hnTarget := hsel.2.2.1
  have hframeDim := hsel.2.2.2.1
  have hP0 := hsel.2.2.2.2.1
  have htargetP0 := hsel.2.2.2.2.2.1
  have hepsP0 := hsel.2.2.2.2.2.2.1
  have hprofile := hsel.2.2.2.2.2.2.2.1
  have hDP0 := hsel.2.2.2.2.2.2.2.2.1
  have hdP0 := hsel.2.2.2.2.2.2.2.2.2.1
  have hrPlusOneP0 := hsel.2.2.2.2.2.2.2.2.2.2.1
  have htwoP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.1
  have hτP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudget0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hthreshold := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNlog := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudgetFinal := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hframeDim' : 4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ target := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, target] using hframeDim
  have hthreshold' : scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon target P0 ≤ budget := by
    have hc : Fintype.card (Option (Fin d) × I) = (d + 1) * Fintype.card I := by simp
    rw [hc]
    exact hthreshold
  have hNphysical (i) : Real.exp (((r * d : ℕ) + 4 : ℝ) * (budget + P0 + 20)) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hNlog).trans (hN i)
  obtain ⟨hwidth, hmargin, hZ, hparam, htail⟩ :=
    hgeom (I := I) (V := V) nilmanifold target epsilon P0 level budget σ htarget hepsilon hepsilon1
      hP0 htargetP0 hepsP0 ((Real.exp_le_exp.mpr (neg_le_neg hpTarget)).trans hlevel)
      hlevel2 hnTarget hDP0 hrPlusOneP0 hprofile hσ hσ1 hτP0 hKP0 hframeDim' hbudget0 hthreshold'
      g (hg.mono hpTarget) parameters hlo hhi N hNphysical hunit
  have hpP0 : p ≤ P0 := hpTarget.trans (by linarith only [htargetP0, htarget])
  have hrP0 : (r : ℝ) ≤ Real.exp P0 := by linarith only [hrPlusOneP0]
  have hcutoff := comparableScalarProductivitySize (X := I) d r hd hr hP0 hbudget0
    hdP0 hrP0 hσ (hσinv.trans (Real.exp_le_exp.mpr hpP0)) hτP0 hprofile
    parameters hhi N hNphysical
  have hcollision := congrArg
    (fun dec => @unconditionedCollisionWidth (Fin d) (Fin.fintype d) dec parameters inferInstance σ)
    (Subsingleton.elim (instDecidableEqFin d) (comparableUnconditionedScalarProductiveFinDecidableEq d))
  refine ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, ?_, htail⟩
  intro i
  rw [← hcollision]
  exact hcutoff i

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section

local instance comparableUnconditionedScalarFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def ComparableUnconditionedScalarTransferStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < parameters j),
    budget ≤ (p + F) ^ F ∧
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_comparable_unconditioned_scalar_transfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarTransferStatement.{u,v} s d r epsilon := by
  unfold ComparableUnconditionedScalarTransferStatement
  obtain ⟨E, hE, hgeom⟩ := exists_comparableScalarGeometryTransfer.{u,v} s d r hd hr
  obtain ⟨A, C, F, hA, hC, hF, hselect⟩ :=
    exists_comparableScalarSelectedBudget E d r hE hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv hlevel hlevel2
    g hg target budget L parameters hlo hhi N hN hunit τ Wsite width margin
  let P0 := (A : ℝ) * (target + 1)
  have hsel := hselect (Fintype.card I) hp hn hσ hσinv
  have hpTarget := hsel.1
  have htarget := hsel.2.1
  have hnTarget := hsel.2.2.1
  have hframeDim := hsel.2.2.2.1
  have hP0 := hsel.2.2.2.2.1
  have htargetP0 := hsel.2.2.2.2.2.1
  have hepsP0 := hsel.2.2.2.2.2.2.1
  have hprofile := hsel.2.2.2.2.2.2.2.1
  have hDP0 := hsel.2.2.2.2.2.2.2.2.1
  have hdP0 := hsel.2.2.2.2.2.2.2.2.2.1
  have hrPlusOneP0 := hsel.2.2.2.2.2.2.2.2.2.2.1
  have htwoP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.1
  have hτP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudget0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hthreshold := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNlog := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudgetFinal := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hframeDim' : 4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ target := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, target] using hframeDim
  have hthreshold' : scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon target P0 ≤ budget := by
    have hc : Fintype.card (Option (Fin d) × I) = (d + 1) * Fintype.card I := by simp
    rw [hc]
    exact hthreshold
  have hNphysical (i) : Real.exp (((r * d : ℕ) + 4 : ℝ) * (budget + P0 + 20)) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hNlog).trans (hN i)
  obtain ⟨hwidth, hmargin, hZ, hparam, htail⟩ :=
    hgeom (I := I) (V := V) nilmanifold target epsilon P0 level budget σ htarget hepsilon hepsilon1
      hP0 htargetP0 hepsP0 ((Real.exp_le_exp.mpr (neg_le_neg hpTarget)).trans hlevel)
      hlevel2 hnTarget hDP0 hrPlusOneP0 hprofile hσ hσ1 hτP0 hKP0 hframeDim' hbudget0 hthreshold'
      g (hg.mono hpTarget) parameters hlo hhi N hNphysical hunit
  exact ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩

end
end Erdos3

end

end OAI
