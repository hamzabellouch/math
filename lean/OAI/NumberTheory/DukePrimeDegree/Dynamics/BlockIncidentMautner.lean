import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerBlockL2
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockErgodicity

namespace OAI

/-!
# A block-fixed observable is fixed along incident invariant roots

A root touching a nontrivial special linear block has nonzero weight
for some diagonal inside that block. Mautner therefore fixes that root
on every block-fixed vector, provided the root already acts isometrically.
The lattice corollary uses only roots in the actual measure stabilizer.
It does not infer invariance under a missing reverse root.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma another_mem_block {n : ℕ} (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (p : Fin n) : ∃ r ∈ S, p ≠ r := by
  by_cases hpk : p = k
  · exact ⟨l, hl, by simpa only [hpk] using hkl⟩
  · exact ⟨k, hk, hpk⟩

private lemma block_diagonal_fixed {n : ℕ} (S : Set (Fin n))
    (L : Subgroup (G n)) (hSL : singleBlockRootGroup S ≤ L)
    {Y : Type*} [MetricSpace Y] [MulAction L Y] [ContinuousSMul L Y]
    [IsIsometricSMul L Y] (x : Y)
    (hfix : ∀ h : singleBlockRootGroup S,
      (⟨h.val, hSL h.property⟩ : L) • x = x)
    (p r : Fin n) (hpr : p ≠ r) (hp : p ∈ S) (hr : r ∈ S) :
    ∃ hD : ∀ t : ℝ, diagonalOneParameter (rootIsolationWeights p r)
        (rootIsolationWeights_sum p r) t ∈ L,
      ∀ t : ℝ, (⟨diagonalOneParameter (rootIsolationWeights p r)
        (rootIsolationWeights_sum p r) t, hD t⟩ : L) • x = x := by
  have hDH (t : ℝ) : diagonalOneParameter (rootIsolationWeights p r)
      (rootIsolationWeights_sum p r) t ∈ singleBlockRootGroup S := by
    rw [diagonalOneParameter_rootPair_eq hpr]
    exact diag2n_mem_of_opposite_roots hpr (singleBlockRootGroup S)
      (root_mem_singleBlockRootGroup S p hp r hr hpr)
      (root_mem_singleBlockRootGroup S r hr p hp hpr.symm) _ (Real.exp_ne_zero t)
  exact ⟨fun t => hSL (hDH t), fun t => hfix ⟨_, hDH t⟩⟩

/-- This includes a root with only one endpoint in the fixed block.
Its presence in the ambient isometric action remains essential. -/
theorem incident_root_fixed_of_block_fixed {n : ℕ} (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (L : Subgroup (G n)) (hSL : singleBlockRootGroup S ≤ L)
    {Y : Type*} [MetricSpace Y] [MulAction L Y] [ContinuousSMul L Y]
    [IsIsometricSMul L Y] (x : Y)
    (hfix : ∀ h : singleBlockRootGroup S,
      (⟨h.val, hSL h.property⟩ : L) • x = x)
    (p q : Fin n) (hpq : p ≠ q) (htouch : p ∈ S ∨ q ∈ S)
    (hU : ∀ t : ℝ, SpecialLinearGroup.transvection hpq t ∈ L) (t : ℝ) :
    (⟨SpecialLinearGroup.transvection hpq t, hU t⟩ : L) • x = x := by
  by_cases hp : p ∈ S
  · by_cases hq : q ∈ S
    · exact hfix ⟨_, root_mem_singleBlockRootGroup S p hp q hq hpq t⟩
    · obtain ⟨r, hr, hpr⟩ := another_mem_block S k l hkl hk hl p
      obtain ⟨hD, hDx⟩ := block_diagonal_fixed S L hSL x hfix p r hpr hp hr
      have hqp : q ≠ p := fun h => hq (h.symm ▸ hp)
      have hqr : q ≠ r := fun h => hq (h.symm ▸ hr)
      apply root_fixed_of_diagonal_fixed L (rootIsolationWeights p r)
        (rootIsolationWeights_sum p r) hD x hDx hpq hU _ t
      simp [rootIsolationWeights, hpr, hqp, hqr]
  · have hq : q ∈ S := htouch.resolve_left hp
    obtain ⟨r, hr, hqr⟩ := another_mem_block S k l hkl hk hl q
    obtain ⟨hD, hDx⟩ := block_diagonal_fixed S L hSL x hfix q r hqr hq hr
    have hpr : p ≠ r := fun h => hp (h.symm ▸ hr)
    apply root_fixed_of_diagonal_fixed L (rootIsolationWeights q r)
      (rootIsolationWeights_sum q r) hD x hDx hpq hU _ t
    simp [rootIsolationWeights, hqr, hpq, hpr]

/-- On the actual finite lattice-space measure, an incident root which
already preserves the measure fixes every block-invariant L² observable.
This is the input for transporting such invariance to block components. -/
theorem ae_incident_root_fixed_of_L2_block_fixed {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hSL : singleBlockRootGroup S ≤ invariantRightSubgroup μ)
    (f : Lp ℝ 2 μ)
    (hfix : ∀ h : singleBlockRootGroup S,
      (fun x => f (rightAction x h.val)) =ᵐ[μ] f)
    (p q : Fin n) (hpq : p ≠ q) (htouch : p ∈ S ∨ q ∈ S)
    (hU : ∀ t : ℝ, μ.map (fun x => rightAction x
      (SpecialLinearGroup.transvection hpq t)) = μ) (t : ℝ) :
    (fun x => f (rightAction x (SpecialLinearGroup.transvection hpq t))) =ᵐ[μ] f := by
  let L := invariantRightSubgroup μ
  let : SMulInvariantMeasure L (X n) μ :=
    ⟨fun h s hs => (latticeSubgroup_preserving L μ le_rfl h).measure_preimage
      hs.nullMeasurableSet⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MulAction L (Lp ℝ 2 μ) := MulAction.compHom _ (inverseDomainHom L)
  let : ContinuousSMul L (Lp ℝ 2 μ) :=
    MulAction.continuousSMul_compHom (continuous_inverseDomainHom L)
  let : IsIsometricSMul L (Lp ℝ 2 μ) :=
    ⟨fun h => isometry_smul (Lp ℝ 2 μ) (inverseDomainHom L h)⟩
  have hrep (h : L) : (h • f : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => f (rightAction x h.val)) := by
    have he := DomMulAct.smul_Lp_ae_eq (inverseDomainHom L h) f
    change (h • f : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => f (rightAction x (h.val⁻¹)⁻¹)) at he
    simpa only [inv_inv] using he
  have hblock (h : singleBlockRootGroup S) :
      (⟨h.val, hSL h.property⟩ : L) • f = f :=
    Lp.ext ((hrep _).trans (hfix h))
  have hu (s : ℝ) : SpecialLinearGroup.transvection hpq s ∈ L := hU s
  have ht := incident_root_fixed_of_block_fixed S k l hkl hk hl L hSL f hblock
    p q hpq htouch hu t
  simpa only [ht] using (hrep ⟨_, hu t⟩).symm

end DukePrimeDegree

end

end OAI
