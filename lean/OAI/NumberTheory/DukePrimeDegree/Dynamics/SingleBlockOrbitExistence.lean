import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockShearingContradiction
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockCorrectedPairs
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace OAI

/-!
# A positive-mass block orbit from actual root ergodicity

Local block preservation of the measure stabilizer supplies the fixed
transverse shell.  Haar patches supply the common corrections, and root
ergodicity supplies a common generic set.  If every block orbit were
null, the resulting normalized transverse pairs would contradict the
fixed-window shearing estimate.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] singleBlockRootGroup blockMatrixGroup singleBlockClosureGroup

lemma exists_positive_real_fiber_budget (b t : ℝ≥0∞)
    (hb : b ≠ ⊤) (ht : t ≠ 0) (httop : t ≠ ⊤) :
    ∃ η : ℝ, 0 < η ∧ (b * ENNReal.ofReal η) / t < 1 := by
  let η : ℝ := t.toReal / (2 * (b.toReal + 1))
  have htpos : 0 < t.toReal := ENNReal.toReal_pos ht httop
  have hbpos : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hden : 0 < 2 * (b.toReal + 1) := by positivity
  have hη : 0 < η := div_pos htpos hden
  refine ⟨η, hη, ?_⟩
  rw [ENNReal.div_lt_iff (Or.inl ht) (Or.inl httop), one_mul]
  apply (ENNReal.toReal_lt_toReal (by finiteness) httop).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le]
  dsimp only [η]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

theorem exists_positive_singleBlock_orbit_of_patch {n : ℕ}
    (S : Finset (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup (S : Set (Fin n))) (X n) μ]
    (hlocal : {g : invariantRightSubgroup μ |
      g.val ∈ blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))} ∈
        𝓝 (1 : invariantRightSubgroup μ))
    (ρ : Measure (singleBlockClosureGroup (n := n) (S : Set (Fin n)))) [SFinite ρ] [ρ.IsMulLeftInvariant]
    (W K₀ K₁ : Set (singleBlockClosureGroup (n := n) (S : Set (Fin n))))
    (hW : IsOpen W) (h1W : 1 ∈ W) (hK₀ : IsCompact K₀) (hK : K₀ ⊆ K₁)
    (hK₀pos : 0 < ρ K₀) (hK₁fin : ρ K₁ < ⊤)
    (hpatch : ∀ b ∈ W, ∀ u ∈ K₀, b * u ∈ K₁) :
    ∃ g : G n,
      μ (range (latticeOrbitPoint g (blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))))) ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hK₀fin : ρ K₀ ≠ ⊤ := ((measure_mono hK).trans_lt hK₁fin).ne
  have hmass : 0 < (ρ K₀).toReal := ENNReal.toReal_pos hK₀pos.ne' hK₀fin
  let t : ℝ≥0∞ := ENNReal.ofReal ((ρ K₀).toReal / 4)
  have ht : t ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have httop : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsize : t + t < ρ K₀ := by
    rw [← ENNReal.ofReal_toReal hK₀fin]
    change ENNReal.ofReal ((ρ K₀).toReal / 4) +
      ENNReal.ofReal ((ρ K₀).toReal / 4) < ENNReal.ofReal (ρ K₀).toReal
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff hmass).mpr (by linarith)
  obtain ⟨η, hη, hbudget⟩ := exists_positive_real_fiber_budget (ρ K₁) t hK₁fin.ne ht httop
  obtain ⟨a, ha, F, ε, hε, hsep⟩ := exists_finite_small_transverse_separators
    μ (blockComplementSetoid (S : Set (Fin n))) hlocal
  let K := transverseMatrixShell (blockComplementSetoid (S : Set (Fin n))) a
  have hKcompact : IsCompact K := transverseMatrixShell_isCompact _ _
  obtain ⟨δ, hδ, hδ1, hwindow⟩ := exists_fixed_terminal_observable_fraction
    F K hKcompact a (ε / 4) ha.le (by positivity)
  obtain ⟨E, hE, hEμ, R, _hR, hgood⟩ := exists_singleBlock_terminal_generic_set
    (S : Set (Fin n)) μ F K hKcompact (ε / 4) δ η (by positivity) hδ hδ1 hη
  have hbudgetE : (ρ K₁ * μ Eᶜ) / t < 1 := by
    apply lt_of_le_of_lt _ hbudget
    gcongr
  have hH : singleBlockRootGroup (S : Set (Fin n)) ≤ invariantRightSubgroup μ :=
    subgroup_le_invariantRightSubgroup_of_invariant_action _ μ
  obtain ⟨p, q, g, c, hg, hpq, hpqE, hpart⟩ :=
    exists_singleBlock_corrected_generic_pairs S ⟨k, hk⟩ μ hH ρ K₀ K₁ hK₀ hK
      W hW h1W hpatch E hE t ht httop hsize hbudgetE hnone
  exact singleBlock_fixed_window_contradiction (S : Set (Fin n)) k l hkl hk hl μ a ε ha hε F hsep
    δ hδ hδ1 hwindow E R hgood p q g c hg hpq hpqE hpart

/-- The correction patches are constructed from Haar measure on the
closed root group; no patch or homogeneous-orbit assumption remains. -/
theorem exists_positive_singleBlock_orbit {n : ℕ}
    (S : Finset (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup (S : Set (Fin n))) (X n) μ]
    (hlocal : {g : invariantRightSubgroup μ |
      g.val ∈ blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))} ∈
        𝓝 (1 : invariantRightSubgroup μ)) :
    ∃ g : G n,
      μ (range (latticeOrbitPoint g (blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))))) ≠ 0 := by
  let H : Subgroup (G n) := singleBlockClosureGroup (n := n) (S : Set (Fin n))
  let : LocallyCompactSpace H := by
    unfold H singleBlockClosureGroup
    exact (singleBlockRootGroup (S : Set (Fin n))).isClosed_topologicalClosure.locallyCompactSpace
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let ρ : Measure H := Measure.haar
  obtain ⟨W, K₀, K₁, hW, h1W, hK₀, _hK₁, hK, hpos, hfin, hpatch⟩ :=
    exists_compact_correction_patches ρ
  exact exists_positive_singleBlock_orbit_of_patch S k l hkl hk hl μ hlocal ρ
    W K₀ K₁ hW h1W hK₀ hK hpos hfin hpatch

end DukePrimeDegree

end

end OAI
