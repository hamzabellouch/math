import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.FiniteSeedPacking
import OAI.Analysis.RieszRectifiability.Packing.NoFlatDescendantPacking
import OAI.Analysis.RieszRectifiability.Flatness.FlatSeedGlobalCharge
import OAI.Analysis.RieszRectifiability.Flatness.GlobalFlatSeedSelection
import OAI.Analysis.RieszRectifiability.Nets.RelativeCellMass

namespace OAI

/-!
# Uniform Carleson packing of cells with large bilateral beta

The packing constant is chosen before the measure. Cells without a flat
descendant are bounded separately; the remaining cells are charged through
flat seeds to descendants with large scalar oscillation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_bad_beta_carleson_constant {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ F : Finset (SupportCellDescendant μ R hR k z),
      (∀ i ∈ F, ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)) →
      ∑ i ∈ F, μ i.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨J, α, hα, _, hcharge⟩ := exists_uniform_flat_seed_global_charge hnd C G H ε D
    hC hG.le hH hε
  let A := H * (2 : ℝ) ^ propagationHorizon J + 2
  let Jo := H * propagationTestRadius J + 2
  let v := (H / 64) ^ (p + 2) * propagationScale J ^ 3
  have hHp : 0 < H := by linarith
  have hA : 1 ≤ A := by
    have ht : 0 ≤ H * (2 : ℝ) ^ propagationHorizon J := by positivity
    dsimp [A]
    linarith
  have hJo : 0 < Jo := by dsimp [Jo, propagationTestRadius]; positivity
  have hv : 0 < v := by have hδ := propagationScale_pos J; dsimp [v]; positivity
  obtain ⟨I, hI, Kc, hKc, hNoFlat⟩ := exists_uniform_no_flat_descendant_total_mass
    (by omega : 1 ≤ p + 1) hnd C G A α D hC hG hA hα
  obtain ⟨Ko, hKo, hOsc⟩ := exists_uniform_bad_descendant_total_mass p d C G Jo v D hC hG hJo hv
  let M := flatDescendantMassConstant (p + 1) C G I
  have hM : 0 < M := flatDescendantMassConstant_pos (p + 1) C G I hC hG
  let Kg := M * ((I : ℝ) + 1) * (1 + Ko)
  have hKg : 0 < Kg := by dsimp [Kg]; positivity
  have hcoeff : ENNReal.ofReal Kg = ENNReal.ofReal M * ((I + 1 : ℕ) : ℝ≥0∞) *
      (1 + ENNReal.ofReal Ko) := by
    dsimp [Kg]
    rw [ENNReal.ofReal_mul (mul_nonneg hM.le (by positivity)), ENNReal.ofReal_mul hM.le,
      ENNReal.ofReal_add zero_le_one hKo.le, ENNReal.ofReal_one]
    norm_num [ENNReal.ofReal_add]
  refine ⟨Kc + Kg, add_pos hKc hKg, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore F hbad
  let P (i : SupportCellDescendant μ R hR k z) : Prop :=
    HasFlatDescendant (p + 1) μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I A α
  let Good := F.filter P
  let Ex := F.filter (fun i => ¬ P i)
  have hEx : ∑ i ∈ Ex, μ i.cell ≤ ENNReal.ofReal Kc * μ (cleanSupportCell μ R hR k z) := by
    exact (finite_subtype_sum_le_tsum (fun i => ¬ P i) (fun i => μ i.cell) Ex
      (fun i hi => (Finset.mem_filter.mp hi).2)).trans (hNoFlat μ hg hlower hRiesz R hR k z hcore)
  have hex (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Good) :
      ∃ S : SupportCellDescendant μ R hR k z,
        i.depth < S.depth ∧ S.depth ≤ i.depth + I ∧ S.cell ⊆ i.cell ∧
          A * S.radius ≤ i.radius / 8 ∧
          HasFlatCell (p + 1) μ R hR (k + S.depth) ⟨S.center, S.mem_net⟩ A α :=
    exists_global_flat_seed μ R hR k z i I A α (Finset.mem_filter.mp hi).2
  let seed (i : SupportCellDescendant μ R hR k z) := if hi : i ∈ Good then (hex i hi).choose else i
  have hs (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Good) :
      i.depth < (seed i).depth ∧ (seed i).depth ≤ i.depth + I ∧ (seed i).cell ⊆ i.cell ∧
        A * (seed i).radius ≤ i.radius / 8 ∧
        HasFlatCell (p + 1) μ R hR (k + (seed i).depth) ⟨(seed i).center, (seed i).mem_net⟩ A α := by
    have heq : seed i = (hex i hi).choose := dite_eq_left hi
    rw [heq]
    exact (hex i hi).choose_spec
  let Osc (i : SupportCellDescendant μ R hR k z) : Prop :=
    ¬ ScalarOscillationBound (p + 1) μ i.center (Jo * i.radius) (v * i.radius ^ (p + 2))
  have hGood : ∑ i ∈ Good, μ i.cell ≤ ENNReal.ofReal Kg * μ (cleanSupportCell μ R hR k z) := by
    rw [hcoeff]
    apply finite_parent_mass_of_seed_charges μ R hR k z Good seed Osc I (ENNReal.ofReal M) (ENNReal.ofReal Ko)
    · intro i hi
      exact ⟨(hs i hi).1.le, (hs i hi).2.1, (hs i hi).2.2.1⟩
    · intro i hi
      exact SupportCellDescendant.relative_mass_bound μ C G hC hG hg hlower R hR k z hcore
        i (seed i) I (hs i hi).1.le (hs i hi).2.1 (hs i hi).2.2.1
    · intro i hi j hj hdepth hsub
      have hHpow : 0 < H * (2 : ℝ) ^ propagationHorizon J := by positivity
      have hh := flat_seed_enlargement_admissible μ R hR k z hcore i (seed i) A
        (H * (2 : ℝ) ^ propagationHorizon J) hHpow (by dsimp [A]; linarith) (hs i hi).2.2.2.1
      have horizon : AdmissibleRadius μ ((H * (seed i).radius) * (2 : ℝ) ^ propagationHorizon J) := by
        convert! hh using 1
        ring
      obtain ⟨t, hlow, hhigh, hcontain, _⟩ := hcharge μ hg hlower hRiesz R hR k z (seed i)
        horizon (hs i hi).2.2.2.2 j hdepth hsub (hbad j (Finset.mem_filter.mp hj).1)
      exact ⟨t, hlow, hhigh, hcontain⟩
    · exact hOsc μ hg hlower hRiesz R hR k z hcore
  have hsplit : (∑ i ∈ Good, μ i.cell) + (∑ i ∈ Ex, μ i.cell) = ∑ i ∈ F, μ i.cell :=
    Finset.sum_filter_add_sum_filter_not F P (fun i => μ i.cell)
  calc
    _ = (∑ i ∈ Ex, μ i.cell) + (∑ i ∈ Good, μ i.cell) := by rw [← hsplit, add_comm]
    _ ≤ ENNReal.ofReal Kc * μ (cleanSupportCell μ R hR k z) +
        ENNReal.ofReal Kg * μ (cleanSupportCell μ R hR k z) := add_le_add hEx hGood
    _ = _ := by rw [← add_mul, ENNReal.ofReal_add hKc.le hKg.le]

end

end RieszRectifiability

end OAI
