import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateProfile
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulse

namespace OAI

/-! Finite parallel translation gates. Separation is required for the
whole address table, so the selected computation is never used to define
which gates are present. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

theorem translationGate_eq_zero {χ : Plane → ℝ} {c v x : Plane}
    (hx : x - c ∉ tsupport χ) : translationGate χ c v x = 0 := by
  have hs := (translationGate_support χ c v).trans
    (tsupport_comp_subset_preimage χ (continuous_id.sub continuous_const))
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))

theorem other_gate_eq_zero {R : ℝ} (hR : 0 < R) {c d v x : Plane}
    (hnear : ∀ j, |x j - c j| ≤ 2 * R)
    (hsep : ∃ j, 16 * R ≤ |c j - d j|) :
    translationGate (gateCutoff R) d v x = 0 := by
  apply translationGate_eq_zero
  intro hx
  obtain ⟨j, hj⟩ := hsep
  have hb := gateCutoff_tsupport hR hx j
  change |x j - d j| ≤ 3 * R at hb
  have ht : |c j - d j| ≤ |x j - c j| + |x j - d j| := by
    have hh := abs_add_le (c j - x j) (x j - d j)
    have he : (c j - x j) + (x j - d j) = c j - d j := by ring
    rw [he, abs_sub_comm (c j) (x j)] at hh
    exact hh
  linarith [hnear j]

def parallelGate {ι : Type*} [Fintype ι] (R : ℝ)
    (c v : ι → Plane) (x : Plane) : Plane :=
  ∑ i, translationGate (gateCutoff R) (c i) (v i) x

theorem parallelGate_smooth {ι : Type*} [Fintype ι]
    (R : ℝ) (c v : ι → Plane) : ContDiff ℝ ∞ (parallelGate R c v) :=
  ContDiff.sum (fun i _ => translationGate_smooth (gateCutoff_smooth R) (c i) (v i))

theorem parallelGate_properties {ι : Type*} [Fintype ι]
    {R : ℝ} (hR : 0 < R) (c v : ι → Plane) :
    HasCompactSupport (parallelGate R c v) ∧
      (∀ x, PlanarHamiltonian.divergence (parallelGate R c v) x = 0) ∧
      (∫ x, parallelGate R c v x) = 0 := by
  let H : ι → Plane → ℝ := fun i x => gateCutoff R (x - c i) *
    PlanarHamiltonian.translationPotential (v i) (x - c i)
  have hH (i : ι) : ContDiff ℝ ∞ (H i) :=
    ((gateCutoff_smooth R).comp (contDiff_id.sub contDiff_const)).mul
      ((PlanarHamiltonian.translationPotential_smooth (v i)).comp
        (contDiff_id.sub contDiff_const))
  have hc (i : ι) : HasCompactSupport (H i) := by
    have hχ : HasCompactSupport (fun x => gateCutoff R (x - c i)) := by
      simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
        (gateCutoff_compactSupport hR).comp_homeomorph (Homeomorph.addRight (-c i))
    exact hχ.mul_right
  have hcompact : IsCompact (⋃ i, tsupport (H i)) :=
    isCompact_iUnion (fun i => (hc i).isCompact)
  have hs : ContDiff ℝ ∞ (fun x => ∑ i, H i x) := ContDiff.sum (fun i _ => hH i)
  have hsum : HasCompactSupport (fun x => ∑ i, H i x) := by
    apply HasCompactSupport.intro hcompact
    intro x hx
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport (fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩))
  have he : parallelGate R c v = PlanarHamiltonian.field (fun x => ∑ i, H i x) := by
    funext x
    exact (PlanarHamiltonian.field_sum Finset.univ H (fun i _ => hH i) x).symm
  rw [he]
  exact ⟨PlanarHamiltonian.field_compactSupport hsum,
    PlanarHamiltonian.field_divergence hs, PlanarHamiltonian.field_integral_eq_zero hs hsum⟩

theorem parallelGate_plateau {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ℝ} (hR : 0 < R) (c v : ι → Plane) (i : ι) (x : Plane)
    (hnear : ∀ j, |x j - c i j| < 2 * R)
    (hsep : ∀ k, k ≠ i → ∃ j, 16 * R ≤ |c i j - c k j|) :
    parallelGate R c v x = v i := by
  unfold parallelGate
  rw [Finset.sum_eq_single i]
  · apply translationGate_plateau
    apply gateCutoff_one_near hR
    exact hnear
  · intro k _ hki
    exact other_gate_eq_zero hR (fun j => (hnear j).le) (hsep k hki)
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

end ForcedComputation.ExpandingDetector

end

end OAI
