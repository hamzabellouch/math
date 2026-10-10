import OAI.Analysis.CircleDomains.Sobolev.ScalarFlatteningEnergy
import OAI.Analysis.CircleDomains.Sobolev.LocalScalarEnergy

namespace OAI

/-! Simultaneous uniform and energy control while flattening countably
many prescribed scalar values. The Sobolev chain rule gives a witness on
the open domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_countable_value_flattening
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ p ∈ U, u p ∈ Icc (-B) B)
    {C : Set ℝ} (hC : C.Countable) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ O : Set ℝ, ∃ W' : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ u) U,
      IsOpen O ∧ C ⊆ O ∧ LipschitzWith 1 (flattenValues O) ∧
      (∀ t, |flattenValues O t-t| < δ) ∧
      (∫⁻ p in U, ENNReal.ofReal (‖W'.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε ∧
      (∀ c ∈ C, ∃ V ∈ 𝓝 c, EqOn (flattenValues O) (fun _ => flattenValues O c) V) ∧
      (∀ p, W.weakGrad p = 0 → W'.weakGrad p = 0) := by
  obtain ⟨O, hCO, hO, hvol, henergy⟩ := exists_small_open_local_energy_cover
    hcoarea hU hu W hC (lt_min (ENNReal.ofReal_pos.mpr hδ) (ENNReal.ofReal_pos.mpr hε))
  let W' := flattenedSobolevWitness hU hu W hB hb hO
  have hvolδ := hvol.trans_le (min_le_left _ _)
  have hOfin : volume O ≠ ∞ := (hvolδ.trans_le (le_of_lt ENNReal.ofReal_lt_top)).ne
  refine ⟨O, W', hO, hCO, flattenValues_lipschitz hO.measurableSet, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (flattenValues_close hO.measurableSet hOfin t).trans_lt
      (ENNReal.toReal_lt_of_lt_ofReal hvolδ)
  · change (∫⁻ p in U, ENNReal.ofReal
      (‖flattenedGradient O u W.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε
    rw [flattenedGradient_energy_error U hu W.weakGrad hO.measurableSet]
    exact henergy.trans_le (min_le_right _ _)
  · intro c hc
    exact flattenValues_locally_constant hO (hCO hc)
  · intro p hp
    change flattenedGradient O u W.weakGrad p = 0
    by_cases hpu : u p ∈ O <;> simp [flattenedGradient, hpu, hp]

end CircleDomainRigidity

end

end OAI
