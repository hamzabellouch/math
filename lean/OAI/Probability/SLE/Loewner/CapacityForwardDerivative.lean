import OAI.Probability.SLE.Loewner.CapacityForwardLipschitz
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace OAI

/-! The exact capacity-parametrized map has an almost-everywhere time
derivative, with the height bound needed for the Loewner evolution. -/
noncomputable section
open Set Filter Function Complex MeasureTheory
open scoped Topology

namespace SLEExactGauge

noncomputable def capacityForwardOnPrefix (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (z : ℂ) (c : ℝ) : ℂ :=
  initialForwardChart p hi h0 hH
    (prefixCapacityTime p hi h0 hH T
      (projIcc 0 (initialCapacity p hi h0 hH T)
        (initialCapacity_nonneg p hi h0 hH T) c)) z

theorem capacityForwardOnPrefix_at_initialCapacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (z : ℂ) {s : unitInterval} (hs : s≤T) :
    capacityForwardOnPrefix p hi h0 hH T z (initialCapacity p hi h0 hH s)=
      initialForwardChart p hi h0 hH s z := by
  have hm : initialCapacity p hi h0 hH s∈Icc 0 (initialCapacity p hi h0 hH T) :=
    ⟨initialCapacity_nonneg p hi h0 hH s,initialCapacity_monotone p hi h0 hH hs⟩
  have he := prefixCapacityTime_capacity p hi h0 hH T
    (projIcc 0 (initialCapacity p hi h0 hH T)
      (initialCapacity_nonneg p hi h0 hH T) (initialCapacity p hi h0 hH s))
  have ht : prefixCapacityTime p hi h0 hH T
      (projIcc 0 (initialCapacity p hi h0 hH T)
        (initialCapacity_nonneg p hi h0 hH T) (initialCapacity p hi h0 hH s))=s := by
    apply (initialCapacity_strictMono p hi h0 hH).injective
    simpa only [projIcc_of_mem _ hm] using he
  exact congrArg (fun r => initialForwardChart p hi h0 hH r z) ht

theorem capacityForwardOnPrefix_lipschitz (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    LipschitzWith (NNReal.mk ((initialForwardChart p hi h0 hH T z).im)⁻¹
      (inv_nonneg.mpr (le_of_lt (initialForwardChart_im_pos p hi h0 hH T hz))))
      (capacityForwardOnPrefix p hi h0 hH T z) := by
  have hh := (capacityForward_lipschitz p hi h0 hH hT hz).comp
    (LipschitzWith.projIcc (initialCapacity_nonneg p hi h0 hH T))
  unfold capacityForwardOnPrefix
  convert! hh using 1; simp only [_root_.mul_one]

theorem capacityForwardOnPrefix_ae_differentiable (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    ∀ᵐ c : ℝ, DifferentiableAt ℝ (capacityForwardOnPrefix p hi h0 hH T z) c :=
  (capacityForwardOnPrefix_lipschitz p hi h0 hH hT hz).ae_differentiableAt_real

theorem capacityForwardOnPrefix_derivative_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T)) (c : ℝ) :
    ‖deriv (capacityForwardOnPrefix p hi h0 hH T z) c‖≤
      ((initialForwardChart p hi h0 hH T z).im)⁻¹ :=
  norm_deriv_le_of_lipschitz (capacityForwardOnPrefix_lipschitz p hi h0 hH hT hz)

end SLEExactGauge

end

end OAI
