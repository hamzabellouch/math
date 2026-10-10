import OAI.Probability.SLE.Loewner.CapacityRightLoewner
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace OAI

/-! At every differentiability point the real time derivative is the
identified Loewner kernel. Lipschitz regularity then gives the a.e. ODE. -/
noncomputable section
open Set Filter Function Complex MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem capacityForward_deriv_at_capacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s T : unitInterval} (hsT : s<T) (hT : T<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p T))
    (hd : DifferentiableAt ℝ (capacityForwardOnPrefix p hi h0 hH T z)
      (initialCapacity p hi h0 hH s)) :
    deriv (capacityForwardOnPrefix p hi h0 hH T z) (initialCapacity p hi h0 hH s)=
      1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)) := by
  have hcap := initialCapacity_strictMono p hi h0 hH hsT
  have hr : HasDerivWithinAt (capacityForwardOnPrefix p hi h0 hH T z)
      (1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)))
      (Ioi (initialCapacity p hi h0 hH s)) (initialCapacity p hi h0 hH s) := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
    have hh := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
      (capacityForward_hasDerivWithinAt_right p hi h0 hH hsT hT hz)
    rwa [nhdsWithin_Ioc_eq_nhdsGT hcap] at hh
  have hu := uniqueDiffOn_Ici (initialCapacity p hi h0 hH s)
    (initialCapacity p hi h0 hH s) (Set.mem_Ici.mpr le_rfl)
  exact (hd.hasDerivAt.hasDerivWithinAt.derivWithin hu).symm.trans
    (hr.Ici_of_Ioi.derivWithin hu)

lemma capacityParameterOnPrefix_le (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (c : ℝ) : capacityParameterOnPrefix p hi h0 hH T c≤T :=
  prefixCapacityTime_le p hi h0 hH T _

noncomputable def capacityDriverOnPrefix (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (hT : T<1) (c : ℝ) : ℝ :=
  initialDrivingValue p hi h0 hH (capacityParameterOnPrefix p hi h0 hH T c)
    ((capacityParameterOnPrefix_le p hi h0 hH T c).trans_lt hT)

theorem capacityForward_ae_loewner (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    ∀ᵐ c : ℝ, c∈Ico 0 (initialCapacity p hi h0 hH T) →
      deriv (capacityForwardOnPrefix p hi h0 hH T z) c=
        1/(capacityForwardOnPrefix p hi h0 hH T z c-
          (capacityDriverOnPrefix p hi h0 hH T hT c:ℂ)) := by
  filter_upwards [capacityForwardOnPrefix_ae_differentiable p hi h0 hH hT hz] with c hd hc
  let s := capacityParameterOnPrefix p hi h0 hH T c
  have hcap : initialCapacity p hi h0 hH s=c :=
    capacityParameterOnPrefix_capacity p hi h0 hH T ⟨hc.1,hc.2.le⟩
  have hsT : s<T := (initialCapacity_strictMono p hi h0 hH).lt_iff_lt.mp
    (by rw [hcap]; exact hc.2)
  have hh := capacityForward_deriv_at_capacity p hi h0 hH hsT hT hz
    (by rwa [hcap])
  rw [hcap] at hh
  rw [← capacityForwardOnPrefix_at_initialCapacity p hi h0 hH T z hsT.le,hcap] at hh
  exact hh

end SLEExactGauge

end

end OAI
