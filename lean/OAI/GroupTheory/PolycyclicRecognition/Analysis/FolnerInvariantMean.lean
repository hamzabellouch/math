import OAI.GroupTheory.PolycyclicRecognition.Analysis.ApproximateInvariantMean
import OAI.GroupTheory.Thompson.FiniteAverage

namespace OAI

/-! # Finite Følner averages yield the invariant mean for height correction -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter
open scoped Topology ENNReal

variable {G : Type*} [Group G] [DecidableEq G]

/-- A literal uniform average over a finite set, as a linear functional on
the actual space of bounded real functions. -/
def finiteMeanState (A : Finset G) : BoundedReal G →ₗ[ℝ] ℝ where
  toFun f := realAvg A f
  map_add' f g := realAvg_add A f g
  map_smul' r f := realAvg_const_mul A r f

omit [Group G] [DecidableEq G] in
theorem finiteMeanState_positive (A : Finset G) (f : BoundedReal G)
    (hf : ∀ g, 0 ≤ f g) : 0 ≤ finiteMeanState A f :=
  realAvg_nonneg A (fun g _ => hf g)

omit [Group G] [DecidableEq G] in
theorem finiteMeanState_one (A : Finset G) (hA : A.Nonempty) :
    finiteMeanState A 1 = 1 := realAvg_const A hA 1

/-- The translation defect is bounded by the actual symmetric-difference
ratio times the norm of the bounded function. -/
theorem finiteMeanState_translation_bound (A : Finset G) (hA : A.Nonempty)
    (g : G) (f : BoundedReal G) :
    |finiteMeanState A (leftPull g f) - finiteMeanState A f| ≤
      boundaryRatio A g * ‖f‖ := by
  by_cases hf : ‖f‖ = 0
  · have hfzero : f = 0 := norm_eq_zero.mp hf
    simp [hfzero, finiteMeanState]
  · have hnorm : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    have hu : ∀ x, |f x / ‖f‖| ≤ 1 := by
      intro x
      rw [abs_div, abs_of_pos hnorm]
      apply (div_le_one hnorm).mpr
      simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f x
    have hh := abs_realAvg_translate_sub_le A hA g (fun x => f x / ‖f‖) hu
    simp only [div_eq_mul_inv, realAvg_mul_const, ← sub_mul, abs_mul, abs_inv,
      abs_of_pos hnorm] at hh
    have hh' : |realAvg A (fun x => f (g * x)) - realAvg A f| / ‖f‖ ≤
        boundaryRatio A g := by simpa only [div_eq_mul_inv] using hh
    exact (div_le_iff₀ hnorm).mp hh'

/-- No countability or finite-generation assumption is required for this
compactness step; each group translation has its own vanishing boundary ratio. -/
theorem exists_invariantMean_of_folner_net
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : ι → Finset G) (hA : ∀ i, (A i).Nonempty)
    (hboundary : ∀ g, Tendsto (fun i => boundaryRatio (A i) g) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_approximate (l := l) (fun i => finiteMeanState (A i))
    (fun i => finiteMeanState_positive (A i)) (fun i => finiteMeanState_one (A i) (hA i))
  intro g f
  apply squeeze_zero_norm
    (fun i => by simpa only [Real.norm_eq_abs] using
      finiteMeanState_translation_bound (A i) (hA i) g f)
  simpa only [zero_mul] using (hboundary g).mul_const ‖f‖

end PolycyclicRecognition

end

end OAI
