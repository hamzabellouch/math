import OAI.Geometry.RCD.Heat.LocalSmoothLogarithm
import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace OAI

/-! # Local logarithmic calculus for a bounded-gradient weak Laplacian

Only a positive lower bound on the region of interest is needed. The
constructed global Sobolev function agrees there with the logarithm;
its global L² source comes from a smooth scalar extension.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem exists_local_logarithmic_laplacian (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    {Ω : Set X} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hv : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ hQ u x ∈ Icc a b) :
    ∃ (v : SobolevSpace μ hQ) (q : Lp ℝ 2 μ),
      IsWeakLaplacian μ hQ v q ∧
      (SobolevSpace.toLp μ hQ v =ᵐ[μ.restrict Ω]
        fun x => Real.log (SobolevSpace.toLp μ hQ u x)) ∧
      (q =ᵐ[μ.restrict Ω] fun x => d x / SobolevSpace.toLp μ hQ u x -
        localGamma μ hQ u u x / (SobolevSpace.toLp μ hQ u x)^2) ∧
      ∀ w : SobolevSpace μ hQ, localGamma μ hQ v w =ᵐ[μ.restrict Ω]
        fun x => localGamma μ hQ u w x / SobolevSpace.toLp μ hQ u x := by
  obtain ⟨φ,ψ,χ,C,D,B,E,hφ,hψ,hχ,hφ0,hψ0,hdφ,hdψ,hB,hE,he⟩ :=
    exists_local_smooth_log ha hab
  let U := SobolevSpace.toLp μ hQ u
  have hp : MemLp (fun x => ψ (U x)) ∞ μ := memLp_top_of_bound
    (hψ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (U x))
  have hc : MemLp (fun x => χ (U x)) ∞ μ := memLp_top_of_bound
    (hχ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) E
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (U x))
  have hq : MemLp (fun x => ψ (U x)*d x+χ (U x)*localGamma μ hQ u u x) 2 μ :=
    (hp.mul (Lp.memLp d)).add (hc.mul (localGamma_memLp_of_bounded_gradient μ hQ u u L hL))
  let q := hq.toLp _
  have hqe : q =ᵐ[μ] fun x => ψ (U x)*d x+χ (U x)*localGamma μ hQ u u x :=
    hq.coeFn_toLp
  refine ⟨SobolevSpace.comp μ hQ hφ hφ0 u,q,
    weakLaplacian_comp_C2 μ hQ u d q hd hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE hqe,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae (SobolevSpace.comp_coe μ hQ hφ hφ0 u),hv] with x hx hix
    exact hx.trans (he _ hix).1
  · filter_upwards [ae_restrict_of_ae hqe,hv] with x hx hix
    rw [hx,(he _ hix).2.1,(he _ hix).2.2]
    simp only [div_eq_mul_inv]
    ring
  · intro w
    filter_upwards [ae_restrict_of_ae (localGamma_comp_C1 μ hQ u w hφ hφ0
      hψ.continuous hdφ B hB),hv] with x hx hix
    rw [hx,(he _ hix).2.1,div_eq_mul_inv]
    exact mul_comm _ _

end RegularPointCoordinates

end

end OAI
