import OAI.Geometry.RCD.Heat.LocalLogarithmicLaplacian

namespace OAI

/-! # Bounded Lipschitz logarithmic extensions with their actual source -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem bounded_local_logarithm (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (F : X → ℝ) {L A : ℝ≥0}
    (hF : LipschitzWith L F) (hA : ∀ x, |F x|≤A)
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ] F)
    {Ω : Set X} {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hv : ∀ᵐ x ∂μ.restrict Ω, F x∈Icc a b) :
    ∃ (v : SobolevSpace μ Q) (q : Lp ℝ 2 μ) (V : X → ℝ) (M B : ℝ≥0),
      IsWeakLaplacian μ Q v q ∧ LipschitzWith M V ∧
      (∀ x, |V x|≤B) ∧ (SobolevSpace.toLp μ Q v =ᵐ[μ] V) ∧
      (SobolevSpace.toLp μ Q v =ᵐ[μ.restrict Ω] fun x => Real.log (F x)) := by
  obtain ⟨φ,ψ,χ,C,D,B,E,hφ,hψ,hχ,hφ0,hψ0,hdφ,hdψ,hB,hE,he⟩ :=
    exists_local_smooth_log ha hab
  let U := SobolevSpace.toLp μ Q u
  have hp : MemLp (fun x => ψ (U x)) ∞ μ := memLp_top_of_bound
    (hψ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (U x))
  have hc : MemLp (fun x => χ (U x)) ∞ μ := memLp_top_of_bound
    (hχ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) E
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (U x))
  have hL := SobolevSpace.minimalSlope_le_lipschitz μ Q u hF hu
  have hq : MemLp (fun x => ψ (U x)*d x+χ (U x)*localGamma μ Q u u x) 2 μ :=
    (hp.mul (Lp.memLp d)).add (hc.mul (localGamma_memLp_of_bounded_gradient μ Q u u L hL))
  let q := hq.toLp _
  let v := SobolevSpace.comp μ Q hφ hφ0 u
  have hrep : SobolevSpace.toLp μ Q v =ᵐ[μ] fun x => φ (F x) := by
    filter_upwards [SobolevSpace.comp_coe μ Q hφ hφ0 u,hu] with x hx hy
    exact hx.trans (congrArg φ hy)
  refine ⟨v,q,φ ∘ F,C*L,C*A,
    weakLaplacian_comp_C2 μ Q u d q hd hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE hq.coeFn_toLp,
    hφ.comp hF,?_,hrep,?_⟩
  · intro x
    have hh := hφ.dist_le_mul (F x) 0
    simp only [hφ0,Real.dist_eq,sub_zero] at hh
    exact hh.trans (by simpa only [NNReal.coe_mul] using
      mul_le_mul_of_nonneg_left (hA x) C.coe_nonneg)
  · filter_upwards [ae_restrict_of_ae hrep,hv] with x hx hy
    exact hx.trans (he (F x) hy).1

end RegularPointCoordinates

end

end OAI
