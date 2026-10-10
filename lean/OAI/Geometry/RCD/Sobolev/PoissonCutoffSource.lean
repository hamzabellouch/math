import OAI.Geometry.RCD.Sobolev.CutoffPoissonLaplacian
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # Separating the bounded and annular parts of a localized Poisson source -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The localized source is the sum of bounded data and an integrable L²
error supported in the cutoff annulus. Both parts are constructed from the
actual weak equation. -/
theorem IsConstantLaplacianOn.cutoff_source_decomposition
    {Ω : Set X} (f : SobolevSpace μ hQ) (c : ℝ)
    (hf : IsConstantLaplacianOn μ hQ Ω f c) (A : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A)
    {p : X} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff μ hQ p R C) (hΩ : closedBall p (2*R) ⊆ Ω) :
    ∃ b e : Lp ℝ 2 μ,
      IsWeakLaplacian μ hQ
        (SobolevSpace.cutoffCLM μ hQ (B := 1) χ.lipschitz (χ.hasCompactSupport μ hQ)
          (fun x => by rw [abs_of_nonneg (χ.bounds x).1]; exact (χ.bounds x).2)
          (fun x => (χ.bounds x).1) f) (b+e) ∧
      (∀ᵐ x ∂μ, |b x| ≤ |c|+A*(C/R^2)) ∧
      Integrable e μ ∧
      (e =ᵐ[μ] fun x => 2*localGamma μ hQ f χ.sobolev x) ∧
      (∀ᵐ x ∂μ, e x ≠ 0 → R ≤ dist x p ∧ dist x p ≤ 2*R) := by
  have habs (x : X) : |χ.weight x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (χ.bounds x).1]
    exact (χ.bounds x).2
  obtain ⟨q,hq,hqrep⟩ := hf.cutoff_weakLaplacian μ hQ f χ.sobolev c
    χ.laplacian χ.weak_laplacian χ.lipschitz (χ.hasCompactSupport μ hQ)
    habs (fun x => (χ.bounds x).1) ((χ.tsupport_subset μ hQ).trans hΩ) χ.representative hA
  have hgrad : ∀ᵐ x ∂μ, localGamma μ hQ χ.sobolev χ.sobolev x ≤ (C/R)^2 := by
    have hh := SobolevSpace.minimalSlope_le_lipschitz μ hQ χ.sobolev χ.lipschitz χ.representative
    filter_upwards [hh,localGamma_self μ hQ χ.sobolev,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ χ.sobolev)] with x hx he h0
    rw [Real.coe_toNNReal _ (div_nonneg hC hR.le)] at hx
    rw [he]
    exact pow_le_pow_left₀ h0 hx 2
  have hm : MemLp (localGamma μ hQ f χ.sobolev) 2 μ := by
    simpa only [Measure.restrict_univ] using
      localGamma_memLp_two_of_bound μ hQ univ f χ.sobolev
        (by simpa only [Measure.restrict_univ] using hgrad)
  let e := (hm.const_mul 2).toLp (fun x => 2*localGamma μ hQ f χ.sobolev x)
  have herep : e =ᵐ[μ] fun x => 2*localGamma μ hQ f χ.sobolev x := MemLp.coeFn_toLp _
  let b := q-e
  have hb : b =ᵐ[μ] fun x => c*χ.weight x+SobolevSpace.toLp μ hQ f x*χ.laplacian x := by
    filter_upwards [Lp.coeFn_sub q e,hqrep,herep] with x hx hqx hex
    change (q-e) x = _
    rw [hx]
    change q x-e x = _
    rw [hqx,hex]
    ring
  refine ⟨b,e,?_,?_,?_,herep,?_⟩
  · have heq : b+e = q := by dsimp [b]; abel
    rw [heq]
    exact hq
  · filter_upwards [hb,hA,χ.laplacian_bound] with x hx ha hd
    rw [hx]
    calc
      _ ≤ |c*χ.weight x|+|SobolevSpace.toLp μ hQ f x*χ.laplacian x| := abs_add_le _ _
      _ ≤ |c|+A*(C/R^2) := by
        rw [abs_mul,abs_mul]
        exact add_le_add ((mul_le_mul_of_nonneg_left (habs x) (abs_nonneg c)).trans_eq (mul_one _))
          (mul_le_mul ha hd (abs_nonneg _) A.coe_nonneg)
  · exact ((localGamma_memL1 μ hQ f χ.sobolev).const_mul 2).congr herep.symm
  · filter_upwards [herep,χ.representative,localGamma_comm μ hQ f χ.sobolev,
      localGamma_zero_on_level μ hQ χ.sobolev f 0,
      localGamma_zero_on_level μ hQ χ.sobolev f 1] with x he hc hcomm hz ho
    intro hne
    constructor
    · by_contra hnot
      have hχ : χ.weight x = 1 := χ.one x (lt_of_not_ge hnot)
      have hg : localGamma μ hQ f χ.sobolev x = 0 := hcomm.trans (ho (hc.trans hχ))
      exact hne (by rw [he,hg,mul_zero])
    · by_contra hnot
      have hχ : χ.weight x = 0 := χ.zero x (by rw [dist_comm]; exact lt_of_not_ge hnot)
      have hg : localGamma μ hQ f χ.sobolev x = 0 := hcomm.trans (hz (hc.trans hχ))
      exact hne (by rw [he,hg,mul_zero])

end RegularPointCoordinates

end

end OAI
