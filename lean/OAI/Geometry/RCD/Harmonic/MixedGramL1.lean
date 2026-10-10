import OAI.Geometry.RCD.Sobolev.SobolevQuadraticEnergy
import OAI.Geometry.RCD.Harmonic.WeightedCoreConvergence

namespace OAI

/-! # Three unit-direction energy limits identify each mixed Gram entry -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem mixed_defect_le {a b c p : ℝ} (h : 2*p=a+2*c+b) :
    |c|≤|p-1|+|a-1|+|b-1| := by
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self (p-1),neg_le_abs (p-1),
    le_abs_self (a-1),neg_le_abs (a-1),le_abs_self (b-1),neg_le_abs (b-1),
    abs_nonneg (a-1),abs_nonneg (b-1)]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem mixed_gram_l1_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (A : ℕ → Set X) (hfin : ∀ k, μ (A k)≠⊤) (r c : ℕ → ℝ) (hc : ∀ k, 0≤c k)
    (f g : ℕ → SobolevSpace μ hQ)
    (hf : Tendsto (fun k => c k*∫ x in A k, |r k^2*localGamma μ hQ (f k) (f k) x-1| ∂μ)
      atTop (𝓝 0))
    (hg : Tendsto (fun k => c k*∫ x in A k, |r k^2*localGamma μ hQ (g k) (g k) x-1| ∂μ)
      atTop (𝓝 0))
    (hp : Tendsto (fun k => c k*∫ x in A k,
      |r k^2*localGamma μ hQ ((Real.sqrt 2)⁻¹ • (f k+g k)) ((Real.sqrt 2)⁻¹ • (f k+g k)) x-1| ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in A k, |r k^2*localGamma μ hQ (f k) (g k) x| ∂μ)
      atTop (𝓝 0) := by
  let q := fun k => (Real.sqrt 2)⁻¹ • (f k+g k)
  have hcoef : ((Real.sqrt 2)⁻¹)^2=(1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hpair (k : ℕ) : ∀ᵐ x ∂μ,
      2*(r k^2*localGamma μ hQ (q k) (q k) x)=
        r k^2*localGamma μ hQ (f k) (f k) x+
        2*(r k^2*localGamma μ hQ (f k) (g k) x)+r k^2*localGamma μ hQ (g k) (g k) x := by
    have ha := localGamma_add_smul_square μ hQ (f k) (g k) 1
    simp only [one_smul,one_pow,mul_one,one_mul] at ha
    filter_upwards [localGamma_smul_left μ hQ (Real.sqrt 2)⁻¹ (f k+g k) (q k),
      localGamma_smul_right μ hQ (Real.sqrt 2)⁻¹ (f k+g k) (f k+g k),ha] with x hl hr hh
    change 2*(r k^2*localGamma μ hQ ((Real.sqrt 2)⁻¹ • (f k+g k)) (q k) x)=_
    rw [hl,hr,hh]
    linear_combination (2*r k^2*(localGamma μ hQ (f k) (f k) x+
      2*localGamma μ hQ (f k) (g k) x+localGamma μ hQ (g k) (g k) x))*hcoef
  have hi (u : ℕ → SobolevSpace μ hQ) (k : ℕ) :
      IntegrableOn (fun x => |r k^2*localGamma μ hQ (u k) (u k) x-1|) (A k) μ :=
    (((localGamma_memL1 μ hQ (u k) (u k)).const_mul (r k^2)).integrableOn.sub
      (integrableOn_const (hfin k))).abs
  have hlim := hp.add (hf.add hg)
  simp only [add_zero] at hlim
  apply squeeze_zero (fun k => mul_nonneg (hc k) (integral_nonneg (fun x => abs_nonneg _))) _ hlim
  intro k
  have hupper := integral_mono_ae
    (((localGamma_memL1 μ hQ (f k) (g k)).const_mul (r k^2)).abs.integrableOn)
    ((hi q k).add ((hi f k).add (hi g k))) (by
      filter_upwards [ae_restrict_of_ae (hpair k)] with x hx
      simpa only [Pi.add_apply,add_assoc] using mixed_defect_le hx)
  have hadd := integral_add (hi q k) ((hi f k).add (hi g k))
  have hadd' := integral_add (hi f k) (hi g k)
  simp only [Pi.add_apply] at hupper hadd hadd'
  rw [hadd,hadd'] at hupper
  have hh := mul_le_mul_of_nonneg_left hupper (hc k)
  simpa only [Pi.add_apply,mul_add,add_assoc] using hh

end RegularPointCoordinates

end

end OAI
