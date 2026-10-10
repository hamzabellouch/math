import OAI.Geometry.RCD.Harmonic.MixedGramL1

namespace OAI

/-! # Gram convergence determines the energy of sum directions -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem sum_energy_l1_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (A : ℕ → Set X) (hfin : ∀ k, μ (A k) ≠ ⊤) (r c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (f g : ℕ → SobolevSpace μ hQ) (a b d : ℝ)
    (hf : Tendsto (fun k => c k*∫ x in A k, |r k^2*localGamma μ hQ (f k) (f k) x-a| ∂μ)
      atTop (𝓝 0))
    (hfg : Tendsto (fun k => c k*∫ x in A k, |r k^2*localGamma μ hQ (f k) (g k) x-b| ∂μ)
      atTop (𝓝 0))
    (hg : Tendsto (fun k => c k*∫ x in A k, |r k^2*localGamma μ hQ (g k) (g k) x-d| ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in A k,
      |r k^2*localGamma μ hQ (f k+g k) (f k+g k) x-(a+2*b+d)| ∂μ) atTop (𝓝 0) := by
  let e := fun k (u v : SobolevSpace μ hQ) (a : ℝ) x => |r k^2*localGamma μ hQ u v x-a|
  have hi (k : ℕ) (u v : SobolevSpace μ hQ) (a : ℝ) : IntegrableOn (e k u v a) (A k) μ :=
    (((localGamma_memL1 μ hQ u v).const_mul (r k^2)).integrableOn.sub
      (integrableOn_const (hfin k))).abs
  have hlim := (hf.add (hfg.const_mul 2)).add hg
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero (fun k => mul_nonneg (hc k) (integral_nonneg fun _ => abs_nonneg _)) _ hlim
  intro k
  have hquad := localGamma_add_smul_square μ hQ (f k) (g k) 1
  simp only [one_smul,one_pow,mul_one,one_mul] at hquad
  have hb : ∀ᵐ x ∂μ.restrict (A k), e k (f k+g k) (f k+g k) (a+2*b+d) x ≤
      e k (f k) (f k) a x+2*e k (f k) (g k) b x+e k (g k) (g k) d x := by
    filter_upwards [ae_restrict_of_ae hquad] with x hx
    dsimp only [e]
    rw [hx]
    have he : r k^2*(localGamma μ hQ (f k) (f k) x+2*localGamma μ hQ (f k) (g k) x+
        localGamma μ hQ (g k) (g k) x)-(a+2*b+d) =
        (r k^2*localGamma μ hQ (f k) (f k) x-a)+2*(r k^2*localGamma μ hQ (f k) (g k) x-b)+
          (r k^2*localGamma μ hQ (g k) (g k) x-d) := by ring
    rw [he]
    let A := r k^2*localGamma μ hQ (f k) (f k) x-a
    let B := r k^2*localGamma μ hQ (f k) (g k) x-b
    let D := r k^2*localGamma μ hQ (g k) (g k) x-d
    change |A+2*B+D| ≤ |A|+2*|B|+|D|
    calc
      _ ≤ |A+2*B|+|D| := abs_add_le _ _
      _ ≤ (|A|+|2*B|)+|D| := by linarith [abs_add_le A (2*B)]
      _ = _ := by rw [abs_mul]; norm_num
  have hI := integral_mono_ae (hi k _ _ _) (((hi k _ _ _).add ((hi k _ _ _).const_mul 2)).add (hi k _ _ _)) hb
  simp only [Pi.add_apply] at hI
  have hfirst := integral_add (hi k (f k) (f k) a) ((hi k (f k) (g k) b).const_mul 2)
  have hsecond := integral_add ((hi k (f k) (f k) a).add ((hi k (f k) (g k) b).const_mul 2))
    (hi k (g k) (g k) d)
  simp only [Pi.add_apply] at hfirst hsecond
  rw [hsecond,hfirst,integral_const_mul] at hI
  simpa only [mul_add,mul_left_comm (c k) 2] using mul_le_mul_of_nonneg_left hI (hc k)

end RegularPointCoordinates

end

end OAI
