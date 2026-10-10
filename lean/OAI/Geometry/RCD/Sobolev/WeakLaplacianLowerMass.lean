import OAI.Geometry.RCD.Sobolev.WeakLaplacianFluxIdentity

namespace OAI

/-! # Local absolute source mass from a one-sided Laplacian bound

The positive test and its exact weak pairing control both signs of the
source. This is used with the uniform lower bounds on scaled heat logs.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem weakLaplacian_lower_weighted_mass (u χ : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (v : X → ℝ)
    (hv : SobolevSpace.toLp μ Q χ =ᵐ[μ] v) (hvi : Integrable v μ)
    (hv0 : ∀ x, 0≤v x) {C : ℝ} (hC : 0≤C)
    (hlower : ∀ᵐ x ∂μ, v x≠0 → -C≤d x) :
    Integrable (fun x => v x*|d x|) μ ∧
      (∫ x, v x*|d x| ∂μ)≤|energyForm μ Q u χ|+2*C*(∫ x, v x ∂μ) := by
  have hi : Integrable (fun x => v x*d x) μ :=
    ((Lp.memLp (SobolevSpace.toLp μ Q χ)).integrable_mul (Lp.memLp d)).congr
      (hv.mono fun x hx => congrArg (fun a => a*d x) hx)
  have hia : Integrable (fun x => v x*|d x|) μ := hi.abs.congr
    (Eventually.of_forall fun x => by
      change |v x*d x|=v x*|d x|
      rw [abs_mul,abs_of_nonneg (hv0 x)])
  have hpair : inner ℝ d (SobolevSpace.toLp μ Q χ)=∫ x, v x*d x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [Real.inner_apply,hx]
    ring
  have he := hd χ
  rw [hpair] at he
  refine ⟨hia,?_⟩
  calc
    (∫ x, v x*|d x| ∂μ) ≤ ∫ x, v x*d x+2*C*v x ∂μ := by
      apply integral_mono_ae hia (hi.add (hvi.const_mul (2*C)))
      filter_upwards [hlower] with x hx
      change v x*|d x|≤v x*d x+2*C*v x
      by_cases hz : v x=0
      · simp only [hz,zero_mul,mul_zero,add_zero]
        exact le_rfl
      · have hdC := hx hz
        have ha : |d x|≤d x+2*C := abs_le.mpr ⟨by linarith,by linarith⟩
        have hh := mul_le_mul_of_nonneg_left ha (hv0 x)
        nlinarith only [hh]
    _ = (∫ x, v x*d x ∂μ)+2*C*(∫ x, v x ∂μ) := by
      rw [integral_add hi (hvi.const_mul (2*C)),integral_const_mul]
    _ ≤ |energyForm μ Q u χ|+2*C*(∫ x, v x ∂μ) := by
      have hh := neg_le_abs (energyForm μ Q u χ)
      linarith only [he,hh]

end RegularPointCoordinates

end

end OAI
