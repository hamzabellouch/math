import OAI.Geometry.RCD.Sobolev.LocalZeroSetCoercivity

namespace OAI

/-! # Local coercivity with the exterior fraction furnished by boundary balls -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

private theorem square_mass_le_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Ω B : Set X} (hfin : μ Ω≠⊤) (hsub : B⊆Ω)
    {A : ℝ} (hA : 0≤A) (hsize : μ.real Ω≤A*μ.real B)
    (u : Lp ℝ 2 μ) (hz : u=ᵐ[μ.restrict B] 0) (c : ℝ) :
    (∫ x in Ω, (u x)^2 ∂μ)≤(2+2*A)*(∫ x in Ω, (u x-c)^2 ∂μ) := by
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hu := (Lp.memLp u).restrict Ω
  have hv : IntegrableOn (fun x => (u x-c)^2) Ω μ := (hu.sub (memLp_const c)).integrable_sq
  have hc : c^2*μ.real B≤∫ x in Ω, (u x-c)^2 ∂μ := by
    calc _ = ∫ x in B, (u x-c)^2 ∂μ := by
           have he : (fun x => (u x-c)^2)=ᵐ[μ.restrict B] (fun _ => c^2) :=
             hz.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
           rw [integral_congr_ae he]
           simp [mul_comm]
         _ ≤ _ := setIntegral_mono_set hv (Filter.Eventually.of_forall fun _ => sq_nonneg _)
           (Filter.Eventually.of_forall hsub)
  have hcm := mul_le_mul_of_nonneg_left hsize (sq_nonneg c)
  have hcA := mul_le_mul_of_nonneg_left hc hA
  have hp := integral_mono_ae hu.integrable_sq ((hv.const_mul 2).add (integrable_const (2*c^2)))
    (Filter.Eventually.of_forall fun x => show (u x)^2≤2*(u x-c)^2+2*c^2 by
      nlinarith [sq_nonneg (u x-2*c)])
  change (∫ x in Ω, (u x)^2 ∂μ)≤(∫ x in Ω, 2*(u x-c)^2+2*c^2 ∂μ) at hp
  rw [integral_add (hv.const_mul 2) (integrable_const (2*c^2)),integral_const_mul,
    integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hp
  simp only [Measure.real] at hcm hcA
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_zero_fraction_coercivity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {κ A : ℝ} (hκ : 0≤κ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : X) (r : ℝ), 0<r → -κ≤K*r^2 →
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
      ∀ B : Set X, B⊆ball p r → (hausdorff n X).real (ball p r)≤A*(hausdorff n X).real B →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic w=ᵐ[(hausdorff n X).restrict B] 0 →
        (∫ x in ball p r, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2 ∂hausdorff n X)≤
          C*r^2*(∫ x in ball p (8*r), localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X) := by
  obtain ⟨C,hC,hP⟩ := hX.localMeanPoincareInput hn κ hκ
  refine ⟨(2+2*A)*C^2,by positivity,?_⟩
  intro p r hr hcurv w B hsub hsize hz
  obtain ⟨c,hc⟩ := hP p r hr hcurv w
  have he := square_mass_le_variance (hausdorff n X) (hX.finiteOnBounded _ isBounded_ball).ne
    hsub hA hsize (SobolevSpace.toLp (hausdorff n X) hX.quadratic w) hz c
  calc _ ≤ (2+2*A)*(∫ x in ball p r,
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x-c)^2 ∂hausdorff n X) := he
       _ ≤ (2+2*A)*((C*r)^2*(∫ x in ball p (8*r),
          localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X)) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
       _ = _ := by ring

end RegularPointCoordinates

end

end OAI
