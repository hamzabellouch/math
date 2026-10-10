import OAI.Geometry.RCD.Sobolev.TransverseCutoffFlux
import OAI.Geometry.RCD.Sobolev.TransverseTestError

namespace OAI

/-! # A quantitative transverse barrier from the exact compact zero flux -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem harmonic_transverse_integral_bound
    (w f η : SobolevSpace μ Q) {Ω : Set X} (hΩ : IsOpen Ω)
    (hw : IsSobolevHarmonicOn μ Q Ω w) (W S : X → ℝ) (δ c : ℝ)
    (hf : SobolevSpace.toLp μ Q f =ᵐ[μ.restrict Ω]
      fun x => max (W x+δ) 0*max (c-S x) 0)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x|≤(1:ℝ≥0)) (hn : ∀ x, 0≤χ x)
    (hsΩ : tsupport χ⊆Ω) (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] χ)
    (hplateau : ∀ x∈Ω, -δ<W x → S x<c → χ x=1)
    (hI : AEStronglyMeasurable (fun x => if -δ<W x then max (c-S x) 0 else 0) (μ.restrict Ω))
    (E : X → ℝ) (hE : IntegrableOn E Ω μ) (hE0 : ∀ᵐ x ∂μ.restrict Ω, 0≤E x)
    (herror : ∀ᵐ x ∂μ.restrict Ω,
      |localGamma μ Q f w x-(if -δ<W x then max (c-S x) 0 else 0)|≤E x) :
    IntegrableOn (fun x => if -δ<W x then max (c-S x) 0 else 0) Ω μ ∧
      (∫ x in Ω, (if -δ<W x then max (c-S x) 0 else 0) ∂μ) ≤ ∫ x in Ω, E x ∂μ := by
  let I x := if -δ<W x then max (c-S x) 0 else 0
  let F x := χ x*localGamma μ Q f w x
  obtain ⟨hF,hF0⟩ := harmonic_transverse_cutoff_flux μ Q w f η hΩ hw W S δ c
    hf hχ hs hb hn hsΩ hη hplateau
  have hI0 (x : X) : 0≤I x := by dsimp [I]; split_ifs <;> positivity
  have hbound : ∀ᵐ x ∂μ.restrict Ω, I x≤F x+E x := by
    filter_upwards [herror,hE0,ae_restrict_mem hΩ.measurableSet] with x hx hEx hxΩ
    have hχ1 : χ x≤1 := (le_abs_self _).trans (hb x)
    have hχI : χ x*I x=I x := by
      dsimp [I]
      by_cases hax : -δ<W x
      · by_cases hsx : S x<c
        · rw [ite_eq_left hax,hplateau x hxΩ hax hsx,one_mul]
        · rw [ite_eq_left hax,max_eq_right (by linarith : c-S x≤0),mul_zero]
      · rw [ite_eq_right hax,mul_zero]
    have hi : I x-localGamma μ Q f w x≤E x := by
      exact (le_abs_self _).trans (by simpa only [abs_sub_comm,I] using hx)
    have hm := mul_le_mul_of_nonneg_left hi (hn x)
    have he := mul_le_mul_of_nonneg_right hχ1 hEx
    dsimp [F]
    rw [mul_sub,hχI] at hm
    linarith
  have hInt : IntegrableOn I Ω μ := by
    apply (hF.norm.add hE).mono' hI
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (hI0 x)]
    exact hx.trans (add_le_add (le_abs_self _) le_rfl)
  refine ⟨hInt,?_⟩
  have hi := integral_mono_ae hInt (hF.add hE) hbound
  simp only [Pi.add_apply] at hi
  rw [integral_add hF hE,hF0,zero_add] at hi
  exact hi

end RegularPointCoordinates

end

end OAI
