import OAI.Geometry.RCD.Harmonic.BoundedTransversePotentials
import OAI.Geometry.RCD.Harmonic.BoundedTransverseFormula
import OAI.Geometry.RCD.Coordinates.TransverseCoordinateDefect
import OAI.Geometry.RCD.Harmonic.TransverseIntegralBound

namespace OAI

/-! # The quantitative barrier built from the actual bounded harmonic frame -/

open Set Filter MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem bounded_frame_transverse_barrier {n : ℕ}
    (u : Fin n → SobolevSpace μ Q) (A : Fin n → ℝ≥0)
    (hA : ∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (u i) x|≤A i)
    {Ω : Set X} (hΩ : IsOpen Ω) (hfin : μ Ω≠∞)
    (v : X → Euclidean n)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict Ω] fun x => v x i)
    (hh : ∀ i, IsSobolevHarmonicOn μ Q Ω (u i))
    (a : Euclidean n) (ha : ‖a‖=1) {M c : ℝ} (hM : 0≤M) (hc : 0≤c)
    (hvM : ∀ x∈Ω, ‖v x‖≤M) (δ : ℝ)
    (η : SobolevSpace μ Q)
    (hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q η x|≤(1:ℝ≥0))
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (χsob : SobolevSpace μ Q) {χ : X → ℝ} {L : ℝ≥0}
    (hχ : LipschitzWith L χ) (hχc : HasCompactSupport χ)
    (hχb : ∀ x, |χ x|≤(1:ℝ≥0)) (hχ0 : ∀ x, 0≤χ x)
    (hχs : tsupport χ⊆Ω) (hχrep : SobolevSpace.toLp μ Q χsob =ᵐ[μ] χ)
    (hplateau : ∀ x∈Ω, -δ<⟪v x,a⟫_ℝ → ‖v x‖^2-⟪v x,a⟫_ℝ^2<c → χ x=1) :
    IntegrableOn (fun x => if -δ<⟪v x,a⟫_ℝ then max (c-(‖v x‖^2-⟪v x,a⟫_ℝ^2)) 0 else 0) Ω μ ∧
    (∫ x in Ω, (if -δ<⟪v x,a⟫_ℝ then max (c-(‖v x‖^2-⟪v x,a⟫_ℝ^2)) 0 else 0) ∂μ) ≤
      (c+(M+|δ|)*2*((n:ℝ)+1)*M)*∫ x in Ω, gramDefect μ Q u x ∂μ := by
  let W x := ⟪v x,a⟫_ℝ
  let S x := ‖v x‖^2-(W x)^2
  obtain ⟨w,s,B,D,hwb,hsb,hw,hs,hwh,hwdef,hsdef⟩ :=
    bounded_transverse_potentials μ Q u A hA Ω v hu hh a
  obtain ⟨f,hf,hfw⟩ := exists_bounded_transverse_formula μ Q w s η Ω W S B D 1
    hwb hsb hηb hw hs hη δ c
  have hww : ∀ᵐ x ∂μ.restrict Ω, |localGamma μ Q w w x-1|≤gramDefect μ Q u x := by
    simpa only [hwdef,ha,one_pow,mul_one] using
      ae_restrict_of_ae (localGamma_column_defect μ Q u a)
  have hsw : ∀ᵐ x ∂μ.restrict Ω,
      |localGamma μ Q s w x|≤2*((n:ℝ)+1)*‖v x‖*gramDefect μ Q u x := by
    simpa only [hsdef,hwdef] using localGamma_transverse_defect μ Q u A hA Ω v hu a ha B
      (by simpa only [hwdef] using hwb)
  let C := c+(M+|δ|)*2*((n:ℝ)+1)*M
  have hC : 0≤C := by dsimp [C]; positivity
  have hEI : IntegrableOn (fun x => C*gramDefect μ Q u x) Ω μ :=
    (gramDefect_integrableOn μ Q u hfin).const_mul C
  have hE0 (x : X) : 0≤C*gramDefect μ Q u x := mul_nonneg hC (gramDefect_nonneg μ Q u x)
  have herror : ∀ᵐ x ∂μ.restrict Ω,
      |localGamma μ Q f w x-(if -δ<W x then max (c-S x) 0 else 0)|≤C*gramDefect μ Q u x := by
    filter_upwards [hfw,hww,hsw,ae_restrict_mem hΩ.measurableSet] with x hfx hwwx hswx hx
    have hWM : |W x|≤M := by
      exact ((abs_real_inner_le_norm (v x) a).trans_eq (by rw [ha,mul_one])).trans (hvM x hx)
    have hS0 : 0≤S x := by
      have hb := abs_real_inner_le_norm (v x) a
      rw [ha,mul_one] at hb
      dsimp [S,W]
      have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg (v x))).mpr hb
      simpa only [sq_abs] using sub_nonneg.mpr hsq
    rw [hfx]
    apply (transverse_test_error_of_bounds hc hS0 hWM).trans
    have hs' := hswx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hvM x hx) (by positivity : 0≤2*((n:ℝ)+1)))
      (gramDefect_nonneg μ Q u x))
    calc
      _≤c*gramDefect μ Q u x+(M+|δ|)*(2*((n:ℝ)+1)*M*gramDefect μ Q u x) :=
        add_le_add (mul_le_mul_of_nonneg_left hwwx hc)
          (mul_le_mul_of_nonneg_left hs' (by positivity))
      _=C*gramDefect μ Q u x := by dsimp [C]; ring
  have hWm : AEStronglyMeasurable W (μ.restrict Ω) :=
    ((Lp.aestronglyMeasurable (SobolevSpace.toLp μ Q w)).restrict).congr hw
  have hSm : AEStronglyMeasurable S (μ.restrict Ω) :=
    ((Lp.aestronglyMeasurable (SobolevSpace.toLp μ Q s)).restrict).congr hs
  have hJ : Measurable (fun z : ℝ×ℝ => if -δ<z.1 then max (c-z.2) 0 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      ((measurable_const.sub measurable_snd).max measurable_const) measurable_const
  have hI : AEStronglyMeasurable (fun x => if -δ<W x then max (c-S x) 0 else 0) (μ.restrict Ω) :=
    (hJ.comp_aemeasurable (hWm.aemeasurable.prodMk hSm.aemeasurable)).aestronglyMeasurable
  have hb := (harmonic_transverse_integral_bound μ Q w f χsob hΩ hwh W S δ c hf
    hχ hχc hχb hχ0 hχs hχrep hplateau hI (fun x => C*gramDefect μ Q u x)
    hEI (Eventually.of_forall hE0) herror)
  refine ⟨hb.1,?_⟩
  have hi := hb.2
  rw [integral_const_mul] at hi
  exact hi

end RegularPointCoordinates

end

end OAI
