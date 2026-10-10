import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceNormBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLiftEnergy

namespace OAI

/-! The degree-normalized finite trace extends as a contraction of the
actual energy completions and is a left inverse of the normalized lift. -/
noncomputable section
namespace CubicFirstMoment

local instance primeTraceEnergy_addGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeFiniteEnergy hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeRawTraceEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaFiniteEnergyEmbedding.comp (cubicThetaPrimeTraceFiniteLinear hp)

lemma cubicThetaPrimeRawTraceEnergy_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeRawTraceEnergy hp F‖^2≤
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaPrimeEnergyTest hp F‖^2 := by
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaPrimeEnergy_norm_sq,
    cubicThetaPrimeEnergyInclusion_test,cubicThetaPrimeEnergyDerivative_test]
  change ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeTraceFiniteEnergy hp F)‖^2+
    ‖cubicThetaFiniteEnergyGradient (cubicThetaPrimeTraceFiniteEnergy hp F)‖^2≤_
  calc
    _ ≤ ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaPrimeEnergyValue hp F‖^2+
        ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaPrimeEnergyGradient hp F‖^2 :=
      add_le_add (cubicThetaPrimeTraceFinite_value_norm_sq hp F)
        (cubicThetaPrimeTraceFinite_gradient_norm_sq hp F)
    _ = _ := by ring

def cubicThetaPrimeNormalizedTraceEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  ((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) • cubicThetaPrimeRawTraceEnergy hp

lemma cubicThetaPrimeNormalizedTraceEnergy_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeNormalizedTraceEnergy hp F‖≤‖cubicThetaPrimeEnergyTest hp F‖ := by
  let d : ℝ := (cubicThetaPrimeCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply _root_.le_of_sq_le_sq _ (_root_.norm_nonneg _)
  change ‖((Real.sqrt d)⁻¹:ℂ) • cubicThetaPrimeRawTraceEnergy hp F‖^2≤_
  rw [norm_smul,mul_pow]
  calc
    _ ≤ ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaPrimeEnergyTest hp F‖^2) :=
      mul_le_mul_of_nonneg_left (cubicThetaPrimeRawTraceEnergy_norm_sq hp F) (sq_nonneg _)
    _ = _ := by rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeTraceEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeEnergySpace hp →L[ℂ] cubicThetaGlobalEnergySpace :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (cubicThetaPrimeNormalizedTraceEnergy hp) (cubicThetaPrimeEnergyTest hp)

lemma cubicThetaPrimeTraceEnergy_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    cubicThetaPrimeTraceEnergy hp (cubicThetaPrimeEnergyTest hp F)=
      cubicThetaPrimeNormalizedTraceEnergy hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeNormalizedTraceEnergy hp) (e:=cubicThetaPrimeEnergyTest hp)
    (cubicThetaPrimeEnergyTest_dense hp)
    ⟨1,fun F => by simpa only [one_mul] using cubicThetaPrimeNormalizedTraceEnergy_bound hp F⟩ F

theorem cubicThetaPrimeTraceEnergy_bound {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) : ‖cubicThetaPrimeTraceEnergy hp u‖≤‖u‖ := by
  refine (cubicThetaPrimeEnergyTest_dense hp).induction_on u
    (isClosed_le (cubicThetaPrimeTraceEnergy hp).continuous.norm continuous_norm) ?_
  intro F
  rw [cubicThetaPrimeTraceEnergy_finite]
  exact cubicThetaPrimeNormalizedTraceEnergy_bound hp F

lemma cubicThetaPrimeRawTraceEnergy_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRawTraceEnergy hp (cubicThetaPrimeSmoothEnergyRestriction hp F)=
      ((cubicThetaPrimeCoverGroup hp).index:ℂ) • cubicThetaGlobalEnergyTest F := by
  have he : cubicThetaPrimeTraceFiniteEnergy hp (cubicThetaPrimeSmoothEnergyRestriction hp F)=
      ((cubicThetaPrimeCoverGroup hp).index:ℂ) • cubicThetaSmoothToFiniteEnergy F := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact cubicThetaPrimeTraceSection_restrict hp F.val x
  change cubicThetaFiniteEnergyEmbedding
    (cubicThetaPrimeTraceFiniteEnergy hp (cubicThetaPrimeSmoothEnergyRestriction hp F))=_
  rw [he,map_smul,cubicThetaFiniteEnergyEmbedding_smooth]

theorem cubicThetaPrimeTraceEnergy_lift {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeTraceEnergy hp (cubicThetaPrimeLiftEnergy hp u)=u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeTraceEnergy hp).continuous.comp
      (cubicThetaPrimeLiftEnergy hp).continuous) continuous_id) ?_
  intro F
  change cubicThetaPrimeTraceEnergy hp (cubicThetaPrimeLiftEnergy hp (cubicThetaGlobalEnergyTest F))=_
  rw [cubicThetaPrimeLiftEnergy_smooth]
  change cubicThetaPrimeTraceEnergy hp
    (((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeEnergyTest hp (cubicThetaPrimeSmoothEnergyRestriction hp F))=_
  rw [map_smul,cubicThetaPrimeTraceEnergy_finite]
  change ((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    (((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeRawTraceEnergy hp (cubicThetaPrimeSmoothEnergyRestriction hp F))=_
  rw [cubicThetaPrimeRawTraceEnergy_smooth,smul_smul,smul_smul]
  let d : ℝ := (cubicThetaPrimeCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCoverDegree_pos hp
  have hr : (Real.sqrt d)⁻¹*(Real.sqrt d)⁻¹*d=1 := by
    rw [←pow_two,inv_pow,Real.sq_sqrt hd.le,inv_mul_cancel₀ hd.ne']
  have hc : ((Real.sqrt d)⁻¹:ℂ)*((Real.sqrt d)⁻¹:ℂ)*
      ((cubicThetaPrimeCoverGroup hp).index:ℂ)=1 := by exact_mod_cast hr
  rw [hc,one_smul]
  rfl

end CubicFirstMoment

end

end OAI
