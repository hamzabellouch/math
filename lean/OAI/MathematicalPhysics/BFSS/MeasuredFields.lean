import Mathlib
import OAI.MathematicalPhysics.BFSS.CoreCompactness
import OAI.MathematicalPhysics.BFSS.SmallPatches

namespace OAI

/-! Measured normal fields with uniform moment and derivative bounds. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] gaugeAction normalSlice coreToL2 normalCoreField

def normalMeasuredField (q : Boson N) (h : ℝ) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (f : SmoothCore N) : M.normalSlice q → Fermion N :=
  fun z => Real.sqrt (J (h • z) * φ (q+h • (z : Boson N))) • M.normalCoreField q h f z

lemma normalMeasuredField_continuous (q : Boson N) (h : ℝ) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (f : SmoothCore N) (hJ : Continuous J) (hφ : Continuous φ) :
    Continuous (M.normalMeasuredField q h J φ f) := by
  have hz : Continuous (fun z : M.normalSlice q => h • z) :=
    (continuous_const : Continuous (fun _ : M.normalSlice q => h)).smul continuous_id
  have hx : Continuous (fun z : M.normalSlice q => q+h • (z : Boson N)) :=
    continuous_const.add ((continuous_const : Continuous (fun _ : M.normalSlice q => h)).smul continuous_subtype_val)
  have hw : Continuous (fun z : M.normalSlice q => Real.sqrt (J (h • z)*φ (q+h • (z : Boson N)))) :=
    ((hJ.comp hz).mul (hφ.comp hx)).sqrt
  exact Continuous.smul (M := ℝ) (X := Fermion N) hw (M.normalCoreField_contDiff q h f).continuous

lemma normalMeasuredField_compactSupport (q : Boson N) (h : ℝ) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.normalMeasuredField q h J φ f) := by
  change HasCompactSupport ((fun z : M.normalSlice q => Real.sqrt (J (h • z) * φ (q+h • (z : Boson N)))) • M.normalCoreField q h f)
  exact (M.normalCoreField_compactSupport q h f).smul_left

lemma normalMeasuredField_norm_sq (q : Boson N) {h : ℝ} (hh : 0 < h)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N)
    (hJ : ∀ z, 0 ≤ J z) (hφ : ∀ x, 0 ≤ φ x) (z : M.normalSlice q) :
    ‖M.normalMeasuredField q h J φ f z‖^2 =
      (h ^ M.orbitDimension q)⁻¹ * (J (h • z) *
        (φ (h • (h⁻¹ • q+(z : Boson N))) * ‖f (h⁻¹ • q+(z : Boson N))‖^2)) := by
  have he : h • (h⁻¹ • q+(z : Boson N)) = q+h • (z : Boson N) := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  rw [normalMeasuredField,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow,Real.sq_sqrt (mul_nonneg (hJ _) (hφ _)),M.normalCoreField_norm_sq q hh,he]
  ring

attribute [local irreducible] normalMeasuredField

lemma normalMeasuredField_square_integrable (q : Boson N) (h : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N)
    (hJ : Continuous J) (hφ : Continuous φ) :
    Integrable (fun z => ‖M.normalMeasuredField q h J φ f z‖^2) := by
  exact BFSSNormalMeasure.square_integrable _ (M.normalMeasuredField_continuous q h J φ f hJ hφ)
    (M.normalMeasuredField_compactSupport q h J φ f)

lemma normalMeasuredField_moment_integrable (q : Boson N) (h : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N)
    (hJ : Continuous J) (hφ : Continuous φ) :
    Integrable (fun z => ‖z‖^2 * ‖M.normalMeasuredField q h J φ f z‖^2) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow 2).mul ((M.normalMeasuredField_continuous q h J φ f hJ hφ).norm.pow 2)
  · exact (BFSSNormalMeasure.square_compact _ (M.normalMeasuredField_compactSupport q h J φ f)).mul_left

lemma normalMeasuredField_tail_moment (q : Boson N) (h : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N)
    (hJ : Continuous J) (hφ : Continuous φ) (R : ℝ) (hR : 0 ≤ R) :
    R^2 * (∫ z : M.normalSlice q in {z | R < ‖z‖}, ‖M.normalMeasuredField q h J φ f z‖^2) ≤
      ∫ z : M.normalSlice q, ‖z‖^2 * ‖M.normalMeasuredField q h J φ f z‖^2 := by
  have hi := M.normalMeasuredField_square_integrable q h J φ f hJ hφ
  have hm := M.normalMeasuredField_moment_integrable q h J φ f hJ hφ
  rw [←integral_const_mul]
  apply (setIntegral_mono_on (hi.const_mul _).integrableOn hm.integrableOn
    (measurableSet_lt measurable_const measurable_norm) ?_).trans
  · exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm
  · intro z hz
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hz.le 2) (sq_nonneg _)
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open Matrix MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.gaugeAction AlgebraData.normalSlice AlgebraData.normalMeasuredField AlgebraData.normalCoreField coreToL2

theorem normalMeasuredCore_uniform_bounds (hN : 2 ≤ N) (q : Boson N) (hq : q ∈ M.massiveZeros) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)) (c K : ℝ),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧
      (∀ U : M.gaugeStabilizer q, ∀ z, J (M.stabilizerNormalIsometry q U z) = J z) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      (∀ (h : ℝ), 0 < h → ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
        (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
        (∀ x ∈ Function.support F, h • x ∈ V) →
        (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
          ∫ z : M.normalSlice q, J (h • z) * F (h⁻¹ • q+(z : Boson N))) ∧
      0 < c ∧ 0 ≤ K ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ φ : Boson N → ℝ,
        Continuous φ → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
        (∀ U : unitary (ColorMatrix N), ∀ x, φ (M.gaugeAction U x) = φ x) →
        Function.support φ ⊆ V → ∀ f : G.invariantCore,
        (∫ z, ‖M.normalMeasuredField q h J φ f.val z‖^2) =
          ∫ x, φ (h • x)*‖f.val x‖^2 ∧
        (∫ z, ‖M.normalMeasuredField q h J φ f.val z‖^2) ≤ ‖coreToL2 f.val‖^2 ∧
        c/2 * (∫ z : M.normalSlice q, ‖z‖^2*‖M.normalMeasuredField q h J φ f.val z‖^2) ≤
          M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2 ∧
        ∀ R : ℝ, 0 ≤ R → c/2*R^2 *
          (∫ z : M.normalSlice q in {z | R < ‖z‖}, ‖M.normalMeasuredField q h J φ f.val z‖^2) ≤
          M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2 := by
  obtain ⟨J,V,δ,hJ,hJn,hJ0,hδ,hδJ,hJi,hV,hqV,hVi,hm⟩ := M.normalOrbit_norm_moment hN q hq
  obtain ⟨c,K,hc,hK,hform⟩ := M.massive_core_uniform_distance hN
  have hm₀ := fun h hh F hF hFK hFi hFs => (hm h hh F hF hFK hFi hFs).1
  refine ⟨J,V,c,K,hJ,hJn,hJ0,hJi,hV,hqV,hVi,hm₀,hc,hK,?_⟩
  intro h hh h1 φ hφ hφb hφi hφs f
  let F : Boson N → ℝ := fun x => φ (h • x)*‖f.val x‖^2
  have hsmul : Continuous (fun x : Boson N => h • x) :=
    (continuous_const : Continuous (fun _ : Boson N => h)).smul continuous_id
  have hFc : Continuous F := (hφ.comp hsmul).mul (f.val.continuous.norm.pow 2)
  have hFK : HasCompactSupport F := (f.val.hasCompactSupport.comp_left (g := fun x : Fermion N => ‖x‖^2) (by simp)).mul_left
  have hFi (U : unitary (ColorMatrix N)) (x : Boson N) : F (M.gaugeAction U x) = F x := by
    dsimp [F]
    rw [←M.gaugeAction_smul,hφi,G.invariantCore_norm_unitary hN]
  have hFs (x : Boson N) (hx : x ∈ Function.support F) : h • x ∈ V := by
    apply hφs
    intro hz
    exact hx (by simp only [F,hz,zero_mul])
  obtain ⟨hm0,hm2⟩ := hm h hh F hFc hFK hFi hFs
  have hn : (∫ z, ‖M.normalMeasuredField q h J φ f.val z‖^2) = ∫ x, F x := by
    simp_rw [M.normalMeasuredField_norm_sq q hh J φ f.val hJn (fun x => (hφb x).1)]
    rw [integral_const_mul]
    exact hm0.symm
  have hmom : (∫ z : M.normalSlice q, ‖z‖^2*‖M.normalMeasuredField q h J φ f.val z‖^2) =
      ∫ x, (M.massiveDistance h x)^2 * F x := by
    calc
      _ = (h ^ M.orbitDimension q)⁻¹ *
          ∫ z : M.normalSlice q, ‖z‖^2*(J (h • z)*F (h⁻¹ • q+(z : Boson N))) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        rw [M.normalMeasuredField_norm_sq q hh J φ f.val hJn (fun x => (hφb x).1)]
        dsimp [F]
        ring
      _ = _ := hm2.symm
  have hFi' : Integrable F := hFc.integrable_of_hasCompactSupport hFK
  have hnorm : (∫ x, F x) ≤ ‖coreToL2 f.val‖^2 := by
    rw [coreToL2_norm_sq]
    apply integral_mono hFi' (coreNormSq_integrable f.val)
    intro x
    exact mul_le_of_le_one_left (sq_nonneg _) (hφb _).2
  have hMI : Integrable (fun x => (M.massiveDistance h x)^2*F x) :=
    (((M.massiveDistance_continuous h).pow 2).mul hFc).integrable_of_hasCompactSupport hFK.mul_left
  have hmoment : (∫ x, (M.massiveDistance h x)^2*F x) ≤
      ∫ x, (M.massiveDistance h x)^2*‖f.val x‖^2 := by
    apply integral_mono hMI (weighted_core_square_integrable _ ((M.massiveDistance_continuous h).pow 2) f.val)
    intro x
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg _) (hφb _).2) (sq_nonneg _)
  have hbound : c/2 * (∫ z : M.normalSlice q, ‖z‖^2*‖M.normalMeasuredField q h J φ f.val z‖^2) ≤
      M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2 := by
    rw [hmom]
    have hb := hform h hh h1 f.val
    have hgrad : 0 ≤ (1/2 : ℝ)* ∑ p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f.val)‖^2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hmoment (by positivity)).trans
      (le_of_add_le_of_nonneg_right hb hgrad)
  refine ⟨hn,hn.trans_le hnorm,hbound,?_⟩
  intro R hR
  have ht := M.normalMeasuredField_tail_moment q h J φ f.val hJ hφ R hR
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ c/2 by positivity)
  rw [←mul_assoc] at ht'
  exact ht'.trans hbound
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
