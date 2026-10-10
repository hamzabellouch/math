import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CubeTiling

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeTranslationAverage_scope

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

variable {d : Type*} [Fintype d]

def cubeIndex (x : d → ℝ) : d → ℤ := fun i => ⌊x i⌋

def sameCube (t x y : d → ℝ) : ℝ := if cubeIndex (x-t)=cubeIndex (y-t) then 1 else 0

lemma sameCube_nonneg (t x y : d → ℝ) : 0 ≤ sameCube t x y := by
  unfold sameCube
  split_ifs <;> norm_num

lemma sameCube_le (t x y : d → ℝ) : sameCube t x y ≤ 1 := by
  unfold sameCube
  split_ifs <;> norm_num

omit [Fintype d] in
lemma cubeIndex_measurable : Measurable (cubeIndex (d := d)) :=
  Measurable.of_eval (fun index => Int.measurable_floor.comp (measurable_pi_apply index))

lemma sameCube_measurable : Measurable (fun p : (d → ℝ) × ((d → ℝ) × (d → ℝ)) => sameCube p.1 p.2.1 p.2.2) := by
  unfold sameCube
  exact Measurable.ite (measurableSet_eq_fun
    (cubeIndex_measurable.comp ((measurable_fst.comp measurable_snd).sub measurable_fst))
    (cubeIndex_measurable.comp ((measurable_snd.comp measurable_snd).sub measurable_fst)))
    measurable_const measurable_const

lemma sameCube_t_measurable (x y : d → ℝ) : Measurable (fun t => sameCube t x y) :=
  sameCube_measurable.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))

lemma sameCube_I_integrable (x y : d → ℝ) :
    Integrable (fun t : d → I => sameCube (fun a => (t a:ℝ)) x y) := by
  apply (integrable_const (1:ℝ)).mono'
    ((sameCube_t_measurable x y).comp (Measurable.of_eval (fun index =>
      measurable_subtype_coe.comp (measurable_pi_apply index)))).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    change ‖sameCube (fun a => (t a:ℝ)) x y‖ ≤ 1
    rw [Real.norm_of_nonneg (sameCube_nonneg _ _ _)]; exact sameCube_le _ _ _

lemma cubeChar_sub_cubeShift (x : d → ℝ) (t : d → I) (z : d → ℤ) :
    cubeChar (x-cubeShift z t) = if cubeIndex (x-fun a => (t a:ℝ)) = z then 1 else 0 := by
  have he : x-cubeShift z t ∈ floorCube 0 ↔ cubeIndex (x-fun a => (t a:ℝ))=z := by
    simp only [floorCube,mem_ofPred_eq,cubeShift,Pi.sub_apply,Pi.zero_apply,cubeIndex,
      sub_add_eq_sub_sub_swap,Int.floor_sub_intCast,sub_eq_zero,funext_iff]
  unfold cubeChar
  rw [Set.indicator]
  simp only [he]

lemma sameCube_periodization (t : d → I) (x y : d → ℝ) :
    ENNReal.ofReal (sameCube (fun a => (t a:ℝ)) x y) =
      ∑' z : d → ℤ, ENNReal.ofReal (cubeChar (x-cubeShift z t)*cubeChar (y-cubeShift z t)) := by
  classical
  rw [tsum_eq_single (cubeIndex (x-fun a => (t a:ℝ)))]
  · rw [cubeChar_sub_cubeShift,cubeChar_sub_cubeShift]
    simp only [ite_true,one_mul]
    unfold sameCube
    simp only [eq_comm]
  · intro z hz
    rw [cubeChar_sub_cubeShift,ite_eq_right (Ne.symm hz),zero_mul]
    simp

lemma cubeOverlap_alternative (x y : d → ℝ) :
    (∫ s, cubeChar (x-s)*cubeChar (y-s)) = cubeOverlap (x-y) := by
  have he (s : d → ℝ) : cubeChar (x-s)*cubeChar (y-s) =
      (fun t => cubeChar t*cubeChar (t-(x-y))) (x-s) := by
    congr 2
    abel
  simp only [he]
  exact integral_sub_left_eq_self (fun t => cubeChar t*cubeChar (t-(x-y))) volume x

lemma cubeOverlap_alternative_integrable (x y : d → ℝ) :
    Integrable (fun s => cubeChar (x-s)*cubeChar (y-s)) := by
  have hh := (cubeOverlap_section_integrable (x-y)).comp_sub_left x
  convert hh using 1
  funext s
  congr 2
  abel

theorem integral_sameCube (x y : d → ℝ) :
    (∫ t : d → I, sameCube (fun a => (t a:ℝ)) x y) = cubeOverlap (x-y) := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun _ => sameCube_nonneg _ _ _)) (cubeOverlap_nonneg _)).mp
  rw [ofReal_integral_eq_lintegral_ofReal (sameCube_I_integrable x y)
    (Eventually.of_forall (fun _ => sameCube_nonneg _ _ _))]
  simp only [sameCube_periodization]
  have hm : Measurable (fun s : d → ℝ => ENNReal.ofReal (cubeChar (x-s)*cubeChar (y-s))) :=
    ((cubeChar_measurable.comp (measurable_const.sub measurable_id)).mul
      (cubeChar_measurable.comp (measurable_const.sub measurable_id))).ennreal_ofReal
  rw [lintegral_cube_periodization _ hm,
    ←ofReal_integral_eq_lintegral_ofReal (cubeOverlap_alternative_integrable x y)
      (Eventually.of_forall (fun _ => mul_nonneg (cubeChar_nonneg _) (cubeChar_nonneg _))),
    cubeOverlap_alternative]

end Work_CubeTranslationAverage_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate

lemma integral_interval_cos_int (k : ℤ) :
    (∫ x : I, Real.cos (Real.pi*(k:ℝ)*(x:ℝ))) = if k=0 then 1 else 0 := by
  rw [unitInterval.volume_def]
  change (∫ x : Set.Icc (0:ℝ) 1, (fun y : ℝ => Real.cos (Real.pi*(k:ℝ)*y)) x ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc (fun y : ℝ => Real.cos (Real.pi*(k:ℝ)*y)),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  by_cases hk : k=0
  · simp [hk]
  · rw [ite_eq_right hk,intervalIntegral.integral_comp_mul_left _ (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hk)),
      integral_cos]
    simp only [mul_zero,mul_one,Real.sin_zero,sub_zero,smul_eq_mul]
    rw [mul_comm Real.pi (k:ℝ),Real.sin_int_mul_pi,mul_zero]

def cosMode (k : ℕ) : C(I,ℝ) where
  toFun x := Real.cos (Real.pi*(k:ℝ)*(x:ℝ))
  continuous_toFun := by fun_prop

lemma cosMode_integrable (k : ℕ) : Integrable (cosMode k) :=
  (cosMode k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma cosMode_product_integral (m n : ℕ) :
    (∫ x : I, cosMode m x*cosMode n x) =
      if m=n then (if m=0 then 1 else 1/2) else 0 := by
  have he (x : I) : 2*(cosMode m x*cosMode n x) =
      Real.cos (Real.pi*((((m:ℤ)-(n:ℤ)):ℤ):ℝ)*(x:ℝ)) + Real.cos (Real.pi*((((m:ℤ)+(n:ℤ)):ℤ):ℝ)*(x:ℝ)) := by
    dsimp [cosMode]
    push_cast
    rw [show Real.pi*((m:ℝ)-n)*(x:ℝ) = Real.pi*m*(x:ℝ)-Real.pi*n*(x:ℝ) by ring,
      show Real.pi*((m:ℝ)+n)*(x:ℝ) = Real.pi*m*(x:ℝ)+Real.pi*n*(x:ℝ) by ring]
    nlinarith [Real.two_mul_cos_mul_cos (Real.pi*m*(x:ℝ)) (Real.pi*n*(x:ℝ))]
  have hcm (k : ℤ) : Integrable (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ))) :=
    (by fun_prop : Continuous (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh := congrArg (fun f : I → ℝ => ∫ x, f x) (funext he)
  rw [integral_const_mul,integral_add (hcm ((m:ℤ)-n)) (hcm ((m:ℤ)+n)),integral_interval_cos_int,
    integral_interval_cos_int] at hh
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · simp only [hm,Nat.cast_zero,sub_self,add_zero,ite_true] at hh
      simp only [hm,ite_true]
      linarith
    · have hsum : (m:ℤ)+m ≠ 0 := by omega
      simp only [sub_self,ite_true,ite_eq_right hsum,add_zero] at hh
      simp only [ite_true,ite_eq_right hm]
      linarith
  · have hdiff : (m:ℤ)-n ≠ 0 := by omega
    have hsum : (m:ℤ)+n ≠ 0 := by omega
    simp only [ite_eq_right hdiff,ite_eq_right hsum,add_zero] at hh
    rw [ite_eq_right hmn]
    linarith

def cosNormalization (n : ℕ) : ℝ := if n=0 then 1 else Real.sqrt 2

def neumannMode (n : ℕ) : C(I,ℂ) where
  toFun x := (cosNormalization n*cosMode n x : ℝ)
  continuous_toFun := by unfold cosNormalization; fun_prop

lemma neumannMode_inner (m n : ℕ) :
    (∫ x : I, conj (neumannMode m x)*neumannMode n x) = if m=n then 1 else 0 := by
  simp only [neumannMode,ContinuousMap.coe_mk,Complex.conj_ofReal]
  simp_rw [← Complex.ofReal_mul]
  have he (x : I) : (cosNormalization m*cosMode m x)*(cosNormalization n*cosMode n x) =
      (cosNormalization m*cosNormalization n)*(cosMode m x*cosMode n x) := by ring
  simp_rw [he]
  rw [integral_complex_ofReal (f := fun x : I => (cosNormalization m*cosNormalization n)*(cosMode m x*cosMode n x)),integral_const_mul,cosMode_product_integral]
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · simp [cosNormalization,hm]
    · simp only [ite_true,ite_eq_right hm,cosNormalization]
      rw [← sq,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
  · simp [hmn]

end CoulombNeumann

end

end OAI
