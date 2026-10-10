import OAI.Analysis.TracialSplitting.PartitionCoupling

namespace OAI

universe uA


section

noncomputable section

namespace NuclearTrace

open scoped ComplexOrder

def clipScalar (t : ℝ) : ℝ := (Real.sqrt (max t 1))⁻¹

lemma clipScalar_continuous : Continuous clipScalar := by
  apply Continuous.inv₀ (Real.continuous_sqrt.comp (continuous_id.max continuous_const))
  intro t
  exact ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (le_max_right t 1)))

lemma clipScalar_nonneg (t : ℝ) : 0 ≤ clipScalar t := by
  exact inv_nonneg.2 (Real.sqrt_nonneg _)

lemma clipScalar_le_one (t : ℝ) : clipScalar t ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (max t 1) := by
    exact (Real.le_sqrt (by norm_num) (le_trans zero_le_one (le_max_right t 1))).2
      (by simp)
  exact inv_le_one_of_one_le₀ hs

lemma clipScalar_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1-clipScalar t*t*clipScalar t ∧
    1-clipScalar t*t*clipScalar t ≤ |t-1| ∧
    (1-clipScalar t)*t*(1-clipScalar t) ≤ |t-1| := by
  by_cases h : t ≤ 1
  · simp only [clipScalar,max_eq_right h,Real.sqrt_one,inv_one,one_mul,mul_one,
      sub_self,zero_mul,mul_zero]
    rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact ⟨sub_nonneg.2 h, le_rfl, sub_nonneg.2 h⟩
  · have h1 : 1 ≤ t := le_of_not_ge h
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one h1
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hsq := Real.sq_sqrt ht
    have hs1 : 1 ≤ Real.sqrt t := (Real.le_sqrt zero_le_one ht).2 (by simpa using h1)
    have he : (Real.sqrt t)⁻¹*t*(Real.sqrt t)⁻¹ = 1 := by
      calc
        _ = (Real.sqrt t)⁻¹*(Real.sqrt t)^2*(Real.sqrt t)⁻¹ := by rw [hsq]
        _ = 1 := by field_simp [ne_of_gt hs0]
    simp only [clipScalar,max_eq_left h1,he,sub_self,abs_of_nonneg (sub_nonneg.2 h1)]
    refine ⟨le_rfl,sub_nonneg.2 h1,?_⟩
    have he' : (1-(Real.sqrt t)⁻¹)*t*(1-(Real.sqrt t)⁻¹) =
        (Real.sqrt t-1)^2 := by
      calc
        _ = (1-(Real.sqrt t)⁻¹)*(Real.sqrt t)^2*(1-(Real.sqrt t)⁻¹) := by rw [hsq]
        _ = _ := by field_simp [ne_of_gt hs0]
    rw [he']
    nlinarith

section Algebra

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def rowNormalizer (b : A) : A := cfc clipScalar b

lemma rowNormalizer_nonneg (b : A) : 0 ≤ rowNormalizer b :=
  cfc_nonneg (fun t _ => clipScalar_nonneg t)

lemma rowNormalizer_le_one (b : A) : rowNormalizer b ≤ 1 :=
  cfc_le_one clipScalar b (fun t _ => clipScalar_le_one t)

lemma abs_sub_one_cfc {b : A} (hb : IsSelfAdjoint b) :
    CFC.abs (b-1) = cfc (fun t : ℝ => |t-1|) b := by
  rw [CFC.abs_eq_cfcₙ_norm (b-1) (hb.sub (IsSelfAdjoint.one A)),
    cfcₙ_eq_cfc (hf0 := norm_zero)]
  have he : cfc (fun t : ℝ => t-1) b = b-1 := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => 1) b, cfc_id' ℝ b hb,cfc_const_one ℝ b hb]
  rw [← he,← cfc_comp' (fun t : ℝ => ‖t‖) (fun t : ℝ => t-1) b]
  rfl

theorem rowNormalizer_bounds {b : A} (hb : 0 ≤ b) :
    0 ≤ 1-rowNormalizer b*b*rowNormalizer b ∧
    1-rowNormalizer b*b*rowNormalizer b ≤ CFC.abs (b-1) ∧
    (1-rowNormalizer b)*b*(1-rowNormalizer b) ≤ CFC.abs (b-1) := by
  have hs := hb.isSelfAdjoint
  have hf := clipScalar_continuous.continuousOn (s := spectrum ℝ b)
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ b) := continuousOn_id
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ b) := continuousOn_const
  have hprod : rowNormalizer b*b*rowNormalizer b =
      cfc (fun t : ℝ => clipScalar t*t*clipScalar t) b := by
    rw [cfc_mul (fun t : ℝ => clipScalar t*t) clipScalar b
      (show ContinuousOn (fun t : ℝ => clipScalar t*t) _ from hf.mul hid) hf,
      cfc_mul clipScalar (fun t : ℝ => t) b hf hid,cfc_id' ℝ b hs]
    rfl
  have hres : 1-rowNormalizer b*b*rowNormalizer b =
      cfc (fun t : ℝ => 1-clipScalar t*t*clipScalar t) b := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun t => clipScalar t*t*clipScalar t) b hone
      (show ContinuousOn (fun t : ℝ => clipScalar t*t*clipScalar t) _ from (hf.mul hid).mul hf),
      cfc_const_one ℝ b hs,hprod]
  have herr : (1-rowNormalizer b)*b*(1-rowNormalizer b) =
      cfc (fun t : ℝ => (1-clipScalar t)*t*(1-clipScalar t)) b := by
    rw [cfc_mul (fun t : ℝ => (1-clipScalar t)*t) (fun t => 1-clipScalar t) b
      (show ContinuousOn (fun t : ℝ => (1-clipScalar t)*t) _ from (hone.sub hf).mul hid)
      (show ContinuousOn (fun t : ℝ => 1-clipScalar t) _ from hone.sub hf),
      cfc_mul (fun t : ℝ => 1-clipScalar t) (fun t => t) b
        (show ContinuousOn (fun t : ℝ => 1-clipScalar t) _ from hone.sub hf) hid,
      cfc_sub (fun _ : ℝ => 1) clipScalar b hone hf,
      cfc_id' ℝ b hs,cfc_const_one ℝ b hs]
    rfl
  rw [hres,herr,abs_sub_one_cfc hs]
  have hspec (t) (ht : t ∈ spectrum ℝ b) : 0 ≤ t :=
    (spectrum_nonneg_of_nonneg hb) ht
  refine ⟨cfc_nonneg (fun t ht => (clipScalar_bounds (hspec t ht)).1),?_,?_⟩
  · exact cfc_mono (fun t ht => (clipScalar_bounds (hspec t ht)).2.1)
      ((hone.sub ((hf.mul hid).mul hf))) (by fun_prop)
  · exact cfc_mono (fun t ht => (clipScalar_bounds (hspec t ht)).2.2)
      (((hone.sub hf).mul hid).mul (hone.sub hf)) (by fun_prop)

end Algebra

end NuclearTrace

end

end

end OAI
