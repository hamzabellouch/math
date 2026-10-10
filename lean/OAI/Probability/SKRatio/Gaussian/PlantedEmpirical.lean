import Mathlib
import OAI.Probability.SKRatio.Gaussian.GaussianEmpirical
import OAI.Probability.SKRatio.Matrices.PlantedGOE
import OAI.Probability.SKRatio.Matrices.GaussianSquareTails
import OAI.Probability.SKRatio.Variational.ScalarMoments

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression

def modelField (β : ℝ) (n : ℕ) : (Option (Fin n) → ℝ) → Fin n → ℝ :=
  sharedGaussianField (β^2) β (β/sqrt n)

lemma modelField_measurable (β : ℝ) (n : ℕ) : Measurable (modelField β n) := by
  unfold modelField sharedGaussianField
  fun_prop

lemma fieldLaw_eq_affine_map (β : ℝ) : Scalar.fieldLaw β =
    (gaussianReal 0 1).map (fun z : ℝ => β^2+β*z) := by
  have hid : (fun z : ℝ => β^2+β*z) = (fun z : ℝ => β^2+z) ∘ (fun z : ℝ => β*z) := rfl
  rw [hid,←Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero,zero_add,mul_one,Scalar.fieldLaw]
  congr 1
  apply NNReal.eq
  simp only [Scalar.variance_coe,NNReal.coe_mk]

lemma fieldLaw_secondMoment (β : ℝ) :
    (∫ h, h^2 ∂Scalar.fieldLaw β) = β^2+β^4 := by
  have hv := variance_eq_sub (Scalar.memLp_field β)
  change _ = (∫ h, h^2 ∂Scalar.fieldLaw β)-(∫ h, h ∂Scalar.fieldLaw β)^2 at hv
  have hm : (∫ h, h ∂Scalar.fieldLaw β) = β^2 := integral_id_gaussianReal
  have hvar : Var[(fun h : ℝ => h); Scalar.fieldLaw β] = β^2 := by
    change Var[id; gaussianReal (β^2) (Scalar.variance β)] = β^2
    rw [variance_id_gaussianReal,Scalar.variance_coe]
  rw [hm,hvar] at hv
  nlinarith only [hv]

lemma common_field_convergence (β : ℝ) (hβ : 0 < β) :
    ExponentialConvergence (fun n => standardArrayLaw (Option (Fin n)))
      (fun n g => (β/sqrt (n:ℝ))*g none) 0 := by
  intro ε hε
  refine ⟨2,ε^2/(2*β^2),by norm_num,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have ht := subgaussian_abs_tail
    (gaussian_hasSubgaussianMGF (coordinate_hasLaw (none : Option (Fin n))))
      (ε*sqrt (n:ℝ)/β) (by positivity)
  simp only [Real.dist_eq,sub_zero]
  apply (measure_mono (show {g : Option (Fin n) → ℝ | ε ≤ |β/sqrt (n:ℝ)*g none|} ⊆
    {g | ε*sqrt (n:ℝ)/β ≤ |g none|} from ?_)).trans
  · apply ht.trans_eq
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
    norm_num only [ENNReal.ofReal_ofNat,NNReal.coe_one,mul_one]
    congr 2
    rw [div_pow,mul_pow,sq_sqrt hnR.le]
    ring_nf
  · intro g hg
    change ε ≤ |β/sqrt (n:ℝ)*g none| at hg
    rw [abs_mul,abs_of_pos (by positivity : 0<β/sqrt (n:ℝ))] at hg
    apply (div_le_iff₀ hβ).mpr
    have hh := (le_div_iff₀ (sqrt_pos.mpr hnR)).mp
      (show ε ≤ β*|g none|/sqrt (n:ℝ) by simpa only [div_mul_eq_mul_div] using hg)
    nlinarith

lemma modelField_squareTails (β : ℝ) (hβ : 0 < β) :
    ExponentialSquareTails (fun n => standardArrayLaw (Option (Fin n))) (modelField β) := by
  let ρ := fun n => standardArrayLaw (Option (Fin n))
  have hi : ExponentialSquareTails ρ (fun _ g i => g (some i)) := by
    exact iid_exponential_squareTails ρ _ (fun _ _ => measurable_pi_apply _)
      (fun _ => coordinates_independent.precomp (Option.some_injective _))
      (gaussianReal 0 1) (fun _ _ => coordinate_hasLaw _) gaussian_integrable_exp_quarter_sq
  have ha := hi.bounded_mul (fun _ _ _ => β) |β| (abs_nonneg β) (fun _ _ _ => le_rfl)
  have hm := exponentialSquareTails_of_bounded ρ (fun _ _ _ => β^2) (β^2)
    (fun _ _ _ => by rw [abs_of_nonneg (sq_nonneg β)])
  apply (hm.add ha).l2_stability
  have hz := (common_field_convergence β hβ).continuous_map
    (f := fun x : ℝ => x^2) (by fun_prop)
  simp only [zero_pow (by norm_num : (2:ℕ)≠0)] at hz
  intro ε hε
  apply (hz ε hε).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro g hg
  have he : (∑ i : Fin n, (β^2+β*g (some i)-modelField β n g i)^2)/(n:ℝ) =
      ((β/sqrt (n:ℝ))*g none)^2 := by
    simp only [modelField,sharedGaussianField,sub_add_cancel_left,neg_sq,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  change ε ≤ dist _ 0 at hg ⊢
  rwa [he] at hg

lemma modelField_empirical (β : ℝ) (hβ : 0 < β) :
    ExponentialEmpiricalConcentration (fun n => standardArrayLaw (Option (Fin n)))
      (modelField β) (Scalar.fieldLaw β) := by
  intro f K hf B hB ε hε
  let L : ℝ≥0 := K+1
  let D : ℝ := |B|+1
  have hL : (0:ℝ) < L := by dsimp [L]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hf' : LipschitzWith L f := hf.weaken (by simp [L])
  have hB' (z : ℝ) : |f z| ≤ D := (hB z).trans (by dsimp [D]; linarith [le_abs_self B])
  let c := min (ε^2/(8*D^2)) (ε^2/(8*(L:ℝ)^2*β^2))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨4,c,by norm_num,hc,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ht := iid_common_shift_average_tail hn (β^2) β (β/sqrt n)
    f hf' D hD.le hB' ε hε.le
  have hm : (∫ z, f z ∂Scalar.fieldLaw β) = ∫ z, f (β^2+β*z) ∂gaussianReal 0 1 := by
    rw [fieldLaw_eq_affine_map]
    exact integral_map (by fun_prop) hf.continuous.aestronglyMeasurable
  rw [hm]
  change standardArrayLaw (Option (Fin n)) {g | ε ≤
    |(∑ i : Fin n, f (β^2+β*g (some i)+(β/sqrt n)*g none))/(n:ℝ) -
      ∫ z, f (β^2+β*z) ∂gaussianReal 0 1|} ≤ _
  have he1 : -(ε^2*(n:ℝ))/(8*D^2) ≤ -c*n := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (ε^2/(8*D^2)) (ε^2/(8*(L:ℝ)^2*β^2))) hnR.le
    have he : -(ε^2*(n:ℝ))/(8*D^2) = -(ε^2/(8*D^2))*n := by ring
    rw [he]
    dsimp [c]
    linarith only [hh]
  have he2 : -ε^2/(8*(L:ℝ)^2*(β/sqrt (n:ℝ))^2) ≤ -c*n := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (ε^2/(8*D^2)) (ε^2/(8*(L:ℝ)^2*β^2))) hnR.le
    have he : -ε^2/(8*(L:ℝ)^2*(β/sqrt (n:ℝ))^2) = -(ε^2/(8*(L:ℝ)^2*β^2))*n := by
      rw [div_pow,sq_sqrt hnR.le]
      field_simp
    rw [he]
    dsimp [c]
    linarith only [hh]
  apply ht.trans
  calc
    _ ≤ 2*ENNReal.ofReal (exp (-c*n))+2*ENNReal.ofReal (exp (-c*n)) := by
      gcongr
    _ = ENNReal.ofReal (4*exp (-c*n)) := by
      rw [←add_mul]
      norm_num only [show (2:ENNReal)+2=4 by norm_num]
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num

lemma augmentedField_event_eq {n : ℕ} (hn : 0 < n) (β : ℝ)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    standardArrayLaw (Fin n × Fin n) ((augmentedField β) ⁻¹' E) =
      standardArrayLaw (Option (Fin n)) ((modelField β n) ⁻¹' E) := by
  have he := congrArg (fun μ : Measure (Fin n → ℝ) => μ E) (augmentedField_law hn β)
  change ((standardArrayLaw (Fin n × Fin n)).map (augmentedField β)) E =
    ((standardArrayLaw (Option (Fin n))).map (modelField β n)) E at he
  rw [Measure.map_apply_of_aemeasurable (augmentedField_gaussian β).aemeasurable hE,
    Measure.map_apply (modelField_measurable β n) hE] at he
  exact he

theorem augmentedField_empirical (β : ℝ) (hβ : 0 < β) :
    ExponentialEmpiricalConcentration (fun n => standardArrayLaw (Fin n × Fin n))
      (fun _ => augmentedField β) (Scalar.fieldLaw β) := by
  intro f K hf B hB ε hε
  obtain ⟨C,c,hC,hc,he⟩ := modelField_empirical β hβ f K hf B hB ε hε
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he,eventually_gt_atTop 0] with n hn hn0
  have hE : MeasurableSet {v : Fin n → ℝ | ε ≤
    |(∑ i, f (v i))/(n:ℝ) - ∫ z, f z ∂Scalar.fieldLaw β|} := by
    apply measurableSet_le measurable_const
    exact (((Finset.measurable_sum _ (fun i _ => hf.continuous.measurable.comp
      (measurable_pi_apply i))).div_const _).sub_const _).abs
  exact (augmentedField_event_eq hn0 β _ hE).le.trans hn

theorem augmentedField_squareTails (β : ℝ) (hβ : 0 < β) :
    ExponentialSquareTails (fun n => standardArrayLaw (Fin n × Fin n))
      (fun _ => augmentedField β) := by
  intro ε hε
  obtain ⟨R,hR,C,c,hC,hc,he⟩ := modelField_squareTails β hβ ε hε
  refine ⟨R,hR,C,c,hC,hc,?_⟩
  filter_upwards [he,eventually_gt_atTop 0] with n hn hn0
  have hE : MeasurableSet {v : Fin n → ℝ | ε ≤ (∑ i, squareTail R (v i))/(n:ℝ)} := by
    exact measurableSet_le measurable_const ((Finset.measurable_sum _
      (fun i _ => (measurable_squareTail R).comp (measurable_pi_apply i))).div_const _)
  exact (augmentedField_event_eq hn0 β _ hE).le.trans hn

theorem augmentedField_secondMoment (β : ℝ) (hβ : 0 < β) :
    ExponentialConvergence (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n g => (∑ i, augmentedField β g i^2)/(n:ℝ)) (β^2+β^4) := by
  have he := (augmentedField_empirical β hβ).secondMoment
    (augmentedField_squareTails β hβ) (Scalar.memLp_field β).integrable_sq
  rwa [fieldLaw_secondMoment] at he

end SKRatio.Planted

end
end

end OAI
