import Mathlib
import OAI.Probability.SKRatio.Quantization.BinWeightContinuity
import OAI.Probability.SKRatio.Quantization.BinEmpirical
import OAI.Probability.SKRatio.Quantization.QuantizedPopulation
import OAI.Probability.SKRatio.Quantization.ConditionalBins
import OAI.Probability.SKRatio.FiniteChain.FieldSize
import OAI.Probability.SKRatio.FiniteChain.ResidualBounds
import OAI.Probability.SKRatio.Gaussian.PlantedCriterion

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma variance_bilinear_field_error (M : Matrix (Fin n) (Fin n) ℝ)
    (v v' p : Fin n → ℝ) (hp : ∑ i, p i^2=1) {K a : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hM : euclideanOpNorm M ≤ K)
    (hv : ∀ i, |v i-v' i| ≤ a) :
    |p ⬝ᵥ (M*ᵥ (fun i => v i*p i))-p ⬝ᵥ (M*ᵥ (fun i => v' i*p i))| ≤ K*a := by
  have he : p ⬝ᵥ (M*ᵥ (fun i => v i*p i))-p ⬝ᵥ (M*ᵥ (fun i => v' i*p i)) =
      quadratic (M*Matrix.diagonal (fun i => v i-v' i)) p := by
    simp only [quadratic,Matrix.mul_diagonal,dotProduct,Matrix.mulVec,Finset.mul_sum,
      ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hd := matrix_diagonal_opNorm_le (fun i => v i-v' i) a ha hv
  have hnorm : euclideanOpNorm (M*Matrix.diagonal (fun i => v i-v' i)) ≤ K*a := by
    unfold euclideanOpNorm
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul hM hd (norm_nonneg _) hK)
  simpa only [hp,mul_one] using (quadratic_abs_le _ p).trans
    (mul_le_mul_of_nonneg_right hnorm (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma deterministic_corrected_error (β : ℝ) (H p : Fin n → ℝ)
    (hp : ∑ i, p i^2=1) :
    |deterministicForm β H p-correctedForm β H p| ≤  |(∑ i, H i)/(n:ℝ)-β^2| := by
  rw [deterministic_corrected,add_sub_cancel_left,abs_mul,abs_mul,abs_sub_comm]
  have h1 := mul_le_mul_of_nonneg_left (siteMoment_one hp) (abs_nonneg ((∑ i, H i)/(n:ℝ)-β^2))
  have h2 := mul_le_mul_of_nonneg_left (siteMoment_v hp H) (abs_nonneg ((∑ i, H i)/(n:ℝ)-β^2))
  calc
    _  ≤  |(∑ i, H i)/(n:ℝ)-β^2| *|siteMoment p (fun i => v (H i))| := by
      gcongr
      simpa only [mul_one] using h1
    _  ≤  _ := by simpa only [mul_one] using h2

lemma quantized_siteNorm_le (H H' : Fin n → ℝ) {s a : ℝ}
    (hs : siteNorm H ≤ s) (he : siteNorm (fun i => H i-H' i) ≤ a) : siteNorm H' ≤ s+a := by
  have hneg : siteNorm (fun i => H' i-H i)=siteNorm (fun i => H i-H' i) := by
    rw [siteNorm_eq_sqrt,siteNorm_eq_sqrt]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht := siteNorm_add H (fun i => H' i-H i)
  have hid : (fun i => H i+(H' i-H i))=H' := by ext i; ring
  rw [hid,hneg] at ht
  linarith only [ht,hs,he]

theorem reducedForm_upper_rare {β C e : ℝ} (hβ : 0 < β) (he : 0 < e)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C+6*e < reducedForm β g p}) := by
  let K := 2*β+2*β^2+2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨a,R,N,ha,ha1,hR,hN,htotal,hv,hmv,hf,hk,hpop,herr⟩ :=
    scalar_quantizer_exists (augmentedField_squareTails β hβ) hβ hK he hscalar
  let q := intervalBin (gridCut R N)
  let h := gridRep R N
  have hq : Measurable q := measurable_intervalBin (Nat.succ_pos N) (gridCut_strictMono hR hN)
  have hnull : NullSingletonClass (fieldLaw β) := by
    unfold fieldLaw
    exact nullSingletonClass_gaussianReal (variance_ne_zero hβ)
  have hemp := augmentedField_empirical β hβ
  have hcount := intervalBin_binSize_rare (Nat.succ_pos N) (gridCut_strictMono hR hN) hemp
    (intervalBin_mass_pos (Nat.succ_pos N) (gridCut_strictMono hR hN) β hβ.ne')
  obtain ⟨δ,hδ,htol⟩ := finiteV_population_tolerance (μ := fieldLaw β) hq β h he
  have hroot := (intervalBin_roots_empirical (Nat.succ_pos N) (gridCut_strictMono hR hN) hemp) δ hδ
  have hmean := (augmentedField_firstMoment β hβ) e he
  have hsize := (augmentedField_siteNorm β hβ) 1 (by norm_num)
  obtain ⟨L,hL⟩ := random_binForm_tail (C := C+2*e) hβ hK he h q hq
  let E := fun n => {g : (Fin n × Fin n) → ℝ |
    (∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d) ∧
    (∀ z, finiteV β (binT (fun i => q (augmentedField β g i))) h z ≤ C+2*e) ∧
    g ∈ binFormBad β h (fun i => q (augmentedField β g i)) K ((C+2*e)+2*e)}
  have hE : ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n)) E := by
    refine ⟨(L:ℝ)+1,e^2/(π^2*β^2),by positivity,by positivity [pi_pos],?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [←ENNReal.ofReal_toReal (measure_ne_top (standardArrayLaw (Fin n × Fin n)) (E n))]
    apply ENNReal.ofReal_le_ofReal
    have ht := hL hn
    have hexp : -e^2*(n:ℝ)/(π^2*β^2)= -(e^2/(π^2*β^2))*(n:ℝ) := by ring
    rw [hexp] at ht
    exact ht.trans (by nlinarith only [exp_pos (-(e^2/(π^2*β^2))*(n:ℝ))])
  apply ((((((residual_norm_rare hβ).union herr).union hcount).union hroot).union hmean).union hsize).union hE |>.mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  rintro g ⟨p,hp,hbad⟩
  by_contra hb
  have hM : euclideanOpNorm (fieldProjection n*(β • goe g)*fieldProjection n) ≤ K :=
    not_lt.mp (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))))
  have herr' : siteNorm (fun i => augmentedField β g i-gridQuant R N (augmentedField β g i)) < a :=
    lt_of_not_ge (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))
  have hcount' : ∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d := by
    intro d
    exact not_lt.mp (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨d,hx⟩))))))
  have hroot' : dist (binT (fun i => q (augmentedField β g i))) (massRoot (fieldLaw β) q) < δ :=
    lt_of_not_ge (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hmean' : |(∑ i, augmentedField β g i)/(n:ℝ)-β^2| < e :=
    lt_of_not_ge (fun hx => hb (Or.inl (Or.inl (Or.inr hx))))
  have hsize' : siteNorm (augmentedField β g) < sqrt (β^2+β^4)+1 := by
    have hh : |siteNorm (augmentedField β g)-sqrt (β^2+β^4)| < 1 :=
      lt_of_not_ge (fun hx => hb (Or.inl (Or.inr hx)))
    have hh' := (le_abs_self _).trans_lt hh
    linarith only [hh']
  have hfinite : ∀ z, finiteV β (binT (fun i => q (augmentedField β g i))) h z ≤ C+2*e := by
    intro z
    have hne : ∀ d, |binT (fun i => q (augmentedField β g i)) d-massRoot (fieldLaw β) q d| < δ :=
      fun d => by simpa only [Real.dist_eq] using (dist_pi_lt_iff hδ).mp hroot' d
    have h1 := htol hn _ hne z
    have h2 := hpop z
    change finiteV β (massRoot (fieldLaw β) q) h z < C+e at h2
    linarith only [h1,h2]
  have hform : p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
      (fun i => v (h (q (augmentedField β g i)))*p i))+
      correctedForm β (fun i => h (q (augmentedField β g i))) p ≤ C+4*e := by
    apply not_lt.mp
    intro hh
    apply hb
    exact Or.inr ⟨hcount',hfinite,hM, p,hp,by linarith only [hh]⟩
  have hsquant : siteNorm (fun i => gridQuant R N (augmentedField β g i)) ≤  sqrt (β^2+β^4)+2 := by
    have ht := quantized_siteNorm_le _ _ hsize'.le herr'.le
    linarith only [ht,ha1]
  have hcf := correctedForm_field_error hn β (augmentedField β g)
    (fun i => gridQuant R N (augmentedField β g i)) p hp ha.le ha.le
    (show 0 ≤  sqrt (β^2+β^4)+2 by positivity) herr'.le hsquant
    (fun i => hv _) (fun i => hmv _)
    (by intro i j; simpa only [compactF_weight] using hf (augmentedField β g i) (augmentedField β g j))
    (by intro i j; simpa only [compactK_weight] using hk (augmentedField β g i) (augmentedField β g j))
  have hbil := variance_bilinear_field_error (fieldProjection n*(β • goe g)*fieldProjection n)
    (fun i => v (augmentedField β g i)) (fun i => v (gridQuant R N (augmentedField β g i))) p
    hp hK ha.le hM (fun i => hv _)
  have hcor := deterministic_corrected_error β (augmentedField β g) p hp
  rw [reducedForm_decomposition hn] at hbad
  have hsum : 0 ≤ 4*β*sqrt a := by positivity
  change p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
      (fun i => v (gridQuant R N (augmentedField β g i))*p i))+
      correctedForm β (fun i => gridQuant R N (augmentedField β g i)) p ≤ C+4*e at hform
  have hcf' := (le_abs_self _).trans hcf
  have hbil' := (le_abs_self _).trans hbil
  have hcor' := (le_abs_self _).trans hcor
  linarith only [hbad,hform,hcf',hbil',hcor',htotal,hmean',hsum]

end SKRatio.Bins

namespace SKRatio.Planted
open Bins Scalar SKRatioClock.Regression Calculus
attribute [local instance] Classical.propDecidable

theorem formBad_rare_of_scalar {β C : ℝ} (hβ : 0 < β) (hC : C < 1)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ ExponentiallyRare (law β) (formBad ρ) := by
  let e := (1-C)/10
  have he : 0 < e := by dsimp [e]; positivity
  have hred := reducedForm_upper_rare hβ he hscalar
  have herr := reduced_error_rare hβ he
  have hbad : ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => (augmentedDisorder β) ⁻¹' formBad e n) := by
    apply (hred.union herr).mono
    exact .of_forall (fun n g hg => by
      obtain ⟨p,hp,hbad⟩ := (formBad_iff_unit e _).mp hg
      by_contra hnot
      have hr : reducedForm β g p ≤ C+6*e := not_lt.mp (fun hx => hnot (Or.inl ⟨p,hp,hx⟩))
      have hu : |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p| ≤ e := by
        have hh : |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p| ≤
            e*(∑ i, p i^2) := not_lt.mp (fun hx => hnot (Or.inr ⟨p,hx⟩))
        simpa only [hp,mul_one] using hh
      have hle := (le_abs_self _).trans hu
      dsimp [e] at hr hu hbad hle
      linarith only [hr,hbad,hle,hC])
  obtain ⟨A,c,hA,hc,hrare⟩ := hbad
  refine ⟨e,he,A,c,hA,hc,?_⟩
  filter_upwards [hrare,eventually_gt_atTop 0] with n hn hn0
  have hl := (augmentedDisorder_hasLaw hn0 β).measure_eq (formBad_measurable e n)
  exact hl.symm.le.trans hn

theorem ratio_cutoff_of_scalar (β ε η C : ℝ)
    (hβ : 0 < β) (hβhalf : β < 1/2) (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    (hC : C < 1)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    Tendsto (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η  <  (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0  <  mixingTime g (1-ε)) := by
  obtain ⟨ρ,hρ,hρrare⟩ := formBad_rare_of_scalar hβ hC hscalar
  obtain ⟨κ,hκ,hplant⟩ := hρrare.without_prefactor
  exact ratio_cutoff_of_planted_form β ε η hβ.le hβhalf hε hεhalf hη hρ hκ hplant

end SKRatio.Planted

end

end OAI
