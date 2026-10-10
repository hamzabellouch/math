import OAI.MathematicalPhysics.CriticalSK.PathSpectra
import OAI.MathematicalPhysics.CriticalSK.Powers
import OAI.MathematicalPhysics.CriticalSK.TriNoise

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK


lemma directed_neighbor_sum_general (n : ℕ) (b u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then b i.val else 0)*u i.val*u j.val) =
      ∑ i ∈ Finset.range n, b i*u i*u (i+1) := by
  rw [Fin.sum_univ_castSucc]
  have hl : (∑ j : Fin (n+1),
      (if (Fin.last n).val+1=j.val then b (Fin.last n).val else 0)*u (Fin.last n).val*u j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.val_last]; omega),zero_mul,zero_mul]
  rw [hl,add_zero,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (Fin.ext (by simpa using h.symm))),zero_mul,zero_mul]
  · simp

def triSampleMatrix (n : ℕ) (ω : TriSample n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => (if i=j then ω.1 i.val else 0)+
    (if i.val+1=j.val then chi (chiRowDim n i.val) (ω.2 i.val)/Real.sqrt (n+1:ℝ) else 0)+
    (if j.val+1=i.val then chi (chiRowDim n j.val) (ω.2 j.val)/Real.sqrt (n+1:ℝ) else 0)

lemma triSampleMatrix_hermitian (n : ℕ) (ω : TriSample n) : (triSampleMatrix n ω).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,triSampleMatrix]
  by_cases h : i=j
  · subst j; ring
  · simp only [ite_eq_right h,ite_eq_right (Ne.symm h),zero_add,add_comm]

def triSampleOperator (n : ℕ) (ω : TriSample n) : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n+1)) := Matrix.toLpLin 2 2 (triSampleMatrix n ω)

lemma triSampleOperator_symmetric (n : ℕ) (ω : TriSample n) : (triSampleOperator n ω).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (triSampleMatrix_hermitian n ω)

lemma generic_tridiagonal_quadratic (n : ℕ) (d b u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      ((if i=j then d i.val else 0)+(if i.val+1=j.val then b i.val else 0)+
        (if j.val+1=i.val then b j.val else 0))*u j.val*u i.val) =
      (∑ i ∈ Finset.range (n+1), d i*u i^2)+2*(∑ i ∈ Finset.range n, b i*u i*u (i+1)) := by
  simp only [add_mul,Finset.sum_add_distrib]
  have hd : (∑ i : Fin (n+1), ∑ j : Fin (n+1), (if i=j then d i.val else 0)*u j.val*u i.val) =
      ∑ i ∈ Finset.range (n+1), d i*u i^2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hlo : (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then b i.val else 0)*u j.val*u i.val) =
      ∑ i ∈ Finset.range n, b i*u i*u (i+1) := by
    convert directed_neighbor_sum_general n b u using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intros
    ring
  have hhi : (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if j.val+1=i.val then b j.val else 0)*u j.val*u i.val) =
      ∑ i ∈ Finset.range n, b i*u i*u (i+1) := by
    rw [Finset.sum_comm]
    exact directed_neighbor_sum_general n b u
  rw [hd,hlo,hhi]
  ring

lemma triSampleOperator_inner (n : ℕ) (ω : TriSample n) (u : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))
      (triSampleOperator n ω (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))) = triForm n ω u := by
  simp only [triSampleOperator,Matrix.toLpLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply,star_trivial,dotProduct,Matrix.mulVec,triSampleMatrix,Finset.sum_mul]
  exact generic_tridiagonal_quadratic n ω.1 (fun i => chi (chiRowDim n i) (ω.2 i)/Real.sqrt (n+1:ℝ)) u

def extendPath (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (i : ℕ) : ℝ :=
  if hi : i<n+1 then x ⟨i,hi⟩ else 0

lemma extendPath_restrict (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (WithLp.toLp 2 (fun i : Fin (n+1) => extendPath n x i.val)) = x := by
  ext i
  simp only [extendPath,dite_eq_left i.isLt]

lemma extendPath_mass (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (∑ i ∈ Finset.range (n+1), extendPath n x i^2) = ‖x‖^2 := by
  rw [← Fin.sum_univ_eq_sum_range,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [extendPath,dite_eq_left i.isLt]

lemma pathOperator_energy (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    inner ℝ x (pathOperator n x) = 2*‖x‖^2-pathEnergy n (extendPath n x) := by
  have h := pathOperator_inner n (extendPath n x)
  rw [extendPath_restrict] at h
  rw [h,pathEnergy,extendPath_mass]
  ring

lemma pathOperator_inner_le_two (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖=1) :
    inner ℝ x (pathOperator n x) ≤ 2 := by
  rw [pathOperator_energy,hx]
  have := pathEnergy_nonneg n (extendPath n x)
  linarith

lemma pathOperator_eigenvalue_le_two (n : ℕ) (i : Fin (n+1)) :
    (pathOperator_symmetric n).eigenvalues (by simp) i ≤ 2 := by
  let h := pathOperator_symmetric n
  have hh := pathOperator_inner_le_two n (h.eigenvectorBasis (by simp) i) ((h.eigenvectorBasis (by simp)).norm_eq_one i)
  rw [h.apply_eigenvectorBasis] at hh
  simpa only [inner_smul_right,real_inner_self_eq_norm_sq,
    (h.eigenvectorBasis (by simp)).norm_eq_one i,one_pow,mul_one,
    RCLike.ofReal_real_eq_id,id_eq] using hh

lemma triSampleOperator_form_good (n : ℕ) {ω : TriSample n} {h s : ℝ}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s) (hω : ω ∉ triBad n h)
    (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖=1) :
    |inner ℝ x (triSampleOperator n ω x)-inner ℝ x (pathOperator n x)| ≤
      formError n h s (2-inner ℝ x (pathOperator n x)) := by
  have hmass : (∑ i ∈ Finset.range (n+1), extendPath n x i^2) = 1 := by rw [extendPath_mass,hx]; norm_num
  have hc := triForm_good n hh hs hω (extendPath n x)
    (fun i hi => dite_eq_right (by omega)) hmass
  have ht := triSampleOperator_inner n ω (extendPath n x)
  rw [extendPath_restrict] at ht
  rw [ht,pathOperator_energy,hx]
  simp only [one_pow,mul_one]
  convert hc using 1
  congr 1
  ring

open MeasureTheory Set

lemma weighted_resolvent_integrable {s e : ℝ} (hs : 0 < s) (he : 0 ≤ e) :
    IntegrableOn (fun t : ℝ => t^(-5/8:ℝ)/(t+e)^2) (Ioi s) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-21/8:ℝ) < -1) hs).mono'
  · exact ((measurable_id.pow_const _).div ((measurable_id.add_const e).pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hs.trans ht
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      t^(-5/8:ℝ)/(t+e)^2 ≤ t^(-5/8:ℝ)/t^2 := by gcongr; linarith
      _ = t^(-21/8:ℝ) := by
        rw [← Real.rpow_two,← Real.rpow_sub ht0]
        norm_num

lemma fractional_power_integral_bound {s e : ℝ} (hs : 0 < s) (he : 0 ≤ e) :
    (s+e)^(-13/8:ℝ) ≤ (13/2:ℝ)*(∫ t : ℝ in Ioi s, t^(-5/8:ℝ)/(t+e)^2) := by
  have hx : 0 < s+e := by positivity
  have hlo : (∫ t : ℝ in Ioi (s+e), (1/4:ℝ)*t^(-21/8:ℝ)) ≤
      ∫ t : ℝ in Ioi (s+e), t^(-5/8:ℝ)/(t+e)^2 := by
    apply integral_mono_ae ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-21/8:ℝ)< -1) hx).const_mul _) (weighted_resolvent_integrable hx he)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hx.trans ht
    have het : e ≤ t := by change s+e < t at ht; linarith
    calc
      (1/4:ℝ)*t^(-21/8:ℝ) = t^(-5/8:ℝ)/(2*t)^2 := by
        have hp : t^(-21/8:ℝ) = t^(-5/8:ℝ)/t^2 := by
          rw [← Real.rpow_two,← Real.rpow_sub ht0]; norm_num
        rw [hp]; ring
      _ ≤ _ := by gcongr; linarith
  have hmono : (∫ t : ℝ in Ioi (s+e), t^(-5/8:ℝ)/(t+e)^2) ≤
      ∫ t : ℝ in Ioi s, t^(-5/8:ℝ)/(t+e)^2 := by
    apply integral_mono_measure (Measure.restrict_mono_set _ (Ioi_subset_Ioi (by linarith))) _
      (weighted_resolvent_integrable hs he)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (Real.rpow_nonneg (hs.trans ht).le _) (sq_nonneg _)
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-21/8:ℝ)< -1) hx] at hlo
  norm_num at hlo
  linarith

lemma fractional_trace_bound {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    {s C : ℝ} (hs : 0 < s)
    (htrace : ∀ t : ℝ, s ≤ t → (∑ i, (t+e i)⁻¹^2) ≤ C / Real.sqrt t) :
    (∑ i, (s+e i)^(-13/8:ℝ)) ≤ 52*C*s^(-1/8:ℝ) := by
  have hint (i : ι) := weighted_resolvent_integrable hs (he i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => fractional_power_integral_bound hs (he i))
  simp only [← Finset.mul_sum] at hsum
  rw [← integral_finsetSum _ (fun i _ => hint i)] at hsum
  have hi := integrable_finsetSum Finset.univ (fun i _ => hint i)
  have hupper : (∫ t : ℝ in Ioi s, ∑ i, t^(-5/8:ℝ)/(t+e i)^2) ≤
      ∫ t : ℝ in Ioi s, C*t^(-9/8:ℝ) := by
    apply integral_mono_ae hi ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-9/8:ℝ)< -1) hs).const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hs.trans ht
    calc
      (∑ i, t^(-5/8:ℝ)/(t+e i)^2) = t^(-5/8:ℝ)*(∑ i, (t+e i)⁻¹^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; simp only [inv_pow,div_eq_mul_inv]
      _ ≤ t^(-5/8:ℝ)*(C/Real.sqrt t) := mul_le_mul_of_nonneg_left (htrace t ht.le) (by positivity)
      _ = C*t^(-9/8:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have hp : t^(-5/8:ℝ)/t^(1/2:ℝ) = t^(-9/8:ℝ) := by rw [← Real.rpow_sub ht0]; norm_num
        calc
          _ = C*(t^(-5/8:ℝ)/t^(1/2:ℝ)) := by ring
          _ = _ := by rw [hp]
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-9/8:ℝ)< -1) hs] at hupper
  norm_num at hupper
  nlinarith



open MeasureTheory Set

lemma inverse_perturbation_bound {x d E : ℝ} (hx : 0 < x) (hclose : |d-x| ≤ E)
    (hsmall : E ≤ x/2) : 0 < d ∧ |d⁻¹-x⁻¹| ≤ 2*E/x^2 ∧ d⁻¹^2 ≤ 4*x⁻¹^2 := by
  have hd : 0 < d := by have := (abs_le.mp hclose).1; linarith
  have hdx : x/2 ≤ d := by have := (abs_le.mp hclose).1; linarith
  have he : 0 ≤ E := (abs_nonneg _).trans hclose
  refine ⟨hd,?_,?_⟩
  · have hid : d⁻¹-x⁻¹ = (x-d)/(d*x) := by field_simp
    rw [hid,abs_div,abs_of_pos (mul_pos hd hx),abs_sub_comm]
    calc
      |d-x|/(d*x) ≤ E/(d*x) := by gcongr
      _ ≤ E/((x/2)*x) := div_le_div_of_nonneg_left he (by positivity)
        (mul_le_mul_of_nonneg_right hdx hx.le)
      _ = 2*E/x^2 := by field_simp
  · have hinv : d⁻¹ ≤ 2*x⁻¹ := by
      have hh := one_div_le_one_div_of_le (by positivity : 0 < x/2) hdx
      have heq : (x/2)⁻¹ = 2*x⁻¹ := by field_simp
      simpa only [one_div,heq] using hh
    calc
      d⁻¹^2 ≤ (2*x⁻¹)^2 := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 2
      _ = _ := by ring

lemma inverse_perturbation_bound' {x d E : ℝ} (hx : 0 < x) (hclose : |d-x| ≤ E)
    (hsmall : E ≤ x/2) : |d⁻¹-x⁻¹| ≤ 2*E/x^2 :=
  (inverse_perturbation_bound hx hclose hsmall).2.1

lemma resolvent_trace_transfer {ι : Type*} [Fintype ι] (e lam : ι → ℝ)
    {A B C s₀ s D : ℝ} (he : ∀ i, 0 ≤ e i) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hclose : ∀ i, |lam i-(2-e i)| ≤ edgeError A B C s₀ (e i))
    (hsmall : A*s₀^(-5/8:ℝ)+B/s₀+C ≤ 1/2)
    (htrace : ∀ t : ℝ, s ≤ t → (∑ i, (t+e i)⁻¹^2) ≤ D / Real.sqrt t) :
    (∀ i, 0 < 2+s-lam i) ∧
    (∑ i, (2+s-lam i)⁻¹^2) ≤ 4*D/Real.sqrt s ∧
    |(∑ i, (2+s-lam i)⁻¹)-(∑ i, (s+e i)⁻¹)| ≤
      104*A*D*s^(-1/8:ℝ)+2*B*(D/Real.sqrt s)+2*C*(∑ i, (s+e i)⁻¹) := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hrel (i : ι) : edgeError A B C s₀ (e i) ≤ (s+e i)/2 := by
    have hh := edgeError_relative hA hB hC hs₀ hs (he i)
    have hei := he i
    exact hh.trans ((mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (by ring))
  have hc (i : ι) : |(2+s-lam i)-(s+e i)| ≤ edgeError A B C s₀ (e i) := by
    convert hclose i using 1
    rw [show 2+s-lam i-(s+e i) = -(lam i-(2-e i)) by ring,abs_neg]
  have hh (i : ι) := inverse_perturbation_bound (add_pos_of_pos_of_nonneg hspos (he i)) (hc i) (hrel i)
  refine ⟨fun i => (hh i).1,?_,?_⟩
  · calc
      _ ≤ ∑ i, 4*(s+e i)⁻¹^2 := Finset.sum_le_sum (fun i _ => (hh i).2.2)
      _ = 4*∑ i, (s+e i)⁻¹^2 := by rw [Finset.mul_sum]
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (htrace s le_rfl) (by norm_num : (0:ℝ) ≤ 4)
  · have hpoint (i : ι) : 2*edgeError A B C s₀ (e i)/(s+e i)^2 ≤
        2*A*(s+e i)^(-13/8:ℝ)+2*B*(s+e i)⁻¹^2+2*C*(s+e i)⁻¹ := by
      have hei := he i
      have hx : 0 < s+e i := by positivity
      have hexp : (e i+s₀)^(3/8:ℝ) ≤ (s+e i)^(3/8:ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hp : (s+e i)^(3/8:ℝ)/(s+e i)^2 = (s+e i)^(-13/8:ℝ) := by
        rw [← Real.rpow_two,← Real.rpow_sub hx]; norm_num
      have hCe : C*e i ≤ C*(s+e i) := by gcongr; linarith
      calc
        _ ≤ 2*(A*(s+e i)^(3/8:ℝ)+B+C*(s+e i))/(s+e i)^2 := by
          unfold edgeError; gcongr
        _ = _ := by rw [show 2*(A*(s+e i)^(3/8:ℝ)+B+C*(s+e i))/(s+e i)^2 =
            2*A*((s+e i)^(3/8:ℝ)/(s+e i)^2)+2*B*(s+e i)⁻¹^2+2*C*(s+e i)⁻¹ by field_simp,hp]
    calc
      _ = |∑ i, ((2+s-lam i)⁻¹-(s+e i)⁻¹)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |(2+s-lam i)⁻¹-(s+e i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (2*A*(s+e i)^(-13/8:ℝ)+2*B*(s+e i)⁻¹^2+2*C*(s+e i)⁻¹) :=
        Finset.sum_le_sum (fun i _ => (hh i).2.1.trans (hpoint i))
      _ = 2*A*(∑ i, (s+e i)^(-13/8:ℝ))+2*B*(∑ i, (s+e i)⁻¹^2)+2*C*(∑ i, (s+e i)⁻¹) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := by
        have hf := fractional_trace_bound e he hspos htrace
        have ht := htrace s le_rfl
        nlinarith [mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2*A),
          mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*B)]


def formA (n : ℕ) (h : ℝ) : ℝ :=
  41472 * Real.sqrt (32 * (entryVariance n : ℝ)) * (h + 1) *
    ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ)

def formB (n : ℕ) : ℝ := 8 / (n+1)

def formC (n : ℕ) : ℝ := 16 / Real.sqrt (n+1:ℝ)

lemma formError_eq (n : ℕ) (h s e : ℝ) :
    formError n h s e = edgeError (formA n h) (formB n) (formC n) s e := rfl

lemma formA_nonneg (n : ℕ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ formA n h := by unfold formA; positivity

lemma formB_nonneg (n : ℕ) : 0 ≤ formB n := by unfold formB; positivity

lemma formC_nonneg (n : ℕ) : 0 ≤ formC n := by unfold formC; positivity

def orderedJacobiGaps (n : ℕ) (i : Fin (n+1)) : ℝ :=
  2-(pathOperator_symmetric n).eigenvalues (by simp) i

def sampleEigenvalues (n : ℕ) (ω : TriSample n) : Fin (n+1) → ℝ :=
  (triSampleOperator_symmetric n ω).eigenvalues (by simp)

lemma orderedJacobiGaps_nonneg (n : ℕ) (i : Fin (n+1)) : 0 ≤ orderedJacobiGaps n i :=
  sub_nonneg.mpr (pathOperator_eigenvalue_le_two n i)

lemma triSample_eigenvalue_good (n : ℕ) {ω : TriSample n} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1)
    (hω : ω ∉ triBad n h) (i : Fin (n+1)) :
    |sampleEigenvalues n ω i-(2-orderedJacobiGaps n i)| ≤
      edgeError (formA n h) (formB n) (formC n) s (orderedJacobiGaps n i) := by
  have hm := edgeError_eigenvalue_comparison_mono (B := formB n)
    (formA_nonneg n hh) (formC_nonneg n) hs hsmall
  have he := eigenvalue_form_comparison (triSampleOperator_symmetric n ω) (pathOperator_symmetric n)
    (by simp) hm.1 hm.2 (pathOperator_eigenvalue_le_two n)
    (pathOperator_inner_le_two n)
    (fun x hx => by simpa only [← formError_eq] using triSampleOperator_form_good n hh hscale hω x hx) i
  simpa only [sampleEigenvalues,orderedJacobiGaps,sub_sub_cancel] using he

lemma symmetric_eigenvalue_sum_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {m n : ℕ} (hm : Module.finrank ℝ E = m) (hn : Module.finrank ℝ E = n) (f : ℝ → ℝ) :
    (∑ i, f (hT.eigenvalues hm i)) = ∑ i, f (hT.eigenvalues hn i) := by
  subst m
  subst n
  rfl

lemma sum_orderedJacobiGaps (n : ℕ) (f : ℝ → ℝ) :
    (∑ i, f (orderedJacobiGaps n i)) = ∑ i, f (jacobiGaps (n+1) i) := by
  let e : Fin (Fintype.card (Fin (n+1))) ≃ Fin (n+1) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hh := Equiv.sum_comp e (fun i => f (jacobiGaps (n+1) i))
  simp only [jacobiGaps,Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] at hh
  calc
    _ = ∑ i, f (2-(jacobi_hermitian (n+1:ℝ)⁻¹ (n+1)).eigenvalues₀ i) :=
      symmetric_eigenvalue_sum_congr (pathOperator_symmetric n) (by simp) finrank_euclideanSpace (fun x => f (2-x))
    _ = _ := by
      simpa only [jacobiGaps,Matrix.IsHermitian.eigenvalues,Nat.cast_add,Nat.cast_one] using hh

lemma orderedJacobi_trace (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hscale : 2 ≤ (n+1:ℝ)*s*Real.sqrt s) :
    (∑ i, (s+orderedJacobiGaps n i)⁻¹^2) ≤ 4*(n+1:ℝ)/Real.sqrt s ∧
    |(∑ i, (s+orderedJacobiGaps n i)⁻¹)/(n+1)-semicircleResolvent s| ≤ 2/((n+1:ℝ)*s) ∧
    (∑ i, (s+orderedJacobiGaps n i)⁻¹) ≤ n+1 := by
  have ht := jacobi_resolvent_estimates (Nat.succ_pos n) hs (by simpa using hscale)
  have hn : (0:ℝ) < n+1 := by positivity
  have hR := semicircleResolvent_le_one hs.le
  rw [sum_orderedJacobiGaps n (fun e => (s+e)⁻¹^2),
    sum_orderedJacobiGaps n (fun e => (s+e)⁻¹)]
  simp only [empiricalResolventSquare,empiricalResolvent,Fintype.card_fin,Nat.cast_succ] at ht
  refine ⟨?_,?_,?_⟩
  · calc
      _ = (n+1:ℝ)*((n+1:ℝ)⁻¹*(∑ i, (s+jacobiGaps (n+1) i)⁻¹^2)) := by field_simp
      _ ≤ (n+1:ℝ)*(4/Real.sqrt s) := mul_le_mul_of_nonneg_left ht.1 hn.le
      _ = _ := by ring
  · rw [div_eq_mul_inv,mul_comm,abs_sub_comm,abs_of_nonneg ht.2.1]
    exact ht.2.2
  · have hsum : (n+1:ℝ)⁻¹*(∑ i, (s+jacobiGaps (n+1) i)⁻¹) ≤ 1 := by linarith [ht.2.1]
    have hmul := mul_le_mul_of_nonneg_left hsum hn.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul,mul_one] using hmul

lemma triSample_resolvent_good (n : ℕ) {ω : TriSample n} {h s₀ s : ℝ}
    (hh : 0 ≤ h) (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s₀)
    (hsmall : formA n h*s₀^(-5/8:ℝ)+formB n/s₀+formC n ≤ 1/2)
    (hspace : 2 ≤ (n+1:ℝ)*s₀*Real.sqrt s₀)
    (hω : ω ∉ triBad n h) :
    (∀ i, 0 < 2+s-sampleEigenvalues n ω i) ∧
    (∑ i, (2+s-sampleEigenvalues n ω i)⁻¹^2)/(n+1) ≤ 16/Real.sqrt s ∧
    |(∑ i, (2+s-sampleEigenvalues n ω i)⁻¹)/(n+1)-semicircleResolvent s| ≤
      416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n+2/((n+1:ℝ)*s) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hspos : 0 < s := hs₀.trans_le hs
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hmono : formA n h*(3/8:ℝ)*s₀^(-5/8:ℝ)+formC n ≤ 1 := by
    have : 0 ≤ formB n/s₀ := by positivity
    have : 0 ≤ formA n h*s₀^(-5/8:ℝ) := by positivity
    nlinarith
  have hsc (t : ℝ) (hst : s ≤ t) : 2 ≤ (n+1:ℝ)*t*Real.sqrt t := by
    have htpos : 0 < t := hspos.trans_le hst
    exact hspace.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hs.trans hst) hn.le)
      (Real.sqrt_le_sqrt (hs.trans hst)) (Real.sqrt_nonneg _) (by positivity))
  have hc := resolvent_trace_transfer (orderedJacobiGaps n) (sampleEigenvalues n ω)
    (orderedJacobiGaps_nonneg n) hA hB hC hs₀ hs
    (triSample_eigenvalue_good n hh hs₀ hscale hmono hω) hsmall
    (fun t hst => (orderedJacobi_trace n (hspos.trans_le hst) (hsc t hst)).1)
  have hd := orderedJacobi_trace n hspos (hsc s le_rfl)
  refine ⟨hc.1,?_,?_⟩
  · apply (div_le_iff₀ hn).mpr
    convert hc.2.1 using 1
    all_goals first | rfl | ring
  · have hdif : |(∑ i, (2+s-sampleEigenvalues n ω i)⁻¹)/(n+1)-
        (∑ i, (s+orderedJacobiGaps n i)⁻¹)/(n+1)| ≤
        416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n := by
      rw [← sub_div,abs_div,abs_of_pos hn]
      apply (div_le_iff₀ hn).mpr
      calc
        _ ≤ _ := hc.2.2
        _ ≤ 104*formA n h*(4*(n+1))*s^(-1/8:ℝ)+2*formB n*(4*(n+1)/Real.sqrt s)+2*formC n*(n+1) := by gcongr; exact hd.2.2
        _ = _ := by ring
    exact (abs_sub_le _ _ _).trans (add_le_add hdif hd.2.1)

end CriticalSK

end

end OAI
