import Mathlib
import OAI.Probability.SKRatio.Matrices.GOERegression
import OAI.Probability.SKRatio.Gaussian.ExponentialEvents

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

lemma integrable_bounded_lipschitz {F : Type*} [PseudoMetricSpace F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [IsProbabilityMeasure μ]
    {f : F → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) : Integrable f μ := by
  apply Integrable.of_bound hf.continuous.measurable.aestronglyMeasurable B
  exact Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hB)

lemma bounded_product_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {K L B D : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hb : ∀ x, |f x| ≤ B) (hd : ∀ x, |g x| ≤ D) :
    LipschitzWith (K*D+L*B) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hid : f x*g x-f y*g y = (f x-f y)*g x + f y*(g x-g y) := by ring
  rw [hid]
  calc
    |(f x-f y)*g x+f y*(g x-g y)| ≤ |(f x-f y)*g x|+|f y*(g x-g y)| := abs_add_le _ _
    _ = |f x-f y| * |g x|+|f y| * |g x-g y| := by rw [abs_mul, abs_mul]
    _ ≤ ((K:ℝ)*dist x y)*(D:ℝ)+(B:ℝ)*((L:ℝ)*dist x y) := by
      gcongr
      · exact hf.dist_le_mul x y
      · exact hd x
      · exact hb y
      · exact hg.dist_le_mul x y
    _ = ((K*D+L*B:ℝ≥0):ℝ)*dist x y := by push_cast; ring
lemma gaussian_integrable_exp_quarter_sq :
    Integrable (fun x : ℝ => Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1:ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  apply h.congr
  filter_upwards [] with x
  symm
  simp only [toReal_gaussianPDF,
    smul_eq_mul, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, one_div]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma iid_upper_deviation_of_log_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hXi : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (ν : Measure ℝ)
    (hLaw : ∀ i, HasLaw (X i) ν μ) {t : ℝ} (ht : 0 < t)
    (hi : Integrable (fun x : ℝ => Real.exp (t*x)) ν) (a : ℝ) :
    μ {ω | a ≤ (∑ i, X i ω)/(n:ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((t*a-cgf id ν t)*(n:ℝ)))) := by
  have he (i : Fin n) : Integrable (fun ω => Real.exp (t*X i ω)) μ :=
    by
      rw [← (hLaw i).map_eq] at hi
      exact (integrable_map_measure (by fun_prop) (hLaw i).aemeasurable).mp hi
  have hsum := hXi.integrable_exp_mul_sum hXm (s := Finset.univ) (fun i _ => he i)
  have hc := measure_ge_le_exp_cgf (μ := μ) (X := ∑ i, X i) (a*n) ht.le hsum
  have hcgf (i : Fin n) : cgf (X i) μ t = cgf id ν t := by
    unfold cgf mgf
    congr 1
    exact (hLaw i).integral_comp (f := fun x : ℝ => Real.exp (t*x)) (by fun_prop)
  rw [hXi.cgf_sum hXm (fun i _ => he i)] at hc
  simp only [hcgf, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hc
  have hset : {ω | a*(n:ℝ) ≤ (∑ i, X i) ω} =
      {ω | a ≤ (∑ i, X i ω)/(n:ℝ)} := by
    ext ω
    simp only [Finset.sum_apply, Set.mem_ofPred_eq,
      le_div_iff₀ ((show (0:ℝ)<n from Nat.cast_pos.mpr hn))]
  rw [hset] at hc
  have h := ENNReal.ofReal_le_ofReal hc
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  convert h using 2
  congr 1
  ring

noncomputable def squareTail (R x : ℝ) : ℝ := if R < |x| then x^2 else 0

lemma squareTail_nonneg (R x : ℝ) : 0 ≤ squareTail R x := by
  unfold squareTail
  split_ifs <;> positivity

lemma squareTail_le (R x : ℝ) : squareTail R x ≤ x^2 := by
  unfold squareTail
  split_ifs <;> simp [sq_nonneg]

lemma measurable_squareTail (R : ℝ) : Measurable (squareTail R) := by
  unfold squareTail
  exact Measurable.ite (measurableSet_lt measurable_const measurable_abs)
    (by fun_prop) measurable_const

lemma integrable_exp_squareTail {ν : Measure ℝ}
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) (R : ℝ) :
    Integrable (fun x => Real.exp (squareTail R x/4)) ν := by
  apply hi.mono' (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squareTail_le R x) (by norm_num))

lemma tendsto_squareTail_mgf {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) :
    Tendsto (fun R : ℕ => ∫ x, Real.exp (squareTail R x/4) ∂ν) atTop (𝓝 1) := by
  have ht : Tendsto (fun R : ℕ => ∫ x, Real.exp (squareTail R x/4) ∂ν)
      atTop (𝓝 (∫ _x : ℝ, (1:ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => Real.exp (x^2/4))
    · intro R
      exact (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
    · exact hi
    · intro R
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squareTail_le R x) (by norm_num))
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
      have hx : |x| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      simp [squareTail, not_lt.mpr hx]
  simpa using ht

def ExponentialSquareTails {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ExponentiallyRare ρ (fun n => {h | ε ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)})

theorem iid_exponential_squareTails {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (X : ∀ n, H n → Fin n → ℝ)
    (hXm : ∀ n i, Measurable (fun h => X n h i))
    (hXi : ∀ n, iIndepFun (fun i h => X n h i) (ρ n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hLaw : ∀ n i, HasLaw (fun h => X n h i) ν (ρ n))
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) :
    ExponentialSquareTails ρ X := by
  intro ε hε
  have ht : Tendsto (fun R : ℕ => Real.log (∫ x, Real.exp (squareTail R x/4) ∂ν))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp
      (tendsto_squareTail_mgf hi)
  have he : ∀ᶠ R : ℕ in atTop,
      Real.log (∫ x, Real.exp (squareTail R x/4) ∂ν) < ε/4 :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨R,hR,hm⟩ := (eventually_ge_atTop 1 |>.and he).exists
  let m := Real.log (∫ x, Real.exp (squareTail R x/4) ∂ν)
  have htm : Measurable (squareTail R) := measurable_squareTail R
  have hl : HasLaw (squareTail R) (ν.map (squareTail R)) ν := ⟨htm.aemeasurable,rfl⟩
  have hcg : cgf id (ν.map (squareTail R)) (1/4) = m := by
    unfold cgf mgf m
    rw [integral_map htm.aemeasurable (by fun_prop)]
    congr 2
    ext x
    simp only [id_eq]
    congr 1
    ring
  have hint : Integrable (fun x : ℝ => Real.exp (1/4*x)) (ν.map (squareTail R)) := by
    rw [integrable_map_measure (by fun_prop) htm.aemeasurable]
    simpa only [Function.comp_def, one_div_mul_eq_div] using integrable_exp_squareTail hi R
  refine ⟨R,by exact_mod_cast hR,1,ε/4-m,by norm_num,sub_pos.mpr hm,?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := iid_upper_deviation_of_log_mgf hn (fun i h => squareTail R (X n h i))
    ((hXi n).comp (fun _ => squareTail R) (fun _ => htm))
    (fun i => htm.comp (hXm n i)) (ν.map (squareTail R))
    (fun i => hl.fun_comp (hLaw n i)) (by norm_num : (0:ℝ)<1/4) hint ε
  rw [hcg] at hb
  simpa only [one_mul, one_div_mul_eq_div, neg_mul] using hb

theorem gaussian_exponential_squareTails :
    ExponentialSquareTails (fun n => standardArrayLaw (Fin n)) (fun _ g => g) := by
  exact iid_exponential_squareTails _ _ (fun _ _ => measurable_pi_apply _)
    (fun _ => coordinates_independent) (gaussianReal 0 1) (fun _ _ => coordinate_hasLaw _)
    gaussian_integrable_exp_quarter_sq

lemma squareTail_perturbation (R x y : ℝ) (_hR : 0 ≤ R) :
    squareTail (2*R) y ≤ 4*squareTail R x+4*(x-y)^2 := by
  unfold squareTail
  split_ifs with hy hx
  · nlinarith [sq_nonneg (x+y)]
  · have hx' := le_of_not_gt hx
    have habs := abs_sub_abs_le_abs_sub y x
    have hxy : R < |y-x| := by linarith
    have hyb : |y| ≤ 2*|y-x| := by linarith
    have hs := mul_self_le_mul_self (abs_nonneg y) hyb
    nlinarith [sq_abs y, sq_abs (y-x)]
  · positivity
  · positivity

theorem ExponentialSquareTails.l2_stability
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    (hXY : ExponentialConvergence ρ
      (fun n h => (∑ i, (X n h i-Y n h i)^2)/(n:ℝ)) 0) :
    ExponentialSquareTails ρ Y := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX (ε/8) (by positivity)
  refine ⟨2*R,by positivity,?_⟩
  apply (ht.union (hXY (ε/8) (by positivity))).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  simp only [Set.mem_ofPred_eq] at hh
  by_cases hx : ε/8 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  · exact Or.inl hx
  apply Or.inr
  have hb : (∑ i, squareTail (2*R) (Y n h i))/(n:ℝ) ≤
      4*((∑ i, squareTail R (X n h i))/(n:ℝ))+
      4*((∑ i, (X n h i-Y n h i)^2)/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, (4*squareTail R (X n h i)+4*(X n h i-Y n h i)^2))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun i _ => squareTail_perturbation R _ _ hR.le)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  change ε/8 ≤ dist ((∑ i, (X n h i-Y n h i)^2)/(n:ℝ)) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hx' := lt_of_not_ge hx
  linarith

lemma squareTail_add (R x y : ℝ) (_hR : 0 ≤ R) :
    squareTail (2*R) (x+y) ≤ 4*(squareTail R x+squareTail R y) := by
  unfold squareTail
  split_ifs with hxy hx hy hy
  · nlinarith [sq_nonneg (x-y)]
  · have hy' := le_of_not_gt hy
    have hxy' : |y| ≤ |x| := hy'.trans (le_of_lt hx)
    have hs := mul_self_le_mul_self (abs_nonneg y) hxy'
    nlinarith [sq_abs x, sq_abs y, sq_nonneg (x-y)]
  · have hx' := le_of_not_gt hx
    have hxy' : |x| ≤ |y| := hx'.trans (le_of_lt hy)
    have hs := mul_self_le_mul_self (abs_nonneg x) hxy'
    nlinarith [sq_abs x, sq_abs y, sq_nonneg (x-y)]
  · have hx' := le_of_not_gt hx
    have hy' := le_of_not_gt hy
    have := abs_add_le x y
    linarith
  all_goals positivity

lemma squareTail_antitone (x : ℝ) : Antitone (fun R => squareTail R x) := by
  intro R S hRS
  dsimp only [squareTail]
  split_ifs <;> first | exact le_rfl | positivity | (exfalso; linarith)

theorem ExponentialSquareTails.add
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X) (hY : ExponentialSquareTails ρ Y) :
    ExponentialSquareTails ρ (fun n h i => X n h i+Y n h i) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX (ε/8) (by positivity)
  obtain ⟨S,hS,hs⟩ := hY (ε/8) (by positivity)
  refine ⟨2*max R S,by positivity,?_⟩
  apply (ht.union hs).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  simp only [Set.mem_ofPred_eq] at hh
  by_cases hx : ε/8 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  · exact Or.inl hx
  apply Or.inr
  have hb : (∑ i, squareTail (2*max R S) (X n h i+Y n h i))/(n:ℝ) ≤
      4*((∑ i, squareTail R (X n h i))/(n:ℝ))+
      4*((∑ i, squareTail S (Y n h i))/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, 4*(squareTail R (X n h i)+squareTail S (Y n h i)))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        exact (squareTail_add _ _ _ (le_max_of_le_left hR.le)).trans
          (mul_le_mul_of_nonneg_left (add_le_add
            (squareTail_antitone _ (le_max_left _ _))
            (squareTail_antitone _ (le_max_right _ _))) (by norm_num))
      _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]; ring
  have hx' := lt_of_not_ge hx
  change ε/8 ≤ (∑ i, squareTail S (Y n h i))/(n:ℝ)
  linarith

lemma squareTail_mul (R x a B : ℝ) (_hR : 0 ≤ R) (ha : |a| ≤ B) :
    squareTail (B*R) (a*x) ≤ B^2*squareTail R x := by
  have hB := (abs_nonneg a).trans ha
  unfold squareTail
  split_ifs with hax hx
  · have hs := mul_self_le_mul_self (abs_nonneg a) ha
    have hsq : a^2 ≤ B^2 := by nlinarith [sq_abs a]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg x)]
  · have hx' := le_of_not_gt hx
    have hab : |a*x| ≤ B*R := by rw [abs_mul]; exact mul_le_mul ha hx' (abs_nonneg x) hB
    exact False.elim ((not_lt_of_ge hab) hax)
  all_goals positivity

lemma ExponentialSquareTails.bounded_mul
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    (a : ∀ n, H n → Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n h i, |a n h i| ≤ B) :
    ExponentialSquareTails ρ (fun n h i => a n h i*X n h i) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX (ε/(B+1)^2) (by positivity)
  refine ⟨(B+1)*R,by positivity,ht.mono ?_⟩
  filter_upwards [] with n
  intro h hh
  change ε/(B+1)^2 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  apply (div_le_iff₀ (by positivity : 0 < (B+1)^2)).mpr
  have hb : (∑ i, squareTail ((B+1)*R) (a n h i*X n h i))/(n:ℝ) ≤
      (B+1)^2*((∑ i, squareTail R (X n h i))/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, (B+1)^2*squareTail R (X n h i))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun i _ => squareTail_mul R _ _ _ hR.le ((ha n h i).trans (by linarith)))
      _ = _ := by rw [← Finset.mul_sum]; ring
  exact (show ε ≤ _ from hh).trans (by simpa [mul_comm] using hb)

noncomputable def clippedSquare (R x : ℝ) : ℝ := (min |x| R)^2

lemma clippedSquare_bounds (R x : ℝ) (hR : 0 ≤ R) :
    0 ≤ clippedSquare R x ∧ clippedSquare R x ≤ x^2 ∧ clippedSquare R x ≤ R^2 := by
  have hm := le_min (abs_nonneg x) hR
  have hx := mul_self_le_mul_self hm (min_le_left |x| R)
  have hr := mul_self_le_mul_self hm (min_le_right |x| R)
  dsimp [clippedSquare]
  exact ⟨sq_nonneg _, by nlinarith [sq_abs x], by nlinarith⟩

lemma clippedSquare_error (R x : ℝ) (hR : 0 ≤ R) :
    |x^2-clippedSquare R x| ≤ squareTail R x := by
  rw [abs_of_nonneg (sub_nonneg.mpr (clippedSquare_bounds R x hR).2.1)]
  by_cases hx : R < |x|
  · simp only [squareTail, ite_eq_left hx]
    linarith [(clippedSquare_bounds R x hR).1]
  · simp [clippedSquare, squareTail, hx, min_eq_left (le_of_not_gt hx)]

lemma clippedSquare_lipschitz (R : ℝ≥0) :
    LipschitzWith (2*R) (clippedSquare R) := by
  have ha : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  have h : LipschitzWith 1 (fun x : ℝ => min |x| (R:ℝ)) := ha.min_const _
  have hb (x : ℝ) : |min |x| (R:ℝ)| ≤ R := by
    rw [abs_of_nonneg (le_min (abs_nonneg _) R.coe_nonneg)]
    exact min_le_right _ _
  change LipschitzWith (2*R) (fun x : ℝ => (min |x| (R:ℝ))^2)
  simpa only [one_mul, ← two_mul, pow_two] using bounded_product_lipschitz h h hb hb

lemma integrable_clippedSquare (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R : ℝ≥0) : Integrable (clippedSquare R) ν := by
  apply integrable_bounded_lipschitz ν (clippedSquare_lipschitz R) ((R:ℝ)^2)
  intro x
  rw [abs_of_nonneg (clippedSquare_bounds R x R.coe_nonneg).1]
  exact (clippedSquare_bounds R x R.coe_nonneg).2.2

lemma tendsto_integral_clippedSquare (ν : Measure ℝ)
    (hi : Integrable (fun x : ℝ => x^2) ν) :
    Tendsto (fun R : ℕ => ∫ x, clippedSquare R x ∂ν) atTop (𝓝 (∫ x, x^2 ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x^2)
  · intro R
    exact (clippedSquare_lipschitz R).continuous.measurable.aestronglyMeasurable
  · exact hi
  · intro R
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (clippedSquare_bounds R x (Nat.cast_nonneg _)).1]
    exact (clippedSquare_bounds R x (Nat.cast_nonneg _)).2.1
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
    have hx : |x| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
    simp [clippedSquare, min_eq_left hx]

theorem ExponentialEmpiricalConcentration.secondMoment
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (hT : ExponentialSquareTails ρ X)
    (hi : Integrable (fun x : ℝ => x^2) ν) :
    ExponentialConvergence ρ (fun n h => (∑ i, X n h i^2)/(n:ℝ))
      (∫ x, x^2 ∂ν) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hT (ε/3) (by positivity)
  have hbias : ∀ᶠ k : ℕ in atTop,
      |(∫ x, clippedSquare k x ∂ν) - ∫ x, x^2 ∂ν| < ε/3 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp
      (tendsto_integral_clippedSquare ν hi)) (ε/3) (by positivity)
  obtain ⟨k,hk,hbias⟩ := ((eventually_ge_atTop ⌈R⌉₊).and hbias).exists
  have hRk : R ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hc : ExponentiallyRare ρ (fun n => {h | ε/3 ≤
      |(∑ i, clippedSquare k (X n h i))/(n:ℝ) - ∫ x, clippedSquare k x ∂ν|}) := by
    apply hX (clippedSquare k) (2*(k:ℝ≥0)) (clippedSquare_lipschitz k)
      ((k:ℝ)^2)
    · intro x
      rw [abs_of_nonneg (clippedSquare_bounds k x (Nat.cast_nonneg _)).1]
      exact (clippedSquare_bounds k x (Nat.cast_nonneg _)).2.2
    · positivity
  apply (ht.union hc).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  change ε ≤ |(∑ i, X n h i^2)/(n:ℝ) - ∫ x, x^2 ∂ν| at hh
  by_cases htail : ε/3 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  · exact Or.inl htail
  apply Or.inr
  by_contra hclip
  have herror : |(∑ i, X n h i^2)/(n:ℝ) -
      (∑ i, clippedSquare k (X n h i))/(n:ℝ)| ≤
      (∑ i, squareTail R (X n h i))/(n:ℝ) := by
    rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n), ← Finset.sum_sub_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      _ ≤ ∑ i, |X n h i^2-clippedSquare k (X n h i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, squareTail R (X n h i) := by
        apply Finset.sum_le_sum
        intro i _
        exact (clippedSquare_error k _ (Nat.cast_nonneg _)).trans
          (squareTail_antitone _ hRk)
  have htriangle := abs_add_three
    ((∑ i, X n h i^2)/(n:ℝ)-(∑ i, clippedSquare k (X n h i))/(n:ℝ))
    ((∑ i, clippedSquare k (X n h i))/(n:ℝ)-∫ x, clippedSquare k x ∂ν)
    ((∫ x, clippedSquare k x ∂ν)-∫ x, x^2 ∂ν)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at htriangle
  have ht' := lt_of_not_ge htail
  simp only [Set.mem_ofPred_eq] at hclip
  have hc' := lt_of_not_ge hclip
  linarith

lemma exponentialSquareTails_of_bounded
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → ℝ) (B : ℝ)
    (hB : ∀ n h i, |X n h i| ≤ B) : ExponentialSquareTails ρ X := by
  intro ε hε
  refine ⟨|B|+1,by positivity, (exponentiallyRare_empty ρ).mono ?_⟩
  filter_upwards [] with n
  intro h hh
  have hz : ∀ i, squareTail (|B|+1) (X n h i) = 0 := by
    intro i
    have hb := (hB n h i).trans (le_abs_self B)
    simp [squareTail, show ¬ |B|+1 < |X n h i| by linarith]
  simp only [Set.mem_ofPred_eq, hz, Finset.sum_const_zero, zero_div] at hh
  exact False.elim ((not_le_of_gt hε) hh)

end SKRatioClock.Regression

end
end

end OAI
