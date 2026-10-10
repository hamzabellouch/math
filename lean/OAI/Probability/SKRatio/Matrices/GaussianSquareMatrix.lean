import Mathlib
import OAI.Probability.SKRatio.Matrices.RandomMatrixBounded
import OAI.Probability.SKRatio.Gaussian.ExponentialBounds
import OAI.Probability.SKRatio.Matrices.GaussianSquareTails

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma independent_sum_upper_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hXi : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (s : Finset ι) {t M : ℝ} (ht : 0<t)
    (hi : ∀ i ∈ s, Integrable (fun ω => exp (t*X i ω)) μ)
    (hmgf : ∀ i ∈ s, cgf (X i) μ t ≤ M) (hM : 0≤M)
    {n : ℕ} (hn : 0<n) (hcard : s.card≤n) (a : ℝ) :
    μ {ω | a ≤ (∑ i∈s, X i ω)/(n:ℝ)} ≤ ENNReal.ofReal (exp (-((t*a-M)*n))) := by
  have hsum := hXi.integrable_exp_mul_sum hXm (s := s) hi
  have hb := measure_ge_le_exp_cgf (μ := μ) (X := ∑ i∈s, X i) (a*n) ht.le hsum
  rw [hXi.cgf_sum hXm hi] at hb
  have hm : ∑ i∈s, cgf (X i) μ t ≤ (n:ℝ)*M := by
    calc
      _ ≤ ∑ _i∈s, M := Finset.sum_le_sum hmgf
      _ = (s.card:ℝ)*M := by simp
      _ ≤ (n:ℝ)*M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  have he : {ω | a*(n:ℝ) ≤ (∑ i∈s, X i) ω} = {ω | a ≤ (∑ i∈s, X i ω)/(n:ℝ)} := by
    ext ω
    simp only [Finset.sum_apply,mem_ofPred_eq,le_div_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ)<n)]
  rw [he] at hb
  have h := ENNReal.ofReal_le_ofReal hb
  simp only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
  linarith

lemma gaussian_squareTail_row_bound {a : ℝ} (ha : 0<a) :
    ∃ R c : ℝ, 0<R ∧ 0<c ∧
      (∫ z, squareTail R z ∂gaussianReal 0 1) < a ∧
      ∀ {ι : Type} [Fintype ι] (s : Finset ι) {n : ℕ}, 0<n → s.card ≤ n →
      standardArrayLaw ι {z | a ≤ (∑ i∈s, squareTail R (z i))/(n:ℝ)} ≤
        ENNReal.ofReal (exp (-c*n)) := by
  have ht : Tendsto (fun R : ℕ => log (∫ z, exp (squareTail R z/4) ∂gaussianReal 0 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,log_one] using (continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp
      (tendsto_squareTail_mgf gaussian_integrable_exp_quarter_sq)
  have hsq : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).integrable_sq
  have hm : Tendsto (fun R : ℕ => ∫ z, squareTail R z ∂gaussianReal 0 1) atTop (𝓝 0) := by
    have hb := tendsto_integral_of_dominated_convergence (fun z : ℝ => z^2)
      (μ := gaussianReal 0 1)
      (F := fun R : ℕ => squareTail R) (f := fun _ => (0:ℝ))
      (fun R => (measurable_squareTail R).aestronglyMeasurable) hsq
    have h := hb (fun R => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]
      exact squareTail_le _ _)) (ae_of_all _ (fun z => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈|z|⌉₊] with R hR
        have hz : |z| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
        simp [squareTail,not_lt.mpr hz]))
    simpa using h
  obtain ⟨R,hR,hmg,hmean⟩ := ((eventually_ge_atTop 1).and
    ((ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<a/4))).and
      (hm.eventually (gt_mem_nhds ha)))).exists
  let M := log (∫ z, exp (squareTail R z/4) ∂gaussianReal 0 1)
  have hM : 0≤M := by
    apply log_nonneg
    calc
      1 = ∫ _z : ℝ, (1:ℝ) ∂gaussianReal 0 1 := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_exp_squareTail gaussian_integrable_exp_quarter_sq R)
        (by intro z; exact one_le_exp_iff.mpr (div_nonneg (squareTail_nonneg _ _) (by norm_num)))
  refine ⟨R,a/4-M,by exact_mod_cast hR,sub_pos.mpr hmg,hmean,?_⟩
  intro ι _ s n hn hs
  have hc (i : ι) : cgf (fun z : ι → ℝ => squareTail R (z i)) (standardArrayLaw ι) (1/4) = M := by
    unfold cgf mgf M
    congr 1
    have hh := (coordinate_hasLaw i).integral_comp (f := fun z : ℝ => exp (squareTail R z/4)) (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
    simpa only [one_div_mul_eq_div, Function.comp_def] using hh
  have hi (i : ι) : Integrable (fun z : ι → ℝ => exp ((1/4)*squareTail R (z i))) (standardArrayLaw ι) := by
    have hh := integrable_exp_squareTail gaussian_integrable_exp_quarter_sq (R:ℝ)
    rw [←(coordinate_hasLaw i).map_eq] at hh
    have h := (integrable_map_measure (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable) (coordinate_hasLaw i).aemeasurable).mp hh
    simpa only [one_div_mul_eq_div, Function.comp_def] using h
  have hb := independent_sum_upper_tail (fun i (z : ι → ℝ) => squareTail R (z i))
    (coordinates_independent.comp (fun _ => squareTail R) (fun _ => measurable_squareTail R))
    (fun i => (measurable_squareTail R).comp (measurable_pi_apply i)) s
    (by norm_num : (0:ℝ)<1/4) (fun i _ => hi i) (fun i _ => le_of_eq (hc i)) hM hn hs a
  simpa only [one_div_mul_eq_div,neg_mul] using hb

def incidentEdges {n : ℕ} (i : Fin n) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.1.1 = i ∨ e.1.2 = i)

lemma incidentEdges_card_le {n : ℕ} (i : Fin n) : (incidentEdges i).card ≤ n := by
  let other (e : Edge n) : Fin n := if e.1.1 = i then e.1.2 else e.1.1
  have h := Finset.card_le_card_of_injOn other
    (t := (Finset.univ : Finset (Fin n))) (s := incidentEdges i)
    (fun _ _ => Finset.mem_univ _) (by
      intro e he f hf hef
      have he' : e.1.1 = i ∨ e.1.2 = i := (Finset.mem_filter.mp he).2
      have hf' : f.1.1 = i ∨ f.1.2 = i := (Finset.mem_filter.mp hf).2
      have ehe := e.2
      have ehf := f.2
      apply Subtype.ext
      apply Prod.ext
      all_goals dsimp [other] at hef; split_ifs at hef <;> rcases he' with he' | he' <;>
        rcases hf' with hf' | hf' <;> simp_all <;> omega)
  simpa using h

lemma sum_coupling_row {n : ℕ} (g : Disorder n) (i : Fin n) :
    ∑ j, coupling g i j = ∑ e ∈ incidentEdges i, g e := by
  have he := coupling_bilinear (fun j => if j=i then 1 else 0) (fun _ => 1) g
  simp only [mul_one,ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  rw [he,incidentEdges,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hh : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  by_cases h1 : e.1.1=i <;> by_cases h2 : e.1.2=i <;> simp_all

lemma abs_coupling {n : ℕ} (g : Disorder n) (i j : Fin n) :
    |coupling g i j| = coupling (fun e => |g e|) i j := by
  unfold coupling
  split_ifs <;> simp

lemma coupling_nonneg {n : ℕ} {g : Disorder n} (hg : ∀ e, 0 ≤ g e) (i j : Fin n) :
    0 ≤ coupling g i j := by
  unfold coupling
  split_ifs <;> first | exact hg _ | exact le_refl 0

lemma coupling_add {n : ℕ} (g h : Disorder n) :
    coupling (g+h) = coupling g + coupling h := by
  funext i j
  change coupling (g+h) i j = coupling g i j + coupling h i j
  unfold coupling
  split_ifs <;> simp_all

lemma coupling_sub {n : ℕ} (g h : Disorder n) :
    coupling (g-h) = coupling g - coupling h := by
  funext i j
  change coupling (g-h) i j = coupling g i j - coupling h i j
  unfold coupling
  split_ifs <;> simp_all

lemma coupling_const_mul {n : ℕ} (c : ℝ) (g : Disorder n) :
    coupling (fun e => c*g e) = c • coupling g := by
  funext i j
  change coupling (fun e => c*g e) i j = c*coupling g i j
  unfold coupling
  split_ifs <;> simp_all

lemma coupling_const_norm_le {n : ℕ} (c : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun _ => c))‖ ≤ n*|c| := by
  apply matrix_opNorm_le_schur _ (n*|c|) (by positivity)
  all_goals
    intro i
    calc
      _ ≤ ∑ _j : Fin n, |c| := Finset.sum_le_sum (fun j _ => by
        unfold coupling; split_ifs <;> simp [abs_nonneg])
      _ = _ := by simp

lemma integrable_standard_square : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
  simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).integrable_sq

lemma standard_square_integral : ∫ z : ℝ, z^2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal,sub_zero,NNReal.coe_one] using h

def clippedSquare (R z : ℝ) : ℝ := min (z^2) (R^2)

lemma continuous_clippedSquare (R : ℝ) : Continuous (clippedSquare R) := by
  unfold clippedSquare; fun_prop

lemma clippedSquare_nonneg (R z : ℝ) : 0 ≤ clippedSquare R z := le_min (sq_nonneg _) (sq_nonneg _)

lemma clippedSquare_le (R z : ℝ) : clippedSquare R z ≤ R^2 := min_le_right _ _

lemma square_sub_clip_nonneg (R z : ℝ) : 0 ≤ z^2-clippedSquare R z :=
  sub_nonneg.mpr (min_le_left _ _)

lemma square_sub_clip_le {R : ℝ} (hR : 0 ≤ R) (z : ℝ) :
    z^2-clippedSquare R z ≤ squareTail R z := by
  by_cases hz : R < |z|
  · simp only [squareTail,hz,ite_true]
    linarith [clippedSquare_nonneg R z]
  · have h : z^2 ≤ R^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hR).2 (le_of_not_gt hz)
    simp only [clippedSquare,min_eq_left h,sub_self,squareTail,hz,ite_false,le_refl]

lemma clippedSquare_integrable (R : ℝ) : Integrable (clippedSquare R) (gaussianReal 0 1) := by
  apply Integrable.of_bound (continuous_clippedSquare R).aestronglyMeasurable (R^2)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (clippedSquare_nonneg _ _)]; exact clippedSquare_le _ _)

lemma clippedSquare_mean_bounds (R : ℝ) :
    0 ≤ ∫ z, clippedSquare R z ∂gaussianReal 0 1 ∧
      (∫ z, clippedSquare R z ∂gaussianReal 0 1) ≤ R^2 := by
  constructor
  · exact integral_nonneg (clippedSquare_nonneg R)
  · simpa using integral_mono (clippedSquare_integrable R) (integrable_const (R^2))
      (clippedSquare_le R)

lemma clippedSquare_mean_error {R : ℝ} (hR : 0 ≤ R) :
    |(∫ z, clippedSquare R z ∂gaussianReal 0 1)-1| ≤
      ∫ z, squareTail R z ∂gaussianReal 0 1 := by
  have hi : Integrable (squareTail R) (gaussianReal 0 1) :=
    integrable_standard_square.mono' (measurable_squareTail R).aestronglyMeasurable
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]; exact squareTail_le _ _))
  have hm : (∫ z, clippedSquare R z ∂gaussianReal 0 1) ≤ 1 := by
    rw [← standard_square_integral]
    exact integral_mono (clippedSquare_integrable R) integrable_standard_square (fun _ => min_le_left _ _)
  have h := integral_mono (integrable_standard_square.sub (clippedSquare_integrable R)) hi
    (square_sub_clip_le hR)
  simp only [Pi.sub_apply] at h
  rw [integral_sub integrable_standard_square (clippedSquare_integrable R),standard_square_integral] at h
  rw [abs_of_nonpos (sub_nonpos.mpr hm)]
  linarith only [h]

lemma centered_clip_subgaussian {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R) (i : ι) :
    HasSubgaussianMGF
      (fun z : ι → ℝ => clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))
      ((Real.toNNReal (R^2))^2) (standardArrayLaw ι) := by
  apply bounded_zero_subgaussian _
    (((continuous_clippedSquare R).measurable.comp (measurable_pi_apply i)).sub measurable_const).aemeasurable
  · exact ae_of_all _ (fun z => by
      simp only [Pi.sub_apply,Function.comp_def]
      rw [Real.coe_toNNReal _ (sq_pos_of_pos hR).le,abs_le]
      have h := clippedSquare_mean_bounds R
      constructor <;> linarith [clippedSquare_le R (z i),clippedSquare_nonneg R (z i)])
  · have hc := (coordinate_hasLaw i).integral_comp
      (f := fun x : ℝ => clippedSquare R x-(∫ y, clippedSquare R y ∂gaussianReal 0 1))
      (((continuous_clippedSquare R).sub continuous_const).aestronglyMeasurable)
    simp only [Function.comp_def] at hc
    simp only [Pi.sub_apply,Function.comp_def]
    rw [hc,integral_sub (clippedSquare_integrable R) (integrable_const _)]
    simp

lemma clipped_square_matrix_rare {R u : ℝ} (hR : 0 < R) (hu : 0 < u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => (clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))/n))‖}) := by
  apply exponentiallyRare_of_geom_quadratic _ _ (C := 2) (b := 81) (a := (u/2)^2/(4*(R^2)^2))
    (by norm_num) (by positivity) (by norm_num)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hb := bounded_matrix_opNorm_tail hn
    (fun e (z : Edge n → ℝ) => clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))
    (coordinates_independent.comp
      (fun _ x => clippedSquare R x-(∫ y, clippedSquare R y ∂gaussianReal 0 1))
      (fun _ => ((continuous_clippedSquare R).sub continuous_const).measurable))
    (show 0 < Real.toNNReal (R^2) from Real.toNNReal_pos.mpr (by positivity))
    (centered_clip_subgaussian hR) (u := u/2) (by positivity)
  rw [show 2*(u/2) = u by ring,Real.coe_toNNReal _ (sq_nonneg _)] at hb
  convert hb using 1
  congr 2
  ring_nf

lemma square_remainder_norm_le {n : ℕ} (hn : 0<n) (z : Disorder n)
    {R a : ℝ} (hR : 0≤R) (ha : 0≤a)
    (hrow : ∀ i, (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (z e^2-clippedSquare R (z e))/n))‖ ≤ a := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  let g : Disorder n := fun e => (z e^2-clippedSquare R (z e))/n
  have hg : ∀ e, 0≤g e := fun e => div_nonneg (square_sub_clip_nonneg _ _) hnR.le
  have hr (i : Fin n) : ∑ j, |coupling g i j| ≤ a := by
    simp_rw [abs_of_nonneg (coupling_nonneg hg _ _)]
    rw [sum_coupling_row]
    change (∑ e ∈ incidentEdges i, (z e^2-clippedSquare R (z e))/(n:ℝ)) ≤ a
    rw [←Finset.sum_div]
    exact (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun e _ => square_sub_clip_le hR _)) hnR.le).trans (hrow i)
  exact matrix_opNorm_le_schur (coupling g) a ha hr (fun j => by
    simpa only [coupling_symm] using hr j)

lemma coupling_norm_add_three {n : ℕ} (A B D : Disorder n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (A+B+D))‖ ≤
      (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling A)‖ +
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling B)‖) +
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling D)‖ := by
  rw [coupling_add,coupling_add]
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    ((Matrix.of (coupling A)+Matrix.of (coupling B))+Matrix.of (coupling D))‖ ≤ _
  rw [map_add,map_add]
  exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)

lemma centered_square_mean_norm_le {n : ℕ} (hn : 0<n) {R : ℝ} (hR : 0≤R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling
      (fun _ => ((∫ x, clippedSquare R x ∂gaussianReal 0 1)-1)/n))‖ ≤
        ∫ x, squareTail R x ∂gaussianReal 0 1 := by
  let m := ∫ x, clippedSquare R x ∂gaussianReal 0 1
  have hh := coupling_const_norm_le (n := n) ((m-1)/n)
  have hnR : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm : (n:ℝ)*|(m-1)/n| = |m-1| := by
    rw [abs_div,show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    field_simp
  rw [hm] at hh
  exact hh.trans (clippedSquare_mean_error hR)

lemma centered_square_norm_le {n : ℕ} (hn : 0<n) (z : Disorder n)
    {R a : ℝ} (hR : 0≤R) (ha : 0≤a)
    (hrow : ∀ i, (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (z e^2-1)/n))‖ ≤
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))/n))‖ +
      (∫ x, squareTail R x ∂gaussianReal 0 1) + a := by
  let m := ∫ x, clippedSquare R x ∂gaussianReal 0 1
  let A : Disorder n := fun e => (clippedSquare R (z e)-m)/n
  let B : Disorder n := fun _ => (m-1)/n
  let D : Disorder n := fun e => (z e^2-clippedSquare R (z e))/n
  have he : (fun e => (z e^2-1)/(n:ℝ)) = A+B+D := by
    funext e
    dsimp only [A,B,D,Pi.add_apply]
    ring
  have hB := centered_square_mean_norm_le hn hR
  have hD := square_remainder_norm_le hn z hR ha hrow
  rw [he]
  exact (coupling_norm_add_three A B D).trans (add_le_add (add_le_add_right hB _) hD)

theorem centered_gaussian_square_matrix_rare {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => (z e^2-1)/n))‖}) := by
  obtain ⟨R,c,hR,hc,hmean,hb⟩ := gaussian_squareTail_row_bound (a := u/3) (by positivity)
  have htail : ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => ⋃ i : Fin n, {z | u/3 ≤ (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ)}) := by
    apply exponentiallyRare_iUnion_polynomial _ _ hc (hC := zero_lt_one) (hD := zero_lt_one) 1
    · apply Eventually.of_forall
      intro n
      simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      intro i
      simpa only [one_mul] using hb (incidentEdges i) hn (incidentEdges_card_le i)
  apply ((clipped_square_matrix_rare hR (show 0<u/3 by positivity)).union htail).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro z hz
  by_contra hnot
  have hclip : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))/n))‖ ≤ u/3 :=
    le_of_not_gt (fun h => hnot (Or.inl h))
  have hrows : ∀ i, (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) ≤ u/3 := by
    intro i
    exact (not_le.mp (fun hi => hnot (Or.inr (mem_iUnion.mpr ⟨i,hi⟩)))).le
  have hh := centered_square_norm_le hn z hR.le (by positivity : 0≤u/3) hrows
  change u < _ at hz
  linarith

end SKRatio.MatrixNet

end
end

end OAI
