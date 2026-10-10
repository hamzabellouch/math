import OAI.Geometry.QuadricBundles.BallAverage

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38

noncomputable section

namespace QuadricCounterexample
open Set Metric MeasureTheory Topology Filter Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
open Matrix
open scoped ComplexOrder

noncomputable def quadraticValue {n : Type u1} [Fintype n]
    (H : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (H *ᵥ v)).re

lemma star_basis {n : Type u2} [DecidableEq n] (i : n) :
    star (Pi.single i (1 : ℂ) : n → ℂ) = Pi.single i (1 : ℂ) := by
  ext k
  by_cases h : k = i <;> simp [h]

lemma basis_pair {n : Type u3} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i j : n) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ (H *ᵥ Pi.single j 1) = H i j := by
  simp [single_dotProduct]

lemma quadraticValue_basis {n : Type u4} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i : n) : quadraticValue H (Pi.single i 1) = (H i i).re := by
  rw [quadraticValue, basis_pair]

lemma quadraticValue_add_basis {n : Type u5} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i j : n) :
    quadraticValue H (Pi.single i 1 + Pi.single j 1) =
      (H i i).re + (H i j).re + (H j i).re + (H j j).re := by
  simp only [quadraticValue, star_add, mulVec_add, add_dotProduct, dotProduct_add,
    basis_pair, Complex.add_re]
  ring

lemma quadraticValue_add_I_basis {n : Type u6} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i j : n) :
    quadraticValue H (Pi.single i 1 + Complex.I • Pi.single j 1) =
      (H i i).re - (H i j).im + (H j i).im + (H j j).re := by
  simp only [quadraticValue, star_add, star_smul, mulVec_add, mulVec_smul,
    add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, basis_pair,
    smul_eq_mul, Complex.star_def, Complex.conj_I, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.neg_re,
    Complex.I_im, Complex.I_re]
  ring

noncomputable def matrixFromQuadratic {n : Type u7} [DecidableEq n]
    (q : (n → ℂ) → ℝ) : Matrix n n ℂ := fun i j ↦
  ⟨(q (Pi.single i 1 + Pi.single j 1) - q (Pi.single i 1) - q (Pi.single j 1)) / 2,
   (q (Pi.single i 1) + q (Pi.single j 1) -
     q (Pi.single i 1 + Complex.I • Pi.single j 1)) / 2⟩

lemma matrixFromQuadratic_value {n : Type u8} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    matrixFromQuadratic (quadraticValue H) = H := by
  funext i j
  apply Complex.ext
  all_goals
    have hre := congrArg Complex.re (hH.apply i j)
    have him := congrArg Complex.im (hH.apply i j)
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hre him
    simp only [matrixFromQuadratic, quadraticValue_add_basis, quadraticValue_add_I_basis,
      quadraticValue_basis]
    linarith

theorem quadraticValue_pointwise_limit
    {n : Type u9} [Fintype n] [DecidableEq n]
    {H : ℕ → Matrix n n ℂ} {q : (n → ℂ) → ℝ}
    (hH : ∀ k, (H k).PosSemidef)
    (hq : ∀ v, Tendsto (fun k ↦ quadraticValue (H k) v) atTop (𝓝 (q v))) :
    ∃ M : Matrix n n ℂ, M.PosSemidef ∧ ∀ v, q v = quadraticValue M v := by
  let M := matrixFromQuadratic q
  have hm (i j : n) : Tendsto (fun k ↦ H k i j) atTop (𝓝 (M i j)) := by
    change Tendsto (fun k ↦ H k i j) atTop (𝓝 (matrixFromQuadratic q i j))
    have hrec (k : ℕ) : matrixFromQuadratic (quadraticValue (H k)) i j = H k i j :=
      congrFun (congrFun (matrixFromQuadratic_value (hH k).1) i) j
    simp_rw [← hrec, matrixFromQuadratic, Complex.mk_eq_add_mul_I]
    exact (((hq _).sub (hq _)).sub (hq _)).div_const 2 |>.ofReal |>.add
      ((((hq _).add (hq _)).sub (hq _)).div_const 2 |>.ofReal |>.mul_const Complex.I)
  have hmat : Tendsto H atTop (𝓝 M) :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ hm i j
  have hherm : M.IsHermitian := by
    ext i j
    exact tendsto_nhds_unique ((hm j i).star)
      ((hm i j).congr' (Filter.Eventually.of_forall fun k ↦ ((hH k).1.apply i j).symm))
  have hform (v : n → ℂ) :
      Tendsto (fun k ↦ star v ⬝ᵥ ((H k) *ᵥ v)) atTop (𝓝 (star v ⬝ᵥ (M *ᵥ v))) := by
    have hc : Continuous (fun N : Matrix n n ℂ ↦ star v ⬝ᵥ (N *ᵥ v)) := by fun_prop
    exact hc.continuousAt.tendsto.comp hmat
  refine ⟨M, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun v ↦ ?_), fun v ↦ ?_⟩
  · exact ge_of_tendsto (hform v)
      (Filter.Eventually.of_forall fun k ↦ (hH k).dotProduct_mulVec_nonneg v)
  · exact tendsto_nhds_unique (hq v) (Complex.continuous_re.continuousAt.tendsto.comp (hform v))

lemma isClosed_matrix_positive_semidefinite {n : Type u10} [Fintype n] [DecidableEq n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  have heq : {M : Matrix n n ℂ | M.PosSemidef} =
      {M | M.conjTranspose = M} ∩ ⋂ v : n → ℂ, {M | 0 ≤ star v ⬝ᵥ (M *ᵥ v)} := by
    ext M
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun h ↦ ⟨h.1, h.dotProduct_mulVec_nonneg⟩,
      fun h ↦ Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h.1 h.2⟩
  rw [heq]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun v ↦ ?_)
  exact isClosed_le continuous_const (by fun_prop)

lemma convex_matrix_positive_semidefinite {n : Type u11} [Fintype n] [DecidableEq n] :
    Convex ℝ {M : Matrix n n ℂ | M.PosSemidef} := by
  intro M hM N hN a b ha hb _
  exact (hM.smul ha).add (hN.smul hb)

local instance matrixContinuousENorm {n : Type u12} [Fintype n] :
    ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

noncomputable def quadraticValueCLM {n : Type u13} [Fintype n]
    (v : n → ℂ) : Matrix n n ℂ →L[ℝ] ℝ where
  toFun H := quadraticValue H v
  map_add' H K := by
    simp only [quadraticValue, add_mulVec, dotProduct_add, Complex.add_re]
  map_smul' a H := by
    simp [quadraticValue, smul_mulVec, dotProduct_smul, RCLike.real_smul_eq_coe_mul]
  cont := by unfold quadraticValue; fun_prop

lemma quadraticValue_average {α : Type u14} {n : Type u15} [MeasurableSpace α]
    [Fintype n] {μ : Measure α} {H : α → Matrix n n ℂ}
    (hH : Integrable H μ) (v : n → ℂ) :
    quadraticValue (⨍ x, H x ∂μ) v = ⨍ x, quadraticValue (H x) v ∂μ := by
  exact ((quadraticValueCLM v).integral_comp_comm hH.to_average).symm

lemma positive_semidefinite_average {α : Type u16} {n : Type u17} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {H : α → Matrix n n ℂ} (hH : Integrable H μ)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef) : (⨍ x, H x ∂μ).PosSemidef :=
  convex_matrix_positive_semidefinite.average_mem isClosed_matrix_positive_semidefinite hpos hH

lemma quadraticValue_nonneg {n : Type u18} [Fintype n]
    {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) : 0 ≤ quadraticValue H v :=
  (hH.dotProduct_mulVec_nonneg v).1

theorem matrix_ball_infimum_representative
    {E : Type u19} {n : Type u20} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ}
    (hH : Integrable H μ) (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef)
    {Ω : Set E} (hΩ : IsOpen Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ v k, ∀ᵐ x ∂μ.restrict Ω,
      quadraticValue (H x) v ≤ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) :
    ∀ x ∈ Ω, ∃ M : Matrix n n ℂ, M.PosSemidef ∧ ∀ v,
      (⨅ k, ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) = quadraticValue M v := by
  intro x hx
  let Hbar : ℕ → Matrix n n ℂ := fun k ↦ ⨍ y in ball x (r k), H y ∂μ
  have hbar (k : ℕ) : (Hbar k).PosSemidef := by
    have : Fact (μ (ball x (r k)) < ∞) := ⟨measure_ball_lt_top⟩
    have : NeZero (μ (ball x (r k))) :=
      ⟨ne_of_gt (Metric.measure_ball_pos μ x (hr k))⟩
    exact positive_semidefinite_average hH.integrableOn (ae_restrict_of_ae hpos)
  apply quadraticValue_pointwise_limit hbar
  intro v
  have hi : Integrable (fun y ↦ quadraticValue (H y) v) μ :=
    (quadraticValueCLM v).integrable_comp hH
  have hp : 0 ≤ᵐ[μ] fun y ↦ quadraticValue (H y) v :=
    hpos.mono fun y hy ↦ quadraticValue_nonneg hy v
  have hl := (ball_infimum_representative_limit hi hp hΩ hr hr0 (hmean v)).2.2.2 x hx
  simpa only [Hbar, quadraticValue_average hH.integrableOn] using hl

lemma continuous_joint_averaged_quadratic
    {E : Type u21} {n : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] {H : E → Matrix n n ℂ} (hH : Integrable H μ) (r : ℝ) :
    Continuous (fun p : E × (n → ℂ) ↦ quadraticValue (⨍ y in ball p.1 r, H y ∂μ) p.2) := by
  have hc : Continuous (fun p : E × (n → ℂ) ↦ ⨍ y in ball p.1 r, H y ∂μ) :=
    (continuous_ball_average hH r).comp continuous_fst
  unfold quadraticValue
  fun_prop

lemma joint_upperSemicontinuous_infimum
    {E : Type u23} {n : Type u24} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] {H : E → Matrix n n ℂ} (hH : Integrable H μ)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef) (r : ℕ → ℝ) :
    UpperSemicontinuous (fun p : E × (n → ℂ) ↦
      ⨅ k, ⨍ y in ball p.1 (r k), quadraticValue (H y) p.2 ∂μ) := by
  apply upperSemicontinuous_ciInf
  · intro p
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact ball_average_nonneg (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy p.2) _ _
  · intro k
    simpa only [quadraticValue_average hH.integrableOn] using
      (continuous_joint_averaged_quadratic hH (r k)).upperSemicontinuous

lemma matrixFromQuadratic_ae_recovery {α : Type u25} {n : Type u26} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] {μ : Measure α}
    {H : α → Matrix n n ℂ} {q : α → (n → ℂ) → ℝ}
    (hH : ∀ᵐ x ∂μ, (H x).IsHermitian)
    (hq : ∀ v, (fun x ↦ q x v) =ᵐ[μ] fun x ↦ quadraticValue (H x) v) :
    (fun x ↦ matrixFromQuadratic (q x)) =ᵐ[μ] H := by
  have hd := ae_all_iff.mpr (fun i : n ↦ hq (Pi.single i 1))
  have hs := ae_all_iff.mpr (fun i : n ↦ ae_all_iff.mpr
    (fun j : n ↦ hq (Pi.single i 1 + Pi.single j 1)))
  have hi := ae_all_iff.mpr (fun i : n ↦ ae_all_iff.mpr
    (fun j : n ↦ hq (Pi.single i 1 + Complex.I • Pi.single j 1)))
  filter_upwards [hH, hd, hs, hi] with x hx hdx hsx hix
  rw [← matrixFromQuadratic_value hx]
  ext i j
  all_goals simp only [matrixFromQuadratic, hdx, hsx, hix]

theorem matrix_regularized_representative
    {E : Type u27} {n : Type u28} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ}
    (hH : Integrable H μ) (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef)
    {Ω : Set E} (hΩ : IsOpen Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ v k, ∀ᵐ x ∂μ.restrict Ω,
      quadraticValue (H x) v ≤ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) :
    ∃ M : E → Matrix n n ℂ,
      (∀ x ∈ Ω, (M x).PosSemidef) ∧ M =ᵐ[μ.restrict Ω] H ∧
      UpperSemicontinuousOn (fun p : E × (n → ℂ) ↦ quadraticValue (M p.1) p.2)
        (Ω ×ˢ univ) ∧
      ∀ x ∈ Ω, ∀ v, Tendsto
        (fun k ↦ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ)
        atTop (𝓝 (quadraticValue (M x) v)) := by
  let q := fun x v ↦ ⨅ k, ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ
  let M := fun x ↦ matrixFromQuadratic (q x)
  have hxM (x : E) (hx : x ∈ Ω) : (M x).PosSemidef ∧ ∀ v, q x v = quadraticValue (M x) v := by
    obtain ⟨N, hN, hqN⟩ := matrix_ball_infimum_representative hH hpos hΩ hr hr0 hmean x hx
    have he : M x = N := by
      change matrixFromQuadratic (q x) = N
      rw [show q x = quadraticValue N from funext hqN, matrixFromQuadratic_value hN.1]
    simpa only [he] using And.intro hN hqN
  have hqae (v : n → ℂ) : (fun x ↦ q x v) =ᵐ[μ.restrict Ω]
      fun x ↦ quadraticValue (H x) v :=
    ball_infimum_representative_ae ((quadraticValueCLM v).integrable_comp hH)
      (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy v) hΩ hr hr0 (hmean v)
  refine ⟨M, fun x hx ↦ (hxM x hx).1,
    matrixFromQuadratic_ae_recovery (ae_restrict_of_ae (hpos.mono fun _ h ↦ h.1)) hqae, ?_, ?_⟩
  · intro p hp
    apply UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (((joint_upperSemicontinuous_infimum hH hpos r).upperSemicontinuousOn
        (Ω ×ˢ (univ : Set (n → ℂ)))) p hp) hp
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hxM z.1 hz.1).2 z.2
  · intro x hx v
    have hl := (ball_infimum_representative_limit ((quadraticValueCLM v).integrable_comp hH)
      (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy v) hΩ hr hr0 (hmean v)).2.2.2 x hx
    change Tendsto (fun k ↦ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ)
      atTop (𝓝 (quadraticValue (M x) v))
    rw [← (hxM x hx).2 v]
    exact hl

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

lemma integral_ball_translate
    {E : Type u29} {F : Type u30} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] (f : E → F) (x : E) (r : ℝ) :
    (∫ a in ball (0 : E) r, f (x + a) ∂μ) = ∫ y in ball x r, f y ∂μ := by
  have he : (fun a : E ↦ x + a) ⁻¹' ball x r = ball 0 r := by
    ext a
    simp only [mem_preimage, mem_ball, dist_self_add_left, dist_zero_right]
  have hh := ((MeasurePreserving.id μ).add_left μ x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding f (ball x r)
  simpa only [id_eq, he] using hh

theorem DiskPshOn.base_ball_average
    {E : Type u31} {V : Type u32} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [LocallyCompactSpace V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {Ω U : Set E} (hU : IsOpen U) {q : E × V → ℝ}
    (hq : DiskPshOn (Ω ×ˢ univ) q) (hc : ContinuousOn q (Ω ×ˢ univ))
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ a ∈ closedBall (0 : E) r, ∀ x ∈ U, x + a ∈ Ω) :
    DiskPshOn (U ×ˢ univ) (fun p ↦ ⨍ y in ball p.1 r, q (y,p.2) ∂μ) := by
  let K := closedBall (0 : E) r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) r)
  let : Fact (μ (ball (0 : E) r) < ∞) := ⟨measure_ball_lt_top⟩
  have hm0 : μ (ball (0 : E) r) ≠ 0 := ne_of_gt (Metric.measure_ball_pos μ 0 hr)
  let ν : Measure E := (μ (ball (0 : E) r))⁻¹ • μ.restrict (ball 0 r)
  let : IsFiniteMeasure ν := Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hm0)
  let η : Measure K := Measure.comap Subtype.val ν
  let F := fun a : K ↦ fun p : E × V ↦ q (p.1 + a, p.2)
  have hFc : ContinuousOn (Function.uncurry F) (univ ×ˢ (U ×ˢ univ)) := by
    exact hc.comp (by fun_prop) (fun p hp ↦ ⟨hb p.1 p.1.property p.2.1 hp.2.1, mem_univ _⟩)
  have hFp (a : K) : DiskPshOn (U ×ˢ univ) (F a) := by
    exact hq.comp (by fun_prop) (fun p hp ↦ ⟨hb a a.property p.1 hp.1, mem_univ _⟩)
  have hi := DiskPshOn.integral_compact_parameter (μ := η) (hU.prod isOpen_univ) hFc hFp
  have he (p : E × V) : (∫ a, F a p ∂η) = ⨍ y in ball p.1 r, q (y,p.2) ∂μ := by
    change (∫ a : K, q (p.1 + a, p.2) ∂(Measure.comap Subtype.val ν)) = _
    rw [integral_subtype_comap (show MeasurableSet K from measurableSet_closedBall) (fun a : E ↦ q (p.1 + a, p.2))]
    change (∫ a in K, q (p.1 + a, p.2) ∂((μ (ball (0 : E) r))⁻¹ •
      μ.restrict (ball 0 r))) = _
    rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict measurableSet_closedBall]
    rw [show K ∩ ball (0 : E) r = ball 0 r from inter_eq_right.mpr ball_subset_closedBall]
    rw [integral_ball_translate (fun y : E ↦ q (y,p.2)) p.1 r, setAverage_eq, measureReal_def, μ.addHaar_ball_center]
    simp only [ENNReal.toReal_inv, μ.addHaar_ball_center]
  simpa only [he] using hi

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

lemma DiskPshOn.pointwise_limit_of_continuous_bound {E : Type u33} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ω : Set E} {u : ℕ → E → ℝ} {q B : E → ℝ}
    (hu : ∀ n, DiskPshOn Ω (u n)) (hq : UpperSemicontinuousOn q Ω)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (q x)))
    (hB : Continuous B) (hbound : ∀ n, ∀ x ∈ Ω, ‖u n x‖ ≤ B x) :
    DiskPshOn Ω q := by
  apply DiskPshOn.pointwise_limit hu hq hlim
  intro K hK hKΩ
  obtain ⟨C, hC⟩ := hK.bddAbove_image hB.continuousOn
  exact ⟨C, fun n x hx ↦ (hbound n x (hKΩ hx)).trans (hC (mem_image_of_mem B hx))⟩

open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
local instance {n : Type u34} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

theorem averaged_matrix_limit_psh
    {E : Type u35} {n : Type u36} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    [Fintype n] [DecidableEq n]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {H : E → Matrix n n ℂ} {Hm : ℕ → E → Matrix n n ℂ}
    {Ω U : Set E} (hU : IsOpen U)
    (hH : Integrable H μ) (hHm : ∀ m, Integrable (Hm m) μ)
    (hpos : ∀ m, ∀ᵐ x ∂μ, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {C r : ℝ} (hr : 0 < r)
    (hb : ∀ a ∈ closedBall (0 : E) r, ∀ x ∈ U, x + a ∈ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2)
    (hl : ∀ x ∈ U, ∀ v, Tendsto
      (fun m ↦ ⨍ y in ball x r, quadraticValue (Hm m y) v ∂μ)
      atTop (𝓝 (⨍ y in ball x r, quadraticValue (H y) v ∂μ))) :
    DiskPshOn (U ×ˢ univ)
      (fun p : E × (n → ℂ) ↦ ⨍ y in ball p.1 r, quadraticValue (H y) p.2 ∂μ) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hcq := continuous_joint_averaged_quadratic hH r
  have huc : UpperSemicontinuousOn
      (fun p : E × (n → ℂ) ↦ ⨍ y in ball p.1 r, quadraticValue (H y) p.2 ∂μ)
      (U ×ˢ univ) := by
    simpa only [quadraticValue_average hH.integrableOn] using hcq.upperSemicontinuous.upperSemicontinuousOn (U ×ˢ univ)
  apply DiskPshOn.pointwise_limit_of_continuous_bound
    (fun m ↦ (hp m).base_ball_average hU (hc m) hr hb) huc
    (fun p hp ↦ hl p.1 hp.1 p.2) (B := fun p : E × (n → ℂ) ↦ C * ‖p.2‖ ^ 2)
    (by fun_prop)
  intro m p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (ball_average_nonneg
    ((hpos m).mono fun _ hy ↦ quadraticValue_nonneg hy p.2) _ _)]
  have hi : Integrable (fun y : E ↦ quadraticValue (Hm m y) p.2) μ :=
    (quadraticValueCLM p.2).integrable_comp (hHm m)
  apply ball_average_le_const (μ := μ) (x := p.1) hr hi.integrableOn
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  apply hbound m y _ p.2
  have ha : y - p.1 ∈ closedBall (0 : E) r := by
    simpa only [mem_closedBall, dist_zero_right, ← dist_eq_norm] using (mem_ball.mp hy).le
  simpa only [add_sub_cancel] using hb (y-p.1) ha p.1 hp.1

theorem joint_matrix_regularized_representative
    {E : Type u37} {n : Type u38} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    [Fintype n] [DecidableEq n]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {H : E → Matrix n n ℂ} {Hm : ℕ → E → Matrix n n ℂ}
    {Ω U : Set E} (hU : IsOpen U)
    (hH : Integrable H μ) (hHm : ∀ m, Integrable (Hm m) μ)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef)
    (hposm : ∀ m, ∀ᵐ x ∂μ, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {C : ℝ} {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hb : ∀ k, ∀ a ∈ closedBall (0 : E) (r k), ∀ x ∈ U, x + a ∈ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2)
    (hl : ∀ k, ∀ x ∈ U, ∀ v, Tendsto
      (fun m ↦ ⨍ y in ball x (r k), quadraticValue (Hm m y) v ∂μ)
      atTop (𝓝 (⨍ y in ball x (r k), quadraticValue (H y) v ∂μ)))
    (hmean : ∀ v k, ∀ᵐ x ∂μ.restrict U,
      quadraticValue (H x) v ≤ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) :
    ∃ M : E → Matrix n n ℂ,
      (∀ x ∈ U, (M x).PosSemidef) ∧ M =ᵐ[μ.restrict U] H ∧
      DiskPshOn (U ×ˢ univ) (fun p : E × (n → ℂ) ↦ quadraticValue (M p.1) p.2) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  obtain ⟨M, hM, hMae, hMusc, hMl⟩ :=
    matrix_regularized_representative hH hpos hU hr hr0 hmean
  refine ⟨M, hM, hMae, ?_⟩
  apply DiskPshOn.pointwise_limit_of_continuous_bound
    (fun k ↦ averaged_matrix_limit_psh hU hH hHm hposm hc hp (hr k) (hb k) hbound (hl k))
    hMusc (fun p hp ↦ hMl p.1 hp.1 p.2)
    (B := fun p : E × (n → ℂ) ↦ C * ‖p.2‖ ^ 2) (by fun_prop)
  intro k p hpU
  rw [Real.norm_eq_abs, abs_of_nonneg (ball_average_nonneg
    (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy p.2) _ _)]
  apply le_of_tendsto (hl k p.1 hpU.1 p.2)
  apply Eventually.of_forall
  intro m
  have hi : Integrable (fun y : E ↦ quadraticValue (Hm m y) p.2) μ :=
    (quadraticValueCLM p.2).integrable_comp (hHm m)
  apply ball_average_le_const (μ := μ) (x := p.1) (hr k) hi.integrableOn
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  apply hbound m y _ p.2
  have ha : y - p.1 ∈ closedBall (0 : E) (r k) := by
    simpa only [mem_closedBall, dist_zero_right, ← dist_eq_norm] using (mem_ball.mp hy).le
  simpa only [add_sub_cancel] using hb k (y-p.1) ha p.1 hpU.1

end QuadricCounterexample

end

end OAI
