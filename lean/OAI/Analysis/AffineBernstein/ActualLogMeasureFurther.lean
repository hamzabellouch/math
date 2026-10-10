import Mathlib
import OAI.Analysis.AffineBernstein.RegularFiberDomain

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ActualLogMeasure
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- Joint regularity and positivity of the actual source logarithmic density. -/
/- The paper's sigma measure, pushed to logarithmic coordinates. This definition
uses the actual affine epigraph support function, not an abstract model metric. -/
/- Actual measure form of Proposition log-inequality, with the Euclidean
operator norm of the true derivative in logarithmic coordinates. -/
end ActualLogMeasure

open Filter Metric
open scoped Topology

/- The quantifier order in bounds.tex: every finite box has its own eventual
index. No common threshold for infinitely many boxes is needed. -/
theorem no_eventual_polynomial_exponential_growth
    (M : ℕ → ℕ → ℝ) (k l₀ : ℕ) {c q C : ℝ}
    (hc : 0 < c) (hq : 1 < q)
    (hpos : ∀ᶠ j in atTop, c ≤ M j l₀)
    (hstep : ∀ l, l₀ ≤ l → ∀ᶠ j in atTop, q * M j l ≤ M j (l+1))
    (hupper : ∀ L, l₀ ≤ L → ∀ᶠ j in atTop, M j L ≤ C * (L+1:ℝ)^k) : False := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hlower : ∀ r : ℕ, ∀ᶠ j in atTop, c*q^r ≤ M j (l₀+r) := by
    intro r
    induction r with
    | zero => simpa using hpos
    | succ r ihr =>
      filter_upwards [ihr,hstep (l₀+r) (Nat.le_add_right _ _)] with j hj hs
      have hh := (mul_le_mul_of_nonneg_left hj hq0.le).trans hs
      simpa only [Nat.add_succ, pow_succ, mul_left_comm q c, mul_comm q (q^r)] using hh
  have ht : Tendsto (fun r : ℕ => C * ((l₀+r+1:ℕ):ℝ)^k / q^r) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_const_div_const_pow_of_one_lt k hq).comp
      (tendsto_add_atTop_nat (l₀+1))).const_mul (C*q^(l₀+1))
    simpa only [mul_zero] using hh.congr (fun r => by
      dsimp only [Function.comp_def]
      have hn : r+(l₀+1) = l₀+r+1 := by omega
      rw [← hn, pow_add]
      field_simp [hq0.ne']
      ring)
  have hsmall : ∀ᶠ r in atTop, C * ((l₀+r+1:ℕ):ℝ)^k / q^r < c := ht.eventually (gt_mem_nhds hc)
  obtain ⟨r,hr⟩ := hsmall.exists
  have he := (hlower r).and (hupper (l₀+r) (Nat.le_add_right _ _))
  obtain ⟨j,hj,hju⟩ := he.exists
  have hle : c ≤ C * ((l₀+r+1:ℕ):ℝ)^k / q^r := by
    apply (le_div_iff₀ (pow_pos hq0 _)).mpr
    exact hj.trans (by simpa only [Nat.cast_add,Nat.cast_one] using hju)
  exact (not_lt_of_ge hle) hr

/- The source shell inequality has precisely the exponential recurrence
required above. Integrals may vary with the approximating index. -/
theorem no_eventual_polynomial_shell_growth
    (M : ℕ → ℕ → ℝ) (k l₀ : ℕ) {c A C : ℝ}
    (hc : 0 < c) (hA : 0 < A)
    (hpos : ∀ᶠ j in atTop, c ≤ M j l₀)
    (hshell : ∀ l, l₀ ≤ l → ∀ᶠ j in atTop,
      M j l ≤ A * (M j (l+1)-M j l))
    (hupper : ∀ L, l₀ ≤ L → ∀ᶠ j in atTop, M j L ≤ C * (L+1:ℝ)^k) : False := by
  apply no_eventual_polynomial_exponential_growth M k l₀ hc
    (show 1 < 1+A⁻¹ by linarith [inv_pos.mpr hA]) hpos _ hupper
  intro l hl
  filter_upwards [hshell l hl] with j hj
  apply (le_of_mul_le_mul_left (a := A) ?_ hA)
  field_simp
  nlinarith

/- A product of two unit-bounded Lipschitz functions has the sum of their
Lipschitz constants. Here the multiplication is the ring multiplication on ℝ. -/
theorem lipschitzWith_mul_unit {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L : NNReal} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ x, ‖g x‖ ≤ 1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi : f x*g x-f y*g y = f x*(g x-g y)+(f x-f y)*g y := by ring
  rw [dist_eq_norm,hi]
  calc
    ‖f x*(g x-g y)+(f x-f y)*g y‖ ≤ ‖f x‖*‖g x-g y‖+‖f x-f y‖*‖g y‖ :=
      by simpa only [norm_mul] using (norm_add_le (f x*(g x-g y)) ((f x-f y)*g y))
    _ ≤ 1*((L:ℝ)*dist x y)+((K:ℝ)*dist x y)*1 := by
      gcongr
      · exact hfb x
      · simpa only [dist_eq_norm] using hg.dist_le_mul x y
      · simpa only [dist_eq_norm] using hf.dist_le_mul x y
      · exact hgb y
    _ = (↑(K+L):ℝ)*dist x y := by simp only [NNReal.coe_add]; ring

theorem lipschitzWith_prod_unit {X I : Type*} [PseudoMetricSpace X]
    (s : Finset I) (f : I → X → ℝ) (K : I → NNReal)
    (hl : ∀ i ∈ s, LipschitzWith (K i) (f i))
    (hb : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ 1) :
    LipschitzWith (∑ i ∈ s, K i) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,Finset.prod_insert ha]
    apply lipschitzWith_mul_unit (hl a (by simp))
      (ih (fun i hi => hl i (by simp [hi])) (fun i hi => hb i (by simp [hi])))
      (hb a (by simp))
    intro x
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i hi => hb i (by simp [hi]) x)

/- The fixed smooth transition has some finite global Lipschitz constant;
constancy off [0,1] makes the derivative bound compact. -/
theorem smoothTransition_exists_lipschitz : ∃ K : NNReal, LipschitzWith K Real.smoothTransition := by
  have hcd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 2)).exists_bound_of_continuousOn
    ((hcd.continuous_deriv (by simp)).continuousOn)
  refine ⟨⟨max B 0,le_max_right _ _⟩,lipschitzWith_of_nnnorm_deriv_le (hcd.differentiable (by simp)) ?_⟩
  intro x
  change ‖deriv Real.smoothTransition x‖ ≤ max B 0
  by_cases hx : x ∈ Icc (-1:ℝ) 2
  · exact (hB x hx).trans (le_max_left _ _)
  have hd : deriv Real.smoothTransition x = 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
        filter_upwards [gt_mem_nhds (show x < 0 by linarith)] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      exact ((hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he).deriv
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
        filter_upwards [lt_mem_nhds (show 1 < x by linarith)] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      exact ((hasDerivAt_const x (1:ℝ)).congr_of_eventuallyEq he).deriv
  simp only [hd,norm_zero]
  exact le_max_right _ _

/- Closed boxes in the literal logarithmic base coordinates. -/
/- A fixed-width smooth box cutoff; its derivatives have no dependence on L
apart from coordinate translations. -/
def logarithmicCutoff (k : ℕ) (L : ℝ) (x : Space k) : ℝ :=
  ∏ i : Fin k, (1-Real.smoothTransition (x i-L))*(1-Real.smoothTransition (-x i-L))

theorem logarithmicCutoff_mem_Icc (k : ℕ) (L : ℝ) (x : Space k) :
    logarithmicCutoff k L x ∈ Icc (0:ℝ) 1 := by
  have hb : ∀ t : ℝ, 0 ≤ 1-Real.smoothTransition t ∧ 1-Real.smoothTransition t ≤ 1 :=
    fun t => ⟨sub_nonneg.mpr (Real.smoothTransition.le_one t),by linarith [Real.smoothTransition.nonneg t]⟩
  exact ⟨Finset.prod_nonneg (fun i _ => mul_nonneg (hb _).1 (hb _).1),
    Finset.prod_le_one₀ (fun i _ => mul_nonneg (hb _).1 (hb _).1)
      (fun i _ => (mul_le_of_le_one_left (hb _).1 (hb _).2).trans (hb _).2)⟩

theorem logarithmicCutoff_one {k : ℕ} {L : ℝ} {x : Space k}
    (hx : x ∈ logarithmicBox k L) : logarithmicCutoff k L x = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  have hh := abs_le.mp (hx i)
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : x i-L ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : -x i-L ≤ 0)]
  norm_num

theorem logarithmicCutoff_zero {k : ℕ} {L : ℝ} {x : Space k}
    (hx : ∃ i, L+1 ≤ |x i|) : logarithmicCutoff k L x = 0 := by
  classical
  obtain ⟨i,hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases le_abs.mp hi with hi | hi
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x i-L)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ -x i-L)]
    simp

theorem logarithmicCutoff_smooth (k : ℕ) (L : ℝ) : ContDiff ℝ ∞ (logarithmicCutoff k L) := by
  unfold logarithmicCutoff
  apply contDiff_prod
  intro i hi
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((EuclideanSpace.proj i).contDiff.sub contDiff_const))).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((EuclideanSpace.proj i).contDiff.neg.sub contDiff_const)))

/- One constant controls every translated logarithmic cutoff. -/
theorem logarithmicCutoff_uniform_lipschitz (k : ℕ) :
    ∃ K : NNReal, 0 < K ∧ ∀ L : ℝ, LipschitzWith K (logarithmicCutoff k L) := by
  obtain ⟨K,hK⟩ := smoothTransition_exists_lipschitz
  refine ⟨(k:NNReal)*(K+K)+1,by positivity,?_⟩
  intro L
  have hproj : ∀ i : Fin k, LipschitzWith 1 (fun x : Space k => x i) := by
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one,one_mul,dist_eq_norm,PiLp.sub_apply] using
      (PiLp.norm_apply_le (x-y) i)
  have hb : ∀ t : ℝ, ‖1-Real.smoothTransition t‖ ≤ 1 := by
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one t))]
    linarith [Real.smoothTransition.nonneg t]
  have hf : ∀ i : Fin k, LipschitzWith (K+K)
      (fun x : Space k => (1-Real.smoothTransition (x i-L))*(1-Real.smoothTransition (-x i-L))) := by
    intro i
    apply lipschitzWith_mul_unit
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (1-Real.smoothTransition (x i-L)) (1-Real.smoothTransition (y i-L)) =
            dist (Real.smoothTransition (x i-L)) (Real.smoothTransition (y i-L)) := dist_sub_left _ _ _
        _ ≤ (K:ℝ)*dist (x i-L) (y i-L) := hK.dist_le_mul _ _
        _ ≤ (K:ℝ)*dist x y := by
          gcongr
          simpa only [dist_sub_right,NNReal.coe_one,one_mul] using (hproj i).dist_le_mul x y
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (1-Real.smoothTransition (-x i-L)) (1-Real.smoothTransition (-y i-L)) =
            dist (Real.smoothTransition (-x i-L)) (Real.smoothTransition (-y i-L)) := dist_sub_left _ _ _
        _ ≤ (K:ℝ)*dist (-x i-L) (-y i-L) := hK.dist_le_mul _ _
        _ ≤ (K:ℝ)*dist x y := by
          gcongr
          simpa only [dist_sub_right,dist_neg_neg,NNReal.coe_one,one_mul] using (hproj i).dist_le_mul x y
    · exact fun x => hb _
    · exact fun x => hb _
  have hp := lipschitzWith_prod_unit Finset.univ _ (fun _ : Fin k => K+K)
    (fun i _ => hf i) (fun i _ x => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hb _)).trans (hb _))
  change LipschitzWith _ (logarithmicCutoff k L) at hp
  have he : (∑ i : Fin k, (K+K)) = (k:NNReal)*(K+K) := by simp [mul_add]
  rw [he] at hp
  exact hp.weaken (le_add_of_nonneg_right (by positivity))

theorem logarithmicBox_mono {k : ℕ} {a b : ℝ} (h : a ≤ b) :
    logarithmicBox k a ⊆ logarithmicBox k b := fun _ hx i => (hx i).trans h

theorem logarithmicBox_isClosed (k : ℕ) (L : ℝ) : IsClosed (logarithmicBox k L) := by
  convert isClosed_iInter (fun i : Fin k => isClosed_le ((EuclideanSpace.proj i).continuous.abs)
    (show Continuous (fun _ : Space k => L) from continuous_const)) using 1
  ext x
  simp [logarithmicBox]

theorem logarithmicBox_isCompact (k : ℕ) (L : ℝ) : IsCompact (logarithmicBox k L) := by
  have h : IsCompact (Set.pi univ (fun _ : Fin k => Icc (-L) L)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : logarithmicBox k L = (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)) ⁻¹'
      (Set.pi univ (fun _ : Fin k => Icc (-L) L)) := by
    ext x
    simp only [logarithmicBox,mem_ofPred_eq,mem_preimage,Set.mem_pi,mem_univ,true_implies,mem_Icc]
    exact forall_congr' (fun i => abs_le)
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr h

theorem logarithmicCutoff_hasCompactSupport (k : ℕ) (L : ℝ) :
    HasCompactSupport (logarithmicCutoff k L) := by
  apply (logarithmicBox_isCompact k (L+1)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (logarithmicBox_isClosed k (L+1))
  intro x hx i
  by_contra hi
  exact hx (logarithmicCutoff_zero ⟨i,(not_le.mp hi).le⟩)

/- The derivative vanishes on the inner closed box, including its faces. -/
theorem logarithmicCutoff_fderiv_eq_zero_of_mem {k : ℕ} {L : ℝ} {x : Space k}
    (hx : x ∈ logarithmicBox k L) : fderiv ℝ (logarithmicCutoff k L) x = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [logarithmicCutoff_one hx]
  exact (logarithmicCutoff_mem_Icc k L y).2

/- The same holds at and outside the outer faces; no zero-boundary-mass
assumption is needed in the ensuing shell estimate. -/
theorem logarithmicCutoff_fderiv_eq_zero_of_outside {k : ℕ} {L : ℝ} {x : Space k}
    (hx : ∃ i, L+1 ≤ |x i|) : fderiv ℝ (logarithmicCutoff k L) x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [logarithmicCutoff_zero hx]
  exact (logarithmicCutoff_mem_Icc k L y).1

/- The logarithmic Poincaré inequality turns the genuine smooth cutoff into
mass growth in a fixed-width shell. Measures need only be finite on this box. -/
theorem logarithmic_shell_growth {k : ℕ} {L : ℝ} (μ : Measure (Space k))
    {K : NNReal} (hK : LipschitzWith K (logarithmicCutoff k L)) (hfin : μ (logarithmicBox k (L+1)) ≠ ⊤)
    {A : ℝ} (hA : 0 ≤ A)
    (hP : (∫ x, (logarithmicCutoff k L x)^2 ∂μ) ≤
      A * ∫ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ∂μ) :
    μ.real (logarithmicBox k L) ≤ A*(K:ℝ)^2 *
      (μ.real (logarithmicBox k (L+1))-μ.real (logarithmicBox k L)) := by
  classical
  let B₀ := logarithmicBox k L
  let B₁ := logarithmicBox k (L+1)
  let S := B₁ \ B₀
  have hm₀ : MeasurableSet B₀ := (logarithmicBox_isClosed _ _).measurableSet
  have hm₁ : MeasurableSet B₁ := (logarithmicBox_isClosed _ _).measurableSet
  have hmS : MeasurableSet S := hm₁.diff hm₀
  have hsub : B₀ ⊆ B₁ := logarithmicBox_mono (by linarith)
  have hfin₀ : μ B₀ ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hsub)
  have hfinS : μ S ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)
  have hi₀ : Integrable (B₀.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hm₀).mpr (integrableOn_const hfin₀)
  have hi₁ : Integrable (B₁.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hm₁).mpr (integrableOn_const hfin)
  have hiS : Integrable (S.indicator (fun _ => (K:ℝ)^2)) μ :=
    (integrable_indicator_iff hmS).mpr (integrableOn_const hfinS)
  have hsq : ∀ x, (logarithmicCutoff k L x)^2 ≤ B₁.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B₁
    · rw [indicator_of_mem hx]
      have hh := logarithmicCutoff_mem_Icc k L x
      nlinarith [sq_nonneg (logarithmicCutoff k L x),mul_nonneg hh.1 (sub_nonneg.mpr hh.2)]
    · rw [indicator_of_notMem hx]
      have ho : ∃ i, L+1 ≤ |x i| := by
        change ¬∀ i, |x i| ≤ L+1 at hx
        push Not at hx
        obtain ⟨i,hi⟩ := hx
        exact ⟨i,hi.le⟩
      rw [logarithmicCutoff_zero ho]
      norm_num
  have hd : ∀ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ≤
      S.indicator (fun _ => (K:ℝ)^2) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2
    · rw [indicator_of_notMem hx]
      have he : fderiv ℝ (logarithmicCutoff k L) x = 0 := by
        by_cases hx₀ : x ∈ B₀
        · exact logarithmicCutoff_fderiv_eq_zero_of_mem hx₀
        · have hx₁ : x ∉ B₁ := fun h => hx ⟨h,hx₀⟩
          change ¬∀ i, |x i| ≤ L+1 at hx₁
          push Not at hx₁
          obtain ⟨i,hi⟩ := hx₁
          exact logarithmicCutoff_fderiv_eq_zero_of_outside ⟨i,hi.le⟩
      simp [he]
  have hiv : Integrable (fun x => (logarithmicCutoff k L x)^2) μ :=
    hi₁.mono' ((logarithmicCutoff_smooth k L).continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hsq x))
  have hid : Integrable (fun x => ‖fderiv ℝ (logarithmicCutoff k L) x‖^2) μ :=
    hiS.mono' (((logarithmicCutoff_smooth k L).continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hd x))
  have hlo : μ.real B₀ ≤ ∫ x, (logarithmicCutoff k L x)^2 ∂μ := by
    have hh := integral_mono hi₀ hiv (show B₀.indicator (fun _ => (1:ℝ)) ≤
        (fun x => (logarithmicCutoff k L x)^2) from by
      intro x
      by_cases hx : x ∈ B₀
      · simp only [indicator_of_mem hx,logarithmicCutoff_one hx,one_pow,le_refl]
      · simp only [indicator_of_notMem hx]
        exact sq_nonneg _)
    simpa only [integral_indicator_const _ hm₀,smul_eq_mul,mul_one] using hh
  have hhi : (∫ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ∂μ) ≤
      (K:ℝ)^2 * (μ.real B₁-μ.real B₀) := by
    have hh := integral_mono hid hiS hd
    rw [integral_indicator_const _ hmS,smul_eq_mul,measureReal_sdiff hsub hm₀ hfin,mul_comm] at hh
    exact hh
  exact (hlo.trans hP).trans ((mul_le_mul_of_nonneg_left hhi hA).trans_eq (by ring))

/- The growth contradiction, for actual Borel measures and actual smooth
cutoffs, with only eventual availability on each finite logarithmic box. -/
theorem no_polynomial_logarithmic_poincare {k l₀ : ℕ} (μ : ℕ → Measure (Space k))
    {c A C : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hpos : ∀ᶠ j in atTop, c ≤ (μ j).real (logarithmicBox k l₀))
    (hfin : ∀ L : ℕ, l₀ ≤ L → ∀ᶠ j in atTop, μ j (logarithmicBox k L) ≠ ⊤)
    (hupper : ∀ L : ℕ, l₀ ≤ L → ∀ᶠ j in atTop,
      (μ j).real (logarithmicBox k L) ≤ C*(L+1:ℝ)^k)
    (hP : ∀ L : ℕ, l₀ ≤ L → ∀ᶠ j in atTop,
      (∫ x, (logarithmicCutoff k L x)^2 ∂μ j) ≤
        A * ∫ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ∂μ j) : False := by
  obtain ⟨K,hKpos,hK⟩ := logarithmicCutoff_uniform_lipschitz k
  apply no_eventual_polynomial_shell_growth (fun j L => (μ j).real (logarithmicBox k L))
    k l₀ hc (show 0 < A*(K:ℝ)^2 by exact mul_pos hA (sq_pos_of_pos (by exact_mod_cast hKpos))) hpos ?_ hupper
  intro L hL
  filter_upwards [hP L hL,hfin (L+1) (by omega)] with j hj hf
  have hf' : μ j (logarithmicBox k ((L:ℝ)+1)) ≠ ⊤ := by
    simpa only [Nat.cast_add,Nat.cast_one] using hf
  simpa only [Nat.cast_add,Nat.cast_one] using logarithmic_shell_growth (μ j) (hK L) hf' hA.le hj

end AffineBernstein

end

end OAI
