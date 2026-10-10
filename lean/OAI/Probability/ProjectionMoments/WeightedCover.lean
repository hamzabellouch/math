import OAI.Probability.ProjectionMoments.CapDuality

namespace OAI

noncomputable section

open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace ProjectionMoments
namespace Weighted

section
variable {ι : Type*}

def budget (b : ι → ℝ) (K : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∀ s : Finset ι, ∑ i ∈ s, a i*b i ≤ K}

lemma budget_closed (b : ι → ℝ) (K : ℝ) : IsClosed (budget b K) := by
  have he : budget b K = (⋂ i, {a | 0 ≤ a i}) ∩
      (⋂ s : Finset ι, {a | ∑ i ∈ s, a i*b i ≤ K}) := by ext a; simp [budget]
  rw [he]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_iInter (fun s => isClosed_le (by fun_prop) continuous_const))

lemma budget_mem_single {b : ι → ℝ} {K : ℝ} {a : ι → ℝ} (ha : a ∈ budget b K) (i : ι) :
    a i * b i ≤ K := by
  classical
  simpa using ha.2 {i}

lemma budget_compact {b : ι → ℝ} (hb : ∀ i, 0 < b i) (K : ℝ) : IsCompact (budget b K) := by
  apply (isCompact_pi_infinite (fun i => isCompact_Icc (a := (0:ℝ)) (b := K/b i))).of_isClosed_subset
    (budget_closed b K)
  intro a ha
  exact fun i => ⟨ha.1 i, (le_div_iff₀ (hb i)).mpr (budget_mem_single ha i)⟩

lemma budget_convex (b : ι → ℝ) (K : ℝ) : Convex ℝ (budget b K) := by
  intro a ha a' ha' t u ht hu htu
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ht (ha.1 i)) (mul_nonneg hu (ha'.1 i))
  · intro s
    have he : (∑ i ∈ s, (t • a + u • a') i * b i) =
        t*(∑ i ∈ s, a i*b i) + u*(∑ i ∈ s, a' i*b i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum]
    rw [he]
    calc
      _ ≤ t*K+u*K := add_le_add (mul_le_mul_of_nonneg_left (ha.2 s) ht)
        (mul_le_mul_of_nonneg_left (ha'.2 s) hu)
      _ = K := by rw [← add_mul, htu, one_mul]

lemma cost_summable {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : Summable (fun i => a i*b i) :=
  summable_of_sum_le (fun i => mul_nonneg (ha.1 i) (hb i)) ha.2

lemma cost_le {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : (∑' i, a i*b i) ≤ K :=
  (cost_summable hb ha).tsum_le_of_sum_le ha.2

lemma eval_summable {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) : Summable (fun i => a i*v i) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (ha.1 i) (hv i).1)
    (fun i => mul_le_mul_of_nonneg_left ((hv i).2.trans (hb i)) (ha.1 i))
    (cost_summable (fun i => (zero_le_one.trans (hb i))) ha)

lemma eval_le {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) : (∑' i, a i*v i) ≤ K := by
  exact ((eval_summable hb ha hv).tsum_le_tsum
    (fun i => mul_le_mul_of_nonneg_left ((hv i).2.trans (hb i)) (ha.1 i))
    (cost_summable (fun i => (zero_le_one.trans (hb i))) ha)).trans (cost_le (fun i => (zero_le_one.trans (hb i))) ha)

lemma eval_tail {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1)
    (s : Finset ι) {R : ℝ} (hR : 0 < R) (hs : ∀ i ∉ s, R ≤ b i) :
    0 ≤ (∑' i, a i*v i) - ∑ i ∈ s, a i*v i ∧
      (∑' i, a i*v i) - ∑ i ∈ s, a i*v i ≤ K/R := by
  classical
  have hc := cost_summable (fun i => zero_le_one.trans (hb i)) ha
  have he := eval_summable hb ha hv
  have hid := he.sum_add_tsum_subtype_compl s
  have hnon : 0 ≤ ∑' i : {i // i ∉ s}, a i*v i :=
    tsum_nonneg (fun i => mul_nonneg (ha.1 i) (hv i).1)
  have hcost : (∑' i : {i // i ∉ s}, a i*b i) ≤ K := by
    have heq := hc.sum_add_tsum_subtype_compl s
    have hsum : 0 ≤ ∑ i ∈ s, a i*b i :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (ha.1 i) (zero_le_one.trans (hb i)))
    have htot := cost_le (fun i => zero_le_one.trans (hb i)) ha
    linarith
  have hbound : (∑' i : {i // i ∉ s}, a i*v i) ≤ K/R := by
    calc
      _ ≤ ∑' i : {i // i ∉ s}, (a i*b i)/R := by
        apply (he.subtype _).tsum_le_tsum _ ((hc.subtype _).div_const R)
        intro i
        apply (le_div_iff₀ hR).mpr
        calc
          a i*v i*R ≤ a i*1*R :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv i).2 (ha.1 i)) hR.le
          _ ≤ a i*b i := by simpa using mul_le_mul_of_nonneg_left (hs i i.2) (ha.1 i)
      _ = (∑' i : {i // i ∉ s}, a i*b i)/R := tsum_div_const
      _ ≤ K/R := div_le_div_of_nonneg_right hcost hR.le
  constructor <;> linarith

lemma eval_continuousOn {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i)
    (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    {v : ι → ℝ} (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) :
    ContinuousOn (fun a : ι → ℝ => ∑' i, a i*v i) (budget b K) := by
  classical
  have hconv : TendstoUniformlyOn (fun s : Finset ι => fun a : ι → ℝ => ∑ i ∈ s, a i*v i)
      (fun a => ∑' i, a i*v i) atTop (budget b K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let R := (K+1)/ε
    have hR : 0 < R := by dsimp [R]; positivity
    let s := (hproper R).toFinset
    filter_upwards [eventually_ge_atTop s] with t ht
    intro a ha
    have hsmall : ∀ i ∉ t, R ≤ b i := by
      intro i hi
      apply le_of_lt
      by_contra! hh
      exact hi (ht (by simpa [s] using hh))
    have hh := eval_tail hb ha hv t hR hsmall
    rw [Real.dist_eq, abs_of_nonneg hh.1]
    apply hh.2.trans_lt
    apply (div_lt_iff₀ hR).mpr
    have he : ε*R = K+1 := by dsimp [R]; field_simp
    linarith
  apply hconv.continuousOn
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun _ => (by fun_prop : Continuous _).continuousOn))

lemma zero_mem_budget {b : ι → ℝ} {K : ℝ} (hK : 0 ≤ K) : (0 : ι → ℝ) ∈ budget b K := by
  constructor
  · simp
  · simpa using (fun _ : Finset ι => hK)

lemma single_mem_budget [DecidableEq ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i) {K : ℝ} (hK : 0 ≤ K) (i : ι) :
    (Pi.single i (K/b i) : ι → ℝ) ∈ budget b K := by
  classical
  constructor
  · intro j
    simp only [Pi.single_apply]
    split_ifs
    · exact div_nonneg hK (hb i).le
    · exact le_rfl
  · intro s
    have he : (fun j => (Pi.single i (K/b i) : ι → ℝ) j * b j) = (Pi.single i K : ι → ℝ) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [div_mul_cancel₀ K (hb i).ne']
      · simp [hj]
    rw [he]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hK

lemma eval_single [DecidableEq ι] {b : ι → ℝ} (K : ℝ) (i : ι) (v : ι → ℝ) :
    (∑' j, (Pi.single i (K/b i) : ι → ℝ) j * v j) = (K/b i)*v i := by
  classical
  rw [tsum_eq_single i (by intro j hj; simp [hj])]
  simp

lemma eval_smul_add {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a a' v : ι → ℝ}
    (ha : a ∈ budget b K) (ha' : a' ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1)
    (t u : ℝ) :
    (∑' i, (t • a + u • a') i * v i) = t*(∑' i, a i*v i)+u*(∑' i, a' i*v i) := by
  have he : (fun i => (t • a + u • a') i * v i) =
      fun i => t*(a i*v i)+u*(a' i*v i) := by ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [he, ((eval_summable hb ha hv).mul_left t).tsum_add ((eval_summable hb ha' hv).mul_left u),
    tsum_mul_left, tsum_mul_left]

lemma finite_dual_domination {J : Type*} [Fintype J] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ c : J → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by
  classical
  let F : (ι → ℝ) → (J → ℝ) := fun a j => ∑' i, a i*v j i
  let C := F '' budget b K
  let D := C + Set.Iic (0 : J → ℝ)
  have hCc : IsCompact C := (budget_compact (fun i => zero_lt_one.trans_le (hb i)) K).image_of_continuousOn
    (continuousOn_pi.mpr (fun j => eval_continuousOn hb hproper hK.le (hv j)))
  have hCv : Convex ℝ C := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨a',ha',rfl⟩ t u ht hu htu
    refine ⟨t • a + u • a', budget_convex b K ha ha' ht hu htu, ?_⟩
    ext j
    exact eval_smul_add hb ha ha' (hv j) t u
  have hDc : IsClosed D := isClosed_Iic.add_left_of_isCompact hCc
  have hDv : Convex ℝ D := hCv.add (convex_Iic (0 : J → ℝ))
  have h00 : (0 : J → ℝ) ∈ C := ⟨0,zero_mem_budget hK.le,by ext j; simp [F]⟩
  have hneg : ∀ w : J → ℝ, w ≤ 0 → w ∈ D := by
    intro w hw
    exact ⟨0,h00,w,hw,zero_add _⟩
  have hymem : y ∈ D := by
    by_contra hy
    obtain ⟨f,U,hf,hUy⟩ := geometric_hahn_banach_closed_point hDv hDc hy
    have hU : 0 < U := by simpa using hf 0 (hneg 0 le_rfl)
    let c : J → ℝ := fun j => f (Pi.single j 1)
    have hfe (x : J → ℝ) : f x = ∑ j, c j*x j := by
      have he : x = ∑ j, x j • Pi.single j (1:ℝ) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [he, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      change x j * c j = c j * x j
      ring
    have hc : ∀ j, 0 ≤ c j := by
      intro j
      by_contra! hj
      let t := (U+1)/(-c j)
      have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hj)
      have hw : -t • Pi.single j (1:ℝ) ≤ (0 : J → ℝ) := by
        intro i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply]
        split_ifs <;> nlinarith
      have hh := hf _ (hneg _ hw)
      rw [map_smul] at hh
      change -t*c j < U at hh
      have he : -t*c j = U+1 := by dsimp [t]; field_simp [hj.ne]
      linarith
    have hsingle (i : ι) : (K/b i)*(∑ j, c j*v j i) < U := by
      have ha := single_mem_budget (fun i => zero_lt_one.trans_le (hb i)) hK.le i
      have hmem : F ((Pi.single i (K/b i) : ι → ℝ)) ∈ D :=
        ⟨F ((Pi.single i (K/b i) : ι → ℝ)),⟨_,ha,rfl⟩,0,by simp,add_zero _⟩
      have hh := hf _ hmem
      rw [hfe] at hh
      simp only [F, eval_single] at hh
      convert hh using 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have htest : ∀ i, ∑ j, (K/U*c j)*v j i ≤ b i := by
      intro i
      have hh := hsingle i
      rw [div_mul_eq_mul_div, div_lt_iff₀ (zero_lt_one.trans_le (hb i))] at hh
      have he : (∑ j, (K/U*c j)*v j i) = (K/U)*(∑ j, c j*v j i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
      rw [he, div_mul_eq_mul_div, div_le_iff₀ hU]
      nlinarith
    have hres := hdual (fun j => K/U*c j) (fun j => mul_nonneg (div_nonneg hK.le hU.le) (hc j)) htest
    have he : (∑ j, K/U*c j*y j) = (K/U)*f y := by
      rw [hfe, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
    rw [he, div_mul_eq_mul_div, div_le_iff₀ hU] at hres
    nlinarith
  obtain ⟨z,⟨a,ha,rfl⟩,w,hw,he⟩ := hymem
  refine ⟨a,ha,?_⟩
  intro j
  have hj := congrFun he j
  have hh := hw j
  change F a j + w j = y j at hj
  change w j ≤ 0 at hh
  dsimp [F] at hj
  linarith

theorem dual_domination {J : Type*} {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ s : Finset J, ∀ c : s → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by
  classical
  let B := budget b K
  let : CompactSpace B := isCompact_iff_compactSpace.mp (budget_compact (fun i => zero_lt_one.trans_le (hb i)) K)
  let t : J → Set B := fun j => {a | y j ≤ ∑' i, a.val i*v j i}
  have hclosed : ∀ j, IsClosed (t j) := by
    intro j
    exact isClosed_le continuous_const (eval_continuousOn hb hproper hK.le (hv j)).domRestrict
  have hfinite : ∀ s : Finset J, (Set.univ ∩ ⋂ j ∈ s, t j).Nonempty := by
    intro s
    obtain ⟨a,ha,haj⟩ := finite_dual_domination hb hproper hK
      (fun j : s => v j) (fun j => hv j) (fun j : s => y j) (hdual s)
    refine ⟨⟨a,ha⟩,Set.mem_univ _,?_⟩
    simp only [Set.mem_iInter]
    intro j hj
    exact haj ⟨j,hj⟩
  obtain ⟨a,_,ha⟩ := isCompact_univ.inter_iInter_nonempty t hclosed hfinite
  exact ⟨a.val,a.property,fun j => Set.mem_iInter.mp ha j⟩

end

variable {Ω ι : Type*} [MeasurableSpace Ω]

lemma lintegral_finite_test {J : Type*} [Fintype J] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : J → Set Ω) (hS : ∀ j, MeasurableSet (S j)) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (∫⁻ x, ∑ j, ENNReal.ofReal (c j) * (S j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) =
      ENNReal.ofReal (∑ j, c j * μ.real (S j)) := by
  rw [lintegral_finsetSum (f := fun j x => ENNReal.ofReal (c j) * (S j).indicator (fun _ => (1 : ℝ≥0∞)) x) _ (fun j _ => measurable_const.mul (measurable_const.indicator (hS j)))]
  simp only [lintegral_const_mul _ (measurable_const.indicator (hS _))]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc j) (measureReal_nonneg))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ENNReal.ofReal_mul (hc j), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [lintegral_indicator (hS j)]
  simp

theorem measure_domination [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧ (∑' i, a i*b i) ≤ K ∧
      μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by
  classical
  let J := {S : Set Ω // MeasurableSet S}
  let v : J → ι → ℝ := fun S i => (P i).real S
  let y : J → ℝ := fun S => μ.real S
  have hv : ∀ S i, v S i ∈ Icc (0:ℝ) 1 := by
    intro S i
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hd : ∀ s : Finset J, ∀ c : s → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K := by
    intro s c hc hci
    let h : Ω → ℝ≥0∞ := fun x => ∑ j : s,
      ENNReal.ofReal (c j) * (j.val.val).indicator (fun _ => (1:ℝ≥0∞)) x
    have hm : Measurable h := by
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul
        (measurable_const.indicator j.val.property))
    have hbnd : ∃ H : ℝ≥0, ∀ x, h x ≤ H := by
      refine ⟨∑ j : s, (c j).toNNReal, ?_⟩
      intro x
      rw [ENNReal.ofNNReal_finsetSum]
      change (∑ j : s, ENNReal.ofReal (c j) * (j.val.val).indicator (fun _ => (1:ℝ≥0∞)) x) ≤ _
      apply Finset.sum_le_sum
      intro j hj
      by_cases hx : x ∈ j.val.val <;> simp [Set.indicator, hx, ENNReal.ofReal]
    have he (ν : Measure Ω) [IsFiniteMeasure ν] : (∫⁻ x, h x ∂ν) =
        ENNReal.ofReal (∑ j : s, c j*ν.real j.val.val) :=
      lintegral_finite_test ν (fun j : s => j.val.val) (fun j => j.val.property) c hc
    have ht := hdual h hm hbnd (fun i => by rw [he]; exact ENNReal.ofReal_le_ofReal (hci i))
    rw [he, ENNReal.ofReal_le_ofReal_iff hK.le] at ht
    exact ht
  obtain ⟨a,ha,has⟩ := dual_domination hb hproper hK v hv y hd
  refine ⟨a,ha.1,cost_summable (fun i => zero_le_one.trans (hb i)) ha,
    cost_le (fun i => zero_le_one.trans (hb i)) ha,?_⟩
  apply Measure.le_iff.mpr
  intro S hS
  have hs := has ⟨S,hS⟩
  have hsum := eval_summable hb ha (hv ⟨S,hS⟩)
  have hc : ∀ i, 0 ≤ a i*(P i).real S := fun i => mul_nonneg (ha.1 i) measureReal_nonneg
  have hh := ENNReal.ofReal_le_ofReal hs
  change ENNReal.ofReal (μ.real S) ≤ ENNReal.ofReal (∑' i, a i*(P i).real S) at hh
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_tsum_of_nonneg hc hsum] at hh
  rw [Measure.sum_apply _ hS]
  convert hh using 1
  congr 1
  funext i
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (ha.1 i),
    measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem measure_domination_nonneg [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 ≤ K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧
      (∑' i, a i*b i) ≤ K ∧ μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · subst K
    have hm := hdual (fun _ => 1) measurable_const ⟨1,fun _ => le_rfl⟩
      (fun i => by simp only [lintegral_const,measure_univ,mul_one]; exact ENNReal.one_le_ofReal.mpr (hb i))
    simp only [lintegral_const,one_mul,ENNReal.ofReal_zero,nonpos_iff_eq_zero] at hm
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp hm
    refine ⟨fun _ => 0,fun _ => le_rfl,?_,?_,?_⟩ <;> simp [hμ]
  · exact measure_domination μ P hb hproper hKpos hdual

end Weighted
end ProjectionMoments

end

end OAI
