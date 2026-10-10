import OAI.Probability.GaussianReplacement.ConditionalInfo

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

def CriticalComparisonMain : Prop :=
  ∃ (K : ℝ) (d₀ : ℕ), 0 < K ∧ ∀ (d : ℕ), d₀ ≤ d →
    ∀ (W : Type) [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W],
    ∀ (P : Measure ((Sphere d×W)×Rows (d/10) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d) →
    shannonEntropy (P.map swapLast).snd ≤ ENNReal.ofReal ((d:ℝ)^2) →
    exposedInformation (P.fst.prod (gaussianRows (d/10+(d/2-d/10)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/2-d/10) P) + ENNReal.ofReal (K*d)




def criticalRadius (j : ℕ) : ℝ := 2 * (1/2:ℝ)^j

lemma criticalRadius_pos (j : ℕ) : 0 < criticalRadius j := by
  unfold criticalRadius
  positivity

lemma criticalRadius_le_two (j : ℕ) : criticalRadius j ≤ 2 := by
  unfold criticalRadius
  nlinarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n:=j)]

lemma criticalRadius_tendsto : Tendsto criticalRadius atTop (𝓝 0) := by
  change Tendsto (fun j => 2 * (1/2:ℝ)^j) atTop (𝓝 0)
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul 2

def ballRatio {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) (j : ℕ) : ℝ :=
  (F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius j}).toReal / criticalRadius j ^ ℓ

lemma sphere_dist_le_two {d : ℕ} (s t : Sphere d) : dist (s:Vector d) (t:Vector d) ≤ 2 := by
  have hs : ‖(s:Vector d)‖ = 1 := by simp
  have ht : ‖(t:Vector d)‖ = 1 := by simp
  calc
    _ ≤ dist (s:Vector d) 0 + dist (0:Vector d) t := dist_triangle _ _ _
    _ = 2 := by simp only [dist_zero_right,dist_zero_left,hs,ht]; norm_num

lemma ballRatio_zero {d : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (ℓ : ℕ) (s : Sphere d) : ballRatio F ℓ s 0 = (2:ℝ)⁻¹ ^ ℓ := by
  have he : {x : Sphere d | dist (x:Vector d) (s:Vector d) ≤ criticalRadius 0} = univ := by
    ext x
    simp [criticalRadius, sphere_dist_le_two x s]
  unfold ballRatio
  rw [he]
  simp [criticalRadius,one_div]

lemma ballRatio_nonneg {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) (j : ℕ) :
    0 ≤ ballRatio F ℓ s j := div_nonneg ENNReal.toReal_nonneg (pow_pos (criticalRadius_pos j) _).le

lemma measurable_ballRatio {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ j : ℕ) :
    Measurable (fun s => ballRatio F ℓ s j) := by
  have hm : MeasurableSet {p : Sphere d × Sphere d |
      dist (p.2:Vector d) (p.1:Vector d) ≤ criticalRadius j} :=
    measurableSet_le (by fun_prop) measurable_const
  exact (measurable_measure_prodMk_left hm).ennreal_toReal.div_const _

lemma ballRatio_le_growth {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsFiniteMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ ≤ n)
    (s : Sphere d) (j : ℕ) : ballRatio F ℓ s j ≤ D * criticalRadius j^(n-ℓ) := by
  have hr := criticalRadius_pos j
  have hb : (F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius j}).toReal ≤
      D * criticalRadius j^n := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hD (pow_nonneg hr.le _))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hF s (criticalRadius j) hr)
  apply (div_le_iff₀ (pow_pos hr ℓ)).mpr
  calc
    _ ≤ D * criticalRadius j^n := hb
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hℓ]

lemma ballRatio_tendsto_zero {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsFiniteMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    Tendsto (ballRatio F ℓ s) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => D * criticalRadius j^(n-ℓ)) atTop (𝓝 0) := by
    simpa [Nat.ne_of_gt (Nat.sub_pos_of_lt hℓ)] using (criticalRadius_tendsto.pow (n-ℓ)).const_mul D
  exact squeeze_zero (ballRatio_nonneg F ℓ s) (ballRatio_le_growth F D hD hF hℓ.le s) ht

lemma exists_max_of_tendsto_zero (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0))
    (h0 : 0 < f 0) : ∃ j, ∀ i, f i ≤ f j := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hf.eventually (gt_mem_nhds h0))
  obtain ⟨j,hj,hmax⟩ := (Finset.range (N+1)).exists_max_image f (by simp)
  refine ⟨j,fun i => ?_⟩
  by_cases hi : i < N+1
  · exact hmax _ (Finset.mem_range.mpr hi)
  · exact (hN i (by omega)).le.trans (hmax 0 (by simp))

lemma ballRatio_has_max {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j := by
  apply exists_max_of_tendsto_zero _ (ballRatio_tendsto_zero F D hD hF hℓ s)
  rw [ballRatio_zero]
  positivity


def criticalIndex {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) : ℕ := by
  classical
  exact if h : ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j then Nat.find h else 0

def criticalMass {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) : ℝ :=
  ballRatio F ℓ s (criticalIndex F ℓ s)

def criticalLevel {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) : ℤ :=
  ⌈Real.log (criticalMass F ℓ s)⌉

lemma criticalIndex_max {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) (i : ℕ) :
    ballRatio F ℓ s i ≤ criticalMass F ℓ s := by
  classical
  have hm := ballRatio_has_max F D hD hF hℓ s
  simp only [criticalMass,criticalIndex,dite_eq_left hm]
  exact Nat.find_spec hm i

lemma criticalIndex_least {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d)
    (j : ℕ) (hj : ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j) : criticalIndex F ℓ s ≤ j := by
  classical
  have hm := ballRatio_has_max F D hD hF hℓ s
  simp only [criticalIndex,dite_eq_left hm]
  exact Nat.find_min' hm hj

lemma measurable_criticalIndex {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ : ℕ) :
    Measurable (criticalIndex F ℓ) := by
  classical
  have hp (j : ℕ) : MeasurableSet {s | ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_ballRatio F ℓ i) (measurable_ballRatio F ℓ j))
  have he : MeasurableSet {s | ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion hp
  apply measurable_to_countable'
  intro j
  change MeasurableSet {s | criticalIndex F ℓ s = j}
  by_cases hj : j = 0
  · subst j
    have hset : {s | criticalIndex F ℓ s = 0} =
        {s | ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s 0} ∪
        {s | ¬ ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} := by
      ext s
      simp only [criticalIndex,mem_ofPred_eq,mem_union]
      split_ifs with h
      · simp [Nat.find_eq_zero,h]
      · simp [h]
    rw [hset]
    exact (hp 0).union he.compl
  · have hset : {s | criticalIndex F ℓ s = j} =
        {s | ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} ∩
        ⋂ k < j, {s | ¬ ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s k} := by
      ext s
      simp only [criticalIndex,mem_ofPred_eq,mem_inter_iff,mem_iInter]
      split_ifs with h
      · exact Nat.find_eq_iff h
      · simp only [eq_comm (a:=0),hj,false_iff,not_and]
        intro hs
        exact False.elim (h ⟨j,hs⟩)
    rw [hset]
    exact (hp j).inter (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => (hp k).compl)))

lemma measurable_criticalMass {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ : ℕ) :
    Measurable (criticalMass F ℓ) := by
  have hm : Measurable (fun p : Sphere d × ℕ => ballRatio F ℓ p.1 p.2) :=
    measurable_from_prod_countable_left (measurable_ballRatio F ℓ)
  have hpair : Measurable (fun s : Sphere d => (s,criticalIndex F ℓ s)) :=
    measurable_id.prodMk (measurable_criticalIndex F ℓ)
  have hcomp := hm.comp hpair
  change Measurable (fun s => ballRatio F ℓ s (criticalIndex F ℓ s))
  exact hcomp

lemma measurable_criticalLevel {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ : ℕ) :
    Measurable (criticalLevel F ℓ) := (measurable_criticalMass F ℓ).log.ceil

lemma criticalMass_pos {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    0 < criticalMass F ℓ s := by
  have hm := criticalIndex_max F D hD hF hℓ s 0
  rw [ballRatio_zero] at hm
  exact lt_of_lt_of_le (by positivity) hm

lemma criticalMass_log_bounds {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 < D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    -(ℓ:ℝ)*Real.log 2 ≤ Real.log (criticalMass F ℓ s) ∧
      Real.log (criticalMass F ℓ s) ≤ Real.log D + (n-ℓ:ℕ)*Real.log 2 := by
  have hp := criticalMass_pos F D hD.le hF hℓ s
  constructor
  · have hm := criticalIndex_max F D hD.le hF hℓ s 0
    rw [ballRatio_zero] at hm
    have h := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)⁻¹^ℓ) hm
    simpa only [Real.log_pow,Real.log_inv,mul_neg,neg_mul] using h
  · have hg := ballRatio_le_growth F D hD.le hF hℓ.le s (criticalIndex F ℓ s)
    have hb : criticalMass F ℓ s ≤ D * 2^(n-ℓ) := hg.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (criticalRadius_pos _).le (criticalRadius_le_two _) _) hD.le)
    simpa only [Real.log_mul hD.ne' (by positivity : (2:ℝ)^(n-ℓ) ≠ 0),Real.log_pow] using Real.log_le_log hp hb

lemma criticalLevel_bounds {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 1 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    -(ℓ:ℝ) ≤ (criticalLevel F ℓ s : ℝ) ∧
      (criticalLevel F ℓ s : ℝ) ≤ Real.log D + n + 1 := by
  obtain ⟨hlo,hup⟩ := criticalMass_log_bounds F D (lt_of_lt_of_le zero_lt_one hD) hF hℓ s
  have hc := Int.le_ceil (Real.log (criticalMass F ℓ s))
  have hc' := Int.ceil_lt_add_one (Real.log (criticalMass F ℓ s))
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hn : ((n-ℓ:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n ℓ
  change -(ℓ:ℝ) ≤ (⌈Real.log (criticalMass F ℓ s)⌉:ℝ) ∧ _
  constructor
  · nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]
  · change (⌈Real.log (criticalMass F ℓ s)⌉:ℝ) ≤ _
    nlinarith [Nat.cast_nonneg (α:=ℝ) (n-ℓ)]

lemma criticalIndex_bound {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 1 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    (criticalIndex F ℓ s : ℝ) ≤ n + 1 + 2 * Real.log D := by
  have hp := criticalMass_pos F D (by linarith) hF hℓ s
  have hlo := (criticalMass_log_bounds F D (by linarith) hF hℓ s).1
  have hg := ballRatio_le_growth F D (by linarith) hF hℓ.le s (criticalIndex F ℓ s)
  have hu := Real.log_le_log hp hg
  have hd0 : D ≠ 0 := by linarith
  have hj := criticalRadius_pos (criticalIndex F ℓ s)
  rw [Real.log_mul hd0 (pow_ne_zero _ hj.ne'),Real.log_pow] at hu
  have hr : Real.log (criticalRadius (criticalIndex F ℓ s)) =
      (1-(criticalIndex F ℓ s:ℝ))*Real.log 2 := by
    rw [criticalRadius,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    simp only [one_div, Real.log_inv]
    ring
  rw [hr] at hu
  have hj0 : 0 ≤ (criticalIndex F ℓ s:ℝ) := Nat.cast_nonneg _
  have hn1 : (1:ℝ) ≤ (n-ℓ:ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hℓ)
  have hn : ((n-ℓ:ℕ):ℝ) = n - ℓ := by exact_mod_cast (Nat.cast_sub hℓ.le : ((n-ℓ:ℕ):ℝ) = n-ℓ)
  have hl2lo : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlD := Real.log_nonneg hD
  have hh : (criticalIndex F ℓ s:ℝ) * ((n-ℓ:ℕ):ℝ) * Real.log 2 ≤ Real.log D + n*Real.log 2 := by
    nlinarith
  have ha : (criticalIndex F ℓ s:ℝ) * Real.log 2 ≤
      (criticalIndex F ℓ s:ℝ) * ((n-ℓ:ℕ):ℝ) * Real.log 2 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  by_cases hjn : (criticalIndex F ℓ s:ℝ) ≤ n
  · linarith
  · have ht := mul_nonneg (show 0 ≤ (criticalIndex F ℓ s:ℝ)-n by linarith)
      (show 0 ≤ Real.log 2-1/2 by linarith)
    nlinarith


def criticalClass {d : ℕ} (F : Measure (Sphere d)) (ℓ j : ℕ) (q : ℤ) : Set (Sphere d) :=
  {s | criticalIndex F ℓ s = j ∧ criticalLevel F ℓ s = q}

lemma measurableSet_criticalClass {d : ℕ} (F : Measure (Sphere d)) [SFinite F]
    (ℓ j : ℕ) (q : ℤ) : MeasurableSet (criticalClass F ℓ j q) :=
  (measurableSet_eq_fun (measurable_criticalIndex F ℓ) measurable_const).inter
    (measurableSet_eq_fun (measurable_criticalLevel F ℓ) measurable_const)

lemma criticalClass_mass_upper {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n)
    {q : ℤ} {s : Sphere d} (hs : s ∈ criticalClass F ℓ j q) (i : ℕ) :
    F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius i} ≤
      ENNReal.ofReal (Real.exp q * criticalRadius i^ℓ) := by
  have hp := criticalMass_pos F D hD hF hℓ s
  have hq : Real.log (criticalMass F ℓ s) ≤ q := by
    have hh := Int.le_ceil (Real.log (criticalMass F ℓ s))
    change Real.log (criticalMass F ℓ s) ≤ (criticalLevel F ℓ s:ℝ) at hh
    rwa [hs.2] at hh
  have hb := (criticalIndex_max F D hD hF hℓ s i).trans ((Real.log_le_iff_le_exp hp).mp hq)
  have hb' := (div_le_iff₀ (pow_pos (criticalRadius_pos i) ℓ)).mp hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top F _)]
  exact ENNReal.ofReal_le_ofReal hb'

lemma criticalClass_mass_lower {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n)
    {q : ℤ} {s : Sphere d} (hs : s ∈ criticalClass F ℓ j q) :
    ENNReal.ofReal (Real.exp ((q:ℝ)-1) * criticalRadius j^ℓ) ≤
      F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius j} := by
  have hp := criticalMass_pos F D hD hF hℓ s
  have hq : (q:ℝ)-1 ≤ Real.log (criticalMass F ℓ s) := by
    have hh := Int.ceil_lt_add_one (Real.log (criticalMass F ℓ s))
    change (criticalLevel F ℓ s:ℝ) < _ at hh
    rw [hs.2] at hh
    linarith
  have hb := (Real.le_log_iff_exp_le hp).mp hq
  unfold criticalMass at hb
  rw [hs.1] at hb
  have hb' := (le_div_iff₀ (pow_pos (criticalRadius_pos j) ℓ)).mp hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top F _)]
  exact ENNReal.ofReal_le_ofReal hb'

lemma exists_criticalRadius {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ j, 2*t ≤ criticalRadius j ∧ criticalRadius j ≤ 4*t := by
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one ht ht1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨j,?_,?_⟩
  · unfold criticalRadius
    linarith
  · rw [pow_succ] at hlo
    unfold criticalRadius
    linarith


lemma criticalClass_restrict_growth {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ) :
    LocalGrowth (F.restrict (criticalClass F ℓ j q)) ℓ ((4:ℝ)^ℓ * Real.exp q) := by
  intro z t ht
  let A := criticalClass F ℓ j q
  let b := {x : Sphere d | dist (x:Vector d) z ≤ t}
  have hB : MeasurableSet b := measurableSet_le (by fun_prop) measurable_const
  by_cases hzero : (F.restrict A) b = 0
  · change (F.restrict A) b ≤ _
    simp [hzero]
  have hm : F (b ∩ A) ≠ 0 := by rwa [Measure.restrict_apply hB] at hzero
  obtain ⟨s,hsb,hsA⟩ := nonempty_of_measure_ne_zero hm
  obtain ⟨i,hiB,hiR⟩ : ∃ i, b ⊆ {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius i} ∧ criticalRadius i ≤ 4*t := by
    by_cases ht1 : t ≤ 1
    · obtain ⟨i,hlo,hhi⟩ := exists_criticalRadius ht ht1
      refine ⟨i,?_,hhi⟩
      intro x hx
      calc
        dist (x:Vector d) s ≤ dist (x:Vector d) z + dist z (s:Vector d) := dist_triangle _ _ _
        _ ≤ t+t := add_le_add hx (by simpa only [b, Set.mem_ofPred_eq, dist_comm] using hsb)
        _ ≤ criticalRadius i := by linarith
    · refine ⟨0,fun x _ => ?_,?_⟩
      · simpa [criticalRadius] using sphere_dist_le_two x s
      · simp only [criticalRadius,pow_zero,mul_one]
        linarith
  calc
    (F.restrict A) b ≤ F b := (Measure.restrict_le_self : F.restrict A ≤ F) b
    _ ≤ F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius i} := measure_mono hiB
    _ ≤ ENNReal.ofReal (Real.exp q * criticalRadius i^ℓ) :=
      criticalClass_mass_upper F D hD hF hℓ hsA i
    _ ≤ ENNReal.ofReal (((4:ℝ)^ℓ * Real.exp q) * t^ℓ) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Real.exp q * (4*t)^ℓ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (criticalRadius_pos i).le hiR ℓ) (Real.exp_pos _).le
        _ = _ := by rw [mul_pow]; ring


def criticalPosterior {d : ℕ} (F : Measure (Sphere d)) (ℓ j : ℕ) (q : ℤ) : Measure (Sphere d) :=
  (F (criticalClass F ℓ j q))⁻¹ • F.restrict (criticalClass F ℓ j q)

lemma criticalPosterior_growth {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ)
    (hη : 0 < F (criticalClass F ℓ j q)) :
    LocalGrowth (criticalPosterior F ℓ j q) ℓ
      ((4:ℝ)^ℓ * Real.exp q / (F (criticalClass F ℓ j q)).toReal) := by
  have hηt := measure_ne_top F (criticalClass F ℓ j q)
  have hηr : 0 < (F (criticalClass F ℓ j q)).toReal := ENNReal.toReal_pos hη.ne' hηt
  intro z t ht
  change (F (criticalClass F ℓ j q))⁻¹ * (F.restrict (criticalClass F ℓ j q)) _ ≤ _
  apply (mul_le_mul' le_rfl (criticalClass_restrict_growth F D hD hF hℓ q z t ht)).trans_eq
  have hei : (F (criticalClass F ℓ j q))⁻¹ =
      ENNReal.ofReal (((F (criticalClass F ℓ j q)).toReal)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hηr, ENNReal.ofReal_toReal hηt]
  rw [hei, ← ENNReal.ofReal_mul (inv_nonneg.mpr hηr.le)]
  congr 1
  ring



lemma criticalClass_packing {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ)
    (s : Finset (Sphere d)) (hs : ∀ x ∈ s, x ∈ criticalClass F ℓ j q)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * criticalRadius j < dist x y) :
    (s.card:ℝ) ≤ Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ := by
  let a := Real.exp ((q:ℝ)-1) * criticalRadius j^ℓ
  have ha : 0 < a := mul_pos (Real.exp_pos _) (pow_pos (criticalRadius_pos j) _)
  let b := fun x : Sphere d => {y : Sphere d | dist (y:Vector d) (x:Vector d) ≤ criticalRadius j}
  have hm (x : Sphere d) : MeasurableSet (b x) := measurableSet_le (by fun_prop) measurable_const
  have hd : (s:Set (Sphere d)).PairwiseDisjoint b := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hz : dist x y ≤ 2*criticalRadius j := by
      change dist (x:Vector d) (y:Vector d) ≤ 2*criticalRadius j
      calc
        _ ≤ dist (x:Vector d) (z:Vector d) + dist (z:Vector d) (y:Vector d) := dist_triangle _ _ _
        _ ≤ criticalRadius j + criticalRadius j := add_le_add
          (by simpa only [b, Set.mem_ofPred_eq, dist_comm] using hzx) hzy
        _ = _ := by ring
    exact (hsep x hx y hy hxy).not_ge hz
  have hb : (s.card:ℝ≥0∞) * ENNReal.ofReal a ≤ 1 := by
    calc
      _ = ∑ x ∈ s, ENNReal.ofReal a := by simp
      _ ≤ ∑ x ∈ s, F (b x) := Finset.sum_le_sum (fun x hx => criticalClass_mass_lower F D hD hF hℓ (hs x hx))
      _ = F (⋃ x ∈ s, b x) := (measure_biUnion_finset hd (fun x _ => hm x)).symm
      _ ≤ F Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hr : (s.card:ℝ)*a ≤ 1 := by
    have hb' : ((s.card:ℝ≥0∞) * ENNReal.ofReal a).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal (by norm_num : (0:ℝ) ≤ 1) (by simpa using hb)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal ha.le] using hb'
  have he : 1/a = Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ := by
    dsimp only [a]
    rw [show (1-(q:ℝ)) = -((q:ℝ)-1) by ring, Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos ((q:ℝ)-1)),ne_of_gt (pow_pos (criticalRadius_pos j) ℓ)]
  exact ((le_div_iff₀ ha).mpr hr).trans_eq he


lemma criticalClass_cover {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ) :
    ∃ s : Finset (Sphere d), (∀ x ∈ s, x ∈ criticalClass F ℓ j q) ∧
      (s.card:ℝ) ≤ Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ ∧
      ∀ x ∈ criticalClass F ℓ j q, ∃ y ∈ s, dist x y ≤ 2*criticalRadius j := by
  let N := ⌊Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ⌋₊
  obtain ⟨s,hs,hsep,hcov⟩ := exists_net_of_finite_packing_bound (criticalClass F ℓ j q)
    (mul_nonneg (by norm_num) (criticalRadius_pos j).le) N
    (fun s hs hsep => Nat.le_floor (criticalClass_packing F D hD hF hℓ q s hs hsep))
  exact ⟨s,hs,criticalClass_packing F D hD hF hℓ q s hs hsep,hcov⟩



end CurrentProjection

end

end OAI
