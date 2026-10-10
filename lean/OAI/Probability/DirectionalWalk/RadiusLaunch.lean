import OAI.Probability.DirectionalWalk.RadiusTails

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def controlledSlabOccurrence {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ) : Set (Path d) :=
  ⋃ i ∈ s, goodRadiusPrefix v a c C b i ∩ {X | slabs v X i ∈ G i}

lemma measurableSet_controlledSlabOccurrence {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ) :
    MeasurableSet (controlledSlabOccurrence v a c C b G s) := by
  apply MeasurableSet.biUnion (Finset.countable_toSet s)
  intro i hi
  exact (measurableSet_goodRadiusPrefix v a c C b i).inter
    ((Set.to_countable (G i)).measurableSet.preimage
      ((measurable_pi_apply i).comp (measurable_slabs v)))

lemma controlledSlabOccurrence_probability {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ) (q : ℝ)
    (hq : ∀ i ∈ s, q ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b i)) :
    q*(∑ i ∈ s, (slabLaw μ v).real (G i)) - (∑ i ∈ s, (slabLaw μ v).real (G i))^2 ≤
      (conditioned μ v).real (controlledSlabOccurrence v a c C b G s) := by
  let := conditioned_probability μ v hp
  have hG (i : ℕ) : MeasurableSet {X | slabs v X i ∈ G i} :=
    (Set.to_countable (G i)).measurableSet.preimage
      ((measurable_pi_apply i).comp (measurable_slabs v))
  have hind (i : ℕ) :
      (conditioned μ v).real (goodRadiusPrefix v a c C b i ∩ {X | slabs v X i ∈ G i}) =
        (conditioned μ v).real (goodRadiusPrefix v a c C b i) *
          (conditioned μ v).real {X | slabs v X i ∈ G i} := by
    rw [goodRadiusPrefix_current_factorization μ hell v hv hp,
      slabs_event_measureReal μ hell v hv hp]
  have hpair (i j : ℕ) (hij : i ≠ j) :
      (conditioned μ v).real ({X | slabs v X i ∈ G i} ∩ {X | slabs v X j ∈ G j}) ≤
        (conditioned μ v).real {X | slabs v X i ∈ G i} *
          (conditioned μ v).real {X | slabs v X j ∈ G j} := by
    rw [slabs_pair_event_factorization μ hell v hv hp hij,
      slabs_event_measureReal μ hell v hv hp,slabs_event_measureReal μ hell v hv hp]
  have hh := controlled_occurrence_lower (conditioned μ v) (goodRadiusPrefix v a c C b)
    (fun i => {X | slabs v X i ∈ G i}) (measurableSet_goodRadiusPrefix v a c C b)
    hG hind hpair s q hq
  simpa only [slabs_event_measureReal μ hell v hv hp,controlledSlabOccurrence] using hh

lemma controlledSlabOccurrence_probability_half {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ)
    (hq : ∀ i ∈ s, (3:ℝ)/4 ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b i))
    (hsmall : (∑ i ∈ s, (slabLaw μ v).real (G i)) ≤ 1/4) :
    (∑ i ∈ s, (slabLaw μ v).real (G i))/2 ≤
      (conditioned μ v).real (controlledSlabOccurrence v a c C b G s) := by
  have hh := controlledSlabOccurrence_probability μ hell v hv hp a c C b G s (3/4) hq
  have hn : 0 ≤ ∑ i ∈ s, (slabLaw μ v).real (G i) :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  nlinarith

lemma slabWidth_pos_of_regeneration {d : ℕ} (v : Fin d → ℝ) (γ : Word d)
    (hγ : RegenerationWord v γ) : 0 < slabWidth v γ := by
  have hh := (hγ.2.2.2.1 0 hγ.1).2
  simpa only [hγ.2.1,height_zero,slabWidth] using hh

lemma slabHeightSum_strictMono {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) : StrictMono (slabHeightSum v X) := by
  apply strictMono_nat_of_lt_succ
  intro k
  change slabHeightSum v X k < ∑ i ∈ Finset.range (k+1), slabWidth v (slabs v X i)
  rw [Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (slabWidth_pos_of_regeneration v _ (hX.2 k))

lemma slabHeightSum_nonneg {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (k : ℕ) : 0 ≤ slabHeightSum v X k :=
  Finset.sum_nonneg (fun i _ => (slabWidth_pos_of_regeneration v _ (hX.2 i)).le)

lemma slabRadiusSum_mono {d : ℕ} (v : Fin d → ℝ) (X : Path d) :
    Monotone (slabRadiusSum v X) := by
  intro m n hmn
  exact nonneg_sum_range_mono (fun i => slabRadius (slabs v X i)) (fun _ => slabRadius_nonneg _) hmn

lemma goodSlabPath_height_nonneg {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (t : ℕ) : 0 ≤ height v (X t) := by
  obtain ⟨k,hkt,htk⟩ := slab_location v X hX t
  have hj : t-slabTime v X k < (slabs v X k).1 := by rw [slabTime_succ] at htk; omega
  have hh := (height_in_slab v X hX k (t-slabTime v X k) hj).1
  rw [Nat.add_sub_of_le hkt] at hh
  exact (slabHeightSum_nonneg v X hX k).trans hh

lemma height_before_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) {k t : ℕ} (ht : t ≤ slabTime v X k) :
    height v (X t) ≤ slabHeightSum v X k := by
  rcases ht.eq_or_lt with ht | ht
  · rw [ht,height_at_slabTime v X hX.1]
  · obtain ⟨j,hjt,htj⟩ := slab_location v X hX t
    have hjk : j < k := (slabTime_strictMono v X hX).lt_iff_lt.mp (hjt.trans_lt ht)
    have hj : t-slabTime v X j < (slabs v X j).1 := by rw [slabTime_succ] at htj; omega
    have hh := (height_in_slab v X hX j (t-slabTime v X j) hj).2
    rw [Nat.add_sub_of_le hjt] at hh
    exact hh.le.trans ((slabHeightSum_strictMono v X hX).monotone (by omega))

lemma height_after_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) {k t : ℕ} (ht : slabTime v X k ≤ t) :
    slabHeightSum v X k ≤ height v (X t) := by
  obtain ⟨j,hjt,htj⟩ := slab_location v X hX t
  have hkj : k ≤ j := by
    have := (slabTime_strictMono v X hX).lt_iff_lt.mp (ht.trans_lt htj)
    omega
  have hj : t-slabTime v X j < (slabs v X j).1 := by rw [slabTime_succ] at htj; omega
  have hh := (height_in_slab v X hX j (t-slabTime v X j) hj).1
  rw [Nat.add_sub_of_le hjt] at hh
  exact ((slabHeightSum_strictMono v X hX).monotone hkj).trans hh

lemma norm_before_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) {k t : ℕ} (ht : t ≤ slabTime v X k) :
    ‖euclideanSite (X t)‖ ≤ slabRadiusSum v X k := by
  rcases ht.eq_or_lt with ht | ht
  · rw [ht]
    exact norm_at_slabTime_le v X hX k
  · obtain ⟨j,hjt,htj⟩ := slab_location v X hX t
    have hjk : j < k := (slabTime_strictMono v X hX).lt_iff_lt.mp (hjt.trans_lt ht)
    have hj : t-slabTime v X j ≤ (slabs v X j).1 := by rw [slabTime_succ] at htj; omega
    have hh := norm_in_slab_le v X hX j (t-slabTime v X j) hj
    rw [Nat.add_sub_of_le hjt] at hh
    exact hh.trans (slabRadiusSum_mono v X (by omega))

def stepDirection {d : ℕ} (e : Step d) : Fin d → ℝ := fun i => (stepVector e i : ℝ)

lemma height_stepDirection {d : ℕ} (e : Step d) (x : Site d) :
    height (stepDirection e) x = if e.2 then (x e.1 : ℝ) else -(x e.1 : ℝ) := by
  simp only [height,stepDirection,stepVector]
  simp only [Int.cast_ite,Int.cast_zero,Int.cast_one,Int.cast_neg,mul_ite,mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ e.1,ite_eq_left (Finset.mem_univ _)]
  cases e.2 <;> simp

lemma height_stepDirection_le_norm {d : ℕ} (e : Step d) (x : Site d) :
    |height (stepDirection e) x| ≤ ‖euclideanSite x‖ := by
  have hh := PiLp.norm_apply_le (euclideanSite x) e.1
  rw [height_stepDirection]
  cases e.2 <;> simpa [euclideanSite] using hh

lemma exists_large_signedCoordinate {d : ℕ} (x : Site d) {A : ℝ} (hA : 0 ≤ A)
    (hx : Real.sqrt d*A < ‖euclideanSite x‖) :
    ∃ e : Step d, A < height (stepDirection e) x := by
  by_contra h
  push Not at h
  have hb (i : Fin d) : |(x i : ℝ)| ≤ A := by
    have hp := h (i,true)
    have hm := h (i,false)
    rw [height_stepDirection] at hp hm
    simp only [Bool.false_eq_true,ite_false,ite_true] at hp hm
    exact abs_le.mpr ⟨by linarith, hp⟩
  have hs : ∑ i : Fin d, (x i : ℝ)^2 ≤ (d : ℝ)*A^2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => sq_le_sq₀ (abs_nonneg (x i : ℝ)) hA |>.mpr (hb i))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have he := EuclideanSpace.real_norm_sq_eq (euclideanSite x)
  simp only [euclideanSite,WithLp.ofLp_toLp] at he
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hprod : (Real.sqrt (d : ℝ)*A)^2 = (d : ℝ)*A^2 := by rw [mul_pow,hd]
  have hp : 0 ≤ Real.sqrt (d : ℝ)*A := mul_nonneg (Real.sqrt_nonneg _) hA
  change ‖euclideanSite x‖^2 = ∑ i : Fin d, (x i : ℝ)^2 at he
  have hx2 := (sq_lt_sq₀ hp (norm_nonneg (euclideanSite x))).mpr hx
  rw [hprod,he] at hx2
  exact (not_lt_of_ge hs) hx2

def tiltDirection {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t : ℝ) : Fin d → ℝ :=
  fun i => stepDirection e i - t*v i

lemma height_tiltDirection {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t : ℝ) (x : Site d) :
    height (tiltDirection v e t) x = height (stepDirection e) x - t*height v x := by
  simp only [height,tiltDirection,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma largeRadius_point {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (a B : ℝ) (ha : 0 ≤ a) {k : ℕ} (hr : B*a*(k+1) < slabRadius (slabs v X k))
    (hp : slabRadiusSum v X k ≤ a*k) :
    ∃ j : ℕ, j ≤ (slabs v X k).1 ∧ (B-1)*a*(k+1) <
      ‖euclideanSite (X (slabTime v X k+j))‖ := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.range ((slabs v X k).1+1)).Nonempty from ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩)
    (fun j => ‖euclideanSite (wordPath (slabs v X k) j - wordPath (slabs v X k) 0)‖)
  have hj' : j ≤ (slabs v X k).1 := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  change slabRadius (slabs v X k) = _ at he
  have hh := iterated_cutSuffix v X hX.1 k j
  rw [← slab_word_path v X k hj'] at hh
  have he' : ‖euclideanSite (wordPath (slabs v X k) j - wordPath (slabs v X k) 0)‖ ≤
      ‖euclideanSite (X (slabTime v X k+j))‖ + ‖euclideanSite (X (slabTime v X k))‖ := by
    rw [(hX.2 k).2.1,sub_zero,hh,euclideanSite_sub]
    exact norm_sub_le _ _
  have hb := (norm_at_slabTime_le v X hX k).trans hp
  refine ⟨j,hj',?_⟩
  rw [he] at hr
  nlinarith

def radiusLaunch {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t L U : ℝ)
    (X : Path d) (n : ℕ) : Prop :=
  strictRecord (tiltDirection v e t) X n ∧
  (∀ j ≤ n, 0 ≤ height v (X j)) ∧
  (∃ j ≤ n, L ≤ height v (X j)) ∧
  (∀ j ≤ n, height v (X j) ≤ U)

lemma measurableSet_radiusLaunch {d : ℕ} (v : Fin d → ℝ) (e : Step d)
    (t L U : ℝ) (n : ℕ) : MeasurableSet {X : Path d | radiusLaunch v e t L U X n} := by
  unfold radiusLaunch
  simp only [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  apply (measurableSet_strictRecord _ _).inter
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const ((measurable_of_countable (height v)).comp (measurable_pi_apply j))
  apply MeasurableSet.inter
  · exact MeasurableSet.iUnion fun j => MeasurableSet.inter (MeasurableSet.const _) <|
      measurableSet_le measurable_const ((measurable_of_countable (height v)).comp (measurable_pi_apply j))
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le ((measurable_of_countable (height v)).comp (measurable_pi_apply j)) measurable_const

lemma radiusLaunch_prefix {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t L U : ℝ)
    {X Y : Path d} {n : ℕ} (hX : radiusLaunch v e t L U X n)
    (hY : Y ∈ pathCylinder n X) : radiusLaunch v e t L U Y n := by
  rcases hX with ⟨hr,hp,⟨j,hj,hL⟩,hu⟩
  exact ⟨strictRecord_prefix _ hr hY, fun i hi => (hY i hi).symm ▸ hp i hi,
    ⟨j,hj,(hY j hj).symm ▸ hL⟩,fun i hi => (hY i hi).symm ▸ hu i hi⟩

lemma first_crossing_strictRecord {d : ℕ} (w : Fin d → ℝ) (X : Path d)
    (A : ℝ) {m t : ℕ} (hm : ∀ j ≤ m, height w (X j) ≤ A)
    (ht : A < height w (X t)) :
    ∃ n, m < n ∧ n ≤ t ∧ strictRecord w X n := by
  let n := Nat.find (show ∃ j, A < height w (X j) from ⟨t,ht⟩)
  have hn : A < height w (X n) := Nat.find_spec (show ∃ j, A < height w (X j) from ⟨t,ht⟩)
  have hmn : m < n := by
    by_contra h
    exact (not_lt_of_ge (hm n (by omega))) hn
  refine ⟨n,hmn,Nat.find_min' _ ht,?_,?_⟩
  · omega
  · intro j hj
    exact (le_of_not_gt (Nat.find_min (show ∃ j, A < height w (X j) from ⟨t,ht⟩) hj)).trans_lt hn

lemma largeRadius_launch {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (a B β K L U : ℝ) (ha : 0 < a) (hβ : 0 ≤ β)
    (hK : 0 ≤ K) (hB : Real.sqrt d*(2+β*K) < B-1) {k : ℕ}
    (hr : B*a*(k+1) < slabRadius (slabs v X k))
    (hp : slabRadiusSum v X k ≤ a*k)
    (hH : slabHeightSum v X (k+1) ≤ K*(k+1))
    (hL : L ≤ slabHeightSum v X k) (hU : K*(k+1) ≤ U) :
    ∃ e : Step d, ∃ n, radiusLaunch v e (β*a) L U X n := by
  obtain ⟨j,hj,hbig⟩ := largeRadius_point v X hX a B ha.le hr hp
  let t := slabTime v X k+j
  have ht : t ≤ slabTime v X (k+1) := by rw [slabTime_succ]; omega
  have hk : (0 : ℝ) < k+1 := by positivity
  have hb : Real.sqrt d*((2+β*K)*a*(k+1)) < ‖euclideanSite (X t)‖ := by
    have h := mul_lt_mul_of_pos_right hB (mul_pos ha hk)
    calc
      _ = (Real.sqrt d*(2+β*K))*(a*(k+1)) := by ring
      _ < (B-1)*(a*(k+1)) := h
      _ < _ := by simpa only [mul_assoc] using hbig
  obtain ⟨e,he⟩ := exists_large_signedCoordinate (X t) (by positivity) hb
  have hy : a*k < height (tiltDirection v e (β*a)) (X t) := by
    rw [height_tiltDirection]
    have hheight := (height_before_slabTime_le v X hX ht).trans hH
    have hmul := mul_le_mul_of_nonneg_left hheight (mul_nonneg hβ ha.le)
    have hak : a*(k:ℝ) < 2*a*(k+1) := by nlinarith
    nlinarith
  have hold (l : ℕ) (hl : l ≤ slabTime v X k) :
      height (tiltDirection v e (β*a)) (X l) ≤ a*k := by
    rw [height_tiltDirection]
    have hc := (le_abs_self (height (stepDirection e) (X l))).trans
      ((height_stepDirection_le_norm e _).trans ((norm_before_slabTime_le v X hX hl).trans hp))
    have hm := mul_nonneg (mul_nonneg hβ ha.le) (goodSlabPath_height_nonneg v X hX l)
    linarith
  obtain ⟨n,hn,hnt,hrec⟩ := first_crossing_strictRecord _ X (a*k) hold hy
  refine ⟨e,n,hrec,fun i _ => goodSlabPath_height_nonneg v X hX i,?_,?_⟩
  · exact ⟨slabTime v X k,hn.le,by rw [height_at_slabTime v X hX.1]; exact hL⟩
  · intro i hi
    exact (height_before_slabTime_le v X hX (hi.trans (hnt.trans ht))).trans (hH.trans hU)

lemma height_signed_step_abs_le_one {d : ℕ} (u e : Step d) :
    |height (stepDirection u) (stepVector e)| ≤ 1 := by
  rw [height_stepDirection]
  cases u.2 <;> simp [stepVector] <;> split_ifs <;> norm_num

lemma tilt_down_step_lower {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (t : ℝ) (he : height v (stepVector e) = -1) :
    t-1 ≤ height (tiltDirection v u t) (stepVector e) := by
  rw [height_tiltDirection,he]
  have hh := (abs_le.mp (height_signed_step_abs_le_one u e)).1
  linarith

lemma radius_script_fresh {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (t : ℝ) (ht : 1 < t) (he : height v (stepVector e) = -1)
    (γ : Path d) {n : ℕ} (hr : strictRecord (tiltDirection v u t) γ n) :
    ∀ i < n, ∀ j : ℕ, γ i ≠ axialRay (γ n) e j := by
  intro i hi j hj
  have h := hr.2 i hi
  rw [hj,height_axialRay] at h
  have hs := tilt_down_step_lower v u e t he
  have hp : 0 ≤ (j : ℝ)*height (tiltDirection v u t) (stepVector e) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

lemma opposite_template_height {d : ℕ} (v : Fin d → ℝ) (Z : Path d)
    (hZ : GoodSlabPath (-v) Z) (t : ℕ) : height v (Z t) ≤ 0 := by
  have hh := goodSlabPath_height_nonneg (-v) Z hZ t
  rw [height_neg_direction] at hh
  linarith

lemma radius_template_before {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (a β c C b : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (x : Site d) (Z : Path d)
    (hZ : GoodSlabPath (-v) Z) (hgood : Z ∈ goodRadiusPrefix (-v) a c C b q)
    {t : ℕ} (ht : t < slabTime (-v) Z q) :
    height (tiltDirection v u (β*a)) x <
      height (tiltDirection v u (β*a)) (Z t + axialRay x e M) := by
  obtain ⟨k,hkt,htk⟩ := slab_location (-v) Z hZ t
  have hkq : k < q := (slabTime_strictMono (-v) Z hZ).lt_iff_lt.mp (hkt.trans_lt ht)
  have hnorm := norm_before_slabTime_le (-v) Z hZ htk.le
  have hgood' := (goodRadiusPrefix_iff (-v) a c C b q Z).mp hgood
  have hnorm' := hnorm.trans (hgood' (k+1) (by omega)).2.2
  have hlow := (hgood' k hkq.le).1.trans (height_after_slabTime_le (-v) Z hZ hkt)
  rw [height_neg_direction] at hlow
  have hu := (abs_le.mp (height_stepDirection_le_norm u (Z t))).1
  have hdown := tilt_down_step_lower v u e (β*a) he
  rw [height_add,height_axialRay,height_tiltDirection v u (β*a) (Z t)]
  simp only [Nat.cast_add,Nat.cast_one] at hnorm'
  have hmm := mul_le_mul_of_nonneg_left hdown (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hhh := mul_le_mul_of_nonneg_left hlow (mul_nonneg hβ ha)
  have hkk := mul_nonneg (show (0:ℝ) ≤ k by positivity) (sub_nonneg.mpr hbc)
  have hkk' := mul_nonneg ha hkk
  nlinarith

lemma radius_template_avoids {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (a β c C b U : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (hq : U-M-c*q+b < 0)
    (γ : Path d) {n : ℕ} (hr : strictRecord (tiltDirection v u (β*a)) γ n)
    (hnonneg : ∀ i ≤ n, 0 ≤ height v (γ i)) (hU : height v (γ n) ≤ U)
    (Z : Path d) (hZ : GoodSlabPath (-v) Z)
    (hgood : Z ∈ goodRadiusPrefix (-v) a c C b q) :
    ∀ i < n+M, ∀ t, Z t + axialRay (γ n) e M ≠
      concatPath n γ (axialRay (γ n) e) i := by
  intro i hi t heq
  by_cases hin : i < n
  · rw [concatPath_before n γ (axialRay (γ n) e) (axialRay_zero _ _).symm hin.le] at heq
    by_cases ht : t < slabTime (-v) Z q
    · have hh := radius_template_before v u e a β c C b ha hβ hbc he M q hM (γ n) Z hZ hgood ht
      rw [heq] at hh
      exact (not_lt_of_ge (hr.2 i hin).le) hh
    · have hh := height_after_slabTime_le (-v) Z hZ (le_of_not_gt ht)
      have hl := ((goodRadiusPrefix_iff (-v) a c C b q Z).mp hgood q le_rfl).1.trans hh
      rw [height_neg_direction] at hl
      have hheight := congrArg (height v) heq
      rw [height_add,height_axialRay,he] at hheight
      have hn := hnonneg i hin.le
      nlinarith
  · have hscript : concatPath n γ (axialRay (γ n) e) i = axialRay (γ n) e (i-n) := by
      simpa only [Nat.add_sub_of_le (le_of_not_gt hin)] using
        concatPath_after n γ (axialRay (γ n) e) (i-n)
    rw [hscript] at heq
    have hh := congrArg (height v) heq
    rw [height_add,height_axialRay,height_axialRay,he] at hh
    have hn := opposite_template_height v Z hZ t
    have hj : ((i-n : ℕ) : ℝ) < M := by exact_mod_cast (show i-n < M by omega)
    nlinarith

lemma radius_continuation_maximum {d : ℕ} (v : Fin d → ℝ) (e : Step d)
    (he : height v (stepVector e) = -1) (γ Y Z : Path d) (n M : ℕ)
    (hprefix : Y ∈ pathCylinder (n+M) (concatPath n γ (axialRay (γ n) e)))
    (htail : tailPath (n+M) Y = shiftPath (axialRay (γ n) e M) Z)
    (hZ : GoodSlabPath (-v) Z) (U : ℝ) (hU : ∀ i ≤ n, height v (γ i) ≤ U) :
    Y ∈ alwaysBelow v U := by
  intro t
  by_cases ht : t < n
  · rw [hprefix t (by omega),concatPath_before n γ (axialRay (γ n) e)
      (axialRay_zero _ _).symm ht.le]
    exact hU t ht.le
  · by_cases htM : t < n+M
    · rw [hprefix t htM.le]
      have hscript : concatPath n γ (axialRay (γ n) e) t = axialRay (γ n) e (t-n) := by
        simpa only [Nat.add_sub_of_le (le_of_not_gt ht)] using
          concatPath_after n γ (axialRay (γ n) e) (t-n)
      rw [hscript,height_axialRay,he]
      have hn := hU n le_rfl
      have hj : (0:ℝ) ≤ (t-n:ℕ) := by positivity
      linarith
    · have hh := congr_fun htail (t-(n+M))
      change Y ((n+M)+(t-(n+M))) = Z (t-(n+M))+axialRay (γ n) e M at hh
      rw [Nat.add_sub_of_le (le_of_not_gt htM)] at hh
      rw [hh,height_add,height_axialRay,he]
      have hz := opposite_template_height v Z hZ (t-(n+M))
      have hn := hU n le_rfl
      have hm : (0:ℝ) ≤ M := by positivity
      linarith

lemma measure_prefix_lower {d : ℕ} (P : Measure (Path d)) (n : ℕ)
    {Q E : Set (Path d)} (hQ : MeasurableSet Q) (hE : MeasurableSet E)
    (hpre : ∀ X ∈ Q, pathCylinder n X ⊆ Q) (q : ℝ≥0∞)
    (hbound : ∀ X ∈ Q, q*P (pathCylinder n X) ≤ P (pathCylinder n X ∩ E)) :
    q*P Q ≤ P (Q ∩ E) := by
  rw [measure_eq_tsum_fibres P (frestrictLe n) (measurable_frestrictLe n) hQ,
    measure_eq_tsum_fibres P (frestrictLe n) (measurable_frestrictLe n) (hQ.inter hE),
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  let γ := extendPrefix n a
  have hcyl : {X : Path d | frestrictLe n X = a} = pathCylinder n γ := by
    rw [pathCylinder_eq_fiber,restrict_extendPrefix]
    rfl
  rw [hcyl,← Set.inter_assoc]
  by_cases hg : γ ∈ Q
  · rw [Set.inter_eq_left.mpr (hpre γ hg)]
    exact hbound γ hg
  · have hempty : pathCylinder n γ ∩ Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX,hXQ⟩
      exact hg (hpre X hXQ (fun i hi => (hX i hi).symm))
    rw [hempty,measure_empty,Set.empty_inter,measure_empty,mul_zero]

lemma measure_first_prefix_lower {d : ℕ} (P : Measure (Path d))
    (F : Path d → ℕ → Prop) (hF : ∀ n, MeasurableSet {X | F X n})
    (hpre : ∀ X n, F X n → ∀ Y ∈ pathCylinder n X, F Y n)
    {E : Set (Path d)} (hE : MeasurableSet E) (q : ℝ≥0∞)
    (hbound : ∀ X n, F X n → q*P (pathCylinder n X) ≤ P (pathCylinder n X ∩ E)) :
    q*P {X | ∃ n, F X n} ≤ P E := by
  let Q (n : ℕ) : Set (Path d) := {X | F X n ∧ ∀ j < n, ¬F X j}
  have hQ (n : ℕ) : MeasurableSet (Q n) := by
    simp only [Q,Set.ofPred_and,Set.ofPred_forall]
    exact (hF n).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hF j).compl)
  have hQpre (n : ℕ) (X : Path d) (hX : X ∈ Q n) : pathCylinder n X ⊆ Q n := by
    intro Y hY
    refine ⟨hpre X n hX.1 Y hY,fun j hj hfj => hX.2 j hj ?_⟩
    exact hpre Y j hfj X (fun i hi => (hY i (hi.trans hj.le)).symm)
  have hQD : Pairwise (fun m n => Disjoint (Q m) (Q n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro X hm hn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hn.2 m h hm.1
    · exact hm.2 n h hn.1
  have heq : {X | ∃ n, F X n} = ⋃ n, Q n := by
    ext X
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨Nat.find h,Nat.find_spec h,fun j hj => Nat.find_min h hj⟩
    · rintro ⟨n,h⟩;exact ⟨n,h.1⟩
  rw [heq,measure_iUnion hQD hQ,← ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' n, P (Q n ∩ E) := ENNReal.tsum_le_tsum fun n =>
      measure_prefix_lower P n (hQ n) hE (hQpre n) q (fun X hX => hbound X n hX.1)
    _ = P (⋃ n, Q n ∩ E) := (measure_iUnion
      (fun m n hmn => (hQD hmn).mono Set.inter_subset_left Set.inter_subset_left)
      (fun n => (hQ n).inter hE)).symm
    _ ≤ P E := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

end DirectionalZeroOne

end OAI
