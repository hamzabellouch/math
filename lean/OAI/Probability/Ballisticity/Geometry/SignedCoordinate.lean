import Mathlib
import OAI.Probability.Ballisticity.Estimates.WordTemplate

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma conditioned_rare_word_template_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (c C C0 a B η : ℝ) (hB : 0 < B) (hη : 0 < η) (hηsmall : η ≤ 1/10)
    (m N : ℕ) (hm : 1 ≤ m)
    (hg : (4/5 : ℝ) ≤ (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a N))
    (hlow : η/(2*B) ≤ ∑ i ∈ Finset.Ico m (N+1),
      (conditionedLaw ν ℓ).real {X | B*a*i < wordRadius (firstWord ℓ X) ∧
        wordHeightGain ℓ (firstWord ℓ X) ≤ i})
    (hupper : (∑ i ∈ Finset.Ico m (N+1),
      (conditionedLaw ν ℓ).real {X | B*a*i < wordRadius (firstWord ℓ X) ∧
        wordHeightGain ℓ (firstWord ℓ X) ≤ i}) ≤ 2*η) :
    η/(4*B) ≤ (conditionedLaw ν ℓ).real {X | ∃ i ∈ Finset.Ico m (N+1),
      B*a*i < wordRadius (regenerationWords ℓ X (i-1)) ∧
      wordHeightGain ℓ (regenerationWords ℓ X (i-1)) ≤ i ∧
      X ∈ WordTemplate ℓ c C C0 a (i-1)} := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let S := Finset.Ico m (N+1)
  let A : ℕ → Set (List (Direction d)) := fun i =>
    {w | B*a*i < wordRadius w ∧ wordHeightGain ℓ w ≤ i}
  have he (i : ℕ) : μ.real {X | regenerationWords ℓ X (i-1) ∈ A i} =
      μ.real {X | firstWord ℓ X ∈ A i} := by
    exact congrArg ENNReal.toReal ((regenerationWords_identDistrib ν ℓ htrans (i-1)).measure_mem_eq
      (Set.to_countable (A i)).measurableSet)
  have hb := independent_rare_words_lower_bound μ S
    (fun i => {X | regenerationWords ℓ X (i-1) ∈ A i}) (fun i => WordTemplate ℓ c C C0 a (i-1))
    (fun i => (Set.to_countable (A i)).measurableSet.preimage (measurable_regenerationWord ℓ (i-1)))
    (fun i => measurableSet_wordTemplate ℓ c C C0 a (i-1)) (4/5)
    (by
      intro i hi
      have hiN : i-1 ≤ N := by have := Finset.mem_Ico.mp hi; omega
      have hgp := hg.trans (measureReal_mono (μ := μ) (wordTemplate_antitone ℓ c C C0 a hiN))
      rw [current_word_template_independent ν ℓ htrans c C C0 a (i-1) (A i), mul_comm]
      exact mul_le_mul_of_nonneg_left hgp measureReal_nonneg)
    (by
      intro i hi j hj hij
      have hh := ((regenerationWords_independent ν ℓ htrans).indepFun
        (show i-1 ≠ j-1 by have := Finset.mem_Ico.mp hi; have := Finset.mem_Ico.mp hj; omega)).measure_inter_preimage_eq_mul
        (A i) (A j) (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
      exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul)
  simp_rw [he] at hb
  apply polynomial_lower_from_small_intensity hB hη hηsmall hlow hupper
  simpa only [A, S, μ, Set.mem_ofPred_eq, and_assoc] using hb

lemma large_regeneration_word_excursion {d : ℕ} (ℓ : Vector d) (X : Path d)
    (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (c C C0 a B : ℝ) (ha : 0 ≤ a) (i : ℕ) (hi : 1 ≤ i)
    (hlarge : B*a*i < wordRadius (regenerationWords ℓ X (i-1)))
    (hL : wordHeightGain ℓ (regenerationWords ℓ X (i-1)) ≤ i)
    (hT : X ∈ WordTemplate ℓ c C C0 a (i-1))
    (hC0 : C*(i-1)+C0+i ≤ (C+2)*i) :
    ∃ n, (B-1)*a*i < ‖latticeVector (X n)‖ ∧
      ∀ j ≤ n, 0 ≤ dot (realPosition (X j)) ℓ ∧
        dot (realPosition (X j)) ℓ ≤ (C+2)*i := by
  obtain ⟨j,hj,he⟩ := wordRadius_attained (regenerationWords ℓ X (i-1))
  let n := regenerationTimes ℓ X (i-1) + j
  have hi' : i-1+1 = i := by omega
  have hcast : ((i-1 : ℕ) : ℝ) = i-1 := by rw [Nat.cast_sub hi]; norm_num
  have hsum := hT (i-1) le_rfl
  have hcut : ‖latticeVector (X (regenerationTimes ℓ X (i-1)))‖ ≤ a*(i-1) := by
    exact (regeneration_radius_sum ℓ X h0 hX (i-1)).trans (by simpa only [hcast] using hsum.2.2)
  have htriangle : wordRadius (regenerationWords ℓ X (i-1)) ≤
      ‖latticeVector (X n)‖ + ‖latticeVector (X (regenerationTimes ℓ X (i-1)))‖ := by
    have he' := regeneration_span ℓ X h0 hX (i-1) j hj
    have he'' : wordPath 0 (regenerationWords ℓ X (i-1)) j =
        X n-X (regenerationTimes ℓ X (i-1)) := by dsimp only [n]; rw [he']; abel
    rw [he, he'', latticeVector_sub]
    exact norm_sub_le _ _
  have hn : n ≤ regenerationTimes ℓ X i := by
    rw [← hi', regenerationTimes_succ]
    exact Nat.add_le_add_left hj _
  refine ⟨n, ?_, ?_⟩
  · nlinarith
  · intro k hk
    obtain ⟨hlo,hhi⟩ := regeneration_prefix_height ℓ X h0 hX (hk.trans hn)
    refine ⟨hlo,hhi.trans ?_⟩
    rw [← hi', Finset.sum_range_succ, hi']
    have hs : (∑ j ∈ Finset.range (i-1), wordHeightGain ℓ (regenerationWords ℓ X j)) ≤
        C*(i-1)+C0 := by simpa only [hcast] using hsum.2.1
    linarith

def signedCoordinate {d : ℕ} (e : Direction d) (x : Lattice d) : ℝ :=
  if e.2 then (x e.1 : ℝ) else -(x e.1 : ℝ)

lemma signedCoordinate_add {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedCoordinate e (x+y) = signedCoordinate e x + signedCoordinate e y := by
  simp only [signedCoordinate, Pi.add_apply, Int.cast_add]
  split <;> ring

lemma signedCoordinate_abs_le_norm {d : ℕ} (e : Direction d) (x : Lattice d) :
    |signedCoordinate e x| ≤ ‖latticeVector x‖ := by
  have hh := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (latticeVector x) e.1
  simpa only [signedCoordinate, apply_ite abs, abs_neg, ite_self, Real.norm_eq_abs,
    latticeVector, realPosition] using hh

lemma latticeVector_norm_le_sum_abs {d : ℕ} (x : Lattice d) :
    ‖latticeVector x‖ ≤ ∑ i, |(x i : ℝ)| := by
  have he : latticeVector x = ∑ i : Fin d, PiLp.single 2 i (x i : ℝ) := by
    ext j
    simp [latticeVector, realPosition]
  rw [he]
  simpa only [PiLp.norm_single, Real.norm_eq_abs] using
    norm_sum_le (Finset.univ : Finset (Fin d)) (fun i => PiLp.single 2 i (x i : ℝ))

lemma exists_large_signedCoordinate {d : ℕ} (x : Lattice d) (r : ℝ)
    (hlarge : (d : ℝ)*r < ‖latticeVector x‖) : ∃ e : Direction d, r < signedCoordinate e x := by
  have hex : ∃ i : Fin d, r < |(x i : ℝ)| := by
    by_contra! h
    have hh := (latticeVector_norm_le_sum_abs x).trans (Finset.sum_le_sum (fun i _ => h i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    linarith
  obtain ⟨i,hi⟩ := hex
  by_cases hx : 0 ≤ (x i : ℝ)
  · exact ⟨(i,true), by simpa [signedCoordinate, abs_of_nonneg hx] using hi⟩
  · exact ⟨(i,false), by simpa [signedCoordinate, abs_of_neg (lt_of_not_ge hx)] using hi⟩

lemma prefixMax_mono (z : ℕ → ℝ) : Monotone (prefixMax z) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

lemma prefixMax_le_iff (z : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    prefixMax z n ≤ r ↔ 0 ≤ r ∧ ∀ j < n, z j ≤ r := by
  induction n with
  | zero => simp [prefixMax]
  | succ n ih =>
    simp only [prefixMax, max_le_iff, ih]
    constructor
    · rintro ⟨⟨hr,h⟩,hn⟩
      refine ⟨hr,fun j hj => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
      · exact h j hj'
      · exact hn
    · rintro ⟨hr,h⟩
      exact ⟨⟨hr,fun j hj => h j (by omega)⟩,h n (by omega)⟩

lemma prefixMax_congr (z w : ℕ → ℝ) (n : ℕ) (h : ∀ j < n, z j = w j) :
    prefixMax z n = prefixMax w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixMax, prefixMax, ih (fun j hj => h j (by omega)), h n (by omega)]

noncomputable def runningHeight {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : ℝ :=
  prefixMax (fun j => dot (realPosition (X j)) ℓ) (n+1)

lemma runningHeight_nonneg {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    0 ≤ runningHeight ℓ X n := prefixMax_nonneg _ _

lemma height_le_runningHeight {d : ℕ} (ℓ : Vector d) (X : Path d) {j n : ℕ} (hj : j ≤ n) :
    dot (realPosition (X j)) ℓ ≤ runningHeight ℓ X n := le_prefixMax (j := j) (n := n+1) (fun k => dot (realPosition (X k)) ℓ) (by omega)

lemma runningHeight_mono {d : ℕ} (ℓ : Vector d) (X : Path d) : Monotone (runningHeight ℓ X) :=
  fun _ _ h => prefixMax_mono _ (Nat.add_le_add_right h 1)

lemma runningHeight_le {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ j ≤ n, dot (realPosition (X j)) ℓ ≤ r) : runningHeight ℓ X n ≤ r :=
  (prefixMax_le_iff _ _ _).mpr ⟨hr,fun j hj => h j (Nat.le_of_lt_succ hj)⟩

lemma runningHeight_congr {d : ℕ} (ℓ : Vector d) {X Y : Path d} (n : ℕ)
    (h : ∀ j ≤ n, X j = Y j) : runningHeight ℓ X n = runningHeight ℓ Y n := by
  apply prefixMax_congr
  intro j hj
  rw [h j (Nat.le_of_lt_succ hj)]

lemma measurable_runningHeight {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => runningHeight ℓ X n) := by
  have hh (k : ℕ) : Measurable (fun X : Path d => prefixMax
      (fun j => dot (realPosition (X j)) ℓ) k) := by
    induction k with
    | zero => exact measurable_const
    | succ k ih => exact ih.max (by unfold dot realPosition; fun_prop)
  exact hh (n+1)

noncomputable def tiltedCoordinate {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (b a : ℝ) (x : Lattice d) : ℝ := signedCoordinate u x + b*a*dot (realPosition x) ℓ

noncomputable def heightRatio {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ)
    (X : Path d) (n : ℕ) : ℝ := tiltedCoordinate ℓ u b a (X n) / (a*(1+runningHeight ℓ X n))

lemma tiltedCoordinate_add {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) (x y : Lattice d) :
    tiltedCoordinate ℓ u b a (x+y) = tiltedCoordinate ℓ u b a x + tiltedCoordinate ℓ u b a y := by
  simp only [tiltedCoordinate, signedCoordinate_add, dot_realPosition_add]
  ring

lemma tiltedCoordinate_zero {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) :
    tiltedCoordinate ℓ u b a 0 = 0 := by simp [tiltedCoordinate, signedCoordinate, dot, realPosition]

lemma measurable_heightRatio {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) (n : ℕ) :
    Measurable (fun X : Path d => heightRatio ℓ u b a X n) := by
  unfold heightRatio
  apply Measurable.div
  · exact (measurable_of_countable (tiltedCoordinate ℓ u b a)).comp (measurable_pi_apply n)
  · exact measurable_const.mul (measurable_const.add (measurable_runningHeight ℓ n))

def AdmissiblePrefix {d : ℕ} (n : ℕ) : Set (Path d) :=
  {X | X 0 = 0 ∧ ∀ j < n, ∃ e : Direction d, X (j+1) = X j+step e}

def BoundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) : Set (Path d) :=
  {X | ∀ j ≤ n, 0 ≤ dot (realPosition (X j)) ℓ ∧ dot (realPosition (X j)) ℓ ≤ H}

def RatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) : Set (Path d) :=
  AdmissiblePrefix n ∩ BoundedHeightPrefix ℓ H n ∩ {X | t < heightRatio ℓ u b a X n}

def RatioHit {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) : Set (Path d) :=
  ⋃ n, RatioExceed ℓ u b a H t n

def FirstRatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) : Set (Path d) :=
  RatioExceed ℓ u b a H t n ∩ {X | ∀ j < n, heightRatio ℓ u b a X j ≤ t}

lemma measurableSet_admissiblePrefix {d : ℕ} (n : ℕ) : MeasurableSet (AdmissiblePrefix (d := d) n) := by
  simp only [AdmissiblePrefix, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  refine (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter ?_
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun e => by
    exact measurableSet_eq_fun (measurable_pi_apply (j+1)) ((show Measurable (fun X : Path d => X j) from measurable_pi_apply j).add_const (step e))

lemma measurableSet_boundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) :
    MeasurableSet (BoundedHeightPrefix ℓ H n) := by
  simp only [BoundedHeightPrefix, Set.ofPred_forall, Set.ofPred_and]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  have hh : Measurable (fun X : Path d => dot (realPosition (X j)) ℓ) := by unfold dot realPosition; fun_prop
  exact (measurableSet_le measurable_const hh).inter (measurableSet_le hh measurable_const)

lemma measurableSet_ratioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) :
    MeasurableSet (RatioExceed ℓ u b a H t n) :=
  ((measurableSet_admissiblePrefix n).inter (measurableSet_boundedHeightPrefix ℓ H n)).inter
    (measurableSet_lt measurable_const (measurable_heightRatio ℓ u b a n))

lemma measurableSet_ratioHit {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) :
    MeasurableSet (RatioHit ℓ u b a H t) :=
  MeasurableSet.iUnion fun n => measurableSet_ratioExceed ℓ u b a H t n

lemma measurableSet_firstRatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) :
    MeasurableSet (FirstRatioExceed ℓ u b a H t n) := by
  apply (measurableSet_ratioExceed ℓ u b a H t n).inter
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_heightRatio ℓ u b a j) measurable_const

lemma admissiblePrefix_mono {d : ℕ} {m n : ℕ} (hmn : m ≤ n) :
    AdmissiblePrefix (d := d) n ⊆ AdmissiblePrefix m :=
  fun _ h => ⟨h.1,fun j hj => h.2 j (hj.trans_le hmn)⟩

lemma boundedHeightPrefix_mono {d : ℕ} (ℓ : Vector d) (H : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    BoundedHeightPrefix ℓ H n ⊆ BoundedHeightPrefix ℓ H m :=
  fun _ h j hj => h j (hj.trans hmn)

lemma ratioHit_eq_first {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) :
    RatioHit ℓ u b a H t = ⋃ n, FirstRatioExceed ℓ u b a H t n := by
  ext X
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    have hex : ∃ n, t < heightRatio ℓ u b a X n := ⟨n,hn.2⟩
    let k := Nat.find hex
    have hk : k ≤ n := Nat.find_min' hex hn.2
    refine Set.mem_iUnion.mpr ⟨k,⟨⟨admissiblePrefix_mono hk hn.1.1,
      boundedHeightPrefix_mono ℓ H hk hn.1.2⟩,Nat.find_spec hex⟩,?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    exact Set.mem_iUnion.mpr ⟨n,hn.1⟩

lemma firstRatioExceed_disjoint {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) :
    Pairwise (fun n m => Disjoint (FirstRatioExceed ℓ u b a H t n) (FirstRatioExceed ℓ u b a H t m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  rintro X ⟨hn,hprevn⟩ ⟨hm,hprevm⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · exact (not_le_of_gt hn.2) (hprevm n h)
  · exact (not_le_of_gt hm.2) (hprevn m h)

lemma ratioHit_antitone {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H : ℝ) {s t : ℝ} (hst : s ≤ t) :
    RatioHit ℓ u b a H t ⊆ RatioHit ℓ u b a H s := by
  intro X hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  exact Set.mem_iUnion.mpr ⟨n,hn.1,hst.trans_lt hn.2⟩

lemma firstRatioExceed_record {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ)
    (ha : 0 < a) (ht : 0 < t) (X : Path d) (n : ℕ)
    (hX : X ∈ FirstRatioExceed ℓ u b a H t n) :
    0 < n ∧ ∀ j < n, tiltedCoordinate ℓ u b a (X j) < tiltedCoordinate ℓ u b a (X n) := by
  have hd (j : ℕ) : 0 < a*(1+runningHeight ℓ X j) := mul_pos ha (by linarith [runningHeight_nonneg ℓ X j])
  have hn0 : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    have hz : heightRatio ℓ u b a X n = 0 := by
      simp only [heightRatio, hn, hX.1.1.1.1, tiltedCoordinate_zero, zero_div]
    have hh : t < heightRatio ℓ u b a X n := hX.1.2
    rw [hz] at hh
    linarith
  refine ⟨hn0,fun j hj => ?_⟩
  have hlo := (div_le_iff₀ (hd j)).mp (hX.2 j hj)
  have hhi := (lt_div_iff₀ (hd n)).mp hX.1.2
  have hM := runningHeight_mono ℓ X hj.le
  have hm := mul_le_mul_of_nonneg_left hM (mul_nonneg ht.le ha.le)
  nlinarith

lemma prefixDetermined_admissiblePrefix {d : ℕ} (n : ℕ) :
    PrefixDetermined n (AdmissiblePrefix (d := d) n) := by
  intro X Y hXY
  simp only [AdmissiblePrefix, Set.mem_ofPred_eq]
  rw [hXY 0 (by omega)]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [hXY j (by omega), hXY (j+1) (by omega)]

lemma prefixDetermined_boundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) :
    PrefixDetermined n (BoundedHeightPrefix ℓ H n) := by
  intro X Y hXY
  simp only [BoundedHeightPrefix, Set.mem_ofPred_eq]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj]

lemma heightRatio_congr {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) {X Y : Path d}
    (n : ℕ) (hXY : ∀ j ≤ n, X j = Y j) : heightRatio ℓ u b a X n = heightRatio ℓ u b a Y n := by
  rw [heightRatio, heightRatio, hXY n le_rfl, runningHeight_congr ℓ n hXY]

lemma prefixDetermined_firstRatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (b a H t : ℝ) (n : ℕ) : PrefixDetermined n (FirstRatioExceed ℓ u b a H t n) := by
  apply prefixDetermined_inter
  · apply prefixDetermined_inter
    · exact prefixDetermined_inter (prefixDetermined_admissiblePrefix n)
        (prefixDetermined_boundedHeightPrefix ℓ H n)
    · intro X Y hXY
      simp only [Set.mem_ofPred_eq, heightRatio_congr ℓ u b a n hXY]
  · intro X Y hXY
    simp only [Set.mem_ofPred_eq]
    exact forall_congr' fun j => forall_congr' fun hj => by
      rw [heightRatio_congr ℓ u b a j (fun k hk => hXY k (by omega))]

lemma firstRatioExceed_overshoot {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (b a H t : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (ht : 0 < t)
    (X : Path d) (n : ℕ) (hX : X ∈ FirstRatioExceed ℓ u b a H t n) :
    heightRatio ℓ u b a X n ≤ t+b+1 := by
  have ha0 : 0 < a := by linarith
  have hn := (firstRatioExceed_record ℓ u b a H t ha0 ht X n hX).1
  obtain ⟨e,he⟩ := hX.1.1.1.2 (n-1) (by omega)
  have hn' : n-1+1 = n := by omega
  rw [hn'] at he
  have hs : signedCoordinate u (step e) ≤ 1 :=
    (le_abs_self _).trans ((signedCoordinate_abs_le_norm _ _).trans_eq (latticeVector_step_norm _))
  have hl : dot (realPosition (step e)) ℓ ≤ 1 := by
    rw [dot_step]
    split
    · exact (le_abs_self _).trans (hℓ _)
    · exact (neg_le_abs _).trans (hℓ _)
  have hstep : tiltedCoordinate ℓ u b a (step e) ≤ 1+b*a := by
    have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hb ha0.le)
    dsimp only [tiltedCoordinate]
    linarith
  have hd (j : ℕ) : 0 < a*(1+runningHeight ℓ X j) :=
    mul_pos ha0 (by linarith [runningHeight_nonneg ℓ X j])
  have hprev := (div_le_iff₀ (hd (n-1))).mp (hX.2 (n-1) (by omega))
  have hm := mul_le_mul_of_nonneg_left (runningHeight_mono ℓ X (Nat.sub_le n 1))
    (mul_nonneg ht.le ha0.le)
  have hend : tiltedCoordinate ℓ u b a (X n) ≤
      t*(a*(1+runningHeight ℓ X n)) + 1+b*a := by
    rw [he, tiltedCoordinate_add]
    nlinarith
  apply (div_le_iff₀ (hd n)).mpr
  have hm0 := runningHeight_nonneg ℓ X n
  have hba := mul_nonneg hb ha0.le
  have hprod := mul_nonneg (show 0 ≤ b*a+a by positivity) hm0
  nlinarith

lemma annealed_prefix_avoiding_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (f : Path d) (n : ℕ) (hn : 0 < n)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (hfresh : ∀ j < n, f j ≠ f n)
    (havoid : ∀ X ∈ A, ∀ k, ∀ j < n, f n + X k ≠ f j) :
    annealedLaw ν ((fun X : Path d => fun k => X (n+k)-f n) ⁻¹' A ∩ pathCylinder f n) =
      annealedLaw ν (pathCylinder f n) * annealedLaw ν A := by
  by_cases hf : f 0 = 0
  · let S : Set (Lattice d) := {y | ∃ j < n, y = f j}
    let T : Set (Lattice d) := Sᶜ
    let B : Set (Path d) := (fun X : Path d => fun k => X k-f n) ⁻¹' A
    have hB : MeasurableSet B := hA.preimage (by fun_prop)
    have hBT : B ⊆ Stay T := by
      intro X hX k
      rintro ⟨j,hj,hjk⟩
      have hh := havoid (fun k => X k-f n) hX k j hj
      have he : f n + (X k-f n) = X k := by abel
      rw [he, hjk] at hh
      exact hh rfl
    have hnT : f n ∈ T := by
      rintro ⟨j,hj,hjn⟩
      exact hfresh j hj hjn.symm
    have hS0 : (0 : Lattice d) ∈ S := ⟨0,hn,hf.symm⟩
    have hm : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => quenchedKernel (ω,0) (pathCylinder f n)) := by
      apply measurable_of_row_locality _
        ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
          (measurable_id.prodMk measurable_const)) S 0 hS0
      intro ω η hωη
      exact pathCylinder_weight_locality S ω η hωη 0 f n (fun j hj => ⟨j,hj,rfl⟩)
    rw [annealed_apply ν ((hA.preimage (by fun_prop)).inter (measurableSet_pathCylinder f n))]
    have hh (ω : Environment d) : quenchedKernel (ω,0)
        ((fun X : Path d => fun k => X (n+k)-f n) ⁻¹' A ∩ pathCylinder f n) =
        quenchedKernel (ω,0) (pathCylinder f n) * quenchedKernel (ω,f n) B :=
      quenched_prefix_future ω 0 f hf n hB
    simp_rw [hh]
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν disjoint_compl_right) hm
      (measurable_quenched_stay_event_rows T (f n) hnT B hB hBT),
      annealed_event_translation ν (f n) A hA,
      ← annealed_apply ν (measurableSet_pathCylinder f n)]
  · have hz : annealedLaw ν (pathCylinder f n) = 0 := by
      rw [annealed_apply ν (measurableSet_pathCylinder f n)]
      simp_rw [quenched_pathCylinder_zero _ _ _ hf n]
      simp
    rw [measure_mono_null Set.inter_subset_right hz, hz, zero_mul]

end DirectionalTransience
end
end

end OAI
