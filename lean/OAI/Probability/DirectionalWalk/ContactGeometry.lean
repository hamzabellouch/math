import OAI.Probability.DirectionalWalk.HittingWords

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def oppositeStep {d : ℕ} (e : Step d) : Step d := (e.1,!e.2)

lemma axisDirection_opposite {d : ℕ} (e : Step d) :
    axisDirection (oppositeStep e) = -axisDirection e := by
  ext i
  rcases e with ⟨j,b⟩
  cases b <;> simp [axisDirection,oppositeStep,Pi.single_apply] <;> split_ifs <;> norm_num

lemma axisHeight_opposite {d : ℕ} (e : Step d) (x : Site d) :
    axisHeight (oppositeStep e) x = -axisHeight e x := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight,oppositeStep]

lemma axisHeight_neg {d : ℕ} (e : Step d) (x : Site d) :
    axisHeight e (-x) = -axisHeight e x := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight]

lemma axisHeight_sum {d : ℕ} {ι : Type*} (e : Step d) (s : Finset ι) (f : ι → Site d) :
    axisHeight e (∑ i ∈ s, f i) = ∑ i ∈ s, axisHeight e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [axisHeight_zero]
  | @insert i s hi ih => simp [Finset.sum_insert hi,axisHeight_add,ih]

lemma axisHeight_step_self {d : ℕ} (e : Step d) : axisHeight e (stepVector e) = 1 := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight,stepVector]

lemma axisHeight_wordEnd {d : ℕ} (e : Step d) (a : Word d)
    (ha : RegenerationWord (axisDirection e) a) :
    axisHeight e (wordEnd a) = (slabRecords (axisDirection e) a : ℤ) := by
  have h := axis_slabWidth_eq_records e a ha
  change height (axisDirection e) (wordEnd a) = _ at h
  rw [height_axisDirection] at h
  exact_mod_cast h

lemma axisHeight_word_interior {d : ℕ} (e : Step d) (a : Word d)
    (ha : RegenerationWord (axisDirection e) a) (i : ℕ) (hi : i < a.1) :
    0 ≤ axisHeight e (wordPath a i) ∧
      axisHeight e (wordPath a i) < (slabRecords (axisDirection e) a : ℤ) := by
  have h := ha.2.2.2.1 i hi
  have hh := axisHeight_wordEnd e a ha
  change axisHeight e (wordPath a a.1) = _ at hh
  rw [height_axisDirection,height_axisDirection,hh] at h
  exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩

def placedAxis {d : ℕ} (e : Step d) (b : Bool) : Step d := if b then oppositeStep e else e

noncomputable def placedWidth {d : ℕ} (e : Step d) (b : Bool) : Word d → ℕ :=
  slabRecords (axisDirection (placedAxis e b))

def opposedAnchor {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (b : Bool) (i : ℕ) : Site d :=
  if b then -stepVector e + ∑ j ∈ Finset.range i, wordEnd (Z (true,j))
  else -(∑ j ∈ Finset.range (i+1), wordEnd (Z (false,j)))

def opposedSite {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (b : Bool) (i t : ℕ) : Site d :=
  opposedAnchor e Z b i + wordPath (Z (b,i)) t

def opposedDeparture {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (b : Bool) (y : Site d) : Prop :=
  ∃ i, ∃ t < (Z (b,i)).1, opposedSite e Z b i t = y

def contactAt {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (y : Site d) : Prop :=
  opposedDeparture e Z false y ∧ opposedDeparture e Z true y

def contactDepth {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (h : ℕ) : Prop :=
  ∃ y, contactAt e Z y ∧ -axisHeight e y = (h : ℤ)

lemma opposedAnchor_height {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (b : Bool) (i : ℕ) :
    -axisHeight e (opposedAnchor e Z b i) =
      if b then 1 + (tapeHeight (placedWidth e true) (fun j => Z (true,j)) i : ℤ)
      else (tapeHeight (placedWidth e false) (fun j => Z (false,j)) (i+1) : ℤ) := by
  have hp (j : ℕ) : axisHeight e (wordEnd (Z (false,j))) = (placedWidth e false (Z (false,j)) : ℤ) :=
    axisHeight_wordEnd e _ (hZ false j)
  have hm (j : ℕ) : axisHeight e (wordEnd (Z (true,j))) = -(placedWidth e true (Z (true,j)) : ℤ) := by
    have hh := axisHeight_wordEnd (oppositeStep e) _ (hZ true j)
    rw [axisHeight_opposite] at hh
    exact neg_eq_iff_eq_neg.mp hh
  cases b <;> simp [opposedAnchor,axisHeight_neg,axisHeight_add,axisHeight_sum,
    axisHeight_step_self,hp,hm,tapeHeight,Finset.sum_neg_distrib,add_comm]

lemma opposed_departure_band {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (b : Bool) (i t : ℕ) (ht : t < (Z (b,i)).1) :
    let s := tapeHeight (placedWidth e b) (fun j => Z (b,j)) i
    let L := placedWidth e b (Z (b,i))
    (s : ℤ) < -axisHeight e (opposedSite e Z b i t) ∧
      -axisHeight e (opposedSite e Z b i t) ≤ (s+L : ℕ) := by
  have hc := axisHeight_word_interior (placedAxis e b) (Z (b,i)) (hZ b i) t ht
  have ha := opposedAnchor_height e Z hZ b i
  dsimp only
  unfold opposedSite
  rw [axisHeight_add]
  cases b
  · simp only [placedAxis,Bool.false_eq_true,↓reduceIte] at hc ha
    simp only [tapeHeight,Finset.sum_range_succ,Nat.cast_add] at ha ⊢
    simp only [placedWidth,placedAxis,Bool.false_eq_true,↓reduceIte] at *
    omega
  · simp only [placedAxis,↓reduceIte,axisHeight_opposite] at hc ha
    simp only [placedWidth,placedAxis,↓reduceIte] at *
    push_cast
    omega

lemma axial_step_unique {d : ℕ} (e f : Step d) (h : axisHeight e (stepVector f) = 1) :
    f = e := by
  rcases e with ⟨i,b⟩
  rcases f with ⟨j,c⟩
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;> simp_all [axisHeight,stepVector]
  · cases b <;> cases c <;> simp [axisHeight,stepVector,hij] at h

lemma axis_word_last_step {d : ℕ} (e : Step d) (a : Word d)
    (ha : RegenerationWord (axisDirection e) a) :
    wordEnd a = wordPath a (a.1-1) + stepVector e := by
  have hp : a.1-1 < a.1 := by have := ha.1; omega
  have hh := axisHeight_word_interior e a ha (a.1-1) hp
  obtain ⟨f,hf⟩ := ha.2.2.1 (a.1-1) hp
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a.1)] at hf
  have he : axisHeight e (stepVector f) = 1 := by
    have htt := axisHeight_wordEnd e a ha
    change axisHeight e (wordPath a a.1) = _ at htt
    rw [hf,axisHeight_add] at htt
    have hle := axisHeight_step_le e f
    omega
  rw [axial_step_unique e f he] at hf
  exact hf

lemma opposed_forced_contact {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i))) :
    contactAt e Z (-stepVector e) ∧ contactDepth e Z 1 := by
  have hc : contactAt e Z (-stepVector e) := by
    constructor
    · refine ⟨0,(Z (false,0)).1-1,by have := (hZ false 0).1; omega,?_⟩
      have ht := axis_word_last_step e (Z (false,0)) (hZ false 0)
      simp only [opposedSite,opposedAnchor,Bool.false_eq_true,↓reduceIte,
        zero_add,Finset.sum_range_one,ht]
      abel
    · refine ⟨0,0,(hZ true 0).1,?_⟩
      simp only [opposedSite,opposedAnchor,↓reduceIte,Finset.sum_range_zero,add_zero,
        (hZ true 0).2.1]
  refine ⟨hc,⟨-stepVector e,hc,?_⟩⟩
  rw [axisHeight_neg,axisHeight_step_self]
  norm_num

def axisLower {d : ℕ} (e : Step d) (k : ℤ) : Set (Site d) := {y | axisHeight e y < k}
def axisUpper {d : ℕ} (e : Step d) (k : ℤ) : Set (Site d) := {y | k ≤ axisHeight e y}

lemma axis_barriers_disjoint {d : ℕ} (e : Step d) {k N : ℤ} (hkN : k ≤ N) :
    Disjoint (axisLower e k) (axisUpper e N) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  exact (not_lt_of_ge (hkN.trans hz)) hy

lemma hitBefore_axis_eq_reach {d : ℕ} (e : Step d) (H : ℕ) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) :
    X ∈ hitBefore (axisUpper e H) (axisLower e 0) ↔ X ∈ reachAxis e H := by
  constructor
  · rintro ⟨n,hn,hb⟩
    obtain ⟨j,hjn,hj,_⟩ := integer_first_crossing (fun i => axisHeight e (X i)) n H
      (fun i _ => axisHeight_nn_le e X hX i) (by simp [h0,axisHeight_zero]) hn
    exact ⟨j,hj,fun i hi => le_of_not_gt (hb i (hi.trans hjn))⟩
  · rintro ⟨n,hn,hb⟩
    exact ⟨n,hn.ge,fun i hi => not_lt_of_ge (hb i hi)⟩

lemma annealed_axis_exit {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (x : Site d) (k N : ℤ) :
    ∀ᵐ X ∂annealed μ x, ∃ n, X n ∈ axisLower e k ∪ axisUpper e N := by
  filter_upwards [annealed_exit_band μ hell x (axisDirection e) (axisDirection_ne_zero e)
    (k : ℝ) (N-1 : ℤ)] with X hX
  obtain ⟨n,hn⟩ := hX
  refine ⟨n,?_⟩
  simp only [height_axisDirection,Set.mem_Icc,not_and,not_le] at hn
  change axisHeight e (X n) < k ∨ N ≤ axisHeight e (X n)
  by_cases h : axisHeight e (X n) < k
  · exact Or.inl h
  · right
    have hh := hn (by exact_mod_cast le_of_not_gt h)
    have : N-1 < axisHeight e (X n) := by exact_mod_cast hh
    omega

lemma annealed_axis_return_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) {r N : ℕ} (hrN : r ≤ N) :
    annealed μ 0 (hitBefore (axisUpper e r) (axisLower e 0) ∩
      hitBefore (axisLower e 0) (axisUpper e N)) = axisReachProb μ e r - axisReachProb μ e N := by
  have hAE := annealed_axis_exit μ hell e 0 0 N
  have hd := hitBefore_disjoint (axisLower e 0) (axisUpper e N)
  have he : (hitBefore (axisUpper e r) (axisLower e 0) ∩
      hitBefore (axisLower e 0) (axisUpper e N) : Set (Path d)) =ᵐ[annealed μ 0]
      (reachAxis e r \ reachAxis e N : Set (Path d)) := by
    filter_upwards [ae_start_and_nearestNeighbour μ 0,hAE] with X hX hx
    have hb : X ∈ hitBefore (axisLower e 0) (axisUpper e N) ∪
        hitBefore (axisUpper e N) (axisLower e 0) := by
      rw [hitBefore_union_eq_eventual _ _ (axis_barriers_disjoint e (by positivity))]
      exact hx
    have h1 := hitBefore_axis_eq_reach e r X hX.1 hX.2
    have h2 := hitBefore_axis_eq_reach e N X hX.1 hX.2
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨h1.mp ha,fun hc => Set.disjoint_left.mp hd hb (h2.mpr hc)⟩
    · rintro ⟨ha,hc⟩
      exact ⟨h1.mpr ha,hb.resolve_right (fun hh => hc (h2.mp hh))⟩
  have he' : (reachAxis e r ∪ reachAxis e N : Set (Path d)) =ᵐ[annealed μ 0] reachAxis e r := by
    filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
    apply propext
    exact ⟨fun h => h.elim id (reachAxis_antitone e X hX.1 hX.2 hrN),Or.inl⟩
  rw [measure_congr he,measure_sdiff' _ (measurableSet_reachAxis e N).nullMeasurableSet
    (measure_ne_top _ _),measure_congr he']
  rfl

lemma annealed_axis_visitAfter_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) {r N : ℕ} (hrN : r ≤ N)
    (a : ℝ≥0∞) (A : Environment d → Set (Site d))
    (hA : ∀ᵐ ω ∂environmentLaw μ, ∀ y ∈ A ω,
      a ≤ quenchedKernel d (ω,y) (hitBefore (axisLower e 0) (axisUpper e N))) :
    a * (∫⁻ ω, quenchedKernel d (ω,0)
      (visitAfter (axisUpper e r) (A ω) (axisLower e 0 ∪ axisUpper e N)) ∂environmentLaw μ) ≤
      axisReachProb μ e r - axisReachProb μ e N := by
  rw [← annealed_axis_return_probability μ hell e hrN,
    annealed_apply μ 0 ((measurableSet_hitBefore _ _).inter (measurableSet_hitBefore _ _))]
  apply (lintegral_const_mul_le _ _).trans
  apply lintegral_mono_ae
  filter_upwards [hA] with ω hω
  exact quenched_visitAfter_bound ω 0 _ _ _ _ a hω

end DirectionalZeroOne

end OAI
