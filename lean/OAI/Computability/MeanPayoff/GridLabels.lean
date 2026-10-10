import OAI.Computability.MeanPayoff.Pivots

namespace OAI

namespace MeanPayoff.Label

variable {n : ℕ}

def massLabels (b : Fin n → ℚ) : Fin n → Bool := fun i => decide (1 < b i)

theorem massBase_good {F : Vec (Fin n) → Vec (Fin n)} {A : Vec (Fin n)} {D : ℤ}
    (hD : 0 < D) {a b : Fin n → ℚ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hprod : ∀ i, 1 < a i*b i) : Good F A D a b (massLabels b) := by
  constructor
  · intro x hx i hi
    have hia : A i < x i := by dsimp [MaxClaim] at hi; omega
    have hm := (weight_le_mass (fun i => (ha i).le)
      (show i ∈ lowerActive A x by simp [lowerActive, hia])).trans hx.2
    have hp := hprod i
    have hbi : 1 < b i := by nlinarith [hb i]
    simpa only [massLabels, decide_eq_true_eq] using hbi
  · intro y hy i hi
    have hib : y i < shift A D i := by dsimp [MinClaim] at hi; dsimp [shift]; omega
    have hm := (weight_le_mass (fun i => (hb i).le)
      (show i ∈ upperActive (shift A D) y by simp [upperActive, hib])).trans hy.2
    simpa only [massLabels, decide_eq_false_iff_not, not_lt] using hm

def widthLabels (A z : Vec (Fin n)) (D : ℤ) : Fin n → Bool :=
  fun i => decide (2*A i + D < 2*z i)

theorem widthBase_good (G : Game) {A : Vec (Fin G.n)} {D : ℤ} (hD : 0 < D)
    (a b : Fin G.n → ℚ) :
    Good (operator G) A D a b
      (widthLabels A (basic G A (shift A D) (fun i => by dsimp [shift]; omega)).1 D) := by
  have h := basic_spec G A (shift A D) (fun i => by dsimp [shift]; omega)
  constructor
  · intro x hx i hi
    have hc := box_comparison G hx.1 h.2.1 i
    dsimp [MaxClaim] at hi
    simp only [widthLabels, decide_eq_true_eq]
    linarith only [hD, hi, hc]
  · intro y hy i hi
    have hc := box_comparison G h.1 hy.1 i
    dsimp [MinClaim] at hi
    simp only [widthLabels, decide_eq_false_iff_not]
    linarith only [hD, hi, hc]

abbrev Grid (n : ℕ) := Fin n → Fin 1025

def gridPivot (A : Vec (Fin n)) (t : ℤ) (g : Grid n) : Vec (Fin n) :=
  fun i => A i + (1536+(g i).val)*t

def gridCenter : Grid n := fun _ => ⟨512, by omega⟩

def gridDown (g : Grid n) (labels : Fin n → Bool) : Grid n := fun i =>
  if labels i then g i else ⟨(g i).val-1, by have := (g i).isLt; omega⟩

def gridUp (g : Grid n) (labels : Fin n → Bool) : Grid n := fun i =>
  if labels i then ⟨min 1024 ((g i).val+1), by omega⟩ else g i

theorem gridPivot_center (A : Vec (Fin n)) (t : ℤ) :
    gridPivot A t gridCenter = fun i => A i+2048*t := by
  funext i
  norm_num [gridPivot, gridCenter]

theorem gridPivot_bounds (A : Vec (Fin n)) {t : ℤ} (ht : 0 ≤ t) (g : Grid n) (i : Fin n) :
    A i+1536*t ≤ gridPivot A t g i ∧ gridPivot A t g i ≤ A i+2560*t := by
  have h0 : (0 : ℤ) ≤ (g i).val := Int.natCast_nonneg _
  have h1 : ((g i).val : ℤ) ≤ 1024 := by exact_mod_cast Nat.le_of_lt_succ (g i).isLt
  dsimp [gridPivot]
  constructor <;> nlinarith

theorem gridPivot_mono (A : Vec (Fin n)) {t : ℤ} (ht : 0 ≤ t) {g g' : Grid n}
    (h : g ≤ g') : gridPivot A t g ≤ gridPivot A t g' := by
  intro i
  have hi : ((g i).val : ℤ) ≤ (g' i).val := by exact_mod_cast (h i)
  dsimp [gridPivot]
  nlinarith

theorem gridDown_le (g : Grid n) (labels : Fin n → Bool) : gridDown g labels ≤ g := by
  intro i
  unfold gridDown
  split
  · exact le_rfl
  · change (g i).val-1 ≤ (g i).val
    omega

theorem le_gridUp (g : Grid n) (labels : Fin n → Bool) : g ≤ gridUp g labels := by
  intro i
  unfold gridUp
  split
  · change (g i).val ≤ min 1024 ((g i).val+1)
    have := (g i).isLt
    omega
  · exact le_rfl

theorem gridPivot_down (A : Vec (Fin n)) {t : ℤ} (ht : 0 ≤ t)
    (g : Grid n) (labels : Fin n → Bool) :
    gridPivot A t (gridDown g labels) = downStep A t (gridPivot A t g) labels := by
  funext i
  cases h : labels i
  · simp only [gridPivot, gridDown, h, Bool.false_eq_true, ↓reduceIte, downStep]
    by_cases hz : (g i).val=0
    · simp only [hz, Nat.zero_sub, Nat.cast_zero, add_zero]
      rw [max_eq_left]; omega
    · have hg : 1 ≤ (g i).val := by omega
      rw [Nat.cast_sub hg]
      norm_num only [Nat.cast_one]
      have hg' : (1 : ℤ) ≤ (g i).val := by exact_mod_cast hg
      have hp : (0 : ℤ) ≤ ((g i).val-1)*t := mul_nonneg (sub_nonneg.mpr hg') ht
      have hh : A i+1536*t ≤ A i+(1536+(g i).val)*t-t := by nlinarith only [hp]
      rw [max_eq_right hh]
      ring
  · simp only [gridPivot, gridDown, h, ↓reduceIte, downStep]

theorem gridPivot_up (A : Vec (Fin n)) {t : ℤ} (ht : 0 ≤ t)
    (g : Grid n) (labels : Fin n → Bool) :
    gridPivot A t (gridUp g labels) = upStep A t (gridPivot A t g) labels := by
  funext i
  cases h : labels i
  · simp only [gridPivot, gridUp, h, Bool.false_eq_true, ↓reduceIte, upStep]
  · simp only [gridPivot, gridUp, h, ↓reduceIte, upStep]
    by_cases hz : (g i).val=1024
    · norm_num [hz]
      exact ht
    · have hg : (g i).val+1≤1024 := by have := (g i).isLt; omega
      rw [min_eq_right hg, Nat.cast_add, Nat.cast_one]
      have hg' : ((g i).val : ℤ)+1≤1024 := by exact_mod_cast hg
      have hp : (0 : ℤ) ≤ (1024-((g i).val+1))*t :=
        mul_nonneg (sub_nonneg.mpr hg') ht
      have hh : A i+(1536+(g i).val)*t+t ≤ A i+2560*t := by nlinarith only [hp]
      rw [min_eq_right hh]
      ring

def settle {α : Type} [DecidableEq α] (f : α → α) (rank : α → ℕ)
    (hdec : ∀ x, f x ≠ x → rank (f x) < rank x) (x : α) :
    {r : α × ℕ // r.1 = f^[r.2] x ∧ f r.1 = r.1 ∧ r.2 ≤ rank x} := by
  by_cases h : f x = x
  · exact ⟨(x, 0), rfl, h, Nat.zero_le _⟩
  · let r := settle f rank hdec (f x)
    refine ⟨(r.val.1, r.val.2+1), ?_, r.property.2.1, ?_⟩
    · rw [Function.iterate_succ_apply]
      exact r.property.1
    · have := r.property.2.2
      have := hdec x h
      omega
termination_by rank x
decreasing_by exact hdec x h

theorem settle_invariant {α : Type} [DecidableEq α] (f : α → α) (rank : α → ℕ)
    (hdec : ∀ x, f x ≠ x → rank (f x) < rank x) (x : α) (P : α → Prop)
    (hinit : P x) (hstep : ∀ z, P z → P (f z)) :
    P (settle f rank hdec x).val.1 := by
  rw [(settle f rank hdec x).property.1]
  generalize (settle f rank hdec x).val.2 = k
  induction k with
  | zero => exact hinit
  | succ k ih => rw [Function.iterate_succ_apply']; exact hstep _ ih

def downRank (g : Grid n) : ℕ := ∑ i, (g i).val

def upRank (g : Grid n) : ℕ := ∑ i, (1024-(g i).val)

theorem downRank_le (g : Grid n) : downRank g ≤ 1024*n := by
  calc
    downRank g ≤ ∑ _i : Fin n, 1024 := Finset.sum_le_sum (fun i _ => by
      have := (g i).isLt; omega)
    _ = 1024*n := by simp [mul_comm]

theorem upRank_le (g : Grid n) : upRank g ≤ 1024*n := by
  calc
    upRank g ≤ ∑ _i : Fin n, 1024 := Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    _ = 1024*n := by simp [mul_comm]

theorem downRank_strict {g g' : Grid n} (hle : g' ≤ g) (hne : g' ≠ g) :
    downRank g' < downRank g := by
  apply Finset.sum_lt_sum
  · intro i _
    exact hle i
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hle i) (Fin.val_injective.ne hi)⟩

theorem upRank_strict {g g' : Grid n} (hle : g ≤ g') (hne : g' ≠ g) :
    upRank g' < upRank g := by
  apply Finset.sum_lt_sum
  · intro i _
    exact Nat.sub_le_sub_left (hle i) _
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hn := (g' i).isLt
    have hl : (g i).val < (g' i).val := lt_of_le_of_ne (hle i) (Fin.val_injective.ne (Ne.symm hi))
    exact ⟨i, Finset.mem_univ _, by omega⟩

def downRun (oracle : Grid n → (Fin n → Bool)) (g : Grid n) :=
  settle (fun z => gridDown z (oracle z)) downRank
    (fun z h => downRank_strict (gridDown_le z _) h) g

def upRun (oracle : Grid n → (Fin n → Bool)) (g : Grid n) :=
  settle (fun z => gridUp z (oracle z)) upRank
    (fun z h => upRank_strict (le_gridUp z _) h) g

theorem downRun_le (oracle : Grid n → (Fin n → Bool)) (g : Grid n) :
    (downRun oracle g).val.1 ≤ g := by
  exact settle_invariant _ _ _ g (fun z => z ≤ g) le_rfl
    (fun z hz => (gridDown_le z _).trans hz)

theorem le_upRun (oracle : Grid n → (Fin n → Bool)) (g : Grid n) :
    g ≤ (upRun oracle g).val.1 := by
  exact settle_invariant _ _ _ g (fun z => g ≤ z) le_rfl
    (fun z hz => hz.trans (le_gridUp z _))

theorem downRun_peak (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hx : MaxWitness F A (4096*t) a x)
    (hrel : ∃ i, MaxClaim A (4096*t) x i) (oracle : Grid n → (Fin n → Bool))
    (horacle : ∀ g, Good F (fun i => gridPivot A t g i-16*t) (32*t) a b (oracle g))
    (g : Grid n) :
    peak hn x (gridPivot A t (downRun oracle g).val.1) = peak hn x (gridPivot A t g) := by
  apply settle_invariant _ _ _ g
    (fun z => peak hn x (gridPivot A t z) = peak hn x (gridPivot A t g)) rfl
  intro z hz
  rw [gridPivot_down A ht.le]
  rw [down_protection hn laws ht ha hx
    (fun i => (gridPivot_bounds A ht.le z i).1)
    (fun i => (gridPivot_bounds A ht.le z i).2) hrel (horacle z)]
  exact hz

theorem upRun_peak (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (hb : ∀ i, 0 < b i) (hy : MinWitness F A (4096*t) b y)
    (hrel : ∃ i, MinClaim A (4096*t) y i) (oracle : Grid n → (Fin n → Bool))
    (horacle : ∀ g, Good F (fun i => gridPivot A t g i-16*t) (32*t) a b (oracle g))
    (g : Grid n) :
    peak hn (gridPivot A t (upRun oracle g).val.1) y = peak hn (gridPivot A t g) y := by
  apply settle_invariant _ _ _ g
    (fun z => peak hn (gridPivot A t z) y = peak hn (gridPivot A t g) y) rfl
  intro z hz
  rw [gridPivot_up A ht.le]
  rw [up_protection hn laws ht hb hy
    (fun i => (gridPivot_bounds A ht.le z i).1)
    (fun i => (gridPivot_bounds A ht.le z i).2) hrel (horacle z)]
  exact hz

def downPivot (A : Vec (Fin n)) (t : ℤ) (oracle : Grid n → (Fin n → Bool)) :=
  gridPivot A t (downRun oracle gridCenter).val.1

def finalGrid (down up : Grid n → (Fin n → Bool)) :=
  (upRun up (downRun down gridCenter).val.1).val.1

def finalPivot (A : Vec (Fin n)) (t : ℤ) (down up : Grid n → (Fin n → Bool)) :=
  gridPivot A t (finalGrid down up)

theorem passes_good (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (down up : Grid n → (Fin n → Bool))
    (hd : ∀ g, Good F (fun i => gridPivot A t g i-16*t) (32*t)
      a (fun i => 4/3*b i) (down g))
    (hu : ∀ g, Good F (fun i => gridPivot A t g i-16*t) (32*t)
      (fun i => 4/3*a i) b (up g))
    {provisional continuation : Fin n → Bool}
    (hp : Good F (fun i => finalPivot A t down up i-1024*t) (2048*t) a b provisional)
    (hc : Good F A (4096*t) (reweight a provisional)
      (reweight b (fun i => !(provisional i))) continuation) :
    Good F A (4096*t) a b
      (override A (downPivot A t down) (finalPivot A t down up) t continuation) := by
  let gd := (downRun down gridCenter).val.1
  let gf := finalGrid down up
  let kd := gridPivot A t gd
  let kf := gridPivot A t gf
  have hdlo : ∀ i, A i+1536*t ≤ kd i := fun i => (gridPivot_bounds A ht.le gd i).1
  have hdhi : ∀ i, kd i ≤ A i+2560*t := fun i => (gridPivot_bounds A ht.le gd i).2
  have hflo : ∀ i, A i+1536*t ≤ kf i := fun i => (gridPivot_bounds A ht.le gf i).1
  have hfhi : ∀ i, kf i ≤ A i+2560*t := fun i => (gridPivot_bounds A ht.le gf i).2
  have hdc : ∀ i, kd i ≤ A i+2048*t := by
    have h := gridPivot_mono A ht.le (downRun_le down gridCenter)
    rw [gridPivot_center] at h
    exact h
  have hdf : kd ≤ kf := gridPivot_mono A ht.le (le_upRun up gd)
  have hdownstop : downStep A t kd (down gd) = kd := by
    rw [← gridPivot_down A ht.le]
    exact congrArg (gridPivot A t) (downRun down gridCenter).property.2.1
  have hupstop : upStep A t kf (up gf) = kf := by
    rw [← gridPivot_up A ht.le]
    exact congrArg (gridPivot A t) (upRun up gd).property.2.1
  apply override_good hn laws ht ha hb hflo hfhi _ _ _ _ hp hc
  · intro x hx i hi
    apply max_mark_safe hn (i := i) _ hi
    have he := downRun_peak hn laws ht ha hx ⟨i, hi⟩ down hd gridCenter
    change peak hn x kd = _ at he
    change peak hn x kd ≤ 2048*t
    rw [he, gridPivot_center]
    apply peak_le
    intro j
    have hj := hx.1.1.2 j
    dsimp only [shift] at hj
    linarith only [hj]
  · intro y hy i hi
    apply min_mark_safe hn (i := i) _ hi
    have he := upRun_peak hn laws ht hb hy ⟨i, hi⟩ up hu gd
    change peak hn kf y = peak hn kd y at he
    rw [he]
    apply peak_le
    intro j
    have hj := hy.1.1.1 j
    have hk := hdc j
    linarith only [hj, hk]
  · intro x hx hclaim
    exact up_stationary_heavy hn laws ht hx hflo hfhi hclaim (hu gf) hupstop
  · intro y hy hclaim
    have hm := down_stationary_heavy hn laws ht hy hdlo hdhi hclaim (hd gd) hdownstop
    have hrel : ∃ i, MinClaim A (4096*t) y i := by
      obtain ⟨i, hi, _⟩ := hclaim
      exact ⟨i, hi⟩
    have he := upRun_peak hn laws ht hb hy hrel up hu gd
    have hs := near_mono_up hn (r := 32*t) hdf he
    exact hm.trans_le (mass_mono (fun i => (hb i).le) hs)

end MeanPayoff.Label

end OAI
