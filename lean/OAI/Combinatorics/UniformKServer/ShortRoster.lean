import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteProbability
import OAI.Combinatorics.UniformKServer.ChronologicalBound
import OAI.Combinatorics.UniformKServer.TierPilot

namespace OAI

noncomputable section

namespace UniformKServer.ShortRoster

section
open FiniteProbability
variable {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable

/-- A clipped distance-to-set ramp, expressed as the minimum of all live
center costs and the empty-roster cost one. -/
def costValue (a : I → ℝ) (H : Finset I) : ℝ :=
  (insert 1 (H.image a)).min' (by simp)

/-- Continue all old lifetime trials using fresh independent keep bits;
compulsory cutoffs apply on the same age increment. The new entry's ramp
value is supplied separately so duplicates of physical centers are harmless. -/
def retained (inc kill : I → Prop) (H : Finset I) (τ : I → Bool) : Finset I :=
  H.filter fun i => ¬inc i ∨ (¬kill i ∧ τ i = true)

def editedValue (a : I → ℝ) (b : ℝ) (inc kill : I → Prop)
    (H : Finset I) (τ : I → Bool) : ℝ := min b (costValue a (retained inc kill H τ))

def fresh (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) : Law (I → Bool) :=
  coins (fun _ => 1-q) (fun _ => ⟨by linarith [hq.2],by linarith [hq.1]⟩)

omit [Fintype I] in
theorem cost_bounds (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) (H : Finset I) :
    costValue a H ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.le_min'
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact (ha i).1
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

omit [Fintype I] in
theorem cost_le (a : I → ℝ) (H : Finset I) (i : I) (hi : i ∈ H) : costValue a H ≤ a i :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hi,rfl⟩))

omit [Fintype I] in
theorem le_cost (a : I → ℝ) (H : Finset I) (v : ℝ) (h1 : v ≤ 1)
    (h : ∀ i ∈ H, v ≤ a i) : v ≤ costValue a H := by
  apply Finset.le_min'
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact h1
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact h i hi

omit [Fintype I] in
theorem cost_witness (a : I → ℝ) (H : Finset I) (h : costValue a H < 1) :
    ∃ i ∈ H, a i = costValue a H := by
  have hm := Finset.min'_mem (insert 1 (H.image a)) (by simp)
  change costValue a H ∈ insert 1 (H.image a) at hm
  rcases Finset.mem_insert.mp hm with he | hm
  · linarith
  · exact Finset.mem_image.mp hm

omit [Fintype I] in
theorem cost_close (a b : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hb : ∀ i, b i ∈ Set.Icc (0:ℝ) 1) (d : ℝ) (hd : 0 ≤ d)
    (hab : ∀ i, |a i-b i| ≤ d) (H : Finset I) :
    |costValue a H-costValue b H| ≤ d := by
  suffices hh : ∀ a b : I → ℝ, (∀ i, a i ∈ Set.Icc (0:ℝ) 1) →
      (∀ i, b i ∈ Set.Icc (0:ℝ) 1) → (∀ i, a i-b i ≤ d) →
      costValue a H-costValue b H ≤ d by
    apply abs_le.mpr
    constructor
    · have hi := hh b a hb ha (fun i => by have := (abs_le.mp (hab i)).1; linarith)
      linarith
    · exact hh a b ha hb (fun i => (le_abs_self _).trans (hab i))
  intro a b ha hb hab
  by_cases hm : costValue b H < 1
  · obtain ⟨i,hi,he⟩ := cost_witness b H hm
    linarith [cost_le a H i hi,hab i]
  · have he : costValue b H = 1 := le_antisymm (cost_bounds b hb H).2 (le_of_not_gt hm)
    rw [he]
    linarith [(cost_bounds a ha H).2]

omit [Fintype I] in
theorem edited_bounds (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) (inc kill : I → Prop)
    (H : Finset I) (τ : I → Bool) : editedValue a b inc kill H τ ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min hb.1 (cost_bounds a ha _).1,(min_le_left _ _).trans hb.2⟩

omit [Fintype I] in
theorem edited_le_retained (a : I → ℝ) (b : ℝ) (inc kill : I → Prop)
    (H : Finset I) (τ : I → Bool) (i : I) (hi : i ∈ H)
    (hkeep : ¬inc i ∨ (¬kill i ∧ τ i = true)) : editedValue a b inc kill H τ ≤ a i :=
  (min_le_right _ _).trans (cost_le a _ i (Finset.mem_filter.mpr ⟨hi,hkeep⟩))

theorem conditional_increase (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) (inc kill : I → Prop)
    (H : Finset I) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    (fresh (I := I) q hq).expect (fun τ => editedValue a b inc kill H τ-costValue a H) ≤
      q+∑ i, if i ∈ H ∧ inc i ∧ kill i ∧ a i < 1 then 1 else 0 := by
  classical
  let Q := fresh (I := I) q hq
  have hs : 0 ≤ ∑ i : I, if i ∈ H ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have trivialBound (τ : I → Bool) : editedValue a b inc kill H τ-costValue a H ≤ 1 := by
    linarith [(edited_bounds a ha b hb inc kill H τ).2,(cost_bounds a ha H).1]
  by_cases hm : costValue a H < 1
  · obtain ⟨i,hi,he⟩ := cost_witness a H hm
    by_cases hinc : inc i
    · by_cases hkill : kill i
      · have hsite : (1:ℝ) ≤ ∑ j : I, if j ∈ H ∧ inc j ∧ kill j ∧ a j < 1 then 1 else 0 := by
          have hi' : a i < 1 := by linarith
          have hx := Finset.single_le_sum (s := Finset.univ) (a := i)
            (f := fun j : I => if j ∈ H ∧ inc j ∧ kill j ∧ a j < 1 then (1:ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
          simpa only [ite_eq_left (show i ∈ H ∧ inc i ∧ kill i ∧ a i < 1 from ⟨hi,hinc,hkill,hi'⟩)] using hx
        have hv := Q.expect_mono _ _ trivialBound
        rw [Q.expect_const] at hv
        exact hv.trans (by linarith [hq.1])
      · have hp : ∀ τ, editedValue a b inc kill H τ-costValue a H ≤ if τ i then 0 else 1 := by
          intro τ
          cases ht : τ i
          · simpa [ht] using trivialBound τ
          · have hh := edited_le_retained a b inc kill H τ i hi (Or.inr ⟨hkill,ht⟩)
            simpa only [ht,Bool.true_eq,ite_true] using (show editedValue a b inc kill H τ-costValue a H ≤ 0 by linarith)
        have hv := Q.expect_mono _ _ hp
        have hQ : Q.expect (fun τ => if τ i then 0 else 1) = q := by
          calc
            _ = 1-(1-q) := coins_false (fun _ : I => 1-q)
              (fun _ => ⟨by linarith [hq.2],by linarith [hq.1]⟩) i
            _ = q := by ring
        rw [hQ] at hv
        exact hv.trans (by linarith)
    · have hp : ∀ τ, editedValue a b inc kill H τ-costValue a H ≤ 0 := by
        intro τ
        have hh := edited_le_retained a b inc kill H τ i hi (Or.inl hinc)
        linarith
      have hv := Q.expect_mono _ _ hp
      rw [Q.expect_const] at hv
      exact hv.trans (by linarith [hq.1])
  · have he : costValue a H = 1 := le_antisymm (cost_bounds a ha H).2 (le_of_not_gt hm)
    have hp : ∀ τ, editedValue a b inc kill H τ-costValue a H ≤ 0 := by
      intro τ
      rw [he]
      exact sub_nonpos.mpr (edited_bounds a ha b hb inc kill H τ).2
    have hv := Q.expect_mono _ _ hp
    rw [Q.expect_const] at hv
    exact hv.trans (by linarith [hq.1])

end

section
open FiniteProbability
attribute [local instance] Classical.propDecidable

/-- The finite random experiment is part of the constructed state, not an
assumed randomized-policy interface. -/
structure State (I : Type) where
  Sample : Type
  finite : Fintype Sample
  law : @Law Sample finite
  live : Sample → Finset I

attribute [instance] State.finite

variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

def ramp (v : ℝ) : ℝ := max 0 (min 1 (8*v-1))

def State.parameter (D : State I) (c : I → X) (r : ℝ) (p : X) : ℝ :=
  D.law.expect fun ω => costValue (fun i => ramp (dist p (c i)/r)) (D.live ω)

def State.Valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) (q : ℝ) : Prop :=
  (∀ ω, D.live ω ⊆ ChronologicalRoster.young S c r K) ∧
  (∀ i, D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) =
    if i ∈ S ∧ ChronologicalRoster.age S c r i < K then
      (1-q)^ChronologicalRoster.age S c r i else 0)

def State.next (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I) : State I where
  Sample := D.Sample × (I → Bool)
  finite := inferInstance
  law := D.law.prod (fresh q hq)
  live ω := insert n (retained (fun i => dist (c i) (c n) ≤ 20*r)
    (fun i => K ≤ ChronologicalRoster.age S c r i+1) (D.live ω.1) ω.2)

end

section
attribute [local instance] Classical.propDecidable
open FiniteProbability
variable {I Ω : Type*} [Fintype I] [Fintype Ω]

theorem mean_increase (P : Law Ω) (H : Ω → Finset I)
    (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) (inc kill : I → Prop)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (C : Finset I)
    (s : ℝ) (hs : 0 ≤ s) (A : ℕ) (hcard : C.card ≤ A)
    (hcover : ∀ ω i, i ∈ H ω → inc i → kill i → a i < 1 → i ∈ C)
    (hmarg : ∀ i ∈ C, P.expect (fun ω => if i ∈ H ω then 1 else 0) ≤ s) :
    P.expect (fun ω => (fresh (I := I) q hq).expect
      (fun τ => editedValue a b inc kill (H ω) τ)) - P.expect (fun ω => costValue a (H ω)) ≤
      q+(A:ℝ)*s := by
  classical
  let Q := fresh (I := I) q hq
  have hpoint (ω : Ω) : Q.expect (fun τ => editedValue a b inc kill (H ω) τ-costValue a (H ω)) ≤
      q+∑ i ∈ C, if i ∈ H ω then (1:ℝ) else 0 := by
    have h := conditional_increase a ha b hb inc kill (H ω) q hq
    have heq : (∑ i : I, if i ∈ H ω ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0) =
        ∑ i ∈ C, if i ∈ H ω ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro i _ hi
      split_ifs with hp
      · exact (hi (hcover ω i hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)).elim
      · rfl
    have hle : (∑ i ∈ C, if i ∈ H ω ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0) ≤
        ∑ i ∈ C, if i ∈ H ω then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ H ω
      · simp only [ite_eq_left hi]
        split_ifs <;> norm_num
      · simp only [hi,false_and,ite_false,le_refl]
    rw [heq] at h
    exact h.trans (add_le_add le_rfl hle)
  have hmean := P.expect_mono _ _ hpoint
  have hleft : P.expect (fun ω => Q.expect (fun τ => editedValue a b inc kill (H ω) τ-costValue a (H ω))) =
      P.expect (fun ω => Q.expect (fun τ => editedValue a b inc kill (H ω) τ)) -
      P.expect (fun ω => costValue a (H ω)) := by
    simp only [Q.expect_sub,Q.expect_const,P.expect_sub]
  rw [hleft,P.expect_add,P.expect_const,P.expect_finset_sum] at hmean
  have hsum := Finset.sum_le_sum (s := C) (fun i hi => hmarg i hi)
  have hsum' : (∑ i ∈ C, P.expect (fun ω => if i ∈ H ω then (1:ℝ) else 0)) ≤ (A:ℝ)*s := by
    calc
      _ ≤ ∑ _i ∈ C, s := hsum
      _ = (C.card:ℝ)*s := by simp
      _ ≤ (A:ℝ)*s := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hs
  exact hmean.trans (add_le_add le_rfl hsum')

end

attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_bounds (v : ℝ) : ramp v ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_zero (v : ℝ) (hv : v ≤ 1/8) : ramp v = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_one (v : ℝ) (hv : 1/4 ≤ v) : ramp v = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_lip (v w : ℝ) : |ramp v-ramp w| ≤ 8*|v-w| := by
  have h₁ := abs_max_sub_max_le_max (0:ℝ) (min 1 (8*v-1)) 0 (min 1 (8*w-1))
  have h₂ := abs_min_sub_min_le_max (1:ℝ) (8*v-1) 1 (8*w-1)
  simp only [sub_self,abs_zero] at h₁ h₂
  rw [max_eq_right (abs_nonneg (min 1 (8*v-1)-min 1 (8*w-1)))] at h₁
  rw [max_eq_right (abs_nonneg (8*v-1-(8*w-1)))] at h₂
  have he : |8*v-1-(8*w-1)| = 8*|v-w| := by
    rw [show 8*v-1-(8*w-1)=8*(v-w) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<8)]
  exact h₁.trans (he ▸ h₂)

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem cost_insert (a : I → ℝ) (H : Finset I) (n : I) :
    costValue a (insert n H) = min (a n) (costValue a H) := by
  classical
  unfold costValue
  simp only [Finset.image_insert, Finset.insert_comm (1:ℝ) (a n)]
  exact Finset.min'_insert (a n) (insert 1 (H.image a)) (by simp)

omit [Fintype I] [LinearOrder I] in
theorem parameter_bounds (D : State I) (c : I → X) (r : ℝ) (p : X) :
    D.parameter c r p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact D.law.expect_nonneg _ (fun ω => (cost_bounds _ (fun _ => ramp_bounds _) (D.live ω)).1)
  · have hi := D.law.expect_mono (fun ω => costValue (fun i => ramp (dist p (c i)/r)) (D.live ω))
      (fun _ => 1) (fun ω => (cost_bounds _ (fun _ => ramp_bounds _) (D.live ω)).2)
    simpa only [State.parameter,D.law.expect_const] using hi

omit [Fintype I] [LinearOrder I] in
theorem parameter_lip (D : State I) (c : I → X) (r : ℝ) (hr : 0 < r) (p y : X) :
    |D.parameter c r p-D.parameter c r y| ≤ 8*dist p y/r := by
  apply D.law.expect_close
  intro ω
  apply cost_close _ _ (fun _ => ramp_bounds _) (fun _ => ramp_bounds _) _ (by positivity)
  intro i
  have hi := ramp_lip (dist p (c i)/r) (dist y (c i)/r)
  have hd : |dist p (c i)/r-dist y (c i)/r| ≤ dist p y/r := by
    rw [←sub_div,abs_div,abs_of_pos hr]
    exact div_le_div_of_nonneg_right (abs_dist_sub_le p y (c i)) hr.le
  have := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 8)
  exact hi.trans (by simpa only [mul_div_assoc] using this)

theorem next_parameter (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I) (p : X) :
    (D.next S c r K q hq n).parameter c r p =
      D.law.expect (fun ω => (fresh (I := I) q hq).expect (fun τ =>
        editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
          (fun i => dist (c i) (c n) ≤ 20*r)
          (fun i => K ≤ age S c r i+1) (D.live ω) τ)) := by
  change (D.law.prod (fresh q hq)).expect (fun ω =>
    costValue (fun i => ramp (dist p (c i)/r))
      (insert n (retained (fun i => dist (c i) (c n) ≤ 20*r)
        (fun i => K ≤ age S c r i+1) (D.live ω.1) ω.2))) = _
  rw [D.law.expect_prod (fresh q hq) (fun ω τ =>
    costValue (fun i => ramp (dist p (c i)/r))
      (insert n (retained (fun i => dist (c i) (c n) ≤ 20*r)
        (fun i => K ≤ age S c r i+1) (D.live ω) τ)))]
  apply D.law.expect_congr
  intro ω
  apply Law.expect_congr
  intro τ
  exact cost_insert _ _ _

theorem parameter_unit_drop (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q)
    (htest : ∀ i ∈ young S c r K, r/2 < dist (c n) (c i))
    (p : X) (hp : dist (c n) p ≤ r/8) :
    D.parameter c r p = 1 ∧ (D.next S c r K q hq n).parameter c r p = 0 := by
  constructor
  · have hpoint (ω : D.Sample) : costValue (fun i => ramp (dist p (c i)/r)) (D.live ω) = 1 := by
      apply le_antisymm (cost_bounds _ (fun _ => ramp_bounds _) _).2
      apply le_cost _ _ 1 le_rfl
      intro i hi
      have hd := htest i (hD.1 ω hi)
      have ht := dist_triangle (c n) p (c i)
      rw [ramp_one _ ((le_div_iff₀ hr).mpr (by linarith))]
    unfold State.parameter
    rw [D.law.expect_congr _ _ hpoint,D.law.expect_const]
  · apply le_antisymm _ (parameter_bounds _ _ _ _).1
    rw [next_parameter]
    have hp' : ramp (dist p (c n)/r) = 0 := by
      rw [dist_comm p (c n)]
      exact ramp_zero _ ((div_le_iff₀ hr).mpr (by linarith))
    have hpoint (ω : D.Sample) : (fresh (I := I) q hq).expect (fun τ =>
        editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
          (fun i => dist (c i) (c n) ≤ 20*r) (fun i => K ≤ age S c r i+1) (D.live ω) τ) ≤ 0 := by
      have hi := (fresh (I := I) q hq).expect_mono
        (fun τ => editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
          (fun i => dist (c i) (c n) ≤ 20*r) (fun i => K ≤ age S c r i+1) (D.live ω) τ)
        (fun _ => 0) (fun τ => by
        unfold editedValue
        rw [hp']
        exact min_le_left _ _)
      simpa only [Law.expect_const] using hi
    have hi := D.law.expect_mono _ _ hpoint
    simpa only [Law.expect_const] using hi

theorem parameter_far (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (p : X) (hp : 21*r < dist (c n) p) :
    (D.next S c r K q hq n).parameter c r p ≤ D.parameter c r p := by
  rw [next_parameter]
  apply D.law.expect_mono
  intro ω
  have hpoint (τ : I → Bool) :
      editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
        (fun i => dist (c i) (c n) ≤ 20*r) (fun i => K ≤ age S c r i+1) (D.live ω) τ ≤
      costValue (fun i => ramp (dist p (c i)/r)) (D.live ω) := by
    apply le_cost _ _ _ (edited_bounds _ (fun _ => ramp_bounds _) _ (ramp_bounds _) _ _ _ _).2
    intro i hi
    by_cases hinc : dist (c i) (c n) ≤ 20*r
    · have hd : 1/4 ≤ dist p (c i)/r := by
        apply (le_div_iff₀ hr).mpr
        have ht := dist_triangle (c n) (c i) p
        rw [dist_comm (c n) (c i),dist_comm (c i) p] at ht
        linarith
      rw [ramp_one _ hd]
      exact (edited_bounds _ (fun _ => ramp_bounds _) _ (ramp_bounds _) _ _ _ _).2
    · exact edited_le_retained _ _ _ _ _ _ i hi (Or.inl hinc)
  have hi := (fresh (I := I) q hq).expect_mono _ _ hpoint
  simpa only [Law.expect_const] using hi

theorem parameter_increase (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q) (p : X) :
    (D.next S c r K q hq n).parameter c r p-D.parameter c r p ≤
      q+(K:ℝ)*(1-q)^(K-1) := by
  classical
  let a : I → ℝ := fun i => ramp (dist p (c i)/r)
  let C := (young S c r K).filter fun i => K ≤ age S c r i+1 ∧ a i < 1
  have hC : C ⊆ (young S c r K).filter (fun i => dist p (c i) ≤ r/4) := by
    intro i hi
    obtain ⟨hy,_,ha⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hy,?_⟩
    by_contra hn
    have hh : 1/4 ≤ dist p (c i)/r :=
      (le_div_iff₀ hr).mpr (by linarith [lt_of_not_ge hn])
    have he : a i = 1 := ramp_one _ hh
    linarith
  have hcard : C.card ≤ K := (Finset.card_le_card hC).trans
    (ball_young_count S c r (r/4) K p (by linarith))
  rw [next_parameter]
  apply mean_increase D.law D.live a (fun _ => ramp_bounds _)
    (ramp (dist p (c n)/r)) (ramp_bounds _) _ _ q hq C
    ((1-q)^(K-1)) (pow_nonneg (by linarith [hq.2]) _) K hcard
  · intro ω i hi _ hk ha
    exact Finset.mem_filter.mpr ⟨hD.1 ω hi,hk,ha⟩
  · intro i hi
    obtain ⟨hy,hkill,_⟩ := Finset.mem_filter.mp hi
    obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp hy
    rw [hD.2 i,ite_eq_left ⟨hiS,hage⟩]
    have he : age S c r i = K-1 := by omega
    rw [he]

/-- Exact source short-roster edit, with the finite lifetime experiment
constructed by `State.next`. No drift or gain hypothesis is present. -/
theorem short_edit (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (_hK : 0 < K) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q) (_hn : ∀ i ∈ S, i < n)
    (htest : ∀ i ∈ young S c r K, r/2 < dist (c n) (c i)) :
    TierPilot.Edit r (q+(K:ℝ)*(1-q)^(K-1)) (c n)
      (D.parameter c r) ((D.next S c r K q hq n).parameter c r) := by
  refine ⟨parameter_bounds D c r,parameter_bounds _ c r,
    parameter_unit_drop D S c r hr K q hq n hD htest,
    parameter_increase D S c r hr K q hq n hD,?_⟩
  intro p hp
  constructor
  · by_contra hdist
    have he := parameter_unit_drop D S c r hr K q hq n hD htest p (le_of_not_gt hdist)
    rw [he.1,he.2] at hp
    norm_num at hp
  · by_contra hdist
    exact (not_lt_of_ge (parameter_far D S c r hr K q hq n p (lt_of_not_ge hdist))) hp

end UniformKServer.ShortRoster

end

end OAI
