import Mathlib
import OAI.Geometry.HyperbolicGroups.MetricHexagon

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace IncidenceTemplate
open scoped BigOperators
/-- All incidences except Y_D--CD. Both sides have fixed named positions. -/
abbrev Edge := {p : Fin 11 × Fin 7 // Incident (pointOfRepresentative p.1) p.2 ∧ p ≠ (10,4)}

def isLoose (e : Edge) : Prop := e.val = (3,4)

instance (e : Edge) : Decidable (isLoose e) := inferInstanceAs (Decidable (_ = _))

def fan (i : Fin 7) : Finset Edge :=
  Finset.univ.filter (fun e => pointOfRepresentative e.val.1 = i ∧ ¬isLoose e)

lemma card_edges : Fintype.card Edge = 32 := by decide

lemma card_fan : ∀ i : Fin 7, (fan i).card = ![6,6,6,4,3,3,3] i := by decide

def code (e : Edge) : ℕ := 7 * e.val.1.val + e.val.2.val

/-- One canonical orientation of each unoriented nonbacktracking two-edge path. -/
abbrev TwoPath := {p : Edge × Edge // code p.1 < code p.2 ∧
  (p.1.val.1 = p.2.val.1 ∨ p.1.val.2 = p.2.val.2)}

lemma card_twoPaths : Fintype.card TwoPath = 90 := by decide

abbrev Field := Edge ⊕ (TwoPath × Fin 2)

instance instFieldDecidableEq : DecidableEq Field := instDecidableEqSum

lemma card_fields : Fintype.card Field = 212 := by
  simp [Fintype.card_sum, Fintype.card_prod, card_twoPaths, card_edges]


/-- The fan membership partition includes the unique loose edge separately. -/
lemma partition_per_edge : ∀ e : Edge,
    (if isLoose e then 1 else 0) + (∑ i, if e ∈ fan i then 1 else 0) = (1 : ℕ) := by
  decide

def fanCount (W : Finset Edge) (i : Fin 7) : ℕ := (W ∩ fan i).card

def looseCount (W : Finset Edge) : ℕ := (W.filter isLoose).card

lemma count_partition (W : Finset Edge) :
    W.card = looseCount W + ∑ i, fanCount W i := by
  classical
  calc
    W.card = ∑ e ∈ W, (1 : ℕ) := by simp
    _ = ∑ e ∈ W, ((if isLoose e then 1 else 0) +
        ∑ i, if e ∈ fan i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (partition_per_edge e).symm
    _ = looseCount W + ∑ i, fanCount W i := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      · simp [looseCount]
      · apply Finset.sum_congr rfl
        intro i _
        simp [fanCount]

lemma fanCount_le (W : Finset Edge) (i : Fin 7) : fanCount W i ≤ (fan i).card :=
  Finset.card_le_card Finset.inter_subset_right

lemma fanCount_eq_iff (W : Finset Edge) (i : Fin 7) :
    fanCount W i = (fan i).card ↔ fan i ⊆ W := by
  unfold fanCount
  constructor
  · intro hc
    have he := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.ge
    exact Finset.inter_eq_right.mp he
  · intro hs
    rw [Finset.inter_eq_right.mpr hs]

lemma fan_card_lower (i : Fin 7) : 3 ≤ (fan i).card := by
  rw [card_fan]
  fin_cases i <;> decide

/-- Each fan retains two units of critical exponent even when fully charged. -/
def fanScore (W : Finset Edge) (i : Fin 7) : ℤ :=
  fanCount W i - if fan i ⊆ W then ((fan i).card : ℤ) - 2 else 0

lemma fanScore_lower (W : Finset Edge) (i : Fin 7) :
    (min (fanCount W i) 2 : ℕ) ≤ fanScore W i := by
  have ha := fanCount_le W i
  have hk := fan_card_lower i
  unfold fanScore
  by_cases h : fan i ⊆ W
  · have he := (fanCount_eq_iff W i).mpr h
    simp only [h, ite_true]
    omega
  · simp only [h, ite_false, sub_zero]
    exact_mod_cast min_le_left (fanCount W i) 2

lemma fanScore_nonneg (W : Finset Edge) (i : Fin 7) : 0 ≤ fanScore W i :=
  (Nat.cast_nonneg _).trans (fanScore_lower W i)

def coreExponent (W : Finset Edge) : ℤ :=
  W.card - (∑ i, if fan i ⊆ W then ((fan i).card : ℤ) - 2 else 0) -
    if W = Finset.univ then 12 else 0

lemma coreExponent_decompose (W : Finset Edge) :
    coreExponent W = looseCount W + ∑ i, fanScore W i -
      if W = Finset.univ then 12 else 0 := by
  unfold coreExponent fanScore
  rw [count_partition W, Nat.cast_add, Nat.cast_sum, Finset.sum_sub_distrib]
  ring

lemma coreExponent_univ : coreExponent Finset.univ = 3 := by
  decide

lemma min_sum_le_sum_min {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    min (∑ i ∈ s, a i) 2 ≤ ∑ i ∈ s, min (a i) 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    omega

lemma coreExponent_lower (W : Finset Edge) :
    (min W.card 2 : ℕ) ≤ coreExponent W := by
  by_cases h : W = Finset.univ
  · subst W
    rw [coreExponent_univ]
    have hmin := min_le_right (Finset.univ : Finset Edge).card 2
    omega
  · rw [coreExponent_decompose, ite_eq_right h, sub_zero]
    have hs : (∑ i, (min (fanCount W i) 2 : ℕ) : ℤ) ≤ ∑ i, fanScore W i :=
      Finset.sum_le_sum (fun i _ => fanScore_lower W i)
    have hs' := min_sum_le_sum_min Finset.univ (fanCount W)
    have hw := count_partition W
    have hm : min W.card 2 ≤ looseCount W + ∑ i, min (fanCount W i) 2 := by omega
    have hc : ((min W.card 2 : ℕ) : ℤ) ≤ (looseCount W : ℤ) +
        ((∑ i, min (fanCount W i) 2 : ℕ) : ℤ) := by exact_mod_cast hm
    rw [Nat.cast_sum] at hc
    linarith

/-- Admissibility of core-field sets, retaining the exact three/two quotas. -/
def CoreAdmissible (S : Finset Edge) : Prop :=
  S.card ≤ 3 ∧ ∀ i, fanCount S i ≤ 2

lemma coreExponent_admissible (S W : Finset Edge) (hS : CoreAdmissible S)
    (hSW : S ⊆ W) : (S.card : ℤ) ≤ coreExponent W := by
  by_cases h : W = Finset.univ
  · subst W
    rw [coreExponent_univ]
    exact_mod_cast hS.1
  · rw [coreExponent_decompose, ite_eq_right h, sub_zero, count_partition S,
      Nat.cast_add, Nat.cast_sum]
    apply add_le_add
    · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hSW)
    · apply Finset.sum_le_sum
      intro i _
      have hm : fanCount S i ≤ fanCount W i :=
        Finset.card_le_card (Finset.inter_subset_inter_right hSW)
      have ha := hS.2 i
      have hmin : fanCount S i ≤ min (fanCount W i) 2 := le_min hm ha
      exact (by exact_mod_cast hmin : (fanCount S i : ℤ) ≤
        (min (fanCount W i) 2 : ℕ)).trans (fanScore_lower W i)


/-- The four coordinates of a square row: two core fields and two private ones. -/
def squareSupport (τ : TwoPath) : Finset Field :=
  {Sum.inl τ.val.1, Sum.inl τ.val.2, Sum.inr (τ, 0), Sum.inr (τ, 1)}

def freshFields (W : Finset Field) (τ : TwoPath) : Finset (Fin 2) :=
  Finset.univ.filter (fun j : Fin 2 => (Sum.inr (τ, j) : Field) ∈ W)

def freshCount (W : Finset Field) (τ : TwoPath) : ℕ := (freshFields W τ).card

lemma freshCount_le (W : Finset Field) (τ : TwoPath) : freshCount W τ ≤ 2 := by
  unfold freshCount
  have h : freshFields W τ ⊆ Finset.univ := Finset.subset_univ _
  exact (Finset.card_le_card h).trans (by simp)

lemma freshCount_eq_two_iff (W : Finset Field) (τ : TwoPath) :
    freshCount W τ = 2 ↔ ∀ j : Fin 2, Sum.inr (τ, j) ∈ W := by
  classical
  simpa only [freshCount, freshFields, Finset.card_univ, Fintype.card_fin,
    Finset.mem_univ, forall_const] using
    (Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin 2)))
      (p := fun j => (Sum.inr (τ, j) : Field) ∈ W))

private lemma card_sum_prod {E T J : Type*} [Fintype E] [Fintype T] [Fintype J]
    [DecidableEq E] [DecidableEq T] [DecidableEq J] (W : Finset (E ⊕ (T × J))) :
    W.card = W.toLeft.card + ∑ t, (Finset.univ.filter
      (fun j => (Sum.inr (t, j) : E ⊕ (T × J)) ∈ W)).card := by
  classical
  calc
    W.card = ∑ x : E ⊕ (T × J), if x ∈ W then (1 : ℕ) else 0 := by simp
    _ = _ := by
      rw [Fintype.sum_sum_type]
      congr 1
      · have he : (Finset.univ.filter (fun a : E =>
              (Sum.inl a : E ⊕ (T × J)) ∈ W)) = W.toLeft := by ext; simp
        simp only [Finset.sum_boole]
        exact congrArg Finset.card he
      · rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro t _
        simp

lemma count_split (W : Finset Field) :
    W.card = W.toLeft.card + ∑ τ, freshCount W τ := by
  have hc := card_sum_prod (E := Edge) (T := TwoPath) (J := Fin 2) W
  exact hc

def freshScore (W : Finset Field) (τ : TwoPath) : ℤ :=
  freshCount W τ - if squareSupport τ ⊆ W then 2 else 0

lemma freshScore_nonneg (W : Finset Field) (τ : TwoPath) : 0 ≤ freshScore W τ := by
  unfold freshScore
  by_cases h : squareSupport τ ⊆ W
  · have hc : freshCount W τ = 2 := by
      rw [freshCount_eq_two_iff]
      intro j
      apply h
      fin_cases j <;> simp [squareSupport]
    simp [h, hc]
  · simp [h]

lemma twoPath_ne (τ : TwoPath) : τ.val.1 ≠ τ.val.2 := by
  intro he
  have hlt := τ.property.1
  rw [he] at hlt
  exact (lt_irrefl _ hlt)

lemma no_square_of_small_core (W : Finset Field) (hW : W.toLeft.card < 2)
    (τ : TwoPath) : ¬squareSupport τ ⊆ W := by
  intro h
  have hs : {τ.val.1, τ.val.2} ⊆ W.toLeft := by
    intro e he
    rw [Finset.mem_toLeft]
    apply h
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [squareSupport]
  have hc := Finset.card_le_card hs
  rw [Finset.card_pair (twoPath_ne τ)] at hc
  omega

lemma coreExponent_small (W : Finset Edge) (hW : W.card < 2) :
    coreExponent W = W.card := by
  have hn (i : Fin 7) : ¬fan i ⊆ W := by
    intro hs
    have hcard := Finset.card_le_card hs
    have hl := fan_card_lower i
    omega
  have hu : W ≠ Finset.univ := by
    intro he
    subst W
    have hc := card_edges
    simp only [Finset.card_univ] at hW
    omega
  simp [coreExponent, hn, hu]

def criticalExponent (W : Finset Field) : ℤ :=
  coreExponent W.toLeft + ∑ τ, freshScore W τ

/-- Source Lemma `sample:lem-budget`, first inequality, for the actual template. -/
theorem criticalExponent_lower (W : Finset Field) :
    ((min 2 W.card : ℕ) : ℤ) ≤ criticalExponent W := by
  have hnonneg : 0 ≤ ∑ τ, freshScore W τ :=
    Finset.sum_nonneg (fun τ _ => freshScore_nonneg W τ)
  by_cases hW : W.toLeft.card < 2
  · have he : criticalExponent W = W.card := by
      simp only [criticalExponent, coreExponent_small _ hW, freshScore,
        no_square_of_small_core W hW, ite_false, sub_zero]
      rw [count_split W, Nat.cast_add, Nat.cast_sum]
    rw [he]
    exact_mod_cast min_le_right 2 W.card
  · have hc := coreExponent_lower W.toLeft
    have hm : min W.toLeft.card 2 = 2 := by omega
    rw [hm] at hc
    have hmin : ((min 2 W.card : ℕ) : ℤ) ≤ 2 := by exact_mod_cast min_le_left 2 W.card
    unfold criticalExponent
    omega

/-- Exact admissibility from Definition 2.3 of the manuscript. -/
def Admissible (S : Finset Field) : Prop :=
  (S.toRight = ∅ ∧ CoreAdmissible S.toLeft) ∨
    ∃ τ : TwoPath, S ⊆ squareSupport τ ∧ S.card ≤ 2

/-- Source Lemma `sample:lem-budget`, the strengthened admissible-set budget. -/
theorem criticalExponent_admissible (S W : Finset Field) (hS : Admissible S)
    (hSW : S ⊆ W) : (S.card : ℤ) ≤ criticalExponent W := by
  rcases hS with ⟨hS0, hcore⟩ | ⟨τ, _, hc⟩
  · have he : S.card = S.toLeft.card := by
      have hh := Finset.card_toLeft_add_card_toRight (u := S)
      rw [hS0, Finset.card_empty, add_zero] at hh
      exact hh.symm
    rw [he]
    have hbase := coreExponent_admissible S.toLeft W.toLeft hcore
      (Finset.toLeft_subset_toLeft hSW)
    have hz : 0 ≤ ∑ τ, freshScore W τ :=
      Finset.sum_nonneg (fun τ _ => freshScore_nonneg W τ)
    unfold criticalExponent
    omega
  · have hcard := Finset.card_le_card hSW
    have hi : S.card ≤ min 2 W.card := le_min hc hcard
    exact (by exact_mod_cast hi : (S.card : ℤ) ≤
      ((min 2 W.card : ℕ) : ℤ)).trans (criticalExponent_lower W)

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
