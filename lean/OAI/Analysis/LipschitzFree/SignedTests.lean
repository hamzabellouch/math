import OAI.Analysis.LipschitzFree.Model

namespace OAI

/-!
# Signed variation, scalar extension, and incidence averaging
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section Records

variable {D S : Type*}

def Exceptional (r : D → S → ℕ) (e : D) (j : S) : Prop :=
  ∀ g : D, g ≠ e → r g j < r e j

theorem exceptional_unique {r : D → S → ℕ} {e f : D} {j : S}
    (he : Exceptional r e j) (hf : Exceptional r f j) : e = f := by
  by_contra h
  exact (Nat.lt_asymm (he f (Ne.symm h)) (hf e h))

theorem exceptional_of_extensions {r t : D → S → ℕ} {e f : D} {j k : S}
    (hr : ∀ g : D, g ≠ f → 1 + t g k ≤ r e j)
    (ht : ∀ g : D, g ≠ e → 1 + r g j ≤ t f k) :
    Exceptional r e j ∨ Exceptional t f k := by
  classical
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  simp only [Exceptional, not_forall, not_lt] at h₁ h₂
  obtain ⟨g, hge, hg⟩ := h₁
  obtain ⟨a, haf, ha⟩ := h₂
  have hrg := hr a haf
  have hta := ht g hge
  omega

end Records

section SignedTests

variable {S : Type*} [Fintype S]

def totalVariation (μ : S → ℝ) : ℝ := ∑ j, |μ j|

def variationOn (μ : S → ℝ) (E : Set S) : ℝ := by
  classical
  exact ∑ j, if j ∈ E then |μ j| else 0

def pairing (μ f : S → ℝ) : ℝ := ∑ j, μ j * f j

theorem pairing_error_le (μ f b : S → ℝ) (E : Set S) (C : ℝ)
    (heq : ∀ j, j ∉ E → f j = b j)
    (hbound : ∀ j, |f j - b j| ≤ C) :
    |pairing μ f - pairing μ b| ≤ C * variationOn μ E := by
  classical
  unfold pairing variationOn
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    |∑ j, (μ j * f j - μ j * b j)| ≤
        ∑ j, |μ j * f j - μ j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, C * (if j ∈ E then |μ j| else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ E
      · rw [ite_eq_left hj, ← mul_sub, abs_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hbound j) (abs_nonneg _)
      · simp [hj, heq j hj]

theorem opposing_pairing_lower (μ ν f b c : S → ℝ) (E F : Set S) (L : ℝ)
    (hf : ∀ j, |f j| ≤ L)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (he : ∀ j, j ∉ E → f j = b j)
    (hF : ∀ j, j ∉ F → f j = -c j) :
    pairing μ b + pairing ν c - 2 * L * (variationOn μ E + variationOn ν F) ≤
      pairing μ f - pairing ν f := by
  have h₁ := pairing_error_le μ f b E (2 * L) he (fun j => by
    have := abs_sub (f j) (b j)
    rw [abs_of_nonneg (hb j).1] at this
    linarith [hf j, (hb j).2])
  have h₂ := pairing_error_le ν f (fun j => -c j) F (2 * L) hF
    (fun j => by
      have := abs_sub (f j) (-c j)
      rw [abs_neg, abs_of_nonneg (hc j).1] at this
      linarith [hf j, (hc j).2])
  have hneg : pairing ν (fun j => -c j) = -pairing ν c := by
    simp [pairing, Finset.sum_neg_distrib]
  rw [hneg] at h₂
  have h₁' := (abs_le.mp h₁).1
  have h₂' := (abs_le.mp h₂).2
  nlinarith

end SignedTests
section

variable {N : Type*} [MetricSpace N]

theorem bounded_scalar_extension (P : Set N) (v : N → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hv : LipschitzOnWith 1 v P) (hvb : ∀ j ∈ P, |v j| ≤ L) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧ Set.EqOn f v P := by
  obtain ⟨F, hF, hFV⟩ := hv.extend_real
  refine ⟨fun z => max (-L) (min L (F z)), ?_, ?_, ?_⟩
  · exact (hF.const_min L).const_max (-L)
  · intro z
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · intro z hz
    change max (-L) (min L (F z)) = v z
    rw [← hFV hz]
    obtain ⟨hl, hu⟩ := abs_le.mp (hvb z hz)
    rw [min_eq_right hu, max_eq_right hl]

theorem opposing_scalar_extension (P Q : Set N) (b c : N → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbLip : LipschitzWith 1 b) (hcLip : LipschitzWith 1 c)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (hcross : ∀ j ∈ P, ∀ k ∈ Q, dist j k < 2 * L → b j = 0 ∧ c k = 0) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      Set.EqOn f b P ∧ Set.EqOn f (fun z => -c z) Q := by
  classical
  have hzero : ∀ j ∈ P ∩ Q, b j = 0 ∧ c j = 0 := by
    intro j hj
    by_cases hpos : 0 < L
    · exact hcross j hj.1 j hj.2 (by simp; linarith)
    · have hz : L = 0 := le_antisymm (le_of_not_gt hpos) hL
      constructor <;> linarith [(hb j).1, (hb j).2, (hc j).1, (hc j).2]
  let v : N → ℝ := fun j => if j ∈ P then b j else -c j
  have hvP : Set.EqOn v b P := fun j hj => ite_eq_left hj
  have hvQ : Set.EqOn v (fun z => -c z) Q := by
    intro j hj
    by_cases hp : j ∈ P
    · have hz := hzero j ⟨hp, hj⟩
      simp [v, hp, hz.1, hz.2]
    · exact ite_eq_right hp
  have hcross' : ∀ j ∈ P, ∀ k ∈ Q, |b j - -c k| ≤ dist j k := by
    intro j hj k hk
    by_cases hd : dist j k < 2 * L
    · obtain ⟨hz, hz'⟩ := hcross j hj k hk hd
      simp [hz, hz', dist_nonneg]
    · rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg (hb j).1 (hc k).1)]
      linarith [(hb j).2, (hc k).2, le_of_not_gt hd]
  have hvLip : LipschitzOnWith 1 v (P ∪ Q) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro j hj k hk
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases hj with hj | hj <;> rcases hk with hk | hk
    · rw [hvP hj, hvP hk]
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hbLip.dist_le_mul j k
    · rw [hvP hj, hvQ hk]
      exact hcross' j hj k hk
    · rw [hvQ hj, hvP hk, abs_sub_comm, dist_comm]
      exact hcross' k hk j hj
    · rw [hvQ hj, hvQ hk]
      have := hcLip.dist_le_mul j k
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, neg_sub_neg, abs_sub_comm] using this
  have hvBound : ∀ j ∈ P ∪ Q, |v j| ≤ L := by
    intro j hj
    rcases hj with hj | hj
    · rw [hvP hj, abs_of_nonneg (hb j).1]
      exact (hb j).2
    · rw [hvQ hj, abs_neg, abs_of_nonneg (hc j).1]
      exact (hc j).2
  obtain ⟨f, hf, hfB, hfv⟩ := bounded_scalar_extension (P ∪ Q) v L hL hvLip hvBound
  exact ⟨f, hf, hfB, fun j hj => (hfv (Or.inl hj)).trans (hvP hj),
    fun j hj => (hfv (Or.inr hj)).trans (hvQ hj)⟩

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

theorem sum_variationOn_le (μ : S → ℝ) (E : D → Set S)
    (hunique : ∀ j e f, j ∈ E e → j ∈ E f → e = f) :
    (∑ e, variationOn μ (E e)) ≤ totalVariation μ := by
  classical
  unfold variationOn totalVariation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ∃ e, j ∈ E e
  · obtain ⟨e, he⟩ := hj
    rw [Finset.sum_eq_single e]
    · simp only [ite_eq_left he, le_refl]
    · intro f _ hfe
      exact ite_eq_right (fun hf => hfe (hunique j f e hf he))
    · simp
  · have hnone : ∀ e, j ∉ E e := by simpa using hj
    simp only [ite_eq_right (hnone _), Finset.sum_const_zero]
    exact abs_nonneg _

theorem variationOn_nonneg (μ : S → ℝ) (E : Set S) : 0 ≤ variationOn μ E := by
  classical
  unfold variationOn
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem variationOn_le (μ : S → ℝ) (E : Set S) : variationOn μ E ≤ totalVariation μ := by
  classical
  unfold variationOn totalVariation
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp [abs_nonneg]

theorem signed_incidence_obstruction [Nonempty X] [Nonempty D]
    (μ : X → S → ℝ) (E : X → D → Set S) (bad : Finset X)
    (rev : (X × D) ≃ (X × D)) (p V : ℝ)
    (hp : 0 < p) (hV : 0 ≤ V)
    (hTV : ∀ x, totalVariation (μ x) ≤ V)
    (hgood : ∀ x, x ∉ bad → ∀ j e f, j ∈ E x e → j ∈ E x f → e = f)
    (hdegree : 20 * V < (Fintype.card D : ℝ))
    (hbad : 20 * V * (bad.card : ℝ) < (Fintype.card X : ℝ))
    (hedge : ∀ e : X × D,
      3 * (10 * p) / 2 - 2 * (10 * p) *
        (variationOn (μ e.1) (E e.1 e.2) +
         variationOn (μ (rev e).1) (E (rev e).1 (rev e).2)) ≤ 2 * p) : False := by
  classical
  let err : X × D → ℝ := fun e => variationOn (μ e.1) (E e.1 e.2)
  let a : ℝ := Fintype.card X
  let d : ℝ := Fintype.card D
  let b : ℝ := bad.card
  have ha : 0 < a := by dsimp [a]; exact_mod_cast Fintype.card_pos (α := X)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos (α := D)
  have hb : 0 ≤ b := by positivity
  have hvtx : ∀ x, (∑ e, err (x, e)) ≤ V + if x ∈ bad then d * V else 0 := by
    intro x
    by_cases hx : x ∈ bad
    · simp only [ite_eq_left hx]
      have hsum : (∑ e, err (x, e)) ≤ d * V := by
        calc
          _ ≤ ∑ _e : D, V := Finset.sum_le_sum (fun e _ =>
            (variationOn_le (μ x) (E x e)).trans (hTV x))
          _ = _ := by simp [d]
      linarith
    · simp only [ite_eq_right hx, add_zero]
      exact (sum_variationOn_le (μ x) (E x) (hgood x hx)).trans (hTV x)
  have hsum : (∑ e, err e) ≤ a * V + b * (d * V) := by
    calc
      _ = ∑ x, ∑ e, err (x, e) := Fintype.sum_prod_type _
      _ ≤ ∑ x, (V + if x ∈ bad then d * V else 0) :=
        Finset.sum_le_sum (fun x _ => hvtx x)
      _ = _ := by simp [Finset.sum_add_distrib, a, b]
  have hsmall : 10 * (∑ e, err e) < a * d := by
    have hd' : 20 * V < d := hdegree
    have hb' : 20 * V * b < a := hbad
    have h₁ := mul_lt_mul_of_pos_left hd' ha
    have h₂ := mul_lt_mul_of_pos_left hb' hd
    nlinarith
  have hreverse : (∑ e, err (rev e)) = ∑ e, err e := Equiv.sum_comp rev err
  have hsumedge := Finset.sum_le_sum (s := (Finset.univ : Finset (X × D)))
    (fun e _ => hedge e)
  change (∑ e, (3 * (10 * p) / 2 - 2 * (10 * p) *
      (err e + err (rev e)))) ≤ ∑ _e : X × D, 2 * p at hsumedge
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsumedge
  rw [hreverse] at hsumedge
  have hcard : (Fintype.card (X × D) : ℝ) = a * d := by simp [a, d]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsumedge
  have hap : 0 < a * d := mul_pos ha hd
  have h₃ := mul_lt_mul_of_pos_left hsmall hp
  nlinarith

end DiscreteFree

end

end OAI
