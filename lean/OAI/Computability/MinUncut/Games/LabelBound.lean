import Mathlib
import OAI.Computability.MinUncut.Games.Basic

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

variable [Fintype α] [Nonempty α]

theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h

end

open scoped BigOperators

noncomputable section

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

theorem mem_profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) (k : κ) (s : S) : P k s ∈ profileThresholds P := by
  classical
  exact List.mem_map.mpr ⟨(k, s), by simp, rfl⟩

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

def sharedProfileLeft (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (L x).weight

def sharedProfileRight (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (R y).weight

def sharedProfileReject (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (y : Q₂) : ℝ :=
  eventMass (rectangleWeight (sharedProfileThresholds L R))
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s))

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

theorem uniformRejectionRate_nonnegative (S : Type*) [Fintype S] [Nonempty S] :
    0 ≤ uniformRejectionRate S := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hc₁ : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hc).2 (by simpa using hc₁)

theorem uniformRejectionRate_lt_one (S : Type*) [Fintype S] [Nonempty S] :
    uniformRejectionRate S < 1 := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hp : (0 : ℝ) < 1 / (Fintype.card S : ℝ) := div_pos (by norm_num) hc
  dsimp [uniformRejectionRate]
  linarith

theorem sharedProfileReject_nonnegative [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : 0 ≤ sharedProfileReject L R x y := by
  exact eventMass_nonneg _ _
    (rectangleDistribution (α := S) (sharedProfileThresholds L R)).nonnegative

theorem sharedProfile_reject_le_rate [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : sharedProfileReject L R x y ≤ uniformRejectionRate S := by
  let thresholds := sharedProfileThresholds L R
  have hsum : (∑ s : RectangleSeed thresholds S, rectangleWeight thresholds s) = 1 :=
    (rectangleDistribution (α := S) thresholds).normalized
  have hcomp := eventMass_complement (rectangleWeight thresholds)
    (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) hsum
  have hu : eventMass (rectangleWeight thresholds)
      (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) =
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) := by
    change eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds (L x).weight s ||
        rectangleAccept thresholds (R y).weight s) = _
    rw [rectangle_union_mass thresholds (L x).weight (R y).weight
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))]
    rw [unionMass_eq (L x).weight (R y).weight (L x).normalized (R y).normalized]
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hquot : 1 / (Fintype.card S : ℝ) ≤
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  rw [hu] at hcomp
  change eventMass (rectangleWeight thresholds)
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s)) ≤
      1 - 1 / (Fintype.card S : ℝ)
  linarith

private theorem nonnegative_powers_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ) : a ^ n ≤ b ^ n := by
  have hb : 0 ≤ b := le_trans ha hab
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg hb n)

theorem sharedProfile_label_diagonal_bound [Nonempty S] [DecidableEq S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) (fallback a : S) (n : ℕ) :
    min ((L x).weight a) ((R y).weight a) /
        (1 + totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      traceAverage (rectangleWeight (sharedProfileThresholds L R)) n
        (localDiagonal (sharedProfileLeft L R x) (sharedProfileRight L R y)
          Prod.fst fallback a) := by
  have hp := nonnegative_powers_mono (sharedProfileReject L R x y)
    (uniformRejectionRate S) (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hm : 0 ≤ min ((L x).weight a) ((R y).weight a) /
      (1 + totalVariation (L x).weight (R y).weight) :=
    div_nonneg (le_min ((L x).nonnegative a) ((R y).nonnegative a)) (by linarith)
  have hsurv :
      min ((L x).weight a) ((R y).weight a) /
          (1 + totalVariation (L x).weight (R y).weight) *
          (1 - uniformRejectionRate S ^ n) ≤
        min ((L x).weight a) ((R y).weight a) /
          (1 + totalVariation (L x).weight (R y).weight) *
          (1 - sharedProfileReject L R x y ^ n) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  refine hsurv.trans ?_
  simpa only [sharedProfileReject, sharedProfileLeft, sharedProfileRight] using
    rectangle_label_diagonal_bound (sharedProfileThresholds L R)
      (L x).weight (R y).weight fallback a
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))
      (L x).normalized (R y).normalized n

theorem exists_uniformRejectionRate_pow_lt (S : Type*) [Fintype S] [Nonempty S]
    (η : ℝ) (hη : 0 < η) : ∃ n : ℕ, uniformRejectionRate S ^ n < η := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (uniformRejectionRate_nonnegative S) (uniformRejectionRate_lt_one S)
  exact (ht.eventually (gt_mem_nhds hη)).exists

end

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
