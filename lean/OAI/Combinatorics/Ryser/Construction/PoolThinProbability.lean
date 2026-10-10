import OAI.Combinatorics.Ryser.Construction.PoolThinGeometry
import OAI.Combinatorics.Ryser.Probability.Product
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def poolThinLaw (G : Type*) [Fintype G] [DecidableEq G] (K : ℕ) :
    FiniteLaw (G → Fin K → Point F) :=
  FiniteLaw.pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))

def poolGroupBad {K : ℕ} (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (a : Fin K → Point F) : Prop :=
  ∃ j, ShiftHits W S p ell (a j)

variable {G : Type*} [Fintype G] [DecidableEq G] {K : ℕ}

def poolBadGroups (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (ω : G → Fin K → Point F) : Finset G :=
  Finset.univ.filter (fun i => poolGroupBad (W i) (S i) p ell (ω i))

def PoolThin (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (ω : G → Fin K → Point F) : Prop :=
  ∀ p ell, ¬ Incidence p ell → (poolBadGroups W S p ell ω).card ≤ 5

theorem uniform_prob_poolGroupBad_le
    (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Fin K → Point F)).prob (poolGroupBad W S p ell) ≤
      (K : ℝ) * W.card * S.card / (Fintype.card F : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ j : Fin K, (FiniteLaw.uniform (Fin K → Point F)).prob
        (fun a => ShiftHits W S p ell (a j)) :=
      FiniteLaw.prob_exists_le _ _
    _ = ∑ _j : Fin K, (FiniteLaw.uniform (Point F)).prob
        (ShiftHits W S p ell) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← FiniteLaw.pi_uniform]
      exact FiniteLaw.prob_pi_coordinate
        (fun _ : Fin K => FiniteLaw.uniform (Point F)) j (ShiftHits W S p ell)
    _ ≤ ∑ _j : Fin K,
        (W.card : ℝ) * S.card / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun _ _ => uniform_prob_shiftHits_le W S p ell hp)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem uniform_prob_poolGroupBad_le_of_card
    (W : Finset (Point F)) (S : Finset (Direction F))
    (w s : ℕ) (hW : W.card ≤ w) (hS : S.card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Fin K → Point F)).prob (poolGroupBad W S p ell) ≤
      (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2 := by
  refine (uniform_prob_poolGroupBad_le W S p ell hp).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left K hW) hS

theorem poolThinLaw_prob_all_bad_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) (T : Finset G) :
    (poolThinLaw (F := F) G K).prob
        (fun ω => ∀ i ∈ T, poolGroupBad (W i) (S i) p ell (ω i)) ≤
      ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ T.card := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  change (FiniteLaw.pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))).prob
    (fun ω => ∀ i, i ∈ T → poolGroupBad (W i) (S i) p ell (ω i)) ≤ b ^ T.card
  rw [FiniteLaw.prob_pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))
    (fun i a => i ∈ T → poolGroupBad (W i) (S i) p ell a)]
  calc
    _ ≤ ∏ i : G, if i ∈ T then b else 1 := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact FiniteLaw.prob_nonneg _ _
      · intro i _
        by_cases hi : i ∈ T
        · simpa [hi] using
            uniform_prob_poolGroupBad_le_of_card (K := K)
              (W i) (S i) w s (hW i) (hS i) p ell hp
        · simp [hi]
    _ = b ^ T.card := by
      rw [Finset.prod_ite_mem_eq]
      exact Finset.prod_const b

theorem poolThinLaw_prob_six_bad_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (poolThinLaw (F := F) G K).prob
        (fun ω => 6 ≤ (poolBadGroups W S p ell ω).card) ≤
      (Fintype.card G : ℝ) ^ 6 *
        ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ 6 := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let C : Finset (Finset G) := (Finset.univ : Finset G).powersetCard 6
  change (poolThinLaw (F := F) G K).prob
    (fun ω => 6 ≤ (poolBadGroups W S p ell ω).card) ≤
      (Fintype.card G : ℝ) ^ 6 * b ^ 6
  calc
    _ ≤ (poolThinLaw (F := F) G K).prob
        (fun ω => ∃ T : ↥C, ∀ i ∈ T.val, poolGroupBad (W i) (S i) p ell (ω i)) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
      refine ⟨⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hT hi)).2
    _ ≤ ∑ T : ↥C, (poolThinLaw (F := F) G K).prob
        (fun ω => ∀ i ∈ T.val, poolGroupBad (W i) (S i) p ell (ω i)) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _T : ↥C, b ^ 6 := by
      apply Finset.sum_le_sum
      intro T _
      have hT := poolThinLaw_prob_all_bad_le (K := K) W S w s hW hS p ell hp T.val
      have hcard : T.val.card = 6 := (Finset.mem_powersetCard.mp T.property).2
      simpa only [hcard] using hT
    _ = ((Fintype.card G).choose 6 : ℝ) * b ^ 6 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        C, Finset.card_powersetCard, nsmul_eq_mul]
    _ ≤ (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _)
      exact_mod_cast Nat.choose_le_pow (Fintype.card G) 6

theorem prob_not_poolThin_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s) :
    (poolThinLaw (F := F) G K).prob (fun ω => ¬ PoolThin W S ω) ≤
      (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) + 1) *
        (Fintype.card G : ℝ) ^ 6 *
          ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ 6 := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by positivity
  change (poolThinLaw (F := F) G K).prob (fun ω => ¬ PoolThin W S ω) ≤
    (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) + 1) *
      (Fintype.card G : ℝ) ^ 6 * b ^ 6
  calc
    _ ≤ (poolThinLaw (F := F) G K).prob
        (fun ω => ∃ z : Point F × AffineLine F,
          ¬ Incidence z.1 z.2 ∧ 6 ≤ (poolBadGroups W S z.1 z.2 ω).card) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      by_contra hn
      apply hω
      intro p ell hp
      by_contra hcard
      apply hn
      refine ⟨(p, ell), hp, ?_⟩
      change 6 ≤ (poolBadGroups W S p ell ω).card
      omega
    _ ≤ ∑ z : Point F × AffineLine F, (poolThinLaw (F := F) G K).prob
        (fun ω => ¬ Incidence z.1 z.2 ∧
          6 ≤ (poolBadGroups W S z.1 z.2 ω).card) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _z : Point F × AffineLine F, (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hp : Incidence z.1 z.2
      · simpa [hp] using hB
      · simpa [hp] using
          poolThinLaw_prob_six_bad_le (K := K) W S w s hW hS z.1 z.2 hp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        card_direction, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.Construction

end

end OAI
