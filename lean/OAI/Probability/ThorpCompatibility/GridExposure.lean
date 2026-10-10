import Mathlib
import OAI.Probability.ThorpCompatibility.Prediction
import OAI.Probability.ThorpCompatibility.GridEntropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
abbrev PastSpace (A D : ℕ) :=
  (Rows A D × (Fin D → Option (Equiv.Perm (Fin A)))) × (Fin A → Option (Fin A))

noncomputable def gridAllowed {A D : ℕ} (k : Fin D) (i : Fin A)
    (y : PastSpace A D) (w : Fin A) : Prop :=
  ∀ h : Fin A, ∀ σ : Equiv.Perm (Fin A),
    y.1.2 (y.1.1 h ((y.1.1 i).symm k)) = some σ → σ h ≠ w

lemma gridAllowed_actual {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) :
    gridAllowed k i (gridPast e k i a) (a.2 k i) := by
  intro h σ hσ heq
  dsimp [gridPast, priorCols] at hσ
  split_ifs at hσ with hlt
  · have hσ' : a.2 (a.1 h ((a.1 i).symm k)) = σ := Option.some.inj hσ
    have heq' : a.2 (a.1 h ((a.1 i).symm k)) h =
        a.2 (a.1 i ((a.1 i).symm k)) i := by simpa [hσ'] using heq
    have hi : h = i := ha _ heq'
    simp [hi] at hlt

noncomputable def outputEquiv {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) : Equiv.Perm (Fin A) :=
  Equiv.ofBijective (fun h => a.2 (a.1 h j) h)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨ha j, rfl⟩)

@[simp] lemma outputEquiv_apply {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) (h : Fin A) : outputEquiv a ha j h = a.2 (a.1 h j) h := rfl

noncomputable def columnFor {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) (w : Fin A) : Fin D := a.1 ((outputEquiv a ha j).symm w) j

@[simp] lemma columnFor_output {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) (h : Fin A) : columnFor a ha j (outputEquiv a ha j h) = a.1 h j := by
  simp only [columnFor, Equiv.symm_apply_apply]

lemma columnFor_actual {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (k : Fin D) (i : Fin A) : columnFor a ha ((a.1 i).symm k) (a.2 k i) = k := by
  have hout : outputEquiv a ha ((a.1 i).symm k) i = a.2 k i := by simp
  rw [← hout, columnFor_output]
  simp

lemma gridAllowed_iff_rank {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (w : Fin A) :
    gridAllowed k i (gridPast e k i a) w ↔ e k ≤ e (columnFor a ha ((a.1 i).symm k) w) := by
  let j := (a.1 i).symm k
  let h := (outputEquiv a ha j).symm w
  have hout : a.2 (a.1 h j) h = w := (outputEquiv a ha j).apply_symm_apply w
  change gridAllowed k i (gridPast e k i a) w ↔ e k ≤ e (a.1 h j)
  constructor
  · intro hall
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hx := hall h (a.2 (a.1 h j)) (by simp [gridPast, priorCols, j, hlt])
    exact hx hout
  · intro hle l σ hσ heq
    dsimp [gridPast, priorCols] at hσ
    split_ifs at hσ with hlt
    · have hσ' : a.2 (a.1 l j) = σ := Option.some.inj hσ
      have hlh : l = h := ha j (by change a.2 (a.1 l j) l = a.2 (a.1 h j) h; rw [hσ', heq, hout])
      subst l
      exact (not_lt_of_ge hle) hlt

noncomputable def columnPrediction {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    (v : Fin A → Option (Fin A)) : Law (Fin A) :=
  Q.predict (fun a => a.2 k i) (colHistory k i) v

noncomputable def columnLight {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (v : Fin A → Option (Fin A)) (w : Fin A) : Prop :=
  (columnPrediction Q k i v).mass w ≤ H / ((A - (i : ℕ) : ℕ) : ℝ)

noncomputable def columnCost {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (a : Grid A D) : ℝ :=
  if columnLight Q H k i (colHistory k i a) (a.2 k i) then
    -Real.log ((columnPrediction Q k i (colHistory k i a)).prob
      (fun w => columnLight Q H k i (colHistory k i a) w ∧
        gridAllowed k i (gridPast e k i a) w) /
          (columnPrediction Q k i (colHistory k i a)).prob (columnLight Q H k i (colHistory k i a)))
  else 0

lemma columnCost_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (a : Grid A D) :
    0 ≤ columnCost Q H e k i a := by
  unfold columnCost
  split_ifs
  · exact Law.light_cost_nonneg _ _ _
  · rfl

lemma columnCost_le_comparison {A D : ℕ} (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2) (H : ℝ)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) :
    Q.mean (columnCost Q H e k i) ≤
      Q.condEntropy (fun a => a.2 k i) (colHistory k i) -
      Q.condEntropy (fun a => a.2 k i) (gridPast e k i) := by
  have h := Q.condEntropy_light_comparison (fun a => a.2 k i) (gridPast e k i)
    (fun y => columnPrediction Q k i y.2)
    (fun y => columnLight Q H k i y.2) (gridAllowed k i)
    (fun a ha => Q.predict_pos _ _ ha)
    (fun a ha => gridAllowed_actual a (hQ a ha) e k i)
  change Q.mean (columnCost Q H e k i) ≤
    -Q.mean (fun a => Real.log ((Q.predict (fun a => a.2 k i)
      (colHistory k i) (colHistory k i a)).mass (a.2 k i))) - _ at h
  rwa [Q.mean_predict_log, neg_neg] at h

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI
