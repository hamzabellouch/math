import Mathlib
import OAI.Probability.ThorpCompatibility.RandomExclusion
import OAI.Probability.ThorpCompatibility.GridExposure

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
noncomputable def cellRows {α β : Type*} [Fintype α]
    (r : α → Equiv.Perm β) (b : β × β) : Finset α :=
  Finset.univ.filter (fun i => r i b.1 = b.2)

noncomputable def clumpCount {α β : Type*} [Fintype α] [Fintype β]
    (H : ℝ) (r : α → Equiv.Perm β) : ℕ :=
  ∑ b : β × β, if H < (cellRows r b).card then (cellRows r b).card else 0

lemma protected_mass_le {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j k : Fin D) (B : Law (Fin A)) (b : ℝ) (hb : ∀ w, B.mass w ≤ b) :
    B.prob (fun w => columnFor a ha j w = k) ≤ (cellRows a.1 (j,k)).card * b := by
  have he : B.prob (fun w => columnFor a ha j w = k) =
      ∑ h ∈ cellRows a.1 (j,k), B.mass (outputEquiv a ha j h) := by
    unfold Law.prob
    rw [cellRows, Finset.sum_filter]
    symm
    apply Fintype.sum_equiv (outputEquiv a ha j)
    intro h
    simp only [columnFor_output]
    by_cases hh : a.1 h j = k <;> simp [hh]
  rw [he]
  calc
    _ ≤ ∑ _h ∈ cellRows a.1 (j,k), b := Finset.sum_le_sum (fun h _ => hb _)
    _ = _ := by simp

lemma light_restrict_mass_le {α : Type*} [Fintype α] (P : Law α) {b : ℝ}
    (hb : 0 ≤ b) (hL : 1/2 ≤ P.prob (fun w => P.mass w ≤ b)) (w : α) :
    (P.restrict (fun w => P.mass w ≤ b)).mass w ≤ 2 * b := by
  have hp : 0 < P.prob (fun w => P.mass w ≤ b) := by linarith
  rw [P.restrict_mass _ hp]
  split_ifs with hw
  · apply (div_le_iff₀ hp).mpr
    nlinarith
  · simp [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb]

noncomputable def entryClumpSize {A D : ℕ} (k : Fin D) (i : Fin A) (a : Grid A D) : ℕ :=
  (cellRows a.1 ((a.1 i).symm k, k)).card

noncomputable def exposureError (A D : ℕ) (H K : ℝ) (i : Fin A) : ℝ :=
  (1 + Real.log (D : ℝ)) / D +
    (2 * K * H / ((A - (i : ℕ) : ℕ) : ℝ)) * (1 + Real.log (D : ℝ))

lemma exposureError_nonneg {A D : ℕ} (hD : 1 ≤ D) {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (i : Fin A) : 0 ≤ exposureError A D H K i := by
  have hlog : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  unfold exposureError
  positivity

lemma average_columnCost_good {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (a : Grid A D) (hQa : 0 < Q.mass a) (ha : Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (k : Fin D) (i : Fin A)
    (hL : 1/2 ≤ (columnPrediction Q k i (colHistory k i a)).prob
      (columnLight Q H k i (colHistory k i a)))
    (haL : columnLight Q H k i (colHistory k i a) (a.2 k i))
    (hK : (entryClumpSize k i a : ℝ) ≤ K) :
    1 - exposureError A D H K i ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => columnCost Q H e k i a) := by
  let P := columnPrediction Q k i (colHistory k i a)
  let L := columnLight Q H k i (colHistory k i a)
  let B := P.restrict L
  let j := (a.1 i).symm k
  have hpL : 0 < P.prob L := by dsimp [P, L]; linarith
  have hBpos : 0 < B.mass (a.2 k i) := by
    rw [show B.mass (a.2 k i) = (P.restrict L).mass (a.2 k i) from rfl,
      P.restrict_mass L hpL, ite_eq_left haL]
    exact div_pos (Q.predict_pos _ _ hQa) hpL
  have hα : 0 < B.prob (fun w => columnFor a ha j w = k) :=
    lt_of_lt_of_le hBpos (B.mass_le_prob _ (columnFor_actual a ha k i))
  have hu : (0 : ℝ) < (A - (i : ℕ) : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt i.isLt
  have hbound (w : Fin A) : B.mass w ≤ 2 * (H / ((A - (i : ℕ) : ℕ) : ℝ)) :=
    light_restrict_mass_le P (div_nonneg hH hu.le) hL w
  have hαbound : B.prob (fun w => columnFor a ha j w = k) ≤
      2 * K * H / ((A - (i : ℕ) : ℕ) : ℝ) := by
    have h₁ := protected_mass_le a ha j k B _ hbound
    have h₂ := mul_le_mul_of_nonneg_right hK (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (div_nonneg hH hu.le))
    dsimp [entryClumpSize] at h₂
    dsimp [j] at h₁
    calc
      _ ≤ (cellRows a.1 ((a.1 i).symm k, k)).card * (2 * (H / ((A - (i : ℕ) : ℕ) : ℝ))) := h₁
      _ ≤ K * (2 * (H / ((A - (i : ℕ) : ℕ) : ℝ))) := h₂
      _ = _ := by ring
  have hcost (e : Equiv.Perm (Fin D)) : columnCost Q H e k i a =
      -Real.log (B.prob (fun w => e k ≤ e (columnFor a ha j w))) := by
    unfold columnCost
    rw [ite_eq_left haL]
    rw [show B.prob (fun w => e k ≤ e (columnFor a ha j w)) =
      P.prob (fun w => L w ∧ gridAllowed k i (gridPast e k i a) w) / P.prob L by
        rw [show B = P.restrict L from rfl, P.restrict_prob L _ hpL]
        congr 2
        funext w
        rw [gridAllowed_iff_rank]]
  simp_rw [hcost]
  have h := random_order_exclusion hD B (columnFor a ha j) k hα
  have hlog : 0 ≤ 1 + Real.log (D : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast (by omega : 1 ≤ D))
    linarith
  have hmul := mul_le_mul_of_nonneg_right hαbound hlog
  dsimp [exposureError]
  linarith

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI
