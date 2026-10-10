import Mathlib
import OAI.Probability.ThorpCompatibility.ConditionalEntropy
import OAI.Probability.ThorpCompatibility.EntropyEstimate
import OAI.Probability.ThorpCompatibility.WeightedGibbs

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma marginalFactor_nonneg {α : Type*} [Fintype α] (θ : ℝ) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) : 0 ≤ marginalFactor θ w := by
  simp only [marginalFactor, Real.rpow_eq_pow]
  apply Real.rpow_nonneg
  exact div_nonneg (Finset.sum_nonneg (fun x _ => Real.rpow_nonneg (hw x) _))
    (Nat.cast_nonneg _)

lemma Law.marginalFactor_pos {α : Type*} [Fintype α] [Nonempty α]
    (P : Law α) (θ : ℝ) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) :
    0 < marginalFactor θ w := by
  simp only [marginalFactor, Real.rpow_eq_pow]
  exact Real.rpow_pos_of_pos (P.uniformMean_rpow_pos w hw hs _) θ

noncomputable def compatibilityWeight {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ) (a : Grid A D) : ℝ :=
  if Compatible a.1 a.2 then (∏ i, w i (a.1 i)) * (∏ k, v k (a.2 k)) else 0

lemma compatibilityWeight_nonneg {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ) (a : Grid A D) :
    0 ≤ compatibilityWeight w v a := by
  unfold compatibilityWeight
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw i _))
      (Finset.prod_nonneg (fun k _ => hv k _))
  · rfl

lemma compatibilityWeight_support {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    {a : Grid A D} (ha : 0 < compatibilityWeight w v a) :
    Compatible a.1 a.2 ∧ (∀ i, 0 < w i (a.1 i)) ∧ (∀ k, 0 < v k (a.2 k)) := by
  have hc : Compatible a.1 a.2 := by
    by_contra h
    simp [compatibilityWeight, h] at ha
  rw [compatibilityWeight, ite_eq_left hc] at ha
  refine ⟨hc, ?_, ?_⟩
  · intro i
    apply lt_of_le_of_ne (hw i _)
    intro he
    have hz : (∏ j : Fin A, w j (a.1 j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) he.symm
    simp [hz] at ha
  · intro k
    apply lt_of_le_of_ne (hv k _)
    intro he
    have hz : (∏ j : Fin D, v j (a.2 j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) he.symm
    simp [hz] at ha

lemma Law.map_support_weight {α β : Type*} [Fintype α] [Fintype β]
    (P : Law α) (f : α → β) (w : β → ℝ)
    (hs : ∀ a, 0 < P.mass a → 0 < w (f a)) (x : β) (hx : w x = 0) :
    (P.map f).mass x = 0 := by
  by_contra hn
  obtain ⟨a,he,ha⟩ := (P.map_mass_pos_iff f x).mp
    (lt_of_le_of_ne ((P.map f).nonneg x) (Ne.symm hn))
  have hw := hs a ha
  rw [he,hx] at hw
  exact lt_irrefl _ hw

lemma grid_log_weight_mean {A D : ℕ} (Q : Law (Grid A D))
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    (hs : ∀ a, 0 < Q.mass a → 0 < compatibilityWeight w v a) :
    Q.mean (fun a => Real.log (compatibilityWeight w v a)) =
      (∑ i : Fin A, (Q.map (fun a => a.1 i)).mean (fun σ => Real.log (w i σ))) +
      (∑ k : Fin D, (Q.map (fun a => a.2 k)).mean (fun σ => Real.log (v k σ))) := by
  calc
    _ = Q.mean (fun a => (∑ i, Real.log (w i (a.1 i))) +
        (∑ k, Real.log (v k (a.2 k)))) := by
      apply Q.mean_congr_support
      intro a ha
      obtain ⟨hc, hr, hd⟩ := compatibilityWeight_support w v hw hv (hs a ha)
      rw [compatibilityWeight, ite_eq_left hc,
        Real.log_mul (Finset.prod_pos (fun i _ => hr i)).ne'
          (Finset.prod_pos (fun k _ => hd k)).ne',
        Real.log_prod (fun i _ => (hr i).ne'), Real.log_prod (fun k _ => (hd k).ne')]
    _ = _ := by
      rw [Q.mean_add, Law.mean_sum, Law.mean_sum]
      simp only [Law.mean_map, Function.comp_def]

lemma grid_weight_variational {A D : ℕ} (Q : Law (Grid A D)) {θ : ℝ} (hθ : 0 < θ)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    (hs : ∀ a, 0 < Q.mass a → 0 < compatibilityWeight w v a) :
    Q.mean (fun a => Real.log (compatibilityWeight w v a)) - θ*(rowDeficit Q + colDeficit Q) ≤
      (∑ i, Real.log (marginalFactor θ (w i))) + (∑ k, Real.log (marginalFactor θ (v k))) := by
  have hwr (i : Fin A) := (Q.map (fun a => a.1 i)).weighted_gibbs_le hθ (w i) (hw i)
    (Q.map_support_weight (fun a => a.1 i) (w i) (fun a ha =>
      (compatibilityWeight_support w v hw hv (hs a ha)).2.1 i))
  have hvc (k : Fin D) := (Q.map (fun a => a.2 k)).weighted_gibbs_le hθ (v k) (hv k)
    (Q.map_support_weight (fun a => a.2 k) (v k) (fun a ha =>
      (compatibilityWeight_support w v hw hv (hs a ha)).2.2 k))
  have hr := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) => hwr i)
  have hc := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) => hvc k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hr hc
  rw [grid_log_weight_mean Q w v hw hv hs]
  unfold rowDeficit colDeficit
  linarith

lemma compatibility_log_mean_bound {A D : ℕ} (hD : 2 ≤ D) {m : ℝ}
    (hm : 0 < m) (hl : 1000 ≤ Real.log m) (hθ : 0 < 1 - 1000/Real.log m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    (hZ : 0 < ∑ a : Grid A D, compatibilityWeight w v a) :
    Real.log (uniformMean (compatibilityWeight w v)) ≤
      -(A:ℝ)*D + totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) + 1 +
      (∑ i, Real.log (marginalFactor (1-1000/Real.log m) (w i))) +
      (∑ k, Real.log (marginalFactor (1-1000/Real.log m) (v k))) := by
  let Q : Law (Grid A D) := Law.tilt (compatibilityWeight w v) (compatibilityWeight_nonneg w v hw hv) hZ
  have hs (a : Grid A D) (ha : 0 < Q.mass a) : 0 < compatibilityWeight w v a := by
    exact (div_pos_iff_of_pos_right hZ).mp ha
  have hQ (a : Grid A D) (ha : 0 < Q.mass a) : Compatible a.1 a.2 :=
    (compatibilityWeight_support w v hw hv (hs a ha)).1
  have hE := grid_entropy_estimate hD Q hQ hm hl hmgf
  have hW := grid_weight_variational Q hθ w v hw hv hs
  have hG := Law.tilt_log_partition (compatibilityWeight w v) (compatibilityWeight_nonneg w v hw hv) hZ
  change Q.mean _ - Q.uniformDeficit = _ at hG
  linarith

end ThorpCompatibility

end OAI
