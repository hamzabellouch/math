import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SmearRepulsion
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombSelfBound

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma smearPair_self_bound {η : Space → ℝ} (hm : Measurable η) (hn : ∀ x, 0 ≤ η x)
    {R b : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b)
    (hB : ∀ x, η x ≤ b⁻¹^3) (h1 : ∫ x : Space, η x = 1) :
    smearPair η 0 0 ≤ (2*Real.pi+1)/b := by
  have haB : ∀ x, |η x| ≤ b⁻¹^3 := fun x => by rw [abs_of_nonneg (hn x)]; exact hB x
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  have hi := bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport haB
  have hp := bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport haB (5/3 : ENNReal)
  have hc : ∀ x, CoulombAnalysis.tfPotential η x ≤ (2*Real.pi+1)/b := by
    intro x
    have hh := bounded_density_potential_bound hi hp hn hB hb x
    rw [h1] at hh
    convert hh using 1; field_simp
  have hzero : translatedDensity η 0 = η := by funext x; simp only [translatedDensity,sub_zero]
  have hii := smearPair_integrable hm hs haB 0 0
  rw [hzero] at hii
  rw [smearPair,hzero,coulomb_double_eq_potential hii]
  calc
    _ ≤ ∫ x : Space, η x*((2*Real.pi+1)/b) :=
      integral_mono (coulomb_potential_pair_integrable hii) (hi.mul_const _)
        (fun x => mul_le_mul_of_nonneg_left (hc x) (hn x))
    _ = _ := by rw [integral_mul_const,h1,one_mul]

theorem retained_coulomb_lower {n : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R b : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b) (hB : ∀ x, η x ≤ b⁻¹^3)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Fin n → Space) (hy : Function.Injective y) :
    (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) -
      ((2*Real.pi+1)/2)*(n:ℝ)/b ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖y i-y j‖ else 0 := by
  have hlo := retained_coulomb_lower_self hm hn hR hs hB hr h1 y hy
  have hh := mul_le_mul_of_nonneg_left (smearPair_self_bound hm hn hs hb hB h1)
    (show 0 ≤ (n:ℝ)*(1/2:ℝ) by positivity)
  calc
    _ ≤ (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) -
      (n:ℝ)*(1/2:ℝ)*smearPair η 0 0 := by
      have he : ((2*Real.pi+1)/2)*(n:ℝ)/b = (n:ℝ)*(1/2:ℝ)*((2*Real.pi+1)/b) := by ring
      rw [he]
      exact sub_le_sub_left hh _
    _ ≤ _ := hlo

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma sum_embedding_le_univ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) {f : κ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ i : ι, f (e i) ≤ ∑ j : κ, f j := by
  classical
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf i)

lemma retained_pair_sum_le {n k : ℕ} (x : Fin n → Space) (e : Fin k ↪ Fin n) :
    (∑ i : Fin k, ∑ j : Fin k, if i < j then 1/‖x (e i)-x (e j)‖ else 0) ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖x i-x j‖ else 0 := by
  have he (i j : Fin k) : (if i ≠ j then 1/‖x (e i)-x (e j)‖ else 0) =
      (if e i ≠ e j then 1/‖x (e i)-x (e j)‖ else 0) := by simp only [ne_eq,e.injective.eq_iff]
  have h := calc
    (∑ i : Fin k, ∑ j : Fin k, if i ≠ j then 1/‖x (e i)-x (e j)‖ else 0) =
        ∑ i : Fin k, ∑ j : Fin k, if e i ≠ e j then 1/‖x (e i)-x (e j)‖ else 0 := by simp_rw [he]
    _ ≤ ∑ i : Fin k, ∑ j : Fin n, if e i ≠ j then 1/‖x (e i)-x j‖ else 0 :=
      Finset.sum_le_sum (fun i _ => sum_embedding_le_univ e (f := fun j => if e i ≠ j then 1/‖x (e i)-x j‖ else 0) (fun j => by split_ifs <;> positivity))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then 1/‖x i-x j‖ else 0 :=
      sum_embedding_le_univ e (f := fun i => ∑ j : Fin n, if i ≠ j then 1/‖x i-x j‖ else 0)
        (fun i => Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity))
  rw [sum_ordered_pairs _ (fun i j => by rw [norm_sub_rev]),
    sum_ordered_pairs _ (fun i j => by rw [norm_sub_rev])] at h
  linarith

theorem selected_coulomb_lower {n k : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R b : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b) (hB : ∀ x, η x ≤ b⁻¹^3)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (x : Fin n → Space) (hx : Function.Injective x) (e : Fin k ↪ Fin n) :
    (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η (x ∘ e) r.1 *
      finiteSmear η (x ∘ e) r.2/‖r.1-r.2‖) - ((2*Real.pi+1)/2)*(n:ℝ)/b ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖x i-x j‖ else 0 := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hkn' : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hkn
  have he : ((2*Real.pi+1)/2)*(k:ℝ)/b ≤ ((2*Real.pi+1)/2)*(n:ℝ)/b :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkn' (by positivity)) hb.le
  exact (sub_le_sub_left he _).trans ((retained_coulomb_lower hm hn hR hs hb hB hr h1
    (x ∘ e) (hx.comp e.injective)).trans (retained_pair_sum_le x e))

theorem ae_selected_coulomb_lower {n k : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R b : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b) (hB : ∀ x, η x ≤ b⁻¹^3)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (e : Configuration n → (Fin k ↪ Fin n)) :
    ∀ᵐ x : Configuration n, (1/2:ℝ)*(∫ r : Space × Space,
      finiteSmear η (x ∘ e x) r.1*finiteSmear η (x ∘ e x) r.2/‖r.1-r.2‖) -
      ((2*Real.pi+1)/2)*(n:ℝ)/b ≤
        ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖x i-x j‖ else 0 := by
  filter_upwards [configuration_ae_nonsingular n] with x hx
  exact selected_coulomb_lower hm hn hR hs hb hB hr h1 x hx.2 (e x)

end CoulombAtom

end

end OAI
