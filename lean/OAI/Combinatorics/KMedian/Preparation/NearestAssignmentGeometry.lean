import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RepresentativeBundles
import OAI.Combinatorics.KMedian.Preparation.PreparationCostGeometry

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

omit [Fintype I] [DecidableEq I] in

theorem assignment_radius (F : Finset I) (y : I → ℝ) (d : I → ℝ)
    (hunit : ∑ a ∈ F, y a=1) (hd : ∀ a, 0 ≤ d a)
    (hnearest : ∀ a ∈ F, ∀ b ∉ F, d a ≤ d b) :
    ∃ R : ℝ, 0 ≤ R ∧ (∃ a ∈ F, R=d a) ∧
      (∀ a ∈ F, d a ≤ R) ∧ (∀ b ∉ F, R ≤ d b) := by
  have hF : F.Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he,sum_empty] at hunit
    exact zero_ne_one hunit
  obtain ⟨a,ha,hmax⟩ := exists_max_image F d hF
  exact ⟨d a,hd a,⟨a,ha,rfl⟩,hmax,fun b hb => hnearest a ha b hb⟩

noncomputable def relevantRadius (c L R : ℝ) : ℝ := if 0 < c then L else R

omit [Fintype I] [Fintype T] [DecidableEq T] in
theorem assigned_radius_ge {F : T → Finset I} {y : I → ℝ} {s : T → X} {i : I → X}
    {V : T → ℝ} {M δ : ℝ} (G : BundleGeometry F y s i V M δ)
    (hδ1 : δ ≤ 1) (t : T) {R : ℝ} (hR : 0 ≤ R)
    (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R) :
    δ*relevantRadius (G.c t) (G.L t) R ≤ R := by
  dsimp only [relevantRadius]
  split_ifs with hc
  · have hn : G.next t ≠ t := fun ht => (ne_of_gt hc) (G.self_zero t ht)
    have hA : (G.A t).Nonempty := by
      by_contra he
      have hz := G.deficit_mass t
      rw [not_nonempty_iff_eq_empty.mp he,sum_empty] at hz
      exact (ne_of_gt hc) hz.symm
    obtain ⟨a,ha⟩ := hA
    have haF : a ∈ F t := (mem_sdiff.mp ((G.missing t) ▸ ha)).1
    exact (G.outside_radius t hn a ha).le.trans (hmax a haF)
  · exact mul_le_of_le_one_left hR hδ1

theorem distant_scales {c L R M δ T₁ v D : ℝ}
    (_hc : 0 ≤ c) (hM : 0 ≤ M) (hδ : 0 < δ) (hT : 0 < T₁)
    (hD : D ≤ M*v) (hR : δ*relevantRadius c L R ≤ R)
    (hfar : T₁*v < relevantRadius c L R) :
    D ≤ (M/(δ*T₁))*R ∧ (0 < c → D ≤ (M/T₁)*L) := by
  have hv : v ≤ relevantRadius c L R/T₁ := (le_div_iff₀ hT).mpr (by nlinarith only [hfar])
  have hr : relevantRadius c L R ≤ R/δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hR])
  constructor
  · calc
      D ≤ M*v := hD
      _ ≤ M*(relevantRadius c L R/T₁) := mul_le_mul_of_nonneg_left hv hM
      _ ≤ M*((R/δ)/T₁) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr hT.le) hM
      _ = _ := by ring
  · intro hc'
    have hL : relevantRadius c L R=L := ite_eq_left hc'
    rw [hL] at hv
    exact (hD.trans (mul_le_mul_of_nonneg_left hv hM)).trans_eq (by ring)

omit [Fintype I] in

theorem metric_exchange (Fj Fs : Finset I) (y : I → ℝ) (i : I → X) (j s : X)
    {R α : ℝ} (hy : ∀ a, 0 ≤ y a) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ Fs, y a=1) (hα : 0 ≤ α) (hα1 : α < 1)
    (hD : dist j s ≤ α*R) (hmax : ∀ a ∈ Fs, dist s (i a) ≤ R)
    (hmin : ∀ a ∉ Fs, R ≤ dist s (i a)) :
    (∑ a ∈ Fs, y a*dist j (i a)) ≤ (1+α)/(1-α)*(∑ a ∈ Fj, y a*dist j (i a)) := by
  apply far_exchange Fj Fs y (fun a => dist j (i a)) hy (fun _ => dist_nonneg)
    hmj hms hα hα1 hD
  · intro a ha
    have hh := hmax a (mem_sdiff.mp ha).1
    have ht := dist_triangle j s (i a)
    linarith only [hh,ht]
  · intro a ha
    have hh := hmin a (mem_sdiff.mp ha).2
    have ht := dist_triangle s j (i a)
    rw [dist_comm s j] at ht
    linarith only [hh,ht]

end MetricKMedian.Preparation
end
end

end OAI
