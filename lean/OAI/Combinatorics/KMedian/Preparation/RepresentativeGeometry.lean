import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {J I X : Type*} [DecidableEq J] [PseudoMetricSpace X]

theorem representatives (U : Finset J) (client : J → X) (V : J → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hV : ∀ j ∈ U, 0 ≤ V j) :
    ∃ S : Finset J, S ⊆ U ∧
      (↑S : Set J).Pairwise (fun s t => M*max (V s) (V t) < dist (client s) (client t)) ∧
      ∀ j ∈ U, ∃ s ∈ S, V s ≤ V j ∧ dist (client j) (client s) ≤ M*V j := by
  revert hV
  refine U.strongInductionOn ?_
  intro U ih hV
  by_cases hu : U.Nonempty
  · obtain ⟨s,hs,hmin⟩ := U.exists_min_image V hu
    let W := U.filter (fun j => M*V j < dist (client j) (client s))
    have hWU : W ⊆ U := filter_subset _ _
    have hsW : s ∉ W := by
      intro hh
      have hh' := (mem_filter.mp hh).2
      rw [dist_self] at hh'
      exact not_lt_of_ge (mul_nonneg hM (hV s hs)) hh'
    have hproper : W ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hWU,fun he => hsW (he ▸ hs)⟩
    obtain ⟨S,hSW,hpair,hcover⟩ := ih W hproper (fun j hj => hV j (hWU hj))
    refine ⟨insert s S,insert_subset hs (hSW.trans hWU),?_,?_⟩
    · intro a ha b hb hab
      rcases mem_insert.mp ha with rfl | haS
      · have hbS : b ∈ S := (mem_insert.mp hb).resolve_left (Ne.symm hab)
        have hbW := hSW hbS
        rw [max_eq_right (hmin b (hWU hbW)),dist_comm]
        exact (mem_filter.mp hbW).2
      · rcases mem_insert.mp hb with rfl | hb
        · have haW := hSW haS
          rw [max_eq_left (hmin a (hWU haW))]
          exact (mem_filter.mp haW).2
        · exact hpair haS hb hab
    · intro j hj
      by_cases hjW : j ∈ W
      · obtain ⟨a,ha,hV,hD⟩ := hcover j hjW
        exact ⟨a,mem_insert_of_mem ha,hV,hD⟩
      · refine ⟨s,mem_insert_self _ _,hmin j hj,?_⟩
        exact le_of_not_gt (fun h => hjW (mem_filter.mpr ⟨hj,h⟩))
  · have he := not_nonempty_iff_eq_empty.mp hu
    subst U
    refine ⟨∅,Subset.rfl,?_,?_⟩ <;> simp

omit [DecidableEq J] in

theorem bundle_disjoint_geometry (s t i : X) {δ Ls Lt : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1/2) (hst : 0 < dist s t)
    (hLs : Ls ≤ dist s t) (hLt : Lt ≤ dist s t)
    (hsi : dist s i ≤ δ*Ls) (hti : dist t i ≤ δ*Lt) : False := by
  have hs := hsi.trans (mul_le_mul_of_nonneg_left hLs hδ)
  have ht := hti.trans (mul_le_mul_of_nonneg_left hLt hδ)
  have htri := dist_triangle s i t
  rw [dist_comm i t] at htri
  have hh := mul_lt_mul_of_pos_right hδ1 hst
  linarith only [hs,ht,htri,hh]

omit [DecidableEq J] [PseudoMetricSpace X] in
                                                                   
theorem outside_mass_bound [DecidableEq I] (F : Finset I) (y d : I → ℝ) {r : ℝ}
    (hy : ∀ i ∈ F, 0 ≤ y i) (hd : ∀ i ∈ F, 0 ≤ d i) :
    r*(∑ i ∈ F.filter (fun i => r < d i), y i) ≤ ∑ i ∈ F, y i*d i := by
  calc
    _ = ∑ i ∈ F.filter (fun i => r < d i), y i*r := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ ∑ i ∈ F.filter (fun i => r < d i), y i*d i := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (mem_filter.mp hi).2.le (hy i (mem_filter.mp hi).1)
    _ ≤ ∑ i ∈ F, y i*d i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i hi _ => mul_nonneg (hy i hi) (hd i hi))

omit [DecidableEq J] [PseudoMetricSpace X] in
 theorem deficit_small {M δ L V c : ℝ} (hM : 0 < M) (hδ : 0 < δ) (hL : 0 < L)
    (hc : δ*L*c ≤ V) (hsep : M*V ≤ L) : c ≤ 1/(M*δ) := by
  have ha : c ≤ V/(δ*L) := (le_div_iff₀ (mul_pos hδ hL)).mpr (by nlinarith only [hc])
  have hb : V ≤ L/M := (le_div_iff₀ hM).mpr (by nlinarith only [hsep])
  calc
    c ≤ V/(δ*L) := ha
    _ ≤ (L/M)/(δ*L) := div_le_div_of_nonneg_right hb (mul_pos hδ hL).le
    _ = 1/(M*δ) := by field_simp

end MetricKMedian.Preparation
end
end

end OAI
