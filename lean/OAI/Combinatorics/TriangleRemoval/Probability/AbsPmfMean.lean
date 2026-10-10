import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.CavityReference
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraphReindex

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma abs_pmfMean_le {α : Type*} [Fintype α] (P : PMF α) (f : α → ℝ) :
    |pmfMean P f| ≤ pmfMean P (fun a => |f a|) := by
  unfold pmfMean
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro a _
  rw [abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]

lemma pmfMean_swap {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (f : α → β → ℝ) :
    pmfMean P (fun a => pmfMean Q (f a)) =
      pmfMean Q (fun b => pmfMean P (fun a => f a b)) := by
  unfold pmfMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma pmfMean_common_error {α : Type*} [Fintype α] (P : PMF α)
    (f err : α → ℝ) (r : ℝ) (h : ∀ a ∈ P.support, |f a-r| ≤ err a) :
    |pmfMean P f-r| ≤ pmfMean P err := by
  rw [← pmfMean_const P r,← pmfMean_sub]
  exact (abs_pmfMean_le P _).trans (pmfMean_mono P h)

lemma relative_error_absolute {a r ε : ℝ} (hr : 0 < r)
    (h : |a/r-1| ≤ ε) : |a-r| ≤ ε*r := by
  have heq : (a/r-1)*r = a-r := by field_simp
  calc
    _ = |(a/r-1)*r| := congrArg abs heq.symm
    _ = |a/r-1| *r := by rw [abs_mul,abs_of_pos hr]
    _ ≤ _ := mul_le_mul_of_nonneg_right h hr.le

lemma product_relative_error {a b r ε : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b)
    (haerr : |a-r| ≤ ε*r) (hberr : |b-r| ≤ ε*r) (hε : 0 ≤ ε) :
    |a*b-r^2| ≤ (2*ε+ε^2)*r^2 := by
  have hbup : b ≤ (1+ε)*r := by
    have := (abs_le.mp hberr).2
    nlinarith
  calc
    _ = |(a-r)*b+r*(b-r)| := by congr 1; ring
    _ ≤ |(a-r)*b|+|r*(b-r)| := abs_add_le _ _
    _ = |a-r| *b+r*|b-r| := by rw [abs_mul,abs_mul,abs_of_nonneg hb,abs_of_nonneg hr]
    _ ≤ (ε*r)*((1+ε)*r)+r*(ε*r) := add_le_add
      (mul_le_mul haerr hbup hb (mul_nonneg hε hr))
      (mul_le_mul_of_nonneg_left hberr hr)
    _ = _ := by ring

lemma focusSurvival_mem_unit {n : ℕ} (G focus : Graph n) :
    focusSurvival G focus ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨trueProbability_nonneg _,trueProbability_le_one _⟩

lemma cavityReference_le_one {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    cavityReference D t ≤ 1 := by
  unfold cavityReference
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith : 1 ≤ 1+2*D*t)
    (by norm_num)

theorem singleton_survival_error {n : ℕ} (G : Graph n) (D ε : ℝ)
    (hD : 0 < D)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε)
    (e : Finset (Fin n)) (he : e ∈ G) :
    |focusSurvival G {e}-cavityReference D 1| ≤
      collisionCost (triangleHypergraph G) {e} none+ε*cavityReference D 1 := by
  classical
  have hc := graph_cavity_error G {e} (Finset.singleton_subset_iff.mpr he)
  rw [Finset.prod_singleton] at hc
  have heq := active_cavity_eq G ⟨e,he⟩ none 1
  simp only [Option.map_none] at heq
  have habs := relative_error_absolute (cavityReference_pos hD (by norm_num)) (hrel ⟨e,he⟩)
  rw [← heq] at habs
  exact (abs_sub_le _ _ _).trans (add_le_add hc habs)

theorem pair_survival_error {n : ℕ} (G : Graph n) (D ε : ℝ)
    (hD : 0 < D) (hε : 0 ≤ ε)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε)
    (e f : Finset (Fin n)) (he : e ∈ G) (hf : f ∈ G) (hef : e ≠ f) :
    |focusSurvival G {e,f}-(cavityReference D 1)^2| ≤
      collisionCost (triangleHypergraph G) {e,f} none+
        (2*ε+ε^2)*(cavityReference D 1)^2 := by
  classical
  have hc := graph_cavity_error G {e,f}
    (by intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption)
  rw [Finset.prod_pair hef] at hc
  have heq := active_cavity_eq G ⟨e,he⟩ none 1
  have hfq := active_cavity_eq G ⟨f,hf⟩ none 1
  simp only [Option.map_none] at heq hfq
  have hr := cavityReference_pos hD (by norm_num : (0 : ℝ) ≤ 1)
  have hea := relative_error_absolute hr (hrel ⟨e,he⟩)
  have hfa := relative_error_absolute hr (hrel ⟨f,hf⟩)
  rw [← heq] at hea
  rw [← hfq] at hfa
  have hh := product_relative_error hr.le
    (cavityLimit_mem_unit (triangleHypergraph G) f none 1).1
    hea hfa hε
  exact (abs_sub_le _ _ _).trans (add_le_add hc hh)

end SharpTerminalLeave

end

end OAI
