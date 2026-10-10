import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk

namespace OAI

section Inline_PCPEqualityExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

lemma correlation_half (hG : G.Contracts (1/2)) (f : V → ℝ) :
    pairing f (G.adjacency f) ≤ (energy f + (𝔼 v, f v)^2)/2 := by
  let g : V → ℝ := fun v => f v - 𝔼 w, f w
  have hg : (𝔼 v, g v)=0 := mean_center f
  have he := energy_nonneg g
  have h₁ := pairing_sq_le g (G.adjacency g)
  have h₂ := hG g hg
  have h₃ := mul_le_mul_of_nonneg_left h₂ he
  have h₄ : pairing g (G.adjacency g) ≤ energy g/2 := by
    nlinarith
  have hc := G.centered_correlation 1 f
  change pairing g (G.adjacency g) = pairing f (G.adjacency f) - (𝔼 v, f v)^2 at hc
  have hv := energy_center f
  change energy g = _ at hv
  linarith

variable [Fintype A] [Nonempty A] (a : V → A)
noncomputable def labelMass (b : A) : ℝ := testRate (fun v => a v=b)
noncomputable def equalityFailure : ℝ := testRate (fun z : V × D => a z.1 ≠ a (G.step z.1 z.2))

omit [Nonempty A] in
lemma labelMass_sum : ∑ b : A, labelMass a b = 1 := by
  classical
  unfold labelMass testRate
  rw [← expect_sum_comm]
  simp [eq_comm]

omit [Nonempty V] [Fintype A] [Nonempty A] in
lemma labelMass_nonneg (b : A) : 0 ≤ labelMass a b := testRate_nonneg _

noncomputable def majorityLabel : A := Classical.choose (show ∃ b : A, ∀ c : A,
    labelMass a c ≤ labelMass a b from by
  obtain ⟨b,_,hb⟩ := exists_max_image univ (labelMass a) univ_nonempty
  exact ⟨b,fun c => hb c (mem_univ c)⟩)

omit [Nonempty V] in
lemma majorityLabel_max (b : A) : labelMass a b ≤ labelMass a (majorityLabel a) :=
  Classical.choose_spec (show ∃ b : A, ∀ c : A, labelMass a c ≤ labelMass a b from by
    obtain ⟨b,_,hb⟩ := exists_max_image univ (labelMass a) univ_nonempty
    exact ⟨b,fun c => hb c (mem_univ c)⟩) b

lemma label_collision_le_majority : ∑ b : A, (labelMass a b)^2 ≤ labelMass a (majorityLabel a) := by
  calc
    _ ≤ ∑ b : A, labelMass a b * labelMass a (majorityLabel a) :=
      sum_le_sum (fun b _ => by simpa [pow_two] using
        mul_le_mul_of_nonneg_left (majorityLabel_max a b) (labelMass_nonneg a b))
    _ = _ := by rw [← sum_mul,labelMass_sum,one_mul]

omit [Nonempty A] in
lemma label_pairing_sum :
    (∑ b : A, pairing (fun v => if a v=b then (1:ℝ) else 0)
      (G.adjacency (fun v => if a v=b then (1:ℝ) else 0))) =
      1 - G.equalityFailure a := by
  classical
  unfold pairing adjacency equalityFailure testRate
  simp_rw [mul_expect]
  rw [← expect_sum_comm]

  have hh : (𝔼 v, ∑ b : A, 𝔼 d, (if a v=b then (1:ℝ) else 0) *
      (if a (G.step v d)=b then (1:ℝ) else 0)) =
      𝔼 v, 𝔼 d, if a v=a (G.step v d) then (1:ℝ) else 0 := by
    apply expect_congr rfl
    intro v _
    rw [← expect_sum_comm]
    apply expect_congr rfl
    intro d _
    simp [eq_comm]
  rw [hh]
  rw [expect_prod]
  have hc := testRate_complement (fun z : V × D => a z.1=a (G.step z.1 z.2))
  rw [testRate_prod (fun v d => a v=a (G.step v d)),
    testRate_prod (fun v d => ¬a v=a (G.step v d))] at hc
  unfold testRate at hc
  linarith

theorem equality_cloud_sound (hG : G.Contracts (1/2)) :
    testRate (fun v => a v ≠ majorityLabel a) ≤ 2*G.equalityFailure a := by
  classical
  have hh := sum_le_sum (s := (univ : Finset A)) (fun b _ =>
    G.correlation_half hG (fun v => if a v=b then (1:ℝ) else 0))
  have he (b : A) : energy (fun v => if a v=b then (1:ℝ) else 0)=labelMass a b := by
    unfold energy labelMass testRate
    apply expect_congr rfl
    intro v _
    split_ifs <;> simp_all
  have hm (b : A) : (𝔼 v, if a v=b then (1:ℝ) else 0)=labelMass a b := by
    unfold labelMass testRate
    apply expect_congr rfl
    intro v _
    by_cases h : a v=b <;> simp [h]
  simp_rw [he,hm] at hh
  rw [label_pairing_sum, ← sum_div, sum_add_distrib,labelMass_sum] at hh
  have hc := label_collision_le_majority a
  have hn := testRate_complement (fun v => a v=majorityLabel a)
  change labelMass a (majorityLabel a) + testRate (fun v => a v ≠ majorityLabel a)=1 at hn
  linarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPEqualityExpansion

end OAI
