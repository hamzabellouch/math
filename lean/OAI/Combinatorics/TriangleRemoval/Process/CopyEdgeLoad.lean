import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeVarianceRate
import OAI.Combinatorics.TriangleRemoval.Probability.HistoryLawPastMean

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def copyEdgeLoad {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (e : Finset (Fin n)) : ℝ :=
  ∑ a, if e ∈ required a then intact (required a) G else 0

lemma intact_nonneg {n : ℕ} (F G : Graph n) : 0 ≤ intact F G := by
  unfold intact
  split <;> norm_num

lemma intact_mono {n : ℕ} (F : Graph n) {G H : Graph n} (h : G ⊆ H) :
    intact F G ≤ intact F H := by
  unfold intact
  by_cases hF : F ⊆ G
  · rw [ite_eq_left hF,ite_eq_left (hF.trans h)]
  · rw [ite_eq_right hF]
    split <;> norm_num

lemma copyEdgeLoad_nonneg {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (e : Finset (Fin n)) :
    0 ≤ copyEdgeLoad required G e := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact intact_nonneg _ _
  · exact le_rfl

lemma copyCount_mono {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) {G H : Graph n} (h : G ⊆ H) :
    copyCount required G ≤ copyCount required H := by
  apply Finset.sum_le_sum
  intro a _
  exact intact_mono (required a) h

lemma intact_deleted_loss_le {n : ℕ} (F G E : Graph n) :
    intact F G - intact F (G \ E) ≤
      ∑ e ∈ E, if e ∈ F then intact F G else 0 := by
  classical
  by_cases hF : F ⊆ G
  · by_cases hFE : F ⊆ G \ E
    · rw [intact,ite_eq_left hF,intact,ite_eq_left hFE,sub_self]
      apply Finset.sum_nonneg
      intro e _
      split <;> positivity
    · obtain ⟨e,heF,heGE⟩ := Finset.not_subset.mp hFE
      have heE : e ∈ E := by
        by_contra he
        exact heGE (Finset.mem_sdiff.mpr ⟨hF heF,he⟩)
      have hh := Finset.single_le_sum
        (f := fun e => if e ∈ F then intact F G else 0)
        (fun _ _ => by split; exact intact_nonneg _ _; exact le_rfl) heE
      simpa only [ite_eq_left heF,intact,ite_eq_left hF,ite_eq_right hFE,sub_zero] using hh
  · have hFE : ¬ F ⊆ G \ E := fun h => hF (h.trans Finset.sdiff_subset)
    simp only [intact,ite_eq_right hF,ite_eq_right hFE,sub_self,ite_self,Finset.sum_const_zero,le_refl]

theorem copyCount_deleted_loss_le {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G E : Graph n) :
    copyCount required G - copyCount required (G \ E) ≤
      ∑ e ∈ E, copyEdgeLoad required G e := by
  classical
  unfold copyCount
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, ∑ e ∈ E, if e ∈ required a then intact (required a) G else 0 := by
      apply Finset.sum_le_sum
      intro a _
      exact intact_deleted_loss_le _ _ _
    _ = _ := Finset.sum_comm

theorem copyCount_step_loss_range {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G H : Graph n) (L : ℝ) (hL : 0 ≤ L)
    (hload : ∀ e ∈ G, copyEdgeLoad required G e ≤ L)
    (hH : H ∈ (step G).support) :
    0 ≤ copyCount required G - copyCount required H ∧
      copyCount required G - copyCount required H ≤ 3*L := by
  constructor
  · exact sub_nonneg.mpr (copyCount_mono required (step_support_subset hH))
  · by_cases hG : (triangles G).Nonempty
    · obtain ⟨t,ht,rfl⟩ := (step_support_active hG).mp hH
      calc
        _ ≤ ∑ e ∈ t.powersetCard 2, copyEdgeLoad required G e :=
          copyCount_deleted_loss_le required G _
        _ ≤ ∑ _e ∈ t.powersetCard 2, L := Finset.sum_le_sum
          (fun e he => hload e ((mem_triangles.mp ht).2 he))
        _ = 3*L := by simp only [Finset.sum_const,nsmul_eq_mul,triangle_edge_card ht]; norm_num
    · simp only [step,dite_eq_right hG,PMF.mem_support_pure_iff] at hH
      subst H
      simpa only [sub_self] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL

theorem pmf_centered_of_loss_range {α : Type*} [Fintype α] (p : PMF α)
    (f : α → ℝ) (a R : ℝ)
    (h : ∀ b ∈ p.support, 0 ≤ a-f b ∧ a-f b ≤ R) :
    ∀ b ∈ p.support, |f b-pmfMean p f| ≤ R := by
  have hlo : a-R ≤ pmfMean p f := by
    rw [← pmfMean_const p (a-R)]
    apply pmfMean_mono
    intro b hb
    have := (h b hb).2
    linarith
  have hhi : pmfMean p f ≤ a := by
    rw [← pmfMean_const p a]
    apply pmfMean_mono
    intro b hb
    have := (h b hb).1
    linarith
  intro b hb
  obtain ⟨h₁,h₂⟩ := h b hb
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem pmf_variance_of_loss_range {α : Type*} [Fintype α] (p : PMF α)
    (f : α → ℝ) (a R : ℝ)
    (h : ∀ b ∈ p.support, 0 ≤ a-f b ∧ a-f b ≤ R) :
    pmfMean p (fun b => (f b-pmfMean p f)^2) ≤ R*(a-pmfMean p f) := by
  apply (pmfMean_centered_sq_le p f a).trans
  calc
    _ ≤ pmfMean p (fun b => R*(a-f b)) := by
      apply pmfMean_mono
      intro b hb
      obtain ⟨h₁,h₂⟩ := h b hb
      nlinarith [mul_nonneg h₁ (sub_nonneg.mpr h₂)]
    _ = _ := by rw [pmfMean_const_mul,pmfMean_sub,pmfMean_const]

noncomputable def copyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (_k : ℕ) (G : Graph n) : ℝ :=
  3*L*(copyCount required G - pmfMean (step G) (copyCount required))

theorem triangle_template_noise_freedman {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L : ℝ) (hL : 0 < L)
    (hload : ∀ j < T, ∀ H ∈ (evolve G j).support,
      ∀ e ∈ H, copyEdgeLoad required H e ≤ L)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        r ≤ historyNoise (fun _ => step) (fun _ => copyCount required) T j ω ∧
        historyCounter (copyVarianceRate required L) T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+(3*L)*r))) := by
  apply history_noise_freedman_maximal (PMF.pure G) (fun _ => step)
    (fun _ => copyCount required) (copyVarianceRate required L) T (3*L) (by positivity)
  · intro j hj H hH J hJ
    rw [markovLaw_triangle_step] at hH
    exact pmf_centered_of_loss_range (step H) (copyCount required) (copyCount required H)
      (3*L) (fun A hA => copyCount_step_loss_range required H A L hL.le (hload j hj H hH) hA) J hJ
  · intro j hj H hH
    rw [markovLaw_triangle_step] at hH
    exact pmf_variance_of_loss_range (step H) (copyCount required) (copyCount required H)
      (3*L) (fun A hA => copyCount_step_loss_range required H A L hL.le (hload j hj H hH) hA)
  · exact hr
  · exact hV

end SharpTerminalLeave

end

end OAI
