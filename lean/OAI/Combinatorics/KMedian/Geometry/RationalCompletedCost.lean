import Mathlib
import OAI.Combinatorics.KMedian.Reduction.CompletionEndpoint
import OAI.Combinatorics.KMedian.Reduction.RationalGreedyCompletion

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Analytic Preparation
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}
local instance : LinearOrder (Copy (F := F) Δ) := RationalPhysicalKernel.copyOrder

def score (d : Fin j → F → ℚ) (O : Finset F) : ℚ :=
  ∑ c, if h : O.Nonempty then (O.image (d c)).min' (h.image _) else 0

omit [LinearOrder F] [Fintype F] in
theorem score_nonneg (d : Fin j → F → ℚ) (hd : ∀ c f, 0 ≤ d c f) (O : Finset F) :
    0 ≤ score d O := by
  apply sum_nonneg
  intro c _
  split_ifs with h
  · obtain ⟨f,_,he⟩ := mem_image.mp (min'_mem (O.image (d c)) (h.image _))
    rw [← he]
    exact hd c f
  · exact le_rfl

omit [LinearOrder F] [Fintype F] in
theorem score_le (d : Fin j → F → ℚ) (O : Finset F) (b : Fin j → ℝ)
    (hO : ∀ c, ∃ f∈O, (d c f:ℝ)≤b c) : (score d O:ℝ)≤∑ c,b c := by
  unfold score
  push_cast
  apply sum_le_sum
  intro c _
  obtain ⟨f,hf,hb⟩ := hO c
  have hn : O.Nonempty := ⟨f,hf⟩
  rw [dite_eq_left hn]
  exact (show ((O.image (d c)).min' (hn.image _):ℝ)≤(d c f:ℝ) by
    exact_mod_cast min'_le (O.image (d c)) (d c f) (mem_image.mpr ⟨f,hf,rfl⟩)).trans hb

theorem output_potential (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (location : F → X) (client : Fin j → X)
    (hdist : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (hR : ∀ c, 0 ≤ R c) {g x : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1)
    (A : Finset (Copy (F := F) Δ)) (B L : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (hm : ∀ c, mass g (B c)=1)
    (hd : ∀ c i, i∈B c → d c i.1≤R c)
    (hbackup : ∀ c, (¬∃ f∈integral Δ A, d c f ≤5*R c) → B c⊆A) :
    (score d (output d R A B hB):ℝ) ≤ ∑ c, (
      potential x g (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (L c)
        (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ A))+
        5*(R c:ℝ)*mass g (L c)) := by
  obtain ⟨hO,hcount,hcover⟩ := output_spec d R location client hdist hR hg hunit A B hB hm hd hbackup
  apply score_le
  intro c
  obtain ⟨f,hf,hfc⟩ := GroupCap.completed_distance (R c:ℝ)
    (fun f => dist (client c) (location f)) (integral Δ A) (output d R A B hB) hO (by
      obtain ⟨f,hf,he⟩ := hcover c
      refine ⟨f,hf,?_⟩
      rw [hdist]
      exact_mod_cast he)
  refine ⟨f,hf,?_⟩
  rw [← hdist]
  apply hfc.trans
  have hb := GroupCap.cap_le_radius (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ A)
  have hy := mass_nonneg hg (L c)
  have hc := cost_nonneg hg (d := fun i : Copy (F := F) Δ => dist (client c) (location i.1))
    (S := L c) (fun _ _ => dist_nonneg)
  have ha := coefficient_ge_one (x := x) hy
  have hmul := mul_nonneg (show 0 ≤ coefficient x (mass g (L c)) by linarith only [ha]) hc
  have hby := mul_le_mul_of_nonneg_right hb hy
  rw [potential,← coefficient_eq]
  nlinarith only [hmul,hby]

end MetricKMedian.Completion.Rational
end

end OAI
