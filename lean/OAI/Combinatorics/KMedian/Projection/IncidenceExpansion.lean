import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk
import OAI.Combinatorics.KMedian.Projection.IncidenceOperator
import OAI.Combinatorics.KMedian.Projection.Expansion

namespace OAI

section Inline_PCPIncidenceExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A B : Type} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D)

omit [Nonempty V] [Nonempty D] in
lemma half_pairing (hG : G.Contracts (1/2)) (g : V → ℝ) (hg : (𝔼 v, g v)=0) :
    pairing g (G.adjacency g) ≤ energy g/2 := by
  have hg0 := energy_nonneg g
  have h := (pairing_sq_le g (G.adjacency g)).trans
    (mul_le_mul_of_nonneg_left (hG g hg) hg0)
  nlinarith only [h,hg0]

omit [Nonempty V] in
lemma up_energy_centered (hG : G.Contracts (1/2)) (g : V → ℝ) (hg : (𝔼 v, g v)=0) :
    energy (G.up g) ≤ (3/4)*energy g := by
  rw [G.up_energy]
  linarith only [G.half_pairing hG g hg]

omit [Nonempty V] in
lemma down_energy_centered (hG : G.Contracts (1/2)) (f : V × D → ℝ)
    (hf : (𝔼 p, f p)=0) : energy (G.down f) ≤ (3/4)*energy f := by
  have hm : (𝔼 v, G.down f v)=0 := (G.down_mean f).trans hf
  have h := pairing_sq_le f (G.up (G.down f))
  rw [← G.down_up_adjoint] at h
  have he : pairing (G.down f) (G.down f)=energy (G.down f) := by
    simp only [pairing,energy,pow_two]
  rw [he] at h
  have hu := mul_le_mul_of_nonneg_left (G.up_energy_centered hG (G.down f) hm) (energy_nonneg f)
  have hd := energy_nonneg (G.down f)
  have hn := energy_nonneg f
  rcases eq_or_lt_of_le hd with hh|hh
  · rw [← hh]; positivity
  · nlinarith only [h,hu,hh]

lemma incidence_expands (hG : G.Contracts (1/2)) (π : (V × D) × Bool → A → B) :
    (G.incidence π).Expands (1/4) := by
  intro f
  rw [G.incidence_average]
  have h := G.down_energy_centered hG (fun p => f p-𝔼 q, f q) (mean_center f)
  rw [G.down_sub,G.down_const] at h
  have he : (fun v => G.down f v-𝔼 p, f p) =
      (fun v => G.down f v-𝔼 w, G.down f w) := by rw [G.down_mean]
  rw [he,energy_center,energy_center,G.down_mean] at h
  linarith only [h]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPIncidenceExpansion

end OAI
