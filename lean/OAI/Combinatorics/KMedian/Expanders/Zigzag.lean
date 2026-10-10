import Mathlib
import OAI.Combinatorics.KMedian.Expanders.Cloud

namespace OAI

section Inline_PCPZigzag

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype S] [Nonempty S]

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma zigzag_decomposition (G : PortGraph V D) (H : PortGraph D S) (f : V × D → ℝ) :
    (G.zigzag H).adjacency f = fun p =>
      lift (G.adjacency (average f)) p +
      cloud H (residual (permute G (lift (average f)))) p +
      cloud H (permute G (cloud H (residual f))) p := by
  rw [zigzag_adjacency,cloud_decompose H f,permute_add,cloud_add]
  rw [cloud_decompose H (permute G (lift (average f))),average_permute_lift]

omit [Nonempty V] in
theorem zigzag_contracts (G : PortGraph V D) (H : PortGraph D S) {ρ σ : ℝ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hG : G.Contracts ρ) (hH : H.Contracts σ) :
    (G.zigzag H).Contracts (ρ+2*σ) := by
  intro f hf
  have hfmean : (𝔼 v, average f v)=0 := (average_mean f).trans hf
  have hfirst : l2 (lift (D := D) (G.adjacency (average f))) ≤ ρ*l2 f := by
    rw [lift_l2]
    exact (G.l2_contracts hρ hG _ hfmean).trans (mul_le_mul_of_nonneg_left (average_l2 f) hρ)
  have havg : l2 (permute G (lift (average f))) ≤ l2 f := by
    rw [permute_l2,lift_l2]
    exact average_l2 f
  have hsecond : l2 (cloud H (residual (permute G (lift (average f))))) ≤ σ*l2 f :=
    (cloud_residual_l2 H hσ hH _).trans (mul_le_mul_of_nonneg_left
      ((residual_l2 _).trans havg) hσ)
  have hthird : l2 (cloud H (permute G (cloud H (residual f)))) ≤ σ*l2 f := by
    calc
      _ ≤ l2 (permute G (cloud H (residual f))) := cloud_l2_le H _
      _ = l2 (cloud H (residual f)) := permute_l2 G _
      _ ≤ σ*l2 (residual f) := cloud_residual_l2 H hσ hH f
      _ ≤ σ*l2 f := mul_le_mul_of_nonneg_left (residual_l2 f) hσ
  have hout : l2 ((G.zigzag H).adjacency f) ≤ (ρ+2*σ)*l2 f := by
    rw [zigzag_decomposition]
    have h1 := l2_add
      (fun p => lift (G.adjacency (average f)) p+
        cloud H (residual (permute G (lift (average f)))) p)
      (cloud H (permute G (cloud H (residual f))))
    have h2 := l2_add (lift (D := D) (G.adjacency (average f)))
      (cloud H (residual (permute G (lift (average f)))))
    linarith
  have hsq := pow_le_pow_left₀ (l2_nonneg ((G.zigzag H).adjacency f)) hout 2
  simpa only [mul_pow,l2_sq] using hsq

omit [Nonempty V] in
theorem square_zigzag_half (G : PortGraph V D) (H : PortGraph (D × D) S)
    (hG : G.Contracts (1/2)) (hH : H.Contracts (1/10)) :
    (G.square.zigzag H).Contracts (1/2) := by
  have h := zigzag_contracts G.square H (by positivity : (0:ℝ) ≤ (1/2)^2)
    (by norm_num : (0:ℝ) ≤ 1/10) (square_contracts G hG) hH
  intro f hf
  have hh := h f hf
  have hn := energy_nonneg f
  norm_num at hh
  nlinarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPZigzag

end OAI
