import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SecretKey

theorem eventually_empty_of_uniform_bit_gap (length : ℕ → ℕ) (error : ℕ → ℝ)
    (hgap : ∀ k, 1≤length k → (1:ℝ)/5≤error k)
    (hsecure : Tendsto error atTop (𝓝 0)) : ∀ᶠ k in atTop, length k=0 := by
  have he : ∀ᶠ k in atTop, error k<(1:ℝ)/5 :=
    hsecure.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [he] with k hk
  by_contra hn
  have hh := hgap k (Nat.one_le_iff_ne_zero.mpr hn)
  linarith

theorem secure_key_rate_zero (length : ℕ → ℕ) (error : ℕ → ℝ)
    (hgap : ∀ k, 1≤length k → (1:ℝ)/5≤error k)
    (hsecure : Tendsto error atTop (𝓝 0)) :
    Filter.liminf (fun k => (length k : ℝ)/(k : ℝ)) atTop=0 := by
  have h0 := eventually_empty_of_uniform_bit_gap length error hgap hsecure
  have he : (fun k => (length k : ℝ)/(k : ℝ))=ᶠ[atTop](fun _ => (0:ℝ)) := by
    filter_upwards [h0] with k hk
    simp [hk]
  rw [Filter.liminf_congr he]
  simp

end SecretKey

end

end OAI
