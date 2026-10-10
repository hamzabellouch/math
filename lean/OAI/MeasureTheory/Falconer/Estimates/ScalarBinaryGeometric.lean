import OAI.MeasureTheory.Falconer.Estimates.ScalarBinaryGrowth
import OAI.MeasureTheory.Falconer.Estimates.ScalarPluennecke

namespace OAI

/-! Geometrically spaced nonporous binary increments force growth of a
 fixed-fold sumset, and hence contradict an appropriately small sumset. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_scaled_binary_growth {N k J L : ℕ} {U : ℝ}
    (f : (Fin N → Bool) → ℝ) (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (scale : ℕ → ℝ) (hs : ∀ n ≤ N, 0 < scale n) (hJ : 0 < J)
    (hcontract : ∀ n < N, scale (n+1)*(1+2*(J:ℝ)*U) ≤ scale n)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hk : (2*L+1)*J ≤ k)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      2*scale ((n:ℕ)+1) ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ U*scale ((n:ℕ)+1)) :
    ∃ E : Finset ℝ, E ⊆ k • A ∧ E.card = (J+1)^N ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → scale N ≤ |x-y| := by
  have hJr : 0 < (J:ℝ) := by exact_mod_cast hJ
  apply scalar_binary_growth f A hf (fun n => scale (n+1)/(4*(J:ℝ)))
    (fun n => U*scale (n+1)) (fun n => 2*scale (n+1)) (fun n => scale n) (fun _ => L) hJ
  · intro n hn
    exact div_pos (hs (n+1) (by omega)) (by positivity)
  · exact hs
  · exact hlo
  · exact hhi
  · intro n hn
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 4*(J:ℝ) by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hL (hs (n+1) (by omega)).le
    calc
      U*scale (n+1)*(4*(J:ℝ)) = (4*(J:ℝ)*U)*scale (n+1) := by ring
      _ ≤ (L:ℝ)*scale (n+1) := hh
  · exact fun _ _ => hk
  · intro n hn
    have he : 2*(J:ℝ)*(scale (n+1)/(4*(J:ℝ))) = scale (n+1)/2 := by
      field_simp
      ring
    rw [he]
    have hp := (hs (n+1) (by omega)).le
    linarith
  · intro n hn
    calc
      scale (n+1)+2*(J:ℝ)*(U*scale (n+1)) = scale (n+1)*(1+2*(J:ℝ)*U) := by ring
      _ ≤ scale n := hcontract n hn

 theorem scalar_geometric_binary_growth {N k J L : ℕ} {r U : ℝ}
    (f : (Fin N → Bool) → ℝ) (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (hr : 0 < r) (hJ : 0 < J)
    (hcontract : r*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hk : (2*L+1)*J ≤ k)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      2*r^((n:ℕ)+1) ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ U*r^((n:ℕ)+1)) :
    ∃ E : Finset ℝ, E ⊆ k • A ∧ E.card = (J+1)^N ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → r^N ≤ |x-y| := by
  apply scalar_scaled_binary_growth f A hf (fun n => r^n)
    (fun n _ => pow_pos hr n) hJ ?_ hL hk hlo hhi
  intro n _
  calc
    r^(n+1)*(1+2*(J:ℝ)*U) = r^n*(r*(1+2*(J:ℝ)*U)) := by rw [pow_succ]; ring
    _ ≤ r^n*1 := mul_le_mul_of_nonneg_left hcontract (pow_nonneg hr.le n)
    _ = _ := mul_one _

 theorem scalar_geometric_binary_cells {N k J L : ℕ} {r U : ℝ}
    (f : (Fin N → Bool) → ℝ) (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (hr : 0 < r) (hJ : 0 < J)
    (hcontract : r*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hk : (2*L+1)*J ≤ k)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      2*r^((n:ℕ)+1) ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ U*r^((n:ℕ)+1)) :
    (J+1)^N ≤ (scalarCells (r^N) (k • A)).card := by
  obtain ⟨E,hE,hcard,hsep⟩ := scalar_geometric_binary_growth f A hf hr hJ hcontract hL hk hlo hhi
  rw [← hcard,← Finset.card_image_of_injOn (scalarCells_injective (pow_pos hr N) hsep)]
  exact Finset.card_le_card (Finset.image_subset_image hE)

 theorem scalar_geometric_binary_doubling_bound {N k J L : ℕ} {r U K : ℝ}
    (f : (Fin N → Bool) → ℝ) (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (hA : A.Nonempty) (hr : 0 < r) (hJ : 0 < J)
    (hcontract : r*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hk : (2*L+1)*J ≤ k)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      2*r^((n:ℕ)+1) ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ U*r^((n:ℕ)+1))
    (hsmall : ((scalarCells (r^N) (A+A)).card:ℝ) ≤ K*(scalarCells (r^N) A).card) :
    (((J+1)^N:ℕ):ℝ) ≤ (k+2)*(2*K)^k*(scalarCells (r^N) A).card := by
  have hlo' : (((J+1)^N:ℕ):ℝ) ≤ ((scalarCells (r^N) (k • A)).card:ℝ) := by
    exact_mod_cast scalar_geometric_binary_cells f A hf hr hJ hcontract hL hk hlo hhi
  have hupper := scalar_pluennecke (r^N) A A hA hsmall k 0
  simp only [zero_nsmul,sub_zero,add_zero,Nat.cast_zero] at hupper
  exact hlo'.trans hupper

end Falconer

end OAI
