import OAI.NumberTheory.TotientAsymptotic.CoordinateEnlargement
import OAI.NumberTheory.TotientAsymptotic.PublishedConcentration

namespace OAI

/-! Uniform comparison of the two coordinate centers with the order of
choices needed in the application: fix the terminal truncation, then the
retained range, then let the main endpoint grow. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_coordinate_centers_close (H : ℕ) :
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
      (99/100:ℝ)*fordBandScale x (i.val+1) ≤ 
        coordinateEnlargement (m x) (N+2) i*
          fordSimplexCenter N (B x+prefixCubeCost (N+2)) i ∧
      coordinateEnlargement (m x) (N+2) i*
          fordSimplexCenter N (B x+prefixCubeCost (N+2)) i ≤ 
        (101/100:ℝ)*fordBandScale x (i.val+1) := by
  filter_upwards [coordinateEnlargement_close,
    eventually_ge_atTop (max (1000*H) (H+3))] with P hκ hP
  filter_upwards [fixed_coordinate_budget_small H,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (1001*H+3))]
    with x hbudget hB hm
  intro N hN i hi
  have hiN : i.val+1 < N+2 := by have := i.isLt; omega
  have hNM : N+2 ≤ m x := by omega
  have hNpos : (0:ℝ) < ((N+2:ℕ):ℝ) := by positivity
  have hdim : m x-H=N+2 := by omega
  have hratio : 1 ≤ (m x:ℝ)/(N+2:ℕ) ∧
      (m x:ℝ)/(N+2:ℕ) ≤ (1001/1000:ℝ) := by
    constructor
    · apply (le_div_iff₀ hNpos).mpr
      simpa only [one_mul] using (Nat.cast_le.mpr hNM : (N+2:ℕ) ≤ (m x:ℝ))
    · apply (div_le_iff₀ hNpos).mpr
      have hlen : (1000*H:ℝ) ≤ (N+2:ℕ) := by
        exact_mod_cast (show 1000*H ≤ N+2 by omega)
      have he : (m x:ℝ)=(N+2:ℕ)+(H:ℝ) := by exact_mod_cast hN.symm
      linarith only [hlen,he]
  have htail : ((m x-(N+2):ℕ):ℝ)/(m x-(i.val+1):ℕ) ≤ (1/1000:ℝ) := by
    have hden : (0:ℝ) < (m x-(i.val+1):ℕ) := by exact_mod_cast (show 0 < m x-(i.val+1) by omega)
    apply (div_le_iff₀ hden).mpr
    have he : m x-(N+2)=H := by omega
    rw [he]
    have hh : (1000*H:ℝ) ≤ (m x-(i.val+1):ℕ) := by
      exact_mod_cast (show 1000*H ≤ m x-(i.val+1) by omega)
    linarith only [hh]
  have hb : 0 ≤ prefixCubeCost (N+2)/B x ∧
      prefixCubeCost (N+2)/B x ≤ (1/1000:ℝ) := by simpa only [hdim] using hbudget
  have hh := truncated_center_bounds hiN hNM hB
    ⟨coordinateEnlargement_one_le _ _ _,hκ _ _ i hi⟩ hb hratio htail
  simpa only [fordBandScale,fordSimplexCenter,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh

end TotientAsymptotic

end

end OAI
