import OAI.MeasureTheory.Falconer.Estimates.ScalarReverseGroupedGain

namespace OAI

/-! Explicit positive gain from a dense first-coordinate group. The second-coordinate
 family may have arbitrarily many children. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_reverse_grouped_half_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 15*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ) (hM : 83521 ≤ M) (hXcard : X.card = M)
    (hoccupancy : ∀ k : ℤ, (scalarGridFiber η w Y k).card ≤ 4*M)
    (hsmall : 16*(M:ℝ)^4*K*(5*r/μ)^κ ≤ 1/4)
    (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log (Y.card : ℝ)+(1/2 : ℝ)*Real.log (M:ℝ)+a ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  have hh := scalar_reverse_grouped_log_gain hδ hη hδr hrη hμ hgap hK hscale hscale1
    B X Y hB hX hY hBb hXsep hYsep hball (4*M) hoccupancy j hXgrid U V hUne hVne hU hV hchild
  rw [hXcard,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hm : 0 < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hy : 0 < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  rw [Real.log_mul hm.ne' hy.ne'] at hh
  have hbase : (17:ℝ)^4 ≤ (M:ℝ) := by exact_mod_cast hM
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 17^4) hbase
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm1 : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hp := mul_le_mul_of_nonneg_right hsmall (Real.log_nonneg hm1)
  have he : ((M:ℝ)*(4*(M:ℝ)))^2*K*(5*r/μ)^κ = 16*(M:ℝ)^4*K*(5*r/μ)^κ := by ring
  rw [he] at hh
  nlinarith

end Falconer

end OAI
