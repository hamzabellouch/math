import OAI.MeasureTheory.Falconer.Estimates.ScalarReverseGroupedWeights
import OAI.MeasureTheory.Falconer.Estimates.ScalarPorousLevel

namespace OAI

/-! The grouped logarithmic gain when the dense group lies in the first
 coordinate. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_reverse_grouped_log_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 15*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (L : ℕ) (hoccupancy : ∀ k : ℤ, (scalarGridFiber η w Y k).card ≤ L)
    (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log ((X.card : ℝ)*(Y.card : ℝ))+a-Real.log 17-
      (((X.card : ℝ)*(L:ℝ))^2*K*(5*r/μ)^κ)*Real.log (X.card : ℝ) ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  let G := fun p : ℝ × ℝ => scalarBadClusterCoefficients B X
    (scalarGridFiber η w Y ⌊(p.2-w)/η⌋) (5*r)
  let p : ℝ := (((X.card : ℝ)*(L:ℝ))^2*K*(5*r/μ)^κ)
  let W := fun x b => scalarCollisionWeight (X.card : ℝ) (G x) b/17
  let Q := fun (x : ℝ × ℝ) (b : ℝ) => ((scalarCells δ (U x.1+(V x.2).image (fun c => b*c))).card : ℝ)
  let R := fun b => ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)
  have hr0 : 0 ≤ r := hδ.le.trans hδr
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hXn : 1 ≤ (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hwpos : ∀ x ∈ X ×ˢ Y, ∀ b ∈ B, 0 < W x b := by
    intro x _ b _
    exact div_pos (scalarCollisionWeight_pos (by linarith) (G x) b) (by norm_num)
  have hwlog : ∀ x ∈ X ×ˢ Y,
      -Real.log 17-p*Real.log (X.card : ℝ) ≤ scalarAverage B (fun b => Real.log (W x b)) := by
    intro x _hx
    have hgb : G x ⊆ B := Finset.filter_subset _ _
    have hgc : ((G x).card : ℝ) ≤ p*(B.card : ℝ) := by
      have hh := scalar_bad_cluster_card hμ (by positivity : 0 ≤ 5*r) (by linarith : 5*r < μ)
        hK hscale hscale1 B X (scalarGridFiber η w Y ⌊(x.2-w)/η⌋) hXsep
        (fun u hu v hv huv => hYsep u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv) hball
      change ((G x).card : ℝ) ≤ _ at hh
      calc
        _ ≤ _ := hh
        _ ≤ p*(B.card : ℝ) := by
          dsimp [p]
          have hc : ((scalarGridFiber η w Y ⌊(x.2-w)/η⌋).card : ℝ) ≤ (L:ℝ) := by
            exact_mod_cast hoccupancy ⌊(x.2-w)/η⌋
          have hmul := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ (X.card : ℝ) by positivity)
          have hsq := pow_le_pow_left₀
            (show (0:ℝ) ≤ (X.card : ℝ)*((scalarGridFiber η w Y ⌊(x.2-w)/η⌋).card : ℝ) by positivity) hmul 2
          have hb := mul_le_mul_of_nonneg_right hsq
            (show (0:ℝ) ≤ K*(5*r/μ)^κ*(B.card : ℝ) by positivity)
          convert hb using 1
          ring
    have hmean : -p*Real.log (X.card : ℝ) ≤
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (X.card : ℝ) (G x) b)) := by
      have hh := scalarCollisionWeight_log_bound B (G x) hgb hXn hgc
      apply (le_div_iff₀ hn).2
      change (-p*Real.log (X.card : ℝ))*(B.card : ℝ) ≤ _
      simpa only [mul_comm] using hh
    have he : scalarAverage B (fun b => Real.log (W x b)) =
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (X.card : ℝ) (G x) b))-Real.log 17 := by
      calc
        _ = scalarAverage B (fun b => Real.log (scalarCollisionWeight (X.card : ℝ) (G x) b)+(-Real.log 17)) := by
          unfold scalarAverage
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          exact Real.log_div (scalarCollisionWeight_pos (by linarith) (G x) b).ne' (by norm_num)
        _ = _ := by rw [scalarAverage_add,scalarAverage_const B hB]; ring
    rw [he]
    linarith
  have hstep : ∀ b ∈ B, (∑ x ∈ X ×ˢ Y, W x b*Q x b) ≤ R b := by
    intro b hb
    have hh := scalar_reverse_grouped_weighted_cells (w := w) hδ hη hδr hrη hgap
      (hBb b hb).1 (hBb b hb).2 B X Y hb hX j hXgrid hYsep U V hU hV
    have he : (∑ x ∈ X ×ˢ Y, W x b*Q x b) =
        (∑ x ∈ X ×ˢ Y, scalarCollisionWeight (X.card : ℝ) (G x) b*Q x b)/17 := by
      dsimp only [W]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [he]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 17)).2
    simpa only [G,Q,R,mul_comm] using hh
  have h := scalar_average_weighted_children (X ×ˢ Y) B (hX.product hY) hB Q W R
    (fun x hx b _ => scalar_sum_cells_pos _ _ (hUne x.1 (Finset.mem_product.mp hx).1)
      (hVne x.2 (Finset.mem_product.mp hx).2)) hwpos hstep hchild hwlog
  rw [Finset.card_product,Nat.cast_mul] at h
  dsimp [p] at h
  linarith

end Falconer

end OAI
