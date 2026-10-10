import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupedWeights
import OAI.MeasureTheory.Falconer.Estimates.ScalarPorousLevel

namespace OAI

/-! A porous gain with unrestricted horizontal branching. Only the
 occupancy of individual horizontal groups enters the exceptional loss. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_grouped_log_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 5*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (L : ℕ) (hoccupancy : ∀ k : ℤ, (scalarGridFiber η z X k).card ≤ L)
    (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log ((X.card : ℝ)*(Y.card : ℝ))+a-Real.log 9-
      (((L:ℝ)*(Y.card : ℝ))^2*K*(5*r/μ)^κ)*Real.log (Y.card : ℝ) ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  let G := fun p : ℝ × ℝ => scalarBadClusterCoefficients B
    (scalarGridFiber η z X ⌊(p.1-z)/η⌋) Y (5*r)
  let p : ℝ := (((L:ℝ)*(Y.card : ℝ))^2*K*(5*r/μ)^κ)
  let W := fun x b => scalarCollisionWeight (Y.card : ℝ) (G x) b/9
  let Q := fun (x : ℝ × ℝ) (b : ℝ) => ((scalarCells δ (U x.1+(V x.2).image (fun c => b*c))).card : ℝ)
  let R := fun b => ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)
  have hr0 : 0 ≤ r := hδ.le.trans hδr
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hYn : 1 ≤ (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hwpos : ∀ x ∈ X ×ˢ Y, ∀ b ∈ B, 0 < W x b := by
    intro x _ b _
    exact div_pos (scalarCollisionWeight_pos (by linarith) (G x) b) (by norm_num)
  have hwlog : ∀ x ∈ X ×ˢ Y,
      -Real.log 9-p*Real.log (Y.card : ℝ) ≤ scalarAverage B (fun b => Real.log (W x b)) := by
    intro x _hx
    have hgb : G x ⊆ B := Finset.filter_subset _ _
    have hgc : ((G x).card : ℝ) ≤ p*(B.card : ℝ) := by
      have hh := scalar_bad_cluster_card hμ (by positivity : 0 ≤ 5*r) hgap hK hscale hscale1
        B (scalarGridFiber η z X ⌊(x.1-z)/η⌋) Y
        (fun u hu v hv huv => hXsep u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv)
        hYsep hball
      change ((G x).card : ℝ) ≤ _ at hh
      calc
        _ ≤ _ := hh
        _ ≤ p*(B.card : ℝ) := by
          dsimp [p]
          have hc : ((scalarGridFiber η z X ⌊(x.1-z)/η⌋).card : ℝ) ≤ (L:ℝ) := by
            exact_mod_cast hoccupancy ⌊(x.1-z)/η⌋
          have hmul := mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ (Y.card : ℝ) by positivity)
          have hsq := pow_le_pow_left₀
            (show (0:ℝ) ≤ ((scalarGridFiber η z X ⌊(x.1-z)/η⌋).card : ℝ)*(Y.card : ℝ) by positivity) hmul 2
          have hb := mul_le_mul_of_nonneg_right hsq
            (show (0:ℝ) ≤ K*(5*r/μ)^κ*(B.card : ℝ) by positivity)
          convert hb using 1
          ring
    have hmean : -p*Real.log (Y.card : ℝ) ≤
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (Y.card : ℝ) (G x) b)) := by
      have hh := scalarCollisionWeight_log_bound B (G x) hgb hYn hgc
      apply (le_div_iff₀ hn).2
      change (-p*Real.log (Y.card : ℝ))*(B.card : ℝ) ≤ _
      simpa only [G,Q,R,mul_comm] using hh
    have he : scalarAverage B (fun b => Real.log (W x b)) =
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (Y.card : ℝ) (G x) b))-Real.log 9 := by
      calc
        _ = scalarAverage B (fun b => Real.log (scalarCollisionWeight (Y.card : ℝ) (G x) b)+(-Real.log 9)) := by
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
    have hh := scalar_grouped_weighted_cells (z := z) hδ hη hδr hrη hgap (hBb b hb).1 (hBb b hb).2
      B X Y hb hY j hYgrid hXsep U V hU hV
    have he : (∑ x ∈ X ×ˢ Y, W x b*Q x b) =
        (∑ x ∈ X ×ˢ Y, scalarCollisionWeight (Y.card : ℝ) (G x) b*Q x b)/9 := by
      dsimp only [W]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [he]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 9)).2
    simpa only [G,Q,R,mul_comm] using hh
  have h := scalar_average_weighted_children (X ×ˢ Y) B (hX.product hY) hB Q W R
    (fun x hx b _ => scalar_sum_cells_pos _ _ (hUne x.1 (Finset.mem_product.mp hx).1)
      (hVne x.2 (Finset.mem_product.mp hx).2)) hwpos hstep hchild hwlog
  rw [Finset.card_product,Nat.cast_mul] at h
  dsimp [p] at h
  linarith

end Falconer

end OAI
