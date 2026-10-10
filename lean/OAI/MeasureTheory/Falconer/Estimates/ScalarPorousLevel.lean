import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterWeights
import OAI.MeasureTheory.Falconer.Estimates.ScalarTreeAmplification

namespace OAI

/-! The scalar porous one-level gain for actual finite sets. This combines
 separated children, the original coefficient ball bound, and logarithmic
 averaging with its explicit exceptional-set loss. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_sum_cells_pos {δ b : ℝ} (A C : Finset ℝ)
    (hA : A.Nonempty) (hC : C.Nonempty) :
    0 < ((scalarCells δ (A+C.image (fun c => b*c))).card : ℝ) := by
  classical
  obtain ⟨a,ha⟩ := hA
  obtain ⟨c,hc⟩ := hC
  have hh : (scalarCells δ (A+C.image (fun c => b*c))).Nonempty :=
    ⟨⌊(a+b*c)/δ⌋,Finset.mem_image.mpr
      ⟨a+b*c,Finset.add_mem_add ha (Finset.mem_image.mpr ⟨c,hc,rfl⟩),rfl⟩⟩
  exact_mod_cast hh.card_pos

 theorem scalar_porous_level_log_gain {δ r μ K κ a : ℝ}
    (hδ : 0 < δ) (hr : δ ≤ r) (hμ : 0 < μ) (hgap : 5*r < μ)
    (hK : 0 ≤ K) (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hBbound : ∀ b ∈ B, |b| ≤ 1)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ z ∈ U x, |z-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ z ∈ V y, |z-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y,
      a ≤ scalarAverage B (fun b => Real.log
        ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log ((X.card : ℝ)*(Y.card : ℝ))+a-
      (((X.card : ℝ)*(Y.card : ℝ))^2*K*(5*r/μ)^κ)*Real.log (Y.card : ℝ) ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  have hr0 : 0 ≤ r := hδ.le.trans hr
  let G := scalarBadClusterCoefficients B X Y (5*r)
  let p : ℝ := ((X.card : ℝ)*(Y.card : ℝ))^2*K*(5*r/μ)^κ
  let w := scalarCollisionWeight (Y.card : ℝ) G
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hYn : 1 ≤ (Y.card : ℝ) := by exact_mod_cast hYne.card_pos
  have hgb : G ⊆ B := Finset.filter_subset _ _
  have hgc : (G.card : ℝ) ≤ p*(B.card : ℝ) := by
    have hh := scalar_bad_cluster_card hμ (by positivity : 0 ≤ 5*r) hgap hK
      hscale hscale1 B X Y hX hY hball
    convert hh using 1
    dsimp [p]
    ring
  have hell : -p*Real.log (Y.card : ℝ) ≤ scalarAverage B (fun b => Real.log (w b)) := by
    have hh := scalarCollisionWeight_log_bound B G hgb hYn hgc
    apply (le_div_iff₀ hn).2
    change (-p*Real.log (Y.card : ℝ))*(B.card : ℝ) ≤ _
    simpa only [mul_comm] using hh
  have hs := scalar_average_weighted_branch (X ×ˢ Y) B (hXne.product hYne) hB
    (fun p b => ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))
    w (fun b => ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ))
    (fun p hp b _ => scalar_sum_cells_pos _ _ (hUne p.1 (Finset.mem_product.mp hp).1)
      (hVne p.2 (Finset.mem_product.mp hp).2))
    (fun b _ => scalarCollisionWeight_pos (by linarith : 0 < (Y.card : ℝ)) G b)
    (fun b hb => scalar_cluster_weighted_cells hδ hr hgap (hBbound b hb)
      B X Y hb hYne hX U V hU hV) hchild hell
  rw [Finset.card_product,Nat.cast_mul] at hs
  dsimp [p] at hs
  linarith

end Falconer

end OAI
