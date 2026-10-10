import OAI.Analysis.PlanarPacking.Certificate.Bernstein0
import OAI.Analysis.PlanarPacking.HalfGapTypes

namespace OAI

namespace SharpPlanar
lemma halfSign_0_N1_right {s : ℝ} (hs : s ∈ Set.Icc 0 (1/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-0)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (0:ℝ)+(1/2)*v=s := by dsimp [v]; ring
  have hh:=analytic_zero hv (fun k => by have hh := (Bernstein0.N1_right.bound k).le; norm_num at hh ⊢; exact hh)
  rw [he] at hh
  simp only [ite_true,one_mul]
  linarith
end SharpPlanar

end OAI
