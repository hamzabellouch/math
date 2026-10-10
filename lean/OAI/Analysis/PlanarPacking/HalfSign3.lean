import OAI.Analysis.PlanarPacking.HalfGapSmall
import OAI.Analysis.PlanarPacking.Certificate.Bernstein3

namespace OAI

namespace SharpPlanar
lemma halfSign_3_N0_right {s : ℝ} (hs : s ∈ Set.Icc 3 (7/2)) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(s-3)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (3:ℝ)+(1/2)*v=s := by dsimp [v]; ring
  have hh:=analytic_3_right false hv (fun k => by have hh := (Bernstein3.N0_right.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (3:ℝ)+(1/2)*v=s := he
  rw [he'] at hh
  exact hh
lemma halfSign_3_N1_right {s : ℝ} (hs : s ∈ Set.Icc 3 (7/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-3)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (3:ℝ)+(1/2)*v=s := by dsimp [v]; ring
  have hh:=analytic_3_right true hv (fun k => by have hh := (Bernstein3.N1_right.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (3:ℝ)+(1/2)*v=s := he
  rw [he'] at hh
  exact hh
lemma halfSign_3_N0_left {s : ℝ} (hs : s ∈ Set.Icc 2 3) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(3-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (3:ℝ)+-1*v=s := by dsimp [v]; ring
  have hh:=analytic_3_left false hv (fun k => by have hh := (Bernstein3.N0_left.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (3:ℝ)+-1*v=s := he
  rw [he'] at hh
  exact hh
lemma halfSign_3_N1_left {s : ℝ} (hs : s ∈ Set.Icc 2 3) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(3-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (3:ℝ)+-1*v=s := by dsimp [v]; ring
  have hh:=analytic_3_left true hv (fun k => by have hh := (Bernstein3.N1_left.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (3:ℝ)+-1*v=s := he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
