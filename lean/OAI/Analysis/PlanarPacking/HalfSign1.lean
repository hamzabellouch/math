import OAI.Analysis.PlanarPacking.HalfGapSmall
import OAI.Analysis.PlanarPacking.Certificate.Bernstein1

namespace OAI

namespace SharpPlanar
lemma halfSign_1_N0_right {s : ℝ} (hs : s ∈ Set.Icc 1 2) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(s-1)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (1:ℝ)+1*v=s := by dsimp [v]; ring
  have hh:=analytic_first_right_false hv (fun k => by have hh := (Bernstein1.N0_right.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (1:ℝ)+1*v=s := by simpa using he
  rw [he'] at hh
  simpa only [Bool.false_eq_true,ite_false,ite_true,neg_one_mul,one_mul] using hh
lemma halfSign_1_N1_right {s : ℝ} (hs : s ∈ Set.Icc 1 2) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-1)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (1:ℝ)+1*v=s := by dsimp [v]; ring
  have hh:=analytic_first_right_true hv (fun k => by have hh := (Bernstein1.N1_right.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (1:ℝ)+1*v=s := by simpa using he
  rw [he'] at hh
  simpa only [Bool.false_eq_true,ite_false,ite_true,neg_one_mul,one_mul] using hh
lemma halfSign_1_N1_left {s : ℝ} (hs : s ∈ Set.Icc (1/2) 1) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(1-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (1:ℝ)+(-1/2)*v=s := by dsimp [v]; ring
  have hh:=analytic_first_left hv (fun k => by have hh := (Bernstein1.N1_left.bound k).le; norm_num at hh ⊢; exact hh)
  have he' : (1:ℝ) + (-1/2)*v=s := by simpa using he
  rw [he'] at hh
  simpa only [Bool.false_eq_true,ite_false,ite_true,neg_one_mul,one_mul] using hh
end SharpPlanar

end OAI
