import OAI.Analysis.PlanarPacking.HalfGapTypes
import OAI.Analysis.PlanarPacking.Certificate.Bernstein13

namespace OAI

namespace SharpPlanar
lemma halfSign_13_N0_right {s : ℝ} (hs : s ∈ Set.Icc 13 14) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(s-13)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (13:ℝ)+1*v=s := by dsimp [v]; ring
  let n : Node:=⟨13,by decide +kernel⟩
  have hh:=analytic_large false n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein13.N0_right.bound k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_13_N1_right {s : ℝ} (hs : s ∈ Set.Icc 13 14) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-13)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (13:ℝ)+1*v=s := by dsimp [v]; ring
  let n : Node:=⟨13,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein13.N1_right.bound k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_13_N0_left {s : ℝ} (hs : s ∈ Set.Icc (25/2) 13) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(13-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (13:ℝ)+(-1/2)*v=s := by dsimp [v]; ring
  let n : Node:=⟨13,by decide +kernel⟩
  have hh:=analytic_large false n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein13.N0_left.bound k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_13_N1_left {s : ℝ} (hs : s ∈ Set.Icc (25/2) 13) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(13-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (13:ℝ)+(-1/2)*v=s := by dsimp [v]; ring
  let n : Node:=⟨13,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein13.N1_left.bound k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
