import OAI.Analysis.PlanarPacking.HalfGapTypes
import OAI.Analysis.PlanarPacking.Certificate.Bernstein28

namespace OAI

namespace SharpPlanar
lemma halfSign_28_N0_right {s : ℝ} (hs : s ∈ Set.Icc 28 (59/2)) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(s-28)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (28:ℝ)+(3/2)*v=s := by dsimp [v]; ring
  let n : Node:=⟨28,by decide +kernel⟩
  have hh:=analytic_large false n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein28.N0_right.bound k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_28_N1_right {s : ℝ} (hs : s ∈ Set.Icc 28 (59/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-28)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (28:ℝ)+(3/2)*v=s := by dsimp [v]; ring
  let n : Node:=⟨28,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein28.N1_right.bound k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_28_N0_left {s : ℝ} (hs : s ∈ Set.Icc (55/2) 28) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  let v : ℝ:=(28-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (28:ℝ)+(-1/2)*v=s := by dsimp [v]; ring
  let n : Node:=⟨28,by decide +kernel⟩
  have hh:=analytic_large false n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein28.N0_left.bound k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_28_N1_left {s : ℝ} (hs : s ∈ Set.Icc (55/2) 28) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(28-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (28:ℝ)+(-1/2)*v=s := by dsimp [v]; ring
  let n : Node:=⟨28,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein28.N1_left.bound k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
