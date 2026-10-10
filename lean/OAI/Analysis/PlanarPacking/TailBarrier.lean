import OAI.Analysis.PlanarPacking.Barrier

namespace OAI

namespace SharpPlanar
lemma P_local_lower (k a : ℕ) (ha : a∈residues) {s : ℝ}
    (hu : s-(12*(k:ℝ)+a) ∈ Set.Icc (-leftHalf a) (rightHalf a)) :
    (17/25:ℝ)*(s-(12*(k:ℝ)+a))^2 ≤ P s := by
  have hv:=dividedP_lower a ha hu
  have hf:=dividedP_factor a ha (s-(12*(k:ℝ)+a))
  have he : P ((a:ℝ)+(s-(12*(k:ℝ)+a)))=P s := by
    convert (show Function.Periodic P (12:ℝ) from P_period).sub_int_mul_eq (k:ℤ) (x:=s) using 1
    push_cast
    congr 1
    ring
  rw [he] at hf
  nlinarith [mul_nonneg (sq_nonneg (s-(12*(k:ℝ)+a))) (sub_nonneg.mpr hv)]
lemma tail_node_of_half (s : ℝ) (hs : (83:ℝ)/2 ≤ s) (k a : ℕ) (ha : a∈residues)
    (hu : s-(12*(k:ℝ)+a) ∈ Set.Icc (-leftHalf a) (rightHalf a))
    (hm : s-(12*(k:ℝ)+a) < (3:ℝ)/2) :
    ∃ n : Node,40 < n.val ∧ (83:ℝ)/2 ≤ n.val ∧ (17/25:ℝ)*(s-n.val)^2 ≤ P s := by
  have hv : (40:ℝ) < 12*(k:ℝ)+a := by linarith
  have hn : 40 < 12*k+a := by exact_mod_cast hv
  have hr : (12*k+a)%12∈residues := by
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,zero_add,
      Nat.mod_eq_of_lt (residue_lt ha)] using ha
  let n : Node:=⟨12*k+a,by omega,hr⟩
  have he : (n.val:ℝ)=12*(k:ℝ)+a := by simp [n]
  have hn43 : 43 ≤ n.val := by
    have hh : 40 < n.val := hn
    have hg:=n.prop.2
    by_contra hh'
    have hc : n.val=41 ∨ n.val=42 := by omega
    rcases hc with hc|hc <;> norm_num [hc,residues] at hg
  have hn43' : (43:ℝ) ≤ n.val := by exact_mod_cast hn43
  exact ⟨n,hn,by linarith,by rw [he]; exact P_local_lower k a ha hu⟩
lemma tail_barrier_node {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    ∃ n : Node,40 < n.val ∧ (83:ℝ)/2 ≤ n.val ∧ (17/25:ℝ)*(s-n.val)^2 ≤ P s := by
  let k : ℕ:=⌊s/12⌋₊
  have hk : (k:ℝ) ≤ s/12 := Nat.floor_le (by linarith : (0:ℝ) ≤ s/12)
  have hk' : s/12 < (k:ℝ)+1 := Nat.lt_floor_add_one _
  let r : ℝ:=s-12*(k:ℝ)
  have hr : 0 ≤ r ∧ r < 12 := by dsimp [r]; constructor <;> linarith
  by_cases h0 : r < (1:ℝ)/2
  · apply tail_node_of_half s hs k 0 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at *; norm_num; linarith
  by_cases h1 : r < 2
  · apply tail_node_of_half s hs k 1 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at *; norm_num; linarith
  by_cases h3 : r < (7:ℝ)/2
  · apply tail_node_of_half s hs k 3 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at *; norm_num; linarith
  by_cases h4 : r < (11:ℝ)/2
  · apply tail_node_of_half s hs k 4 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at *; norm_num; linarith
  by_cases h7 : r < 8
  · apply tail_node_of_half s hs k 7 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at *; norm_num; linarith
  by_cases h9 : r < (21:ℝ)/2
  · apply tail_node_of_half s hs k 9 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at *; norm_num; linarith
  · apply tail_node_of_half s hs (k+1) 0 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf,Nat.cast_add]; dsimp [r] at *; constructor <;> linarith
    · norm_num [Nat.cast_add]; dsimp [r] at *; linarith
end SharpPlanar

end OAI
