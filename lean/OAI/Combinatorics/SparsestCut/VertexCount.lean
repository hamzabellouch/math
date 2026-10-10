import OAI.Combinatorics.SparsestCut.LabelCount

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceCount
open SourceCharts SourceParameters SourceMetric
open scoped BigOperators
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]
lemma integer_bound (hm : 5 ≤ m) (v : V f) (i : Fin (m^6)) : |(v.val.2 i:ℝ)|≤(m:ℝ)^2003 := by
  have hm0 := NeZero.pos m
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hx5 : (5:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0:ℝ)< m := by exact_mod_cast hm0
  obtain ⟨θ,hθ,hr,he⟩ := v.property
  have h := RoundedCharts.integerLabel_bound (u f v.val.1) (p_pos hx0 2000)
    (fun i => (u_norm f hm0 v.val.1 i).2) hθ i
  rw [he] at h
  calc
    _ ≤ 4*Real.sqrt m/p m 2000+1 := h
    _ ≤ 4*(m:ℝ)/p m 2000+1 := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_right _ (p_nonneg hx0.le _)
      exact mul_le_mul_of_nonneg_left (sqrt_le hx) (by norm_num)
    _ = 4*(m:ℝ)^2001+1 := by unfold p; field_simp
    _ ≤ 5*(m:ℝ)^2001 := by nlinarith [one_le_pow₀ hx (n:=2001)]
    _ ≤ (m:ℝ)*(m:ℝ)^2001 := mul_le_mul_of_nonneg_right hx5 (by positivity)
    _ = (m:ℝ)^2002 := by ring
    _ ≤ _ := pow_le_pow_right₀ hx (by norm_num)
lemma card_bound (hm : 5 ≤ m) : Fintype.card (V f)≤ m^(4025*m) := by
  have hm0 := NeZero.pos m
  have hx0 : (0:ℝ)< m := by exact_mod_cast hm0
  let B : ℤ := (m:ℤ)^2003
  have hB : ∀ v : V f, ∀ i, v.val.2 i∈Finset.Icc (-B) B := by
    intro v i
    have h := integer_bound f hm v i
    have h' : |v.val.2 i|≤B := by exact_mod_cast h
    simpa only [Finset.mem_Icc,abs_le] using h'
  have h := LabelCount.vertex_count (u f) (p_pos hx0 2000) B hB
  have hI : (Finset.Icc (-B) B).card=2*m^2003+1 := by
    rw [Int.card_Icc]
    dsimp [B]
    have he : (m:ℤ)^2003+1-(-(m:ℤ)^2003)=((2*m^2003+1:ℕ):ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  rw [hI] at h
  have hm1 : 1 ≤ m := by omega
  have hp : 1≤ m^2003 := one_le_pow₀ hm1
  have hI' : 2*m^2003+1≤ m^2004 := by
    calc
      _ ≤ 3*m^2003 := by omega
      _ ≤ m*m^2003 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hH : m^6*(2*m^2003+1)+1≤ m^2011 := by
    calc
      _ ≤ m^6*m^2004+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hI') _
      _ = m^2010+1 := by ring
      _ ≤ 2*m^2010 := by have hh := one_le_pow₀ hm1 (n:=2010); omega
      _ ≤ m*m^2010 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  calc
    _ ≤ m^3*(m^6*(2*m^2003+1)+1)^(m+1) := h
    _ ≤ m^3*(m^2011)^(m+1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hH _)
    _ = m^(3+2011*(m+1)) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hm1 (by omega)
end
end UniformSparsestCut.SourceCount

end

end OAI
