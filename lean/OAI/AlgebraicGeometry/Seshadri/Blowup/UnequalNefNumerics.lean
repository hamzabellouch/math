import Mathlib

namespace OAI


                                            
section

namespace MaximalSeshadri.NefNumerics
noncomputable section
open Set Topology

lemma exists_bounded_rational_perturbation {H r w d E B : ℝ}
    (hH : 0 < H) (hw : 0 < w) (hd : 0 < d) (hE : 0 ≤ E)
    (hsquare : H-r*w^2=0) (hneg : d-w*E<0) :
    ∃ δ s : ℚ, 0 < δ ∧ 0 < s ∧ w < (s:ℝ) ∧ (δ:ℝ)*E < w ∧
      0 < H-r*(s:ℝ)^2-2*(δ:ℝ)*(d-(s:ℝ)*E)+(δ:ℝ)^2*B ∧
      0 < H-(δ:ℝ)*d := by
  have hb : 0 < |B|+1 := by positivity
  have hh : 0 < min (H/(d+1)) (min (-(d-w*E)/(|B|+1)) (w/(E+1))) := by
    exact lt_min (div_pos hH (by linarith))
      (lt_min (div_pos (neg_pos.mpr hneg) hb) (div_pos hw (by linarith)))
  obtain ⟨δ,hδ,hδb⟩ := exists_rat_btwn hh
  have hδd := (lt_div_iff₀ (show 0 < d+1 by linarith)).mp
    (hδb.trans_le (min_le_left _ _))
  have hδB := (lt_div_iff₀ hb).mp
    (hδb.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hδE := (lt_div_iff₀ (show 0 < E+1 by linarith)).mp
    (hδb.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hmul := mul_le_mul_of_nonneg_left (neg_abs_le B) hδ.le
  have hfac : 0 < -2*(d-w*E)+(δ:ℝ)*B := by nlinarith
  have hquad : 0 < -2*(δ:ℝ)*(d-w*E)+(δ:ℝ)^2*B := by
    nlinarith only [mul_pos hδ hfac]
  let f : ℝ → ℝ := fun s => H-r*s^2-2*(δ:ℝ)*(d-s*E)+(δ:ℝ)^2*B
  have hfw : 0 < f w := by dsimp [f]; rw [hsquare]; simpa using hquad
  have hopen : IsOpen {s | 0 < f s} := isOpen_lt continuous_const (by fun_prop)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen w hfw
  obtain ⟨s,hsw,hsε⟩ := exists_rat_btwn (show w<w+ε by linarith)
  have hsball : (s:ℝ) ∈ Metric.ball w ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hsw)]; linarith
  exact ⟨δ,s,by exact_mod_cast hδ,by exact_mod_cast hw.trans hsw,hsw,
    by linarith,hball hsball,by linarith⟩

lemma rational_positive_common_scale (δ s : ℚ) (hδ : 0 < δ) (hs : 0 < s) :
    ∃ a b m : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧
      (b:ℝ) = (a:ℝ)*(δ:ℝ) ∧ (m:ℝ) = (a:ℝ)*(s:ℝ) := by
  have hd : 0 < δ.num := Rat.num_pos.mpr hδ
  have ht : 0 < s.num := Rat.num_pos.mpr hs
  refine ⟨δ.den*s.den,δ.num.toNat*s.den,s.num.toNat*δ.den,
    Nat.mul_pos δ.den_pos s.den_pos,
    Nat.mul_pos (by omega) s.den_pos,
    Nat.mul_pos (by omega) δ.den_pos,?_,?_⟩
  · have he : (δ.num.toNat:ℝ) = (δ.num:ℝ) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hd.le]
    rw [Nat.cast_mul,Nat.cast_mul,he,Rat.cast_def]
    have hn : (δ.den:ℝ) ≠ 0 := by exact_mod_cast δ.den_ne_zero
    field_simp
  · have he : (s.num.toNat:ℝ) = (s.num:ℝ) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg ht.le]
    rw [Nat.cast_mul,Nat.cast_mul,he,Rat.cast_def]
    have hn : (s.den:ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
    field_simp

theorem exists_integral_unequal_perturbation {r : ℕ} (μ : Fin r → ℕ)
    (H d Q : ℤ) (hH : 0 < H) (hr : 0 < r) (hd : 0 < d)
    (hneg : (d:ℝ)-Real.sqrt ((H:ℝ)/r)*(∑ i, μ i : ℕ) < 0) :
    ∃ a b m : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧
      (a:ℝ)*Real.sqrt ((H:ℝ)/r) < m ∧
      (∀ i, b*μ i ≤ m) ∧ 0 ≤ (a:ℤ)*H-(b:ℤ)*d ∧
      (∑ i, (m-b*μ i)^2 : ℕ) <
        (a:ℤ)^2*H-2*(a:ℤ)*(b:ℤ)*d+(b:ℤ)^2*Q := by
  let w := Real.sqrt ((H:ℝ)/r)
  let E : ℕ := ∑ i, μ i
  let W : ℕ := ∑ i, (μ i)^2
  have hHr : 0 < (H:ℝ) := by exact_mod_cast hH
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hHr hrr)
  have hsquare : (H:ℝ)-(r:ℝ)*w^2=0 := by
    dsimp [w]; rw [Real.sq_sqrt (div_nonneg hHr.le hrr.le)]; field_simp; ring
  obtain ⟨δ,s,hδ,hs,hsw,hδE,hquad,hmix⟩ := exists_bounded_rational_perturbation
    hHr hw (show 0 < (d:ℝ) by exact_mod_cast hd) (Nat.cast_nonneg E) hsquare
    (B := (Q:ℝ)-W) hneg
  obtain ⟨a,b,m,ha,hb,hm,eb,em⟩ := rational_positive_common_scale δ s hδ hs
  have har : 0 < (a:ℝ) := by exact_mod_cast ha
  have hbr : 0 < (b:ℝ) := by exact_mod_cast hb
  have hbm (i : Fin r) : b*μ i ≤ m := by
    have hi : μ i ≤ E := Finset.single_le_sum (fun j _ => Nat.zero_le (μ j)) (Finset.mem_univ i)
    have hE' : (δ:ℝ)*(μ i:ℝ) < (s:ℝ) :=
      (mul_le_mul_of_nonneg_left (show (μ i:ℝ) ≤ (E:ℝ) by exact_mod_cast hi) (show 0 ≤ (δ:ℝ) by exact_mod_cast hδ.le)).trans_lt (hδE.trans hsw)
    have H' := mul_lt_mul_of_pos_left hE' har
    rw [← mul_assoc,← eb,← em] at H'
    exact_mod_cast H'.le
  refine ⟨a,b,m,ha,hb,hm,?_,hbm,?_,?_⟩
  · rw [em]; exact mul_lt_mul_of_pos_left hsw har
  · have hh := mul_pos har hmix
    rw [mul_sub,← mul_assoc,← eb] at hh
    exact_mod_cast hh.le
  · have hsum : ((∑ i, (m-b*μ i)^2 : ℕ):ℝ) =
        (r:ℝ)*(m:ℝ)^2-2*(m:ℝ)*(b:ℝ)*E+(b:ℝ)^2*W := by
      simp only [Nat.cast_sum,Nat.cast_pow,Nat.cast_sub (hbm _),Nat.cast_mul]
      calc
        ∑ i : Fin r, ((m:ℝ)-(b:ℝ)*(μ i:ℝ))^2 =
            ∑ i : Fin r, ((m:ℝ)^2-2*(m:ℝ)*(b:ℝ)*(μ i:ℝ)+(b:ℝ)^2*(μ i:ℝ)^2) := by
          apply Finset.sum_congr rfl; intro i hi; ring
        _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,E,W]
    have hquad' := mul_pos (sq_pos_of_pos har) hquad
    have hh : ((∑ i, (m-b*μ i)^2 : ℕ):ℝ) <
        (a:ℝ)^2*H-2*(a:ℝ)*(b:ℝ)*d+(b:ℝ)^2*Q := by
      rw [hsum,eb,em]
      nlinarith only [hquad']
    exact_mod_cast hh

end
end MaximalSeshadri.NefNumerics

end



end OAI
