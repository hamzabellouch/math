import Mathlib

namespace OAI


                                         
section

namespace MaximalSeshadri.NefNumerics
noncomputable section

lemma negative_boundary_perturbation (H c u v z α : ℤ) (r : ℕ) (w : ℝ)
    (_hH : 0 < H) (_hr : 0 < r) (hw : 0 < w) (hvol : (H:ℝ) = r*w^2)
    (hc : -(r:ℤ) ≤ c) (hneg : (u:ℝ)+w*v < 0)
    (hpos : 0 < (α:ℝ)*H+w*c) :
    ∃ k m b : ℕ, 0 < k ∧ 0 < m ∧ 0 < b ∧ (k:ℝ)*w < m ∧
      0 < (k:ℤ)^2*H+(m:ℤ)^2*c-2*b*((k:ℤ)*u+(m:ℤ)*v)+(b:ℤ)^2*z ∧
      0 ≤ (α:ℤ)*k*H+m*c-b*(α*u+v) := by
  let A : ℝ := -((u:ℝ)+w*v)
  let B : ℝ := (α:ℝ)*H+w*c
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := hpos
  let d := min (A/(|(z:ℝ)|+1)) (B/(|(α:ℝ)*u+v|+1)) / 2
  have hz : (0:ℝ) < |(z:ℝ)|+1 := by positivity
  have hy : (0:ℝ) < |(α:ℝ)*u+v|+1 := by positivity
  have hd : 0 < d := div_pos (lt_min (div_pos hA hz) (div_pos hB hy)) (by norm_num)
  have hd₁ : d < A/(|(z:ℝ)|+1) := by
    have hh := min_le_left (A/(|(z:ℝ)|+1)) (B/(|(α:ℝ)*u+v|+1))
    dsimp [d] at *
    linarith
  have hd₂ : d < B/(|(α:ℝ)*u+v|+1) := by
    have hh := min_le_right (A/(|(z:ℝ)|+1)) (B/(|(α:ℝ)*u+v|+1))
    dsimp [d] at *
    linarith
  have hdA : d*(|(z:ℝ)|+1) < A := (lt_div_iff₀ hz).mp hd₁
  have hdB : d*(|(α:ℝ)*u+v|+1) < B := (lt_div_iff₀ hy).mp hd₂
  let F : ℝ × ℝ → ℝ := fun p => H+c*p.1^2-2*p.2*(u+p.1*v)+p.2^2*z
  let G : ℝ × ℝ → ℝ := fun p => (α:ℝ)*H+p.1*c-p.2*(α*u+v)
  have hbase : 0 ≤ (H:ℝ)+c*w^2 := by
    have hcR : -(r:ℝ) ≤ c := by exact_mod_cast hc
    have hh := mul_le_mul_of_nonneg_right hcR (sq_nonneg w)
    nlinarith only [hh,hvol]
  have hf : 0 < F (w,d) := by
    have hh := mul_le_mul_of_nonneg_left (neg_abs_le (z:ℝ)) hd.le
    have hlin : 0 < 2*A+d*z := by nlinarith only [hh,hdA,hA,hd]
    have hp := mul_pos hd hlin
    dsimp [F,A] at *
    nlinarith only [hbase,hp]
  have hg : 0 < G (w,d) := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self ((α:ℝ)*u+v)) hd.le
    dsimp [G,B] at *
    nlinarith only [hh,hdB,hd]
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have he : ∀ᶠ p in nhds (w,d), 0 < F p ∧ 0 < G p :=
    (hF.continuousAt.eventually (Ioi_mem_nhds hf)).and
      (hG.continuousAt.eventually (Ioi_mem_nhds hg))
  obtain ⟨ε,hε,heε⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨s,hws,hs⟩ := exists_rat_btwn (show w < w+ε/2 by linarith)
  obtain ⟨t,hdt,ht⟩ := exists_rat_btwn (show d < d+ε/2 by linarith)
  have hst : dist ((s:ℝ),(t:ℝ)) (w,d) < ε := by
    rw [Prod.dist_eq, max_lt_iff,Real.dist_eq,Real.dist_eq,
      abs_of_pos (sub_pos.mpr hws),abs_of_pos (sub_pos.mpr hdt)]
    constructor <;> linarith
  obtain ⟨hFs,hGs⟩ := heε hst
  have hs0 : 0 < s := by exact_mod_cast (hw.trans hws)
  have ht0 : 0 < t := by exact_mod_cast (hd.trans hdt)
  let k := s.den*t.den
  let m := s.num.toNat*t.den
  let b := t.num.toNat*s.den
  have hk : 0 < k := Nat.mul_pos s.den_pos t.den_pos
  have hm : 0 < m := Nat.mul_pos (by have := Rat.num_pos.mpr hs0; omega) t.den_pos
  have hb : 0 < b := Nat.mul_pos (by have := Rat.num_pos.mpr ht0; omega) s.den_pos
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have em : (m:ℝ) = (k:ℝ)*(s:ℝ) := by
    dsimp [m,k]
    rw [Nat.cast_mul,Nat.cast_mul,← Int.cast_natCast,
      Int.toNat_of_nonneg (Rat.num_pos.mpr hs0).le,Rat.cast_def]
    have hz : (s.den:ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
    field_simp
  have eb : (b:ℝ) = (k:ℝ)*(t:ℝ) := by
    dsimp [b,k]
    rw [Nat.cast_mul,Nat.cast_mul,← Int.cast_natCast,
      Int.toNat_of_nonneg (Rat.num_pos.mpr ht0).le,Rat.cast_def]
    have hz : (t.den:ℝ) ≠ 0 := by exact_mod_cast t.den_ne_zero
    field_simp
  refine ⟨k,m,b,hk,hm,hb,?_,?_,?_⟩
  · rw [em]; exact mul_lt_mul_of_pos_left hws hkR
  · have hh := mul_pos (sq_pos_of_pos hkR) hFs
    have hh' : 0 < (k:ℝ)^2*H+(m:ℝ)^2*c-2*b*((k:ℝ)*u+(m:ℝ)*v)+(b:ℝ)^2*z := by
      rw [em,eb]
      dsimp [F] at hh
      nlinarith only [hh]
    exact_mod_cast hh'
  · have hh := mul_pos hkR hGs
    have hh' : 0 ≤ (α:ℝ)*k*H+m*c-b*(α*u+v) := by
      rw [em,eb]
      dsimp [G] at hh
      nlinarith only [hh]
    exact_mod_cast hh'

end
end MaximalSeshadri.NefNumerics

end


end OAI
