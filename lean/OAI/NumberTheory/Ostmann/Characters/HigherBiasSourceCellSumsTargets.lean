import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsMass

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource

theorem exists_target_interior_length
    (c b T : ℝ) (a g s r R q : ℕ)
    (_hc : 0 < c) (hb : 1 ≤ b) (hg : 0 < g) (hs : 0 < s)
    (hr : r ≤ R) (hq : 6 ≤ (q:ℝ)*c)
    (ha : b ≤ (a:ℝ)) (hu : (a:ℝ)+(g:ℝ)*s ≤ 3*b)
    (hw : c*b ≤ (g:ℝ)*s)
    (hT : ((6*(R+q+1):ℕ):ℝ) ≤ T/b) :
    ∃ n : ℕ, r ≤ n ∧
      (r:ℝ)*((g:ℝ)*s) ≤ T-(n:ℝ)*a ∧ T-(n:ℝ)*a ≤ ((n:ℝ)-r)*((g:ℝ)*s) ∧
      T/(6*b) ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*T/b := by
  let w : ℝ := (g:ℝ)*s
  let m : ℝ := (a:ℝ)+w/2
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hg0 : (0:ℝ) < g := by exact_mod_cast hg
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  have hw0 : 0 < w := mul_pos hg0 hs0
  have hm0 : 0 < m := by dsimp [m]; linarith
  have hbm : b ≤ m := by dsimp [m]; linarith
  have hm3 : m ≤ 3*b := by dsimp [m,w]; linarith
  have hTN : (6*((R:ℝ)+q+1))*b ≤ T := by
    have hh := (le_div_iff₀ hb0).mp hT
    norm_num at hh ⊢
    exact hh
  have hT0 : 0 < T := by
    have hR0 : (0:ℝ) ≤ R := Nat.cast_nonneg R
    have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  let n : ℕ := ⌊T/m⌋₊
  have hnlo : 2*(R+q) ≤ n := by
    apply (Nat.le_floor_iff (div_nonneg hT0.le hm0.le)).mpr
    apply (le_div_iff₀ hm0).mpr
    have hh : (0:ℝ) ≤ 2*((R:ℝ)+q) := by positivity
    have hp := mul_le_mul_of_nonneg_left hm3 hh
    norm_num at hp ⊢
    nlinarith
  have hnr : r ≤ n := by omega
  have hn1 : 1 ≤ n := by
    have hqpos : 0 < q := by
      by_contra hh
      have hz : q=0 := by omega
      norm_num [hz] at hq
    omega
  have hnf : (n:ℝ)*m ≤ T := by
    have hh := Nat.floor_le (div_nonneg hT0.le hm0.le)
    exact (le_div_iff₀ hm0).mp hh
  have hnf' : T < ((n:ℝ)+1)*m := by
    have hh := Nat.lt_floor_add_one (T/m)
    exact (div_lt_iff₀ hm0).mp hh
  have hnc : 2*((R:ℝ)+q) ≤ (n:ℝ) := by exact_mod_cast hnlo
  have hrc : (r:ℝ) ≤ R := by exact_mod_cast hr
  have hqw : 6*b ≤ (q:ℝ)*w := by
    have hh := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg q)
    have hh' := mul_le_mul_of_nonneg_right hq hb0.le
    dsimp [w] at *
    nlinarith
  have hspread : 2*(r:ℝ)*w+12*b ≤ (n:ℝ)*w := by
    have hh := mul_le_mul_of_nonneg_right hnc hw0.le
    have hh' := mul_le_mul_of_nonneg_right hrc hw0.le
    nlinarith
  have hlower : (r:ℝ)*w ≤ T-(n:ℝ)*a := by
    dsimp [m] at hnf
    nlinarith
  have hupper : T-(n:ℝ)*a ≤ ((n:ℝ)-r)*w := by
    have hh : T < (n:ℝ)*(a:ℝ)+(n:ℝ)*w/2+m := by
      dsimp [m] at *
      nlinarith [hnf']
    nlinarith
  have hnlow : T/(6*b) ≤ (n:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 6*b)).mpr
    have hh := mul_le_mul_of_nonneg_left hm3 (by positivity : 0 ≤ (n:ℝ)+1)
    have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hnup : (n:ℝ) ≤ 2*T/b := by
    apply (le_div_iff₀ hb0).mpr
    have hh := mul_le_mul_of_nonneg_left hbm (Nat.cast_nonneg n)
    nlinarith
  exact ⟨n,hnr,hlower,hupper,hnlow,hnup⟩

theorem exists_nat_rounding_between (U g : ℝ) (l h : ℕ) (hg : 0 < g)
    (hl : (l:ℝ)*g ≤ U) (hh : U ≤ (h:ℝ)*g) :
    ∃ t : ℕ, l ≤ t ∧ t ≤ h ∧ |g*(t:ℝ)-U| ≤ g := by
  have hU : 0 ≤ U/g := by
    apply div_nonneg _ hg.le
    exact le_trans (mul_nonneg (Nat.cast_nonneg l) hg.le) hl
  let t : ℕ := ⌊U/g⌋₊
  have htlo : l ≤ t := (Nat.le_floor_iff hU).mpr ((le_div_iff₀ hg).mpr hl)
  have htfl : (t:ℝ) ≤ U/g := Nat.floor_le hU
  have hthi : t ≤ h := by
    exact_mod_cast (htfl.trans ((div_le_iff₀ hg).mpr hh))
  have htle := (le_div_iff₀ hg).mp htfl
  have htt := (div_lt_iff₀ hg).mp (Nat.lt_floor_add_one (U/g))
  refine ⟨t,htlo,hthi,abs_le.mpr ⟨?_,?_⟩⟩ <;> nlinarith only [htle,htt,hg]

theorem exists_target_interior_rounding_aux
    (c b T : ℝ) (a g s r R q : ℕ)
    (hc : 0 < c) (hb : 1 ≤ b) (hg : 0 < g) (hs : 0 < s)
    (hr : r ≤ R) (hq : 6 ≤ (q:ℝ)*c)
    (ha : b ≤ (a:ℝ)) (hu : (a:ℝ)+(g:ℝ)*s ≤ 3*b)
    (hw : c*b ≤ (g:ℝ)*s)
    (hT : ((6*(R+q+1):ℕ):ℝ) ≤ T/b) :
    ∃ n t : ℕ, r ≤ n ∧ r*s ≤ t ∧ t ≤ (n-r)*s ∧
      |((n*a+g*t:ℕ):ℝ)-T| ≤ (g:ℝ) ∧ T/(6*b) ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*T/b := by
  obtain ⟨n,hnr,hl,hu',hnlo,hnhi⟩ :=
    exists_target_interior_length c b T a g s r R q hc hb hg hs hr hq ha hu hw hT
  have hg' : (0:ℝ) < g := by exact_mod_cast hg
  obtain ⟨t,htlo,hthi,hterr⟩ := exists_nat_rounding_between (T-(n:ℝ)*a) (g:ℝ)
    (r*s) ((n-r)*s) hg' (by push_cast; nlinarith only [hl])
    (by rw [Nat.cast_mul,Nat.cast_sub hnr]; nlinarith only [hu'])
  refine ⟨n,t,hnr,htlo,hthi,?_,hnlo,hnhi⟩
  convert hterr using 1; push_cast; ring_nf

theorem exists_target_interior_rounding (c : ℝ) (hc : 0 < c) (R : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (b T : ℝ) (a g s r : ℕ),
      1 ≤ b → 0 < g → 0 < s → r ≤ R → b ≤ (a:ℝ) →
      (a:ℝ)+(g:ℝ)*s ≤ 3*b → c*b ≤ (g:ℝ)*s → (N:ℝ) ≤ T/b →
      ∃ n t : ℕ, r ≤ n ∧ r*s ≤ t ∧ t ≤ (n-r)*s ∧
        |((n*a+g*t:ℕ):ℝ)-T| ≤ (g:ℝ) ∧ T/(6*b) ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*T/b := by
  obtain ⟨q,hq⟩ := exists_nat_gt (6/c)
  have hqc : 6 ≤ (q:ℝ)*c := by
    exact ((div_lt_iff₀ hc).mp hq).le
  refine ⟨6*(R+q+1),by omega,?_⟩
  intro b T a g s r hb hg hs hr ha hu hw hT
  exact exists_target_interior_rounding_aux c b T a g s r R q hc hb hg hs hr hqc ha hu hw hT

end Ostmann.Characters.HigherBiasSource

end

end OAI
