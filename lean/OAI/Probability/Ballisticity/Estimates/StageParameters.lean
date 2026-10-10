import Mathlib
import OAI.Probability.Ballisticity.Estimates.FiniteStage

namespace OAI

section

open Filter
open scoped Topology
namespace DirectionalTransience

lemma stage_parameter_hierarchy (A lam lamq D₀ : ℝ) (hA : 1 ≤ A)
    (hlam : 0 < lam) (hlamq : 0 < lamq) (hD₀ : 0 ≤ D₀) :
    let j := 1/(8*A)
    let f := 2+Real.log 16*j
    ∃ g K : ℝ, 0 < g ∧ 0 < K ∧ 1/g < (1/2:ℝ)/64 ∧ (1+f/g)*D₀/K < (1/2:ℝ)/64 ∧
      ∃ k L : ℕ, 2 ≤ k ∧ 1 ≤ L ∧
        2*K+4 < lam*k/4 ∧ 2*K+4 < lamq*k/4 ∧
        2*K+4 < (2*k-Real.log 2)*j-((g+1+Real.log 16*j)+2+Real.log 16*j) ∧
        2*K+4 < (L:ℝ)-k/2 := by
  let j := 1/(8*A)
  let f := 2+Real.log 16*j
  have hA0 : 0 < A := by linarith
  have hj : 0 < j := by dsimp [j]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  let g : ℝ := 256
  let K := 256*(1+f/g)*(D₀+1)
  have hg : 0 < g := by norm_num [g]
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨g,K,hg,hK,by norm_num [g],?_,?_⟩
  · apply (div_lt_iff₀ hK).mpr
    dsimp [K]
    have hh : 0 < 1+f/g := by positivity
    nlinarith only [mul_pos hh (show 0 < D₀+2 by linarith)]
  · let D := (g+1+Real.log 16*j)+2+Real.log 16*j
    let lam₀ := min lam lamq
    have hlam₀ : 0 < lam₀ := lt_min hlam hlamq
    obtain ⟨k,hk⟩ := exists_nat_gt (max 2 (max (4*(2*K+4)/lam₀)
      ((D+2*K+4)/j/2+Real.log 2/2)))
    have hk2 : (2:ℝ) < k := (le_max_left _ _).trans_lt hk
    have hkn : 2 ≤ k := by exact_mod_cast hk2.le
    have hkr := (le_max_right _ _).trans_lt hk
    have hkLam : 2*K+4 < lam₀*k/4 := by
      have hh := (div_lt_iff₀ hlam₀).mp ((le_max_left _ _).trans_lt hkr)
      nlinarith only [hh]
    have hkcell : 2*K+4 < (2*k-Real.log 2)*j-D := by
      have hh := (le_max_right _ _).trans_lt hkr
      have hmul := mul_lt_mul_of_pos_right hh hj
      have hjn : j ≠ 0 := ne_of_gt hj
      field_simp at hmul
      nlinarith only [hmul]
    obtain ⟨L,hL⟩ := exists_nat_gt (max 1 ((k:ℝ)/2+2*K+4))
    have hL1 : 1 ≤ L := by exact_mod_cast ((le_max_left _ _).trans_lt hL).le
    refine ⟨k,L,hkn,hL1,?_,?_,hkcell,?_⟩
    · have hh := mul_le_mul_of_nonneg_right (min_le_left lam lamq) (Nat.cast_nonneg k)
      exact hkLam.trans_le (by dsimp [lam₀] at *; linarith)
    · have hh := mul_le_mul_of_nonneg_right (min_le_right lam lamq) (Nat.cast_nonneg k)
      exact hkLam.trans_le (by dsimp [lam₀] at *; linarith)
    · have hh := (le_max_right _ _).trans_lt hL
      linarith only [hh]

lemma stage_budget_parameters (A g₀ g₁ κ _K : ℝ) (k L : ℕ) (hA : 1 ≤ A)
    (hg₀ : 0 < g₀) (hg₁ : 0 < g₁) (hk : 2 ≤ k) :
    ∀ᶠ b : ℝ in atTop, 0 < b ∧
      (k:ℝ)*L*Real.log (1/κ) ≤ k*b/2 ∧
      (2*A*k)*(⌊(1/(8*A))*b⌋₊:ℝ) ≤ 2*k*b ∧
      Real.exp (-(k:ℝ)*b) ≤ Real.exp (-(k:ℝ)*b/4)*
        (g₀*g₁*Real.exp (-A*k*(⌊(1/(8*A))*b⌋₊:ℝ))) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hA0 : 0 < A := by linarith
  let j := 1/(8*A)
  have hj : 0 < j := by dsimp [j]; positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (2*L*Real.log (1/κ)),
    eventually_ge_atTop (-8*Real.log (g₀*g₁)/(5*k))] with b hb hell hc
  have hb0 : 0 < b := by linarith
  have hm : (⌊j*b⌋₊:ℝ) ≤ j*b := Nat.floor_le (by positivity)
  have hym : A*k*(⌊j*b⌋₊:ℝ) ≤ k*b/8 := by
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ A*k by positivity)
    have heq : A*k*(j*b) = k*b/8 := by dsimp [j]; field_simp
    rwa [heq] at hh
  refine ⟨hb0,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hell hk0.le
    nlinarith only [hh]
  · change 2*A*k*(⌊j*b⌋₊:ℝ) ≤ 2*k*b
    nlinarith only [hym,mul_pos hk0 hb0]
  · have hh := (div_le_iff₀ (show 0 < 5*(k:ℝ) by positivity)).mp hc
    calc
      _ ≤ Real.exp (-k*b/4+(Real.log (g₀*g₁)-A*k*(⌊j*b⌋₊:ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hh,hym]
      _ = _ := by rw [Real.exp_add,Real.exp_sub,Real.exp_log (mul_pos hg₀ hg₁)];
                  rw [show -A*(k:ℝ)*(⌊j*b⌋₊:ℝ)= -(A*k*(⌊j*b⌋₊:ℝ)) by ring,Real.exp_neg]; ring

end DirectionalTransience

end

section

open Filter
open scoped Topology
namespace DirectionalTransience

lemma eventually_finest_width (c : ℝ) (hc : 0<c) (m W : ℕ) :
    ∀ᶠ s : ℝ in atTop, 0<s ∧ W ≤ finestCellWidth ⌊s*c⌋₊ m ∧
      s*c/(16*(16:ℝ)^m) ≤ (finestCellWidth ⌊s*c⌋₊ m:ℝ) := by
  let M : ℝ := max 2 (16*16^m*(W+1))
  filter_upwards [eventually_ge_atTop (M/c)] with s hs
  have hx : M ≤ s*c := (div_le_iff₀ hc).mp hs
  have hx2 : (2:ℝ) ≤ s*c := (le_max_left _ _).trans hx
  have hs0 : 0<s := (mul_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hx2)).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_gt hc h.2))
  have hrem := Nat.lt_floor_add_one (s*c)
  have hhalf : s*c/2 ≤ (⌊s*c⌋₊:ℝ) := by linarith
  have hM : 16*(16:ℝ)^m*(W+1) ≤ s*c := (le_max_right _ _).trans hx
  have hpow : 0<(16:ℝ)^m := by positivity
  have hH : 8*16^m ≤ ⌊s*c⌋₊ := by
    have hW0 : (0:ℝ)≤W := Nat.cast_nonneg W
    have hreal : 8*(16:ℝ)^m ≤ (⌊s*c⌋₊:ℝ) := by nlinarith [mul_nonneg hpow.le hW0]
    exact_mod_cast hreal
  have hlow : (⌊s*c⌋₊:ℝ) ≤ 8*(16:ℝ)^m*(finestCellWidth ⌊s*c⌋₊ m:ℝ) := by
    exact_mod_cast finestCellWidth_lower hH
  have hw : (W:ℝ) ≤ (finestCellWidth ⌊s*c⌋₊ m:ℝ) := by nlinarith
  refine ⟨hs0,by exact_mod_cast hw,?_⟩
  apply (div_le_iff₀ (by positivity : 0<16*(16:ℝ)^m)).mpr
  nlinarith only [hhalf,hlow]

lemma stage_cell_count_bound (b χ s : ℝ) (m : ℕ) (hs : 0<s)
    (hw : s*Real.exp (-b)/(16*(16:ℝ)^m) ≤
      (finestCellWidth ⌊s*Real.exp (-b)⌋₊ m:ℝ)) :
    let He := ⌊s*Real.exp (-b)⌋₊
    let H := ⌊s*Real.exp (χ*b)⌋₊
    let w := finestCellWidth He m
    ((((H-He)/w+1)+1:ℕ):ℝ) ≤ 16*(16:ℝ)^m*Real.exp ((χ+1)*b)+2 := by
  dsimp only
  let He := ⌊s*Real.exp (-b)⌋₊
  let H := ⌊s*Real.exp (χ*b)⌋₊
  let w := finestCellWidth He m
  have hw0 : (0:ℝ)<w := (div_pos (mul_pos hs (Real.exp_pos _)) (by positivity)).trans_le hw
  have hwn : 0<w := by exact_mod_cast hw0
  have hcount := integer_cells_card He H w hwn
  have hH : (H:ℝ) ≤ s*Real.exp (χ*b) := Nat.floor_le (by positivity)
  have hratio : (H:ℝ)/(w:ℝ) ≤ 16*(16:ℝ)^m*Real.exp ((χ+1)*b) := by
    apply (div_le_iff₀ hw0).mpr
    have hmul := mul_le_mul_of_nonneg_left hw (show 0≤16*(16:ℝ)^m*Real.exp ((χ+1)*b) by positivity)
    have heq : (16*(16:ℝ)^m*Real.exp ((χ+1)*b))*(s*Real.exp (-b)/(16*(16:ℝ)^m)) =
        s*Real.exp (χ*b) := by
      field_simp
      have hh : Real.exp ((χ+1)*b)*Real.exp (-b)=Real.exp (χ*b) := by rw [← Real.exp_add]; congr 1; ring
      exact hh
    rw [heq] at hmul
    exact hH.trans hmul
  push_cast
  push_cast at hcount
  linarith only [hcount,hratio]

lemma radix_floor_bound (j b : ℝ) (hjb : 0≤j*b) :
    (16:ℝ)^⌊j*b⌋₊ ≤ Real.exp (Real.log 16*j*b) := by
  have hf := Nat.floor_le hjb
  have hl : 0≤Real.log 16 := Real.log_nonneg (by norm_num)
  calc
    _ = Real.exp (Real.log 16*(⌊j*b⌋₊:ℝ)) := by rw [show Real.log 16*(⌊j*b⌋₊:ℝ)=(⌊j*b⌋₊:ℝ)*Real.log 16 by ring,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<16)]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith only [mul_le_mul_of_nonneg_left hf hl]

end DirectionalTransience

end

end OAI
