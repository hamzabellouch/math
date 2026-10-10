import OAI.Geometry.TranslativeCovering.SourceParameters

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace EntropyRates
open Filter SourceParameters LocalizationRounding
open scoped Topology Classical
lemma mesh {n : ℕ} (hn : 0 < n) : h n = 1/(100*(n:ℝ)^5) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [h,RadialShell.η]
  field_simp
lemma mesh_pos {n : ℕ} (hn : 0 < n) : 0 < h n := by rw [mesh hn]; positivity
lemma error_bound {n : ℕ} (hn : 1 ≤ n) : Real.sqrt n*h n/2 ≤ RadialShell.η n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt n ≤ (n:ℝ) := (Real.sqrt_le_iff).mpr ⟨hn0.le,by nlinarith only [hn1]⟩
  have he : (n:ℝ)*h n/2 = RadialShell.η n/200 := by dsimp [h]; field_simp ; ring
  calc
    _ ≤ (n:ℝ)*h n/2 := by gcongr; exact mesh_pos (by omega) |>.le
    _ = _ := he
    _ ≤ _ := by have hh : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
                linarith only [hh]
lemma alphabet_rate : ∀ᶠ n : ℕ in atTop,
    ((alphabet n (h n) (L n)).card:ℝ) ≤ Real.exp ((n:ℝ)^2) := by
  filter_upwards [L_limit.eventually (gt_mem_nhds (show D+a<3 by norm_num [D,a,ε])),
    CoveringGrowth.polynomial (C := 601) (by norm_num : (0:ℝ)<1) 5,eventually_ge_atTop 1] with n hL hp hn
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hm : 0 < h n := mesh_pos (by omega)
  have hLp : 0 ≤ L n := by
    have ha := a_pos; have hD := D_pos; have hh := mesh_pos (by omega : 0<n)
    dsimp [L,b,RadialShell.η]; positivity
  have hQ := alphabet_card (n := n) (mesh_pos (n := n) (by omega)) hLp
  apply hQ.trans
  have hb : 1+2*(L n)/h n ≤ 601*(n:ℝ)^5 := by
    have h5 : 1 ≤ (n:ℝ)^5 := one_le_pow₀ (by exact_mod_cast hn)
    have h3 : L n ≤ 3 := hL.le
    calc
      _ ≤ 1+2*3/h n := by gcongr
      _ = 1+600*(n:ℝ)^5 := by rw [mesh (by omega)]; field_simp ; ring
      _ ≤ _ := by linarith only [h5]
  calc
    _ ≤ (601*(n:ℝ)^5)^n := pow_le_pow_left₀ (by positivity) hb n
    _ ≤ (Real.exp (n:ℝ))^n := pow_le_pow_left₀ (by positivity) (by simpa using hp) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma list_rate : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0≤R → R≤(n:ℝ)^2 →
    (Fintype.card (BoundedLists n (h n) (L n) (N n R)):ℝ) ≤
      Real.exp (Real.exp ((1/10:ℝ)*(n:ℝ))) := by
  filter_upwards [alphabet_rate,length_rate,
    CoveringGrowth.polynomial (C := 3) (by norm_num : (0:ℝ)<9/100) 2,
    eventually_ge_atTop 1] with n hQ hN hp hn R hR hRn
  let E := Real.exp ((1/100:ℝ)*(n:ℝ))
  have hNE : (N n R:ℝ) ≤ E := hN R hR hRn
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ (by exact_mod_cast hn)
  have hq : (max 1 (alphabet n (h n) (L n)).card:ℝ) ≤ Real.exp ((n:ℝ)^2) := by
    exact max_le (Real.one_le_exp_iff.mpr (sq_nonneg _)) hQ
  have hcard := Nat.cast_le (α := ℝ) |>.mpr (boundedLists_card n (N n R) (h n) (L n))
  push_cast at hcard
  apply hcard.trans
  calc
    _ ≤ Real.exp ((N n R:ℝ)+1)*(Real.exp ((n:ℝ)^2))^(N n R) := by
      gcongr
      exact le_trans (by linarith : (N n R:ℝ)+1 ≤ ((N n R:ℝ)+1)+1) (Real.add_one_le_exp _)
    _ = Real.exp (((N n R:ℝ)+1)+(N n R:ℝ)*(n:ℝ)^2) := by rw [← Real.exp_nat_mul,← Real.exp_add]
    _ ≤ Real.exp (3*(n:ℝ)^2*E) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_right hNE (sq_nonneg (n:ℝ))
      have h2 := mul_le_mul_of_nonneg_right hn2 (show 0 ≤ E from (Real.exp_pos _).le)
      dsimp [E] at *
      nlinarith only [hNE,hE,h1,h2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.exp ((9/100:ℝ)*(n:ℝ))*E := by gcongr
        _ = _ := by dsimp [E]; rw [← Real.exp_add]; congr 1; ring
end EntropyRates

end OAI
