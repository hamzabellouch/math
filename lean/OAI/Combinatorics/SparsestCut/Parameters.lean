import OAI.Combinatorics.SparsestCut.ChartMetric

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceParameters
open Filter
noncomputable section

def p (x : ℝ) (n : ℕ) : ℝ := 1/x^n
lemma p_nonneg {x : ℝ} (hx : 0≤x) (n : ℕ) : 0≤p x n := by unfold p; positivity
lemma p_pos {x : ℝ} (hx : 0<x) (n : ℕ) : 0<p x n := by unfold p; positivity
lemma p_mul {x : ℝ} (hx : x≠0) (a b : ℕ) : p x a*p x b=p x (a+b) := by
  simp only [p,pow_add]; field_simp
lemma p_le {x : ℝ} (hx : 1≤x) {a b : ℕ} (hab : a≤b) : p x b≤p x a := by
  unfold p
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hx hab)
lemma p_one_le {x : ℝ} (hx : 1≤x) (a : ℕ) : p x a≤1 := by
  simpa [p] using p_le hx (Nat.zero_le a)
lemma p_succ {x : ℝ} (hx : x≠0) (a : ℕ) : x*p x (a+1)=p x a := by
  unfold p; rw [pow_succ]; field_simp
lemma log_ratio {x : ℝ} (hx : 0<x) : Real.log (x^40/(p x 40))=80*Real.log x := by
  rw [Real.log_div (pow_ne_zero _ hx.ne') (ne_of_gt (p_pos hx 40))]
  simp [p,Real.log_pow]; ring
lemma k_eq {x : ℝ} (hx : 0<x) : p x 5=(Real.sqrt x)^2/x^6 := by
  rw [Real.sq_sqrt hx.le]; unfold p; field_simp
lemma local_formula {m : ℕ} (hm : 0 < m) :
    GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)=
      1440*p m 5*Real.log m+1440*p m 1798*Real.log m+
        16*Real.sqrt m*p m 156*(1+p m 1802)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hq := ne_of_gt (Real.sqrt_pos.mpr hm0)
  unfold GramMetric.localCost
  rw [log_ratio hm0]
  simp only [p,Nat.cast_pow]
  field_simp
  ring
lemma macro_formula {m : ℕ} (hm : 0 < m) :
    GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0=
      2*Real.sqrt m*p m 40+36*Real.sqrt m*p m 39+
        320*p m 191*Real.log m*(1+p m 1802)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  unfold GramMetric.macroCost
  rw [log_ratio hm0]
  simp only [p,Nat.cast_pow,mul_zero,add_zero]
  simp only [mul_pow,Real.sq_sqrt hm0.le]
  field_simp
  ring
end
end UniformSparsestCut.SourceParameters

namespace UniformSparsestCut.SourceParameters
open Filter
noncomputable section
lemma sqrt_le {x : ℝ} (hx : 1≤x) : Real.sqrt x≤x := by
  have h := Real.sq_sqrt (by linarith : 0≤x)
  have hx0 : 0≤x := by linarith
  nlinarith [Real.sqrt_nonneg x]
lemma correction_le {x : ℝ} (hx : 1≤x) : (1+p x 1802)^2≤4 := by
  have h0 := p_nonneg (by linarith : 0≤x) 1802
  have h1 := p_one_le hx 1802
  nlinarith
lemma local_bounds {m : ℕ} (hm1 : 1 ≤ m) (hl : 1≤Real.log m) :
    p m 5≤GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m) ∧
    GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)≤3000*p m 5*Real.log m := by
  have hm0 : 0 < m := by omega
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hn : (0:ℝ) ≤ m := by positivity
  rw [local_formula hm0]
  have hp5 := p_nonneg hn 5
  have hl0 : 0≤Real.log m := by linarith
  have hextra1 : 1440*p m 1798*Real.log m≤1440*p m 5*Real.log m := by
    gcongr
    exact p_le hx (by norm_num)
  have hextra2 : 16*Real.sqrt m*p m 156*(1+p m 1802)^2≤64*p m 5*Real.log m := by
    calc
      _ ≤ 16*(m:ℝ)*p m 156*4 := by
        gcongr <;> first | exact sqrt_le hx | exact correction_le hx | (unfold p; positivity)
      _ = 64*p m 155 := by
        have hh := p_succ (by positivity : (m:ℝ)≠0) 155
        nlinarith
      _ ≤ 64*p m 5*Real.log m := by
        have hh := p_le hx (show 5≤155 by norm_num)
        nlinarith
  constructor
  · have hmain : p m 5≤1440*p m 5*Real.log m := by nlinarith
    linarith [show 0≤1440*p m 1798*Real.log m by unfold p; positivity,
      show 0≤16*Real.sqrt m*p m 156*(1+p m 1802)^2 by unfold p; positivity]
  · nlinarith [mul_nonneg hp5 hl0]
lemma macro_bounds {m : ℕ} (hm1 : 1 ≤ m) :
    0≤GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0 ∧
    GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0≤1318*p m 38 := by
  have hm0 : 0 < m := by omega
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hn : (0:ℝ) ≤ m := by positivity
  have hl0 := Real.log_nonneg hx
  have hl1 : Real.log m≤(m:ℝ) := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  rw [macro_formula hm0]
  constructor
  · unfold p; positivity
  · have h1 : 2*Real.sqrt m*p m 40≤2*p m 38 := by
      calc
        _ ≤ 2*(m:ℝ)*p m 40 := by gcongr <;> first | exact sqrt_le hx | (unfold p; positivity)
        _ = 2*p m 39 := by nlinarith [p_succ (by positivity : (m:ℝ)≠0) 39]
        _ ≤ _ := by gcongr; exact p_le hx (by norm_num)
    have h2 : 36*Real.sqrt m*p m 39≤36*p m 38 := by
      calc
        _ ≤ 36*(m:ℝ)*p m 39 := by gcongr <;> first | exact sqrt_le hx | (unfold p; positivity)
        _ = _ := by nlinarith [p_succ (by positivity : (m:ℝ)≠0) 38]
    have h3 : 320*p m 191*Real.log m*(1+p m 1802)^2≤1280*p m 38 := by
      calc
        _ ≤ 320*p m 191*(m:ℝ)*4 := by gcongr <;> first | exact correction_le hx | exact hl1 | (unfold p; positivity)
        _ = 1280*p m 190 := by nlinarith [p_succ (by positivity : (m:ℝ)≠0) 190]
        _ ≤ _ := by gcongr; exact p_le hx (by norm_num)
    linarith
lemma macro_small {m : ℕ} (hm : 3000 ≤ m) :
    GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0≤p m 8/2 := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (2636:ℝ)≤(m:ℝ)^30 := by
    have hh := pow_le_pow_right₀ hx (show 1≤30 by norm_num)
    simp only [pow_one] at hh
    have hm' : (3000:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  calc
    _ ≤ 1318*p m 38 := (macro_bounds (show 1 ≤ m by omega)).2
    _ ≤ p m 8/2 := by
      have hm0 : (0:ℝ) < m := by positivity
      unfold p
      rw [show (m:ℝ)^38=(m:ℝ)^8*(m:ℝ)^30 by ring]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      field_simp
      nlinarith
end
end UniformSparsestCut.SourceParameters

namespace UniformSparsestCut.SourceParameters
open scoped BigOperators
noncomputable section
lemma sqrt_m6 (m : ℕ) : Real.sqrt (m^6:ℕ)=(m:ℝ)^3 := by
  rw [Nat.cast_pow,show (m:ℝ)^6=((m:ℝ)^3)^2 by ring,Real.sqrt_sq (by positivity)]
lemma rounded_radius {m : ℕ} (hm : 0 < m) : Real.sqrt (m^6:ℕ)*p m 2000=p m 1997 := by
  rw [sqrt_m6]; unfold p; field_simp
lemma radius_le_sqrt {m : ℕ} (hm : 1 ≤ m) : p m 1997≤Real.sqrt m := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  exact (p_one_le hx _).trans (Real.one_le_sqrt.mpr hx)
lemma fourier_radius {m : ℕ} (hm : 6 ≤ m) : 2*(3*Real.sqrt m)/p m 40≤(m:ℝ)^42 := by
  have hx : (6:ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : (1:ℝ) ≤ m := by linarith
  calc
    _ = 6*Real.sqrt m*(m:ℝ)^40 := by unfold p; field_simp ; ring
    _ ≤ (m:ℝ)*(m:ℝ)*(m:ℝ)^40 := by gcongr; exact sqrt_le hx1
    _ = _ := by ring
lemma local_tau {m : ℕ} (hm : 3000 ≤ m) (hl : 1≤Real.log m) :
    let L := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)
    0<L*p m 2000 ∧ L*p m 2000≤p m 8 ∧
    L*p m 2000*(9+8*Real.log (p m 8/(L*p m 2000)))≤
      50000000*p m 2000*p m 5*(Real.log m)^2 := by
  dsimp only
  let L := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)
  change 0<L*p m 2000 ∧ L*p m 2000≤p m 8 ∧ _
  have hx : (3000:ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : (1:ℝ) ≤ m := by linarith
  have hx0 : (0:ℝ) < m := by linarith
  have hτ := p_pos hx0 2000
  have hp5 := p_pos hx0 5
  have hp8 := p_pos hx0 8
  have hL := local_bounds (show 1 ≤ m by omega) hl
  change p m 5≤L ∧ L≤3000*p m 5*Real.log m at hL
  have hδ : 0<L*p m 2000 := mul_pos (hp5.trans_le hL.1) hτ
  have hδ0 : p m 5*p m 2000≤L*p m 2000 := mul_le_mul_of_nonneg_right hL.1 hτ.le
  have hδ1 : L*p m 2000≤3000*p m 2000*p m 5*Real.log m := by nlinarith [mul_le_mul_of_nonneg_right hL.2 hτ.le]
  have hlx : Real.log m≤(m:ℝ) := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hs : L*p m 2000≤p m 8 := by
    calc
      _ ≤ 3000*p m 2000*p m 5*(m:ℝ) := hδ1.trans (mul_le_mul_of_nonneg_left hlx (by unfold p; positivity))
      _ = 3000*p m 2004 := by rw [mul_assoc (3000:ℝ),p_mul hx0.ne']; norm_num; nlinarith [p_succ hx0.ne' 2004]
      _ ≤ 3000*p m 9 := mul_le_mul_of_nonneg_left (p_le hx1 (by norm_num)) (by norm_num)
      _ ≤ (m:ℝ)*p m 9 := mul_le_mul_of_nonneg_right hx (p_nonneg hx0.le _)
      _ = p m 8 := p_succ hx0.ne' 8
  have he : p m 8/(p m 5*p m 2000)=(m:ℝ)^1997 := by unfold p; field_simp
  have hlog : Real.log (p m 8/(L*p m 2000))≤1997*Real.log m := by
    calc
      _ ≤ Real.log (p m 8/(p m 5*p m 2000)) :=
        Real.log_le_log (div_pos hp8 hδ) (div_le_div_of_nonneg_left hp8.le (mul_pos hp5 hτ) hδ0)
      _ = _ := by rw [he,Real.log_pow]; norm_num
  have hlog0 : 0≤Real.log (p m 8/(L*p m 2000)) := Real.log_nonneg ((one_le_div hδ).mpr hs)
  refine ⟨hδ,hs,?_⟩
  change L*p m 2000*(9+8*Real.log (p m 8/(L*p m 2000)))≤_
  calc
    _ ≤ (3000*p m 2000*p m 5*Real.log m)*(15985*Real.log m) := by
      apply mul_le_mul hδ1 (by linarith) (by positivity) (by unfold p; positivity)
    _ ≤ _ := by nlinarith [show 0≤p m 2000*p m 5*(Real.log m)^2 by unfold p; positivity]
end
end UniformSparsestCut.SourceParameters

end

end OAI
