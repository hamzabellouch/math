import Mathlib
import OAI.Probability.Ballisticity.Estimates.FiniteStage

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
namespace DirectionalTransience

lemma cell_radius_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ T : ℝ, 0 < T ∧ ∀ w m i : ℕ, ∀ t : ℝ, T ≤ t →
      t ≤ c^2/(4*C)*(w:ℝ) →
      fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) t ≤
          c*cellRadius ν e f C w m i/2 := by
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hI : Integrable S μ := independent_commonWordIncrement_integrable ν hue _
    (signed_direction_unit e) htrans (signedHeight e) (signedHeight_projection e)
    (signedHeight_step_le e) f
  have hne : 0 < μ {x | S x ≠ 0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  obtain ⟨R,hR,hr⟩ := fluctuationRadius_scaling_compare μ S hS hI hne
  refine ⟨max 1 (fluctuationScale μ S R+1),lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro w m i t ht htw
  have htR : fluctuationScale μ S R < t := by linarith [le_max_right 1 (fluctuationScale μ S R+1)]
  have hw : (w:ℝ) ≤ cellWidth w m i := by exact_mod_cast cellWidth_min w m i
  have htw' : t ≤ (c/2)^2*((cellWidth w m i:ℝ)/C) := by
    calc
      t ≤ c^2/(4*C)*(w:ℝ) := htw
      _ ≤ c^2/(4*C)*(cellWidth w m i:ℝ) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = (c/2)^2*((cellWidth w m i:ℝ)/C) := by ring
  have hh := hr ((cellWidth w m i:ℝ)/C) t (c/2) htR htw' (by positivity) (by linarith)
  simpa only [cellRadius,mul_div_assoc,div_mul_eq_mul_div] using hh

end DirectionalTransience

end

section

open scoped Classical
namespace DirectionalTransience

noncomputable def stageCellStarts (He H w : ℕ) : Fin (((H-He)/w+1)+1) → ℕ :=
  Fin.lastCases H (fun j => He+j.val*w)
noncomputable def stageCellWidths (He H w wplus : ℕ) : Fin (((H-He)/w+1)+1) → ℕ :=
  Fin.lastCases wplus (fun _ => w)
noncomputable def stageCellGaps (He H w : ℕ) (Gminus Gplus : ℝ) : Fin (((H-He)/w+1)+1) → ℝ :=
  Fin.lastCases Gplus (fun _ => Gminus)

lemma stage_cells_geometry (He H m W : ℕ) (hw : W ≤ finestCellWidth He m)
    (hp : W ≤ finestCellWidth H m) (hW : 0<W) (Gminus Gplus : ℝ) :
    let w := finestCellWidth He m
    let wp := finestCellWidth H m
    let v := stageCellStarts He H w
    let ws := stageCellWidths He H w wp
    let gs := stageCellGaps He H w Gminus Gplus
    (∀ j, W ≤ ws j) ∧ (∀ j, 2*cellWidth (ws j) m 0 ≤ v j) ∧
    (∀ h : ℕ, He < h → h ≤ H → ∃ j, v j≤h ∧ h≤v j+ws j ∧ Gminus≤gs j) ∧
    (∃ j, v j≤H ∧ H≤v j+ws j ∧ Gplus≤gs j) := by
  dsimp only
  let w := finestCellWidth He m
  have hw0 : 0<w := hW.trans_le hw
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [stageCellWidths, Fin.lastCases_last]
      exact hp
    · simp only [stageCellWidths, Fin.lastCases_castSucc]
      exact hw
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [stageCellStarts, stageCellWidths, Fin.lastCases_last]
      exact finestCellWidth_start H m
    · simp only [stageCellStarts, stageCellWidths, Fin.lastCases_castSucc]
      exact (finestCellWidth_start He m).trans (Nat.le_add_right _ _)
  · intro h hHe hH
    obtain ⟨j,hj₁,hj₂⟩ := integer_cells_cover He H w hw0 h hHe.le hH
    refine ⟨j.castSucc,?_,?_,?_⟩
    · simp only [stageCellStarts, Fin.lastCases_castSucc]
      exact hj₁
    · simp only [stageCellStarts, stageCellWidths, Fin.lastCases_castSucc]
      exact hj₂
    · simp only [stageCellGaps, Fin.lastCases_castSucc]
      exact le_rfl
  · refine ⟨Fin.last _,?_,?_,?_⟩
    · simp only [stageCellStarts, Fin.lastCases_last]
      exact le_rfl
    · simp only [stageCellStarts, stageCellWidths, Fin.lastCases_last]
      exact Nat.le_add_right _ _
    · simp only [stageCellGaps, Fin.lastCases_last]
      exact le_rfl

lemma stage_cells_gap_bounds {d : ℕ} (ν : MeasureTheory.Measure (Row d))
    (e f : Direction d) (C c Gminus Gplus : ℝ) (He H m : ℕ)
    (hminus : ∀ i, i < m → Gminus ≤ c*cellRadius ν e f C (finestCellWidth He m) m i/2)
    (hplus : ∀ i, i < m → Gplus ≤ c*cellRadius ν e f C (finestCellWidth H m) m i/2) :
    ∀ j i, i < m → stageCellGaps He H (finestCellWidth He m) Gminus Gplus j ≤
      c*cellRadius ν e f C (stageCellWidths He H (finestCellWidth He m) (finestCellWidth H m) j) m i/2 := by
  intro j i hi
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simpa only [stageCellGaps, stageCellWidths, Fin.lastCases_last] using hplus i hi
  · simpa only [stageCellGaps, stageCellWidths, Fin.lastCases_castSucc] using hminus i hi

end DirectionalTransience

end

section

open Filter
open scoped Topology
namespace DirectionalTransience

lemma eventually_exp_affine_le (C a r : ℝ) (h : r < a) :
    ∀ᶠ b : ℝ in atTop, Real.exp (C-a*b) ≤ Real.exp (-r*b)/2 := by
  filter_upwards [eventually_ge_atTop ((C+Real.log 2)/(a-r))] with b hb
  have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hb
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  rw [← Real.exp_log (by norm_num : (0:ℝ)<2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hh]

lemma eventually_mul_exp_le (D a r : ℝ) (h : r < a) :
    ∀ᶠ b : ℝ in atTop, D*Real.exp (-a*b) ≤ Real.exp (-r*b)/2 := by
  let E := max D 1
  have hE : 0 < E := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  filter_upwards [eventually_exp_affine_le (Real.log E) a r h] with b hb
  calc
    _ ≤ E*Real.exp (-a*b) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ = Real.exp (Real.log E-a*b) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hE]; congr 2; ring
    _ ≤ _ := hb

lemma eventually_stage_short_bound (lam C K : ℝ) (k L : ℕ)
    (hC : 0≤C) (hL : 0 < L) (hk : 2*K+3 < lam*k/2) (hLk : 2*K+3 < (L:ℝ)-k/2) :
    ∀ᶠ b : ℝ in atTop,
      (Real.exp (C*k-lam*(k*b/2)/L) +
        (16*C*k*L^2)*Real.exp ((k*b/2)/L-b))^L ≤ Real.exp (-(2*K+3)*b) := by
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hrate₁ : (2*K+3)/(L:ℝ) < lam*k/(2*L) := by
    rw [div_mul_eq_div_div]
    exact (div_lt_div_iff_of_pos_right hLp).mpr hk
  have hrate₂ : (2*K+3)/(L:ℝ) < 1-(k:ℝ)/(2*L) := by
    have hh := (div_lt_div_iff_of_pos_right hLp).mpr hLk
    have heq : ((L:ℝ)-(k:ℝ)/2)/L = 1-(k:ℝ)/(2*L) := by field_simp
    rwa [heq] at hh
  filter_upwards [eventually_exp_affine_le (C*k) (lam*k/(2*L)) ((2*K+3)/L) hrate₁,
    eventually_mul_exp_le (16*C*k*L^2) (1-(k:ℝ)/(2*L)) ((2*K+3)/L) hrate₂] with b h₁ h₂
  have hsum : Real.exp (C*k-lam*(k*b/2)/L)+
      (16*C*k*L^2)*Real.exp ((k*b/2)/L-b) ≤ Real.exp (-((2*K+3)/L)*b) := by
    have h₁' : Real.exp (C*k-lam*(k*b/2)/L) ≤ Real.exp (-((2*K+3)/L)*b)/2 := by convert h₁ using 1; congr 1; ring
    have h₂' : (16*C*k*L^2)*Real.exp ((k*b/2)/L-b) ≤ Real.exp (-((2*K+3)/L)*b)/2 := by convert h₂ using 1; congr 2; ring
    linarith only [h₁',h₂']
  calc
    _ ≤ (Real.exp (-((2*K+3)/L)*b))^L := pow_le_pow_left₀ (by positivity) hsum L
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma cell_count_exp_bound (b j D : ℝ) (k m : ℕ) (n : ℝ)
    (hk : 2 ≤ k) (hm : j*b-1 ≤ (m:ℝ)) (hn : n ≤ Real.exp (D*b)) (hn0 : 0≤n) :
    n*(2:ℝ)^(m-1)*Real.exp (-2*k*m) ≤
      Real.exp ((2*k-Real.log 2)-((2*k-Real.log 2)*j-D)*b) := by
  have hlog : Real.log 2 ≤ 1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hpos : 0 ≤ 2*k-Real.log 2 := by linarith
  have hp : (2:ℝ)^(m-1) ≤ 2^m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1)
  calc
    _ ≤ Real.exp (D*b)*(2:ℝ)^m*Real.exp (-2*k*m) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul_of_nonneg_left hp hn0).trans
        (mul_le_mul_of_nonneg_right hn (by positivity))
    _ = Real.exp (D*b+Real.log 2*m-2*k*m) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_add,show Real.log 2*(m:ℝ)=(m:ℝ)*Real.log 2 by ring,
        Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      congr 2; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hm hpos
      nlinarith only [hh]

lemma eventually_stage_probability_sum (lam lamq C Cq j D K : ℝ) (k L : ℕ)
    (hk : 2 ≤ k) (hL : 0<L) (hCr : 0≤C)
    (hshort : 2*K+3 < lam*k/2) (hLk : 2*K+3 < (L:ℝ)-k/2)
    (hmass : 2*K+3 < lamq*k/4) (hcell : 2*K+3 < (2*k-Real.log 2)*j-D) :
    ∀ᶠ b : ℝ in atTop, ∀ m : ℕ, j*b-1 ≤ m → ∀ n : ℝ, 0≤n → n≤Real.exp (D*b) →
      (Real.exp (C*k-lam*(k*b/2)/L)+(16*C*k*L^2)*Real.exp ((k*b/2)/L-b))^L +
      Real.exp (Cq*k)*(Real.exp (-k*b/4))^lamq + n*2^(m-1)*Real.exp (-2*k*m) ≤ Real.exp (-2*K*b) := by
  filter_upwards [eventually_stage_short_bound lam C K k L hCr hL hshort hLk,
    eventually_exp_affine_le (Cq*k) (lamq*k/4) (2*K+3) hmass,
    eventually_exp_affine_le (2*k-Real.log 2) ((2*k-Real.log 2)*j-D) (2*K+3) hcell,
    eventually_ge_atTop (1:ℝ)] with b hs hq hc hb m hm n hn0 hn
  have hq' : Real.exp (Cq*k)*(Real.exp (-k*b/4))^lamq ≤ Real.exp (-(2*K+3)*b)/2 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
    convert hq using 1; congr 1; ring
  have hc' := (cell_count_exp_bound b j D k m n hk hm hn hn0).trans hc
  have htwo : 2*Real.exp (-(2*K+3)*b) ≤ Real.exp (-2*K*b) := by
    have hlog : Real.log 2 ≤ 1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
    rw [← Real.exp_log (by norm_num : (0:ℝ)<2),← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith only [hb,hlog])
  linarith only [hs,hq',hc',htwo]

end DirectionalTransience

end

end OAI
