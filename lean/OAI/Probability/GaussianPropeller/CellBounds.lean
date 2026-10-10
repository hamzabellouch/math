import OAI.Probability.GaussianPropeller.Attainment

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

lemma winning_inner_nonneg (z : Fin k → Space d) (hz : ∑ j,z j=0)
    (i : Fin k) {x : Space d} (hx : x ∈ closedCell z i) : 0 ≤ ⟪z i,x⟫ := by
  have hh : (0:ℝ) ≤ ∑ j : Fin k, (⟪z i,x⟫-⟪z j,x⟫) :=
    Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hx j))
  have hz' : (∑ j,⟪z j,x⟫)=0 := by rw [← sum_inner,hz,inner_zero_left]
  rw [Finset.sum_sub_distrib, hz', sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact nonneg_of_mul_nonneg_right hh (by exact_mod_cast (NeZero.pos k))

lemma active_probability_mem (_hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) : 0 < (gaussian d).real (A i) ∧ (gaussian d).real (A i) ≤ 1/2 := by
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  have hP : 0 < (gaussian d).real (A i) := ENNReal.toReal_pos hi (measure_ne_top _ _)
  have hzn : centroid (A i) ≠ 0 := active_centroid_ne_zero hA hpos hi
  let e : Space d := - (‖centroid (A i)‖⁻¹ • centroid (A i))
  have he : ‖e‖=1 := by simp [e, norm_smul, norm_ne_zero_iff.mpr hzn]
  have hmap := OneCell.map_unit_inner_gaussian e he
  have hs : closedCell (fun j => centroid (A j)) i ⊆ {x | ⟪e,x⟫ ≤ 0} := by
    intro x hx
    have hn := winning_inner_nonneg (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i hx
    simp only [Set.mem_ofPred_eq,e,inner_neg_left,real_inner_smul_left]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hn)
  have heq : (gaussian d) {x | ⟪e,x⟫ ≤ 0} = (gaussianReal 0 1) (Iic 0) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  refine ⟨hP, ?_⟩
  have hh := measure_mono (μ:=gaussian d) hs
  rw [← measure_congr (active_eq_closedCell_ae hA hpos hi), heq] at hh
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
  change (gaussian d).real (A i) ≤ (gaussianReal 0 1).real (Iic 0) at hh'
  rw [← Φ_eq_gaussianReal, Φ_zero] at hh'
  exact hh'

lemma p_eq_Φ_neg (x : ℝ) : p x=Φ (-x) := by
  rw [Φ_neg, Φ_eq_one_sub_tail]
  simp only [φ, OneCell.gaussianConst, p, OneCell.tail, OneCell.density]
  rw [integral_const_mul]
  ring

lemma loss_eq_quantile {P : ℝ} (_hP : P ∈ Ioo (0:ℝ) 1) {x : ℝ} (hx : p x=P) :
    loss x = φ (q P)*(q P*P+φ (q P)) := by
  have hq : q P = -x := by rw [← hx, p_eq_Φ_neg, q_Φ]
  rw [hq, φ_neg, loss_eq]
  rw [← hx]
  simp only [p, φ, OneCell.gaussianConst, OneCell.density]
  ring

lemma loss_rationalize {C α r L : ℝ} (_hC : 0 < C) (hα : 0 < α)
    (_hr : 0 ≤ r) (hs : 0 ≤ 1-α*r^2)
    (hl : C*(1-Real.sqrt (1-α*r^2)) ≤ α*L) :
    C*r^2/(1+Real.sqrt (1-α*r^2)) ≤ L := by
  have hq := Real.sqrt_nonneg (1-α*r^2)
  have hq2 := Real.sq_sqrt hs
  rw [div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+Real.sqrt (1-α*r^2) by positivity)
  have heq : C*(1-Real.sqrt (1-α*r^2))*(1+Real.sqrt (1-α*r^2)) = α*(C*r^2) := by
    calc
      _ = C*(1-Real.sqrt (1-α*r^2)^2) := by ring
      _ = _ := by rw [hq2]; ring
  rw [heq] at hm
  exact (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_assoc] using hm)

lemma minimal_loss_constraint (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (value A)*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-((k:ℝ)/((k:ℝ)-1))*(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by
  let C := value A
  let r := ‖centroid (A i)‖/Real.sqrt C
  let α := (k:ℝ)/((k:ℝ)-1)
  have hCp : 0 < C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hk1 : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hα : 0<α := div_pos (by linarith) (by linarith)
  have hP := active_probability_mem hk hA hCp (hall i)
  obtain ⟨x,hx,hpx⟩ := exists_p hP.1 hP.2
  refine ⟨x,hx,hpx,?_⟩
  have hl := (optimal_loss_lower hk hA.1 i).trans (minimal_loss_upper hk hA hCp hall i)
  rw [mul_assoc, ← loss_eq_quantile ⟨hP.1,by linarith [hP.2]⟩ hpx] at hl
  have hsq : ‖centroid (A i)‖^2 = C*r^2 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hCp.le]
    field_simp
  have hnon : 0 ≤ C-α*‖centroid (A i)‖^2 := by
    change 0 ≤ (∑ j, ‖centroid (A j)‖^2) - ((k:ℝ)/((k:ℝ)-1))*‖centroid (A i)‖^2
    rw [← recentered_norm_sq hk (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i]
    positivity
  have hs : 0 ≤ 1-α*r^2 := by
    rw [hsq] at hnon
    nlinarith only [hnon,hCp]
  have hsqrt : Real.sqrt (C-α*‖centroid (A i)‖^2) = Real.sqrt C*Real.sqrt (1-α*r^2) := by
    rw [hsq, show C-α*(C*r^2)=C*(1-α*r^2) by ring, Real.sqrt_mul hCp.le]
  change C-Real.sqrt C*Real.sqrt (C-α*‖centroid (A i)‖^2) ≤ α*loss x at hl
  rw [hsqrt] at hl
  have ht := Real.sq_sqrt hCp.le
  apply loss_rationalize hCp hα (by positivity : 0≤r) hs
  have he : C-Real.sqrt C*(Real.sqrt C*Real.sqrt (1-α*r^2)) = C*(1-Real.sqrt (1-α*r^2)) := by
    rw [←mul_assoc, ←pow_two, ht]; ring
  rwa [he] at hl

lemma minimal_universal_loss (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (9/(8*Real.pi))*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by
  obtain ⟨x,hx,hp,hl⟩ := minimal_loss_constraint hk hA hC hall i
  refine ⟨x,hx,hp, le_trans ?_ hl⟩
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)) (by positivity)
  apply add_le_add_right
  apply Real.sqrt_le_sqrt
  have hk1 : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hα : 1≤(k:ℝ)/((k:ℝ)-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hα) (sq_nonneg (‖centroid (A i)‖/Real.sqrt (value A)))]

lemma minimal_linear_quadratic (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    0.415*(‖centroid (A i)‖/Real.sqrt (value A))+
      0.15*(‖centroid (A i)‖/Real.sqrt (value A))^2 < (gaussian d).real (A i) := by
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨x,hx,hp,hl⟩ := minimal_universal_loss hk hA hC hall i
  rw [← hp]
  exact linear_quadratic_of_loss (div_pos (norm_pos_iff.mpr (active_centroid_ne_zero hA hCp (hall i)))
      (Real.sqrt_pos.mpr hCp)) (normalized_centroid_lt_two_thirds (hA.1.1.1 i) hC).le hx hl

end GaussianPropeller.Reduction

end OAI
