import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianSquareMatrix

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma bounded_weights_sum_square {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {A : ℝ} (hA : 0≤A) (ha : ∀ i∈s, |a i|≤A) {n : ℕ} (hn : s.card≤n) :
    ∑ i∈s, a i^2 ≤ (n:ℝ)*A^2 := by
  calc
    _ ≤ ∑ _i∈s, A^2 := Finset.sum_le_sum (fun i hi => by
      nlinarith [sq_abs (a i),ha i hi,abs_nonneg (a i)])
    _ = (s.card:ℝ)*A^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (sq_nonneg _)

lemma weighted_centered_clip_tail {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℝ) {A R : ℝ} (hA : 0<A) (hR : 0<R)
    (ha : ∀ i∈s, |a i| ≤ A) {n : ℕ} (hn : 0<n) (hc : s.card≤n)
    {u : ℝ} (hu : 0≤u) :
    standardArrayLaw ι {z | u ≤ |(∑ i∈s,
      a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ)|} ≤
      2*ENNReal.ofReal (exp (-u^2*(n:ℝ)/(2*A^2*R^4))) := by
  let X (i : ι) (z : ι → ℝ) := clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)
  have hi : iIndepFun X (standardArrayLaw ι) := coordinates_independent.comp
    (fun _ x => clippedSquare R x-(∫ y, clippedSquare R y ∂gaussianReal 0 1))
    (fun _ => ((continuous_clippedSquare R).sub continuous_const).measurable)
  have his := hi.comp (fun i z => a i*z) (fun _ => measurable_const.mul measurable_id)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun his (s := s)
    (fun i _ => (centered_clip_subgaussian hR i).const_mul (a i))
  have hv : (∑ i∈s, (NNReal.mk (a i^2) (sq_nonneg (a i)))*(Real.toNNReal (R^2))^2) ≤
      Real.toNNReal ((n:ℝ)*A^2*R^4) := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_mk,
      Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ (n:ℝ)*A^2*R^4),
      ←Finset.sum_mul,show (R^2)^2=R^4 by ring]
    exact mul_le_mul_of_nonneg_right (bounded_weights_sum_square s a hA.le ha hc) (by positivity)
  have ht := subgaussian_abs_tail (subgaussian_mono hsum hv) (u*n) (by positivity)
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have he (z : ι → ℝ) : (u*(n:ℝ) ≤ |∑ i∈s, a i*X i z|) ↔
      u ≤ |(∑ i∈s, a i*X i z)/(n:ℝ)| := by
    rw [abs_div,abs_of_pos hnR,le_div_iff₀ hnR]
  simp only [Function.comp_apply] at ht
  simp_rw [he] at ht
  convert ht using 1
  congr 3
  rw [Real.coe_toNNReal _ (by positivity : (0:ℝ)≤(n:ℝ)*A^2*R^4)]
  field_simp [hnR.ne']

lemma weighted_square_truncation_error {ι : Type*} (s : Finset ι) (a z : ι → ℝ)
    {A R : ℝ} (hA : 0≤A) (hR : 0≤R) (ha : ∀ i∈s, |a i|≤A)
    {n : ℕ} (hn : 0<n) (hc : s.card≤n) :
    |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)-
      (∑ i∈s, a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ)| ≤
      A*((∑ i∈s, squareTail R (z i))/(n:ℝ)+(∫ x, squareTail R x ∂gaussianReal 0 1)) := by
  let m := ∫ x, clippedSquare R x ∂gaussianReal 0 1
  let t := ∫ x, squareTail R x ∂gaussianReal 0 1
  have ht : 0≤t := integral_nonneg (squareTail_nonneg R)
  have hm : |m-1| ≤ t := clippedSquare_mean_error hR
  have he : (∑ i∈s, a i*(z i^2-1)) - (∑ i∈s, a i*(clippedSquare R (z i)-m)) =
      ∑ i∈s, a i*(z i^2-clippedSquare R (z i)+(m-1)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : |(∑ i∈s, a i*(z i^2-1)) - (∑ i∈s, a i*(clippedSquare R (z i)-m))| ≤
      A*((∑ i∈s, squareTail R (z i))+(n:ℝ)*t) := by
    rw [he]
    calc
      _ ≤ ∑ i∈s, |a i*(z i^2-clippedSquare R (z i)+(m-1))| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ i∈s, A*(squareTail R (z i)+t) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        apply mul_le_mul (ha i hi) _ (abs_nonneg _) hA
        apply (abs_add_le _ _).trans
        rw [abs_of_nonneg (square_sub_clip_nonneg R (z i))]
        exact add_le_add (square_sub_clip_le hR _) hm
      _ = A*((∑ i∈s, squareTail R (z i))+(s.card:ℝ)*t) := by
        simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hc : (s.card:ℝ)≤n) ht) _) hA
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  rw [←sub_div,abs_div,abs_of_pos hnR]
  apply (div_le_div_of_nonneg_right hb hnR.le).trans_eq
  dsimp only [t]
  field_simp

theorem weighted_standard_square_tail {A u : ℝ} (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0<c ∧ ∀ {ι : Type} [Fintype ι] (s : Finset ι) (a : ι → ℝ),
      (∀ i∈s, |a i|≤A) → ∀ {n : ℕ}, 0<n → s.card≤n →
      standardArrayLaw ι {z | u ≤ |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)|} ≤
        ENNReal.ofReal (3*exp (-c*n)) := by
  let d := u/(4*(A+1))
  have hd : 0<d := by dsimp [d]; positivity
  obtain ⟨R,c,hR,hc,hm,hrow⟩ := gaussian_squareTail_row_bound hd
  let c' := (u/2)^2/(2*(A+1)^2*R^4)
  have hc' : 0<c' := by dsimp [c']; positivity
  refine ⟨min c c',lt_min hc hc',?_⟩
  intro ι _ s a ha n hn hs
  let E : Set (ι → ℝ) := {z | d ≤ (∑ i∈s, squareTail R (z i))/(n:ℝ)}
  let F : Set (ι → ℝ) := {z | u/2 ≤ |(∑ i∈s,
    a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ)|}
  have hsub : {z | u ≤ |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)|} ⊆ E ∪ F := by
    intro z hz
    by_cases he : z∈E
    · exact Or.inl he
    apply Or.inr
    change u/2 ≤ _
    have hh := weighted_square_truncation_error s a z hA hR.le ha hn hs
    have hze : (∑ i∈s, squareTail R (z i))/(n:ℝ) < d := not_le.mp he
    have haerr : A*(2*d) ≤ u/2 := by
      dsimp [d]
      rw [show 2*(u/(4*(A+1)))=u/(2*(A+1)) by field_simp; ring,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(A+1))).mpr
      nlinarith
    have hb := mul_le_mul_of_nonneg_left (show
      (∑ i∈s, squareTail R (z i))/(n:ℝ)+(∫ x, squareTail R x ∂gaussianReal 0 1) ≤ 2*d
      by linarith) hA
    have htri := abs_add_le
      ((∑ i∈s, a i*(z i^2-1))/(n:ℝ)-
        (∑ i∈s, a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ))
      ((∑ i∈s, a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ))
    simp only [sub_add_cancel] at htri
    change u ≤ _ at hz
    linarith only [hz,hh,hb,haerr,htri]
  have hE := hrow s hn hs
  have hF := weighted_centered_clip_tail s a (by positivity : 0<A+1) hR
    (fun i hi => (ha i hi).trans (by linarith)) hn hs (by positivity : 0≤u/2)
  have hcn : exp (-c*n) ≤ exp (-min c c'*n) := exp_le_exp.mpr (by
    have := min_le_left c c'; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hcn' : exp (-c'*n) ≤ exp (-min c c'*n) := exp_le_exp.mpr (by
    have := min_le_right c c'; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hc'id : -(u/2)^2*(n:ℝ)/(2*(A+1)^2*R^4) = -c'*n := by dsimp [c']; ring
  rw [hc'id] at hF
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le E F
    _ ≤ ENNReal.ofReal (exp (-c*n))+2*ENNReal.ofReal (exp (-c'*n)) := add_le_add hE hF
    _ ≤ ENNReal.ofReal (exp (-min c c'*n))+2*ENNReal.ofReal (exp (-min c c'*n)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hcn) (mul_le_mul_right (ENNReal.ofReal_le_ofReal hcn') _)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]; norm_num; ring

end SKRatio.MatrixNet

end
end

end OAI
