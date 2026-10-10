import Mathlib
import OAI.Analysis.AffineBernstein.LogBarrierCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogCaccioppoli

lemma contDiff_cofactorHessian_entry_global {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (i j : Fin n) :
    ContDiff ℝ ∞ (fun x => cofactorHessian u x i j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_cofactorHessian_entry isOpen_univ hu.contDiffOn
    (fun y _ => hp y) (mem_univ x) i j

lemma integral_flux_compact {n : ℕ} (F : Fin n → Space n → ℝ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ x, ∑ j, F j x * dirDeriv (coordinateVector n j) g x) =
      -(∫ x, (∑ j, dirDeriv (coordinateVector n j) (F j) x) * g x) := by
  have hi (j : Fin n) : Integrable (fun x => F j x * dirDeriv (coordinateVector n j) g x) :=
    ((hF j).continuous.mul (contDiff_dirDeriv hg _).continuous).integrable_of_hasCompactSupport
      ((hgc.fderiv_apply ℝ _).mul_left)
  have hj (j : Fin n) : Integrable (fun x => dirDeriv (coordinateVector n j) (F j) x * g x) :=
    ((contDiff_dirDeriv (hF j) _).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left)
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hj j), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_mul_fderiv_compact _ g _ (fun _ _ => (hF j).contDiffAt.of_le (by norm_num))
    (hg.of_le (by norm_num)) hgc

lemma inverseHessian_ibp {n : ℕ} {u f g : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ x, (hessian u x).det * inverseHessianPair u f g x) =
      -(∫ x, (hessian u x).det * inverseHessianTrace u f x * g x) := by
  let F : Fin n → Space n → ℝ := fun j x => ∑ i,
    cofactorHessian u x i j * dirDeriv (coordinateVector n i) f x
  have hF : ∀ j, ContDiff ℝ ∞ (F j) := fun j => ContDiff.sum fun i _ =>
    (contDiff_cofactorHessian_entry_global hu hp i j).mul (contDiff_dirDeriv hf _)
  have hleft (x : Space n) : (∑ j, F j x * dirDeriv (coordinateVector n j) g x) =
      (hessian u x).det * inverseHessianPair u f g x := by
    simp only [F,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [inverseHessianPair,cofactorHessian,Matrix.smul_apply,smul_eq_mul,
      Finset.mul_sum,mul_assoc]
  have hright (x : Space n) : (∑ j, dirDeriv (coordinateVector n j) (F j) x) =
      (hessian u x).det * inverseHessianTrace u f x := by
    have hd (i j : Fin n) :
        dirDeriv (coordinateVector n j) (fun y => cofactorHessian u y i j *
          dirDeriv (coordinateVector n i) f y) x =
        dirDeriv (coordinateVector n j) (fun y => cofactorHessian u y i j) x *
          dirDeriv (coordinateVector n i) f x +
        cofactorHessian u x i j * hessian f x j i := by
      exact dirDeriv_mul ((contDiff_cofactorHessian_entry_global hu hp i j).differentiable (by simp) x)
        ((contDiff_dirDeriv hf _).differentiable (by simp) x) (coordinateVector n j)
    simp only [F,dirDeriv_sum (fun i y => cofactorHessian u y i _ *
      dirDeriv (coordinateVector n i) f y) (fun i =>
        ((contDiff_cofactorHessian_entry_global hu hp i _).mul (contDiff_dirDeriv hf _)).differentiable (by simp) x),
      hd, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j i => dirDeriv (coordinateVector n j)
      (fun y => cofactorHessian u y i j) x * dirDeriv (coordinateVector n i) f x)]
    have hzero : (∑ i, ∑ j, dirDeriv (coordinateVector n j)
        (fun y => cofactorHessian u y i j) x * dirDeriv (coordinateVector n i) f x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [← Finset.sum_mul]
      have hh := (cofactorHessian_divergence isOpen_univ u (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffOn
        (fun y _ => hp y) x (mem_univ x) i).1
      change (∑ j, dirDeriv (coordinateVector n j) (fun y => cofactorHessian u y i j) x) = 0 at hh
      rw [hh,zero_mul]
    rw [hzero,zero_add,Finset.sum_comm]
    have hs : (hessian f x).IsSymm := hessian_isSymm hf.contDiffAt
    simp only [hs.apply,cofactorHessian,Matrix.smul_apply,smul_eq_mul,inverseHessianTrace,
      Finset.mul_sum,mul_assoc]
  simpa only [hleft,hright] using integral_flux_compact F hF hg hgc

lemma contDiff_inverseHessianTrace_global {n : ℕ} {u f : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (inverseHessianTrace u f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_inverse_matrix_entry_param
      (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu.contDiffAt i j)
      (ne_of_gt (hp x).det_pos) i j).mul
    (contDiffAt_hessian_entry hf.contDiffAt i j)

lemma contDiff_inverseHessianPair_global {n : ℕ} {u f g : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (inverseHessianPair u f g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffAt_inverse_matrix_entry_param
      (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu.contDiffAt i j)
      (ne_of_gt (hp x).det_pos) i j).mul
    (contDiffAt_dirDeriv hf.contDiffAt _)).mul (contDiffAt_dirDeriv hg.contDiffAt _)

lemma inverseHessianPair_cauchy {n : ℕ} {u f g : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) :
    inverseHessianPair u f g x ^ 2 ≤ inverseHessianPair u f f x * inverseHessianPair u g g x := by
  have he (v w : Space n → ℝ) : inverseHessianPair u v w x =
      inverseMatrixPair (hessian u x) (fun i => dirDeriv (coordinateVector n i) w x)
        (fun i => dirDeriv (coordinateVector n i) v x) := by
    unfold inverseHessianPair inverseMatrixPair
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [he]
  simpa only [mul_comm] using inverseMatrixPair_cauchy hp
    (fun i => dirDeriv (coordinateVector n i) g x) (fun i => dirDeriv (coordinateVector n i) f x)


lemma inverseHessianTrace_log_supersolution {n : ℕ} {u s : Space n → ℝ}
    (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < s x)
    (hL : ∀ x, inverseHessianTrace u s x ≤ 0) (x : Space n) :
    inverseHessianTrace u (fun y => Real.log (s y)) x +
      inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x ≤ 0 := by
  have he : inverseHessianTrace u s x = s x *
      (inverseHessianTrace u (fun y => Real.log (s y)) x +
        inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x) := by
    simp only [inverseHessianTrace,inverseHessianPair,mul_add,Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hh := log_second_identity isOpen_univ hs.contDiffOn (fun y _ => hpos y)
      (mem_univ x) (coordinateVector n i) (coordinateVector n j)
    change hessian s x i j = s x * (hessian (fun y => Real.log (s y)) x i j + _) at hh
    rw [hh]
    ring
  have ht := hL x
  rw [he] at ht
  exact nonpos_of_mul_nonpos_right ht (hpos x)

/-- Caccioppoli for the logarithm of a strictly positive supersolution of the
actual cofactor-divergence operator. The coefficients are not assumed uniformly
elliptic, and no Harnack estimate enters this proof. -/
theorem linearizedMA_log_caccioppoli {n : ℕ} {u s η : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < s x)
    (hL : ∀ x, inverseHessianTrace u s x ≤ 0)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    (∫ x, (hessian u x).det * (η x)^2 *
      inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x) ≤
      4 * ∫ x, (hessian u x).det * inverseHessianPair u η η x := by
  let g := fun y => Real.log (s y)
  have hg : ContDiff ℝ ∞ g := hs.log (fun x => ne_of_gt (hpos x))
  have hdt : Continuous (fun x => (hessian u x).det) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (contDiffAt_det_hessian hu.contDiffAt).continuousAt
  have hQ (f k : Space n → ℝ) (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) :
      Continuous (inverseHessianPair u f k) := (contDiff_inverseHessianPair_global hu hp hf hk).continuous
  have hη2c : HasCompactSupport (fun x => (η x)^2) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    intro x hx
    exact subset_tsupport η (fun h => hx (by simp only [h,zero_pow (by norm_num : 2 ≠ 0)]))
  have hE : Integrable (fun x => (hessian u x).det * (η x)^2 * inverseHessianPair u g g x) :=
    ((hdt.mul (hη.continuous.pow 2)).mul (hQ g g hg hg)).integrable_of_hasCompactSupport
      (hη2c.mul_left.mul_right)
  have hcut : HasCompactSupport (inverseHessianPair u η η) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    intro x hx
    by_contra hxi
    apply hx
    have hd : ∀ i, dirDeriv (coordinateVector n i) η x = 0 := fun i => by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hh => hxi (tsupport_fderiv_apply_subset ℝ (coordinateVector n i) hh)
    simp [inverseHessianPair,hd]
  have hC : Integrable (fun x => (hessian u x).det * inverseHessianPair u η η x) :=
    (hdt.mul (hQ η η hη hη)).integrable_of_hasCompactSupport hcut.mul_left
  have hT : Integrable (fun x => (hessian u x).det * inverseHessianTrace u g x * (η x)^2) :=
    ((hdt.mul (contDiff_inverseHessianTrace_global hu hp hg).continuous).mul
      (hη.continuous.pow 2)).integrable_of_hasCompactSupport (hη2c.mul_left)
  have hX : Integrable (fun x => 2*(hessian u x).det*η x*inverseHessianPair u g η x) :=
    (((continuous_const.mul hdt).mul hη.continuous).mul (hQ g η hg hη)).integrable_of_hasCompactSupport
      (hηc.mul_left.mul_right)
  have hpair (x : Space n) : inverseHessianPair u g (fun y => (η y)^2) x =
      2*η x*inverseHessianPair u g η x := by
    have hd (j : Fin n) : dirDeriv (coordinateVector n j) (fun y => (η y)^2) x =
        2*η x*dirDeriv (coordinateVector n j) η x := by
      unfold dirDeriv
      rw [((hη.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
      norm_num [smul_apply,smul_eq_mul]
    simp only [inverseHessianPair,hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hIBP := inverseHessian_ibp hu hp hg (hη.pow 2) hη2c
  simp only [hpair] at hIBP
  have hIBP' : (∫ x, 2*(hessian u x).det*η x*inverseHessianPair u g η x) =
      -(∫ x, (hessian u x).det* inverseHessianTrace u g x * (η x)^2) := by
    convert hIBP using 1
    congr 1
    funext x
    ring
  have hbound := integral_mono hE hT.neg (fun x => by
    have hlog := inverseHessianTrace_log_supersolution hs hpos hL x
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hp x).det_pos.le (sq_nonneg (η x))) hlog
    change (hessian u x).det*(η x)^2*inverseHessianPair u g g x ≤
      -((hessian u x).det*inverseHessianTrace u g x*(η x)^2)
    change inverseHessianTrace u g x + inverseHessianPair u g g x ≤ 0 at hlog
    nlinarith)
  simp only [Pi.neg_apply] at hbound
  rw [integral_neg, ← hIBP'] at hbound
  have hyoung (x : Space n) : 2*(hessian u x).det*η x*inverseHessianPair u g η x ≤
      (1/2:ℝ)*((hessian u x).det*(η x)^2*inverseHessianPair u g g x) +
        2*((hessian u x).det*inverseHessianPair u η η x) := by
    have hh := cauchy_young (inverseHessianPair_self_nonneg (hp x) η)
      (inverseHessianPair_self_nonneg (hp x) g)
      (show inverseHessianPair u g η x ^ 2 ≤
        inverseHessianPair u η η x * inverseHessianPair u g g x by
        simpa only [mul_comm] using inverseHessianPair_cauchy (f := g) (g := η) (hp x))
      (a := 2*η x) (show (0:ℝ)<2 by norm_num)
    have hh' := mul_le_mul_of_nonneg_left hh (hp x).det_pos.le
    nlinarith
  have hy := integral_mono hX ((hE.const_mul (1/2)).add (hC.const_mul 2)) hyoung
  simp only [Pi.add_apply] at hy
  rw [integral_add (hE.const_mul _) (hC.const_mul _),integral_const_mul,integral_const_mul] at hy
  nlinarith

end LogCaccioppoli



end
end AffineBernstein
end

end OAI
