import Mathlib
import OAI.Probability.SKRatio.Calculus.RowControl
import OAI.Probability.SKRatio.Calculus.HeatBathLinearKernel

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma symmetric_row_cost {ι : Type*} [Fintype ι]
    (U : ι → ι → ℝ) (D : ι → ℝ) {R : ℝ}
    (hU : ∀ i j, U i j = U j i) (hD : ∀ i, 0 ≤ D i)
    (hR : ∀ i, ∑ j, U i j ≤ R) :
    (∑ i, ∑ j, U i j*(D i+D j)) ≤ 2*R*(∑ i, D i) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have h₁ : (∑ i, ∑ j, U i j*D i) ≤ R*∑ i, D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hR i) (hD i)
  have h₂ : (∑ i, ∑ j, U i j*D j) = ∑ i, ∑ j, U i j*D i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hU j i]
  rw [h₂]
  linarith only [h₁]

lemma symmetric_row_quadratic {ι : Type*} [Fintype ι]
    (U : ι → ι → ℝ) (z : ι → ℝ) {R : ℝ}
    (hU : ∀ i j, U i j = U j i) (habs : ∀ i j, 0 ≤ U i j)
    (hR : ∀ i, ∑ j, U i j ≤ R) :
    (∑ i, ∑ j, U i j*z i*z j) ≤ R*(∑ i, z i^2) := by
  have hc := symmetric_row_cost U (fun i => z i^2) hU (fun _ => sq_nonneg _) hR
  have hpt (i j : ι) : 2*(U i j*z i*z j) ≤ U i j*(z i^2+z j^2) := by
    have hh := mul_nonneg (habs i j) (sq_nonneg (z i-z j))
    nlinarith only [hh]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpt i j))
  simp only [← Finset.mul_sum] at hh
  linarith only [hh,hc]

lemma quadratic_le_euclideanOpNorm (T : Interaction n) (z : Fin n → ℝ) :
    (∑ i, ∑ j, T i j*z i*z j) ≤ euclideanOpNorm T * ∑ i, z i^2 := by
  let Z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
  have hid : (∑ i, ∑ j, T i j*z i*z j) =
      ⟪Z,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T Z⟫ := by
    rw [Matrix.inner_toEuclideanCLM (T : Matrix (Fin n) (Fin n) ℝ) Z Z]
    simp only [dotProduct,Matrix.mulVec,Z,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [hid]
  calc
    _ ≤ ‖Z‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T Z‖ := real_inner_le_norm _ _
    _ ≤ ‖Z‖ * (euclideanOpNorm T * ‖Z‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = euclideanOpNorm T * ∑ i, z i^2 := by
      rw [show ‖Z‖*(euclideanOpNorm T*‖Z‖) = euclideanOpNorm T*‖Z‖^2 by ring,
        EuclideanSpace.real_norm_sq_eq]

theorem gibbs_cubic_curvature (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) {R : ℝ}
    (hc : ∀ i j, |tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i, ∑ j, |tanh (coupling g i j)|^3 ≤ R) :
    (1-3840000*R)*dirichlet g h f - expectation g h (fun x =>
      ∑ i, ∑ j, (tanh (coupling g i j)+2*tanh (coupling g i j)^2*
        tanh (localField g h i x)*tanh (localField g h j x))*
          siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x) ≤
    expectation g h (fun x => heatBathGenerator g h f x^2) := by
  let U := fun i j => tanh (coupling g i j)
  let D := fun i => expectation g h (fun x => siteVariance g h i x * spinGradient i f x^2)
  let A := fun i j => expectation g h (fun x =>
    (U i j+2*(U i j)^2*tanh (localField g h i x)*tanh (localField g h j x))*
      siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x)
  let X := fun i j => expectation g h (fun x => (f x-conditionalExpectation g h i f x)*
    (f x-conditionalExpectation g h j f x))
  have hpair (i j : Fin n) :
      (if i=j then D i else 0)-A i j-1920000*|U i j|^3*(D i+D j) ≤ X i j := by
    by_cases hij : i=j
    · subst j
      have hX : X i i=D i := by
        dsimp [X,D,siteVariance]
        simp only [← sq,conditionalSiteEnergy_local]
      have hA : A i i=0 := by
        simp [A,U,coupling_diag]
      simp [U,coupling_diag,hA,hX]
    · simpa only [ite_eq_right hij,zero_sub,U,A,D,X] using gibbs_pair_cubic_bound g h i j hij f (hc i j)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpair i j))
  have hcost := symmetric_row_cost (fun i j => |U i j|^3) D
    (fun i j => by dsimp [U];rw [coupling_symm g i j])
    (fun i => expectation_nonneg g h (fun x => mul_nonneg (siteVariance_pos g h i x).le (sq_nonneg _))) hR
  have hD : (∑ i, D i) = dirichlet g h f := (dirichlet_weighted g h f).symm
  have hX : (∑ i, ∑ j, X i j) = expectation g h (fun x => heatBathGenerator g h f x^2) :=
    (heatBathGenerator_square g h f).symm
  simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hsum
  have hcoef : (∑ i, ∑ j, 1920000*|U i j|^3*(D i+D j)) =
      1920000*(∑ i, ∑ j, |U i j|^3*(D i+D j)) := by simp only [mul_assoc,← Finset.mul_sum]
  rw [hcoef,hD,hX] at hsum
  rw [hD] at hcost
  simp only [expectation_sum]
  change _- (∑ i, ∑ j, A i j) ≤ _
  nlinarith only [hsum,hcost]

lemma signed_forms_le (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ)
    (x : Spin n) {M B : ℝ} (hM : 0 ≤ M)
    (hT : euclideanOpNorm (fun i j => tanh (coupling g i j)) ≤ M)
    (hB : ∀ i, ∑ j, tanh (coupling g i j)^2 ≤ B) (hBM : 2*B ≤ M) :
    (∑ i, ∑ j, (tanh (coupling g i j)+2*tanh (coupling g i j)^2*
      tanh (localField g h i x)*tanh (localField g h j x))*
        siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x) ≤
      M*∑ i, siteVariance g h i x*spinGradient i f x^2 := by
  let T := fun i j => tanh (coupling g i j)
  let z := fun i => siteVariance g h i x*spinGradient i f x
  let z' := fun i => tanh (localField g h i x)*z i
  have h₁ := (quadratic_le_euclideanOpNorm T z).trans
    (mul_le_mul_of_nonneg_right hT (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have h₂ := symmetric_row_quadratic (fun i j => T i j^2) z'
    (fun i j => by dsimp [T]; rw [coupling_symm g i j]) (fun _ _ => sq_nonneg _) hB
  have hs : (∑ i, z i^2)+(∑ i, z' i^2) ≤
      ∑ i, siteVariance g h i x*spinGradient i f x^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_nonneg (mul_nonneg (siteVariance_pos g h i x).le
      (sq_nonneg (tanh (localField g h i x)^2))) (sq_nonneg (spinGradient i f x))
    dsimp [z,z',siteVariance] at hh ⊢
    nlinarith only [hh]
  have he : (∑ i, ∑ j, (tanh (coupling g i j)+2*tanh (coupling g i j)^2*
      tanh (localField g h i x)*tanh (localField g h j x))*
        siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x) =
      (∑ i, ∑ j, T i j*z i*z j)+2*(∑ i, ∑ j, T i j^2*z' i*z' j) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [z,z',T]; ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hs hM
  have hb := mul_le_mul_of_nonneg_right hBM
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (z' i)))
  nlinarith only [h₁,h₂,hm,hb]

theorem all_fields_poincare (g : Disorder n) {M B R ρ : ℝ}
    (hM : 0 ≤ M) (hρ : 0 < ρ) (hmargin : ρ ≤ 1-M-3840000*R)
    (hc : ∀ i j, |tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i, ∑ j, |tanh (coupling g i j)|^3 ≤ R)
    (hT : euclideanOpNorm (fun i j => tanh (coupling g i j)) ≤ M)
    (hB : ∀ i, ∑ j, tanh (coupling g i j)^2 ≤ B) (hBM : 2*B ≤ M)
    (h : Fin n → ℝ) (f : Spin n → ℝ) : ρ*variance g h f ≤ dirichlet g h f := by
  apply heatBath_curvature_poincare g h hρ
  intro F
  have hh := gibbs_cubic_curvature g h F hc hR
  have hb := expectation_mono g h (fun x => signed_forms_le g h F x hM hT hB hBM)
  conv_rhs at hb => rw [expectation_const_mul,expectation_sum,← dirichlet_weighted]
  have hm := mul_le_mul_of_nonneg_right hmargin (dirichlet_nonneg g h F)
  nlinarith only [hh,hb,hm]

lemma symmetric_abs_row_quad (T : Interaction n) (hs : ∀ i j, T i j=T j i)
    {R : ℝ} (hR : ∀ i, ∑ j, |T i j| ≤ R) (z : Fin n → ℝ) :
    |∑ i, ∑ j, T i j*z i*z j| ≤ R*∑ i, z i^2 := by
  calc
    _ ≤ ∑ i, ∑ j, |T i j*z i*z j| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ i, ∑ j, |T i j| *|z i| *|z j| := by simp only [abs_mul]
    _ ≤ R*∑ i, |z i|^2 := symmetric_row_quadratic _ _
      (fun i j => by rw [hs i j]) (fun _ _ => abs_nonneg _) hR
    _ = _ := by simp only [sq_abs]

lemma euclideanOpNorm_le_abs_row (T : Interaction n) (hs : ∀ i j, T i j=T j i)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ i, ∑ j, |T i j| ≤ R) : euclideanOpNorm T ≤ R := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T
  have hsa : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    change (T : Matrix (Fin n) (Fin n) ℝ)ᴴ = T
    ext i j
    change T j i=T i j
    exact hs j i)
  change ‖A‖ ≤ R
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := A) hsa]
  apply ciSup_le
  intro z
  by_cases hz : z=0
  · simp [hz,ContinuousLinearMap.rayleighQuotient,hR0]
  have hn : 0 < ‖z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hh := symmetric_abs_row_quad T hs hR (fun i => z i)
  have he : ⟪A z,z⟫ = ∑ i, ∑ j, T i j*z i*z j := by
    rw [real_inner_comm]
    change ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T z⟫ = _
    rw [Matrix.inner_toEuclideanCLM (T : Matrix (Fin n) (Fin n) ℝ) z z]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _; ring
  simpa only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real,he,abs_div,abs_pow,abs_norm,div_le_iff₀ hn] using
    (show |∑ i, ∑ j, T i j*z i*z j| ≤ R*‖z‖^2 by simpa only [EuclideanSpace.real_norm_sq_eq] using hh)

lemma cubic_row_bound (T : Interaction n) {δ B : ℝ} (hδ : 0 ≤ δ)
    (he : ∀ i j, |T i j| ≤ δ) (hB : ∀ i, ∑ j, T i j^2 ≤ B) (i : Fin n) :
    (∑ j, |T i j|^3) ≤ δ*B := by
  calc
    _ = ∑ j, |T i j| *T i j^2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ,sq_abs];ring
    _ ≤ ∑ j, δ*T i j^2 := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (he i j) (sq_nonneg _))
    _ = δ*∑ j, T i j^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB i) hδ

lemma tanh_euclideanOpNorm (T : Interaction n) (hs : ∀ i j, T i j=T j i)
    {δ B : ℝ} (hδ : 0 ≤ δ) (hB0 : 0 ≤ B)
    (he : ∀ i j, |T i j| ≤ δ) (hB : ∀ i, ∑ j, T i j^2 ≤ B) :
    euclideanOpNorm (fun i j => tanh (T i j)) ≤ euclideanOpNorm T+δ*B/3 := by
  have hr : euclideanOpNorm (fun i j => tanh (T i j)-T i j) ≤ δ*B/3 := by
    apply euclideanOpNorm_le_abs_row _ (fun i j => by rw [hs i j]) (by positivity)
    intro i
    calc
      _ ≤ ∑ j, |T i j|^3/3 := Finset.sum_le_sum (fun j _ => tanh_cubic_error _)
      _ = (∑ j, |T i j|^3)/3 := (Finset.sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right (cubic_row_bound T hδ he hB i) (by norm_num)
  have hh := norm_add_le (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j)-T i j))
  have hi : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T+
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j)-T i j) := by
    ext z i
    change (∑ j, tanh (T i j)*z j) = (∑ j, T i j*z j)+(∑ j, (tanh (T i j)-T i j)*z j)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _;ring
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j))‖ ≤ _
  rw [hi]
  exact hh.trans (add_le_add le_rfl hr)

lemma tanh_square_row (T : Interaction n) {B : ℝ} (hB : ∀ i, ∑ j, T i j^2 ≤ B)
    (i : Fin n) : (∑ j, tanh (T i j)^2) ≤ B := by
  apply le_trans _ (hB i)
  apply Finset.sum_le_sum
  intro j _
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_tanh_le_abs (T i j)) 2

theorem poincare_of_matrix_bounds (g : Disorder n) {K B δ ρ : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hρ : 0 < ρ) (hmargin : ρ ≤ 1-(K+δ*B/3)-3840000*(δ*B))
    (hBK : 2*B ≤ K) (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (he : ∀ i j, |coupling g i j| ≤ δ) (hrow : ∀ i, ∑ j, coupling g i j^2 ≤ B)
    (h : Fin n → ℝ) (f : Spin n → ℝ) : ρ*variance g h f ≤ dirichlet g h f := by
  apply all_fields_poincare g (M := K+δ*B/3) (B := B) (R := δ*B)
    (by positivity) hρ hmargin
  · intro i j
    exact ((abs_tanh_le_abs _).trans (he i j)).trans hδsmall
  · intro i
    apply le_trans _ (cubic_row_bound _ hδ he hrow i)
    exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (abs_tanh_le_abs _) 3)
  · exact (tanh_euclideanOpNorm _ (coupling_symm g) hδ hB he hrow).trans
      (add_le_add hnorm le_rfl)
  · exact tanh_square_row _ hrow
  · linarith only [hBK,mul_nonneg hδ hB]

end SKRatio.Fields

end
end

end OAI
