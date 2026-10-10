import Mathlib
import OAI.Probability.SKRatio.Quantization.BinProcess
import OAI.Probability.SKRatio.Variational.ReducedForm

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma fieldProjection_apply (i j : Fin n) :
    fieldProjection n i j = (if i=j then 1 else 0)-(n:ℝ)⁻¹ := by
  simp only [fieldProjection,residualProjection,Matrix.sub_apply,Matrix.one_apply,
    Matrix.mul_apply,Matrix.transpose_apply,queryColumn,constantDirection,Fin.sum_univ_one]
  congr 1
  rw [←mul_inv_rev,←pow_two,sq_sqrt (Nat.cast_nonneg n)]

lemma fieldProjection_symmetric : (fieldProjection n)ᵀ=fieldProjection n := by
  ext i j
  simp only [Matrix.transpose_apply,fieldProjection_apply,eq_comm]

lemma fieldProjection_mulVec (p : Fin n → ℝ) :
    fieldProjection n *ᵥ p = Bins.centered p := by
  ext i
  simp only [Matrix.mulVec,dotProduct,fieldProjection_apply,sub_mul,Finset.sum_sub_distrib,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    ←Finset.mul_sum,Bins.centered,Bins.average,Fintype.card_fin,div_eq_mul_inv]
  ring

lemma fieldProjection_vecMul (p : Fin n → ℝ) :
    p ᵥ* fieldProjection n = Bins.centered p := by
  rw [←fieldProjection_symmetric,Matrix.vecMul_transpose,fieldProjection_mulVec]

lemma projected_bilinear (M : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ) :
    p ⬝ᵥ ((fieldProjection n*M*fieldProjection n)*ᵥ q) =
      Bins.centered p ⬝ᵥ (M*ᵥ Bins.centered q) := by
  rw [←Matrix.mulVec_mulVec,fieldProjection_mulVec,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,fieldProjection_vecMul]

lemma fullCoeff_goe (β : ℝ) (v p : Fin n → ℝ)
    (g : Bins.Coordinates (Fin n) → ℝ) :
    (∑ k, Bins.fullCoeff v p (β/sqrt n) k*g k) =
      p ⬝ᵥ ((fieldProjection n*(β • goe (fun ij => g (.inl ij)))*fieldProjection n)*ᵥ
        (fun i => v i*p i)) := by
  rw [projected_bilinear]
  simp only [Fintype.sum_sum_type,Bins.fullCoeff,zero_mul,Finset.sum_const_zero,add_zero,
    Fintype.sum_prod_type,dotProduct,Matrix.mulVec,Matrix.smul_apply,smul_eq_mul,goe,
    Finset.mul_sum]
  have hs : sqrt (2*(n:ℝ))=sqrt 2*sqrt n := sqrt_mul (by norm_num) _
  rw [hs]
  let x := Bins.centered p
  let y := Bins.centered (fun i => v i*p i)
  change (∑ i, ∑ j, β/sqrt n/sqrt 2*(x i*y j+x j*y i)*g (.inl (i,j))) =
    ∑ i, ∑ j, x i*(β*((g (.inl (i,j))+g (.inl (j,i)))/(sqrt 2*sqrt n))*y j)
  have he (i j : Fin n) : β/sqrt n/sqrt 2*(x i*y j+x j*y i)*g (.inl (i,j)) =
      β/(sqrt 2*sqrt n)*(x i*y j*g (.inl (i,j))+x j*y i*g (.inl (i,j))) := by ring
  simp_rw [he,mul_add,Finset.sum_add_distrib,←Finset.mul_sum]
  have hswap : (∑ i, ∑ j, x j*y i*g (.inl (i,j)))=
      ∑ i, ∑ j, x i*y j*g (.inl (j,i)) := Finset.sum_comm
  rw [hswap]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma weightedForm_variance_bilinear (M : Matrix (Fin n) (Fin n) ℝ)
    (H p : Fin n → ℝ) :
    weightedForm M varianceKernel (fun i => compactWeight (H i)) p =
      p ⬝ᵥ (M*ᵥ (fun i => v (H i)*p i)) := by
  simp only [weightedForm,quadratic,varianceKernel,compactV_weight,dotProduct,
    Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def rankForm (H v p : Fin n → ℝ) : ℝ :=
  ((∑ i, p i*H i)*(∑ i, p i*v i)+(∑ i, p i)*(∑ i, p i*H i*v i)-
    ((∑ i, H i)/(n:ℝ))*(∑ i, p i)*(∑ i, p i*v i))/(n:ℝ)

lemma rank_form_expansion (H v p : Fin n → ℝ) :
    (∑ i, ∑ j, ((H i+H j-(∑ k, H k)/(n:ℝ))/(n:ℝ))*v j*p i*p j) =
      rankForm H v p := by
  simp only [rankForm,add_div,sub_div,add_mul,sub_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have h1 (i : Fin n) : (∑ j, H i/(n:ℝ)*v j*p i*p j) =
      p i*H i*(∑ j, p j*v j)/(n:ℝ) := by
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 (i : Fin n) : (∑ j, H j/(n:ℝ)*v j*p i*p j) =
      p i*(∑ j, p j*H j*v j)/(n:ℝ) := by
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h3 (i : Fin n) : (∑ j, ((∑ k, H k)/(n:ℝ))/(n:ℝ)*v j*p i*p j) =
      ((∑ k, H k)/(n:ℝ))*p i*(∑ j, p j*v j)/(n:ℝ) := by
    conv_rhs => rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h1,h2,h3]
  simp only [←Finset.sum_div,←Finset.sum_mul,←Finset.mul_sum]

def deterministicForm (β : ℝ) (H p : Fin n → ℝ) : ℝ :=
  rankForm H (fun i => v (H i)) p +
    2*β^2/(n:ℝ)*(∑ i, p i)*(∑ i, p i*m (H i)*v (H i)) +
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H i)) p +
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H i)) p

theorem reducedForm_decomposition (hn : 0<n) (β : ℝ)
    (g : (Fin n × Fin n) → ℝ) (p : Fin n → ℝ) :
    reducedForm β g p =
      p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
        (fun i => v (augmentedField β g i)*p i)) +
      deterministicForm β (augmentedField β g) p := by
  have h1 : weightedForm (augmented β g) varianceKernel
      (fun i => compactWeight (augmentedField β g i)) p =
      weightedForm (fieldProjection n*(β • goe g)*fieldProjection n) varianceKernel
        (fun i => compactWeight (augmentedField β g i)) p +
      rankForm (augmentedField β g) (fun i => v (augmentedField β g i)) p := by
    simp only [weightedForm,quadratic,varianceKernel,compactV_weight]
    simp_rw [augmented_decomposition hn,add_mul,Finset.sum_add_distrib]
    rw [rank_form_expansion]
  have h2 : 2*weightedForm (fun _ _ => β^2/(n:ℝ)) meanVarianceKernel
      (fun i => compactWeight (augmentedField β g i)) p =
      2*β^2/(n:ℝ)*(∑ i, p i)*(∑ i, p i*m (augmentedField β g i)*v (augmentedField β g i)) := by
    simp only [weightedForm,quadratic,meanVarianceKernel,compactV_weight,compactWeight_coe,
      w,sub_sub_cancel]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [reducedForm]
  rw [h1,h2,weightedForm_variance_bilinear]
  unfold deterministicForm
  ring

end SKRatio.Planted

namespace SKRatio.Bins
open SKRatioClock.Regression Planted
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

lemma inl_array_hasLaw :
    HasLaw (fun g : Coordinates (Fin n) → ℝ => fun ij : Fin n × Fin n => g (.inl ij))
      (standardArrayLaw (Fin n × Fin n)) (SKRatioGaussian.gaussianCoordinates (Coordinates (Fin n))) := by
  exact iIndepFun.hasLaw_pi (fun ij => coordinate_hasLaw (Sum.inl ij : Coordinates (Fin n)))
    (iIndepFun.precomp Sum.inl_injective coordinates_independent)

def projectedSup (β : ℝ) (v : Fin n → ℝ) (p : I → Fin n → ℝ)
    (g : (Fin n × Fin n) → ℝ) : ℝ :=
  sSup (Set.range (fun t => p t ⬝ᵥ
    ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ (fun i => v i*p t i))))

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
lemma projectedSup_eq (β : ℝ) (v : Fin n → ℝ) (p : I → Fin n → ℝ)
    (g : Coordinates (Fin n) → ℝ) :
    projectedSup β v p (fun ij => g (.inl ij)) =
      SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => fullCoeff v (p t) (β/sqrt n)) g := by
  unfold projectedSup SKRatioGaussian.gaussianSup
  congr 2
  funext t
  simp only [SKRatioGaussian.gaussianAffine,zero_add,fullCoeff_goe]

omit [Nonempty I] in
lemma projectedSup_continuous [Nonempty (Fin n)] (β : ℝ) (v : Fin n → ℝ)
    {p : I → Fin n → ℝ} (hp : Continuous p) : Continuous (projectedSup β v p) := by
  have he : projectedSup β v p = fun g =>
      SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => fullCoeff v (p t) (β/sqrt n))
        (Sum.elim g (fun _ => 0)) := by
    ext g
    exact projectedSup_eq β v p (Sum.elim g (fun _ => 0))
  rw [he]
  apply (SKRatioGaussian.continuous_gaussianSup continuous_const ((continuous_fullCoeff v _).comp hp)).comp
  apply continuous_pi
  intro k
  cases k with
  | inl ij => exact continuous_apply ij
  | inr i => exact continuous_const

lemma le_projectedSup [Nonempty (Fin n)] (β : ℝ) (v : Fin n → ℝ) {p : I → Fin n → ℝ}
    (hp : Continuous p) (g : (Fin n × Fin n) → ℝ) (t : I) :
    p t ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ (fun i => v i*p t i)) ≤
      projectedSup β v p g := by
  have hh := SKRatioGaussian.gaussianAffine_le_gaussianSup (m := fun _ : I => 0) continuous_const
    ((continuous_fullCoeff v (β/sqrt n)).comp hp) (Sum.elim g (fun _ => 0)) t
  simpa only [SKRatioGaussian.gaussianAffine,Function.comp_def,zero_add,fullCoeff_goe,←projectedSup_eq,Sum.elim_inl] using hh

theorem projectedSup_tail (hn : 0<n) (σ : Fin n → α) (v b : α → ℝ)
    (hv : ∀ a, |v a|≤1) {s : α → ℝ} {β : ℝ} (hβ : 0<β)
    {u : I → Fin n → ℝ} (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s)
    (hp : ∀ t, ∑ i, (b (σ i)+u t i)^2=1) {a : ℝ} (ha : 0≤a) :
    (standardArrayLaw (Fin n × Fin n)).real {g |
      (∑ d, β/sqrt n*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤
      projectedSup β (fun i => v (σ i)) (fun t i => b (σ i)+u t i) g} ≤
      exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hδ : 0<β/sqrt (n:ℝ) := div_pos hβ (sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hsup := full_sup_tail σ v b hv hδ huc hu0 hus hp ha
  have hmeas : MeasurableSet {g |
      (∑ d, β/sqrt n*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤
      projectedSup β (fun i => v (σ i)) (fun t i => b (σ i)+u t i) g} :=
    measurableSet_le measurable_const
      (projectedSup_continuous β _ (continuous_const.add huc)).measurable
  rw [←inl_array_hasLaw.measureReal_eq hmeas]
  simp_rw [projectedSup_eq]
  convert hsup using 1
  apply congrArg Real.exp
  rw [div_pow,sq_sqrt (Nat.cast_nonneg n)]
  field_simp

end SKRatio.Bins

end

end OAI
