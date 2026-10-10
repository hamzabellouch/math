import Mathlib
import OAI.Probability.SKRatio.FiniteChain.WeightedKernelOperator
import OAI.Probability.SKRatio.Variational.FormContinuity
import OAI.Probability.SKRatio.Matrices.AugmentedBounds

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma weighted_operator_event_measurable {X : Type*} (β u : ℝ) (G : X × X → ℝ) :
    MeasurableSet {g : Disorder n | ∃ x : Fin n → X,
      u < euclideanOpNorm (fun i j => squareError β g i j*G (x i,x j))} := by
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n)) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearMap.continuousSMul
  simp only [ofPred_exists]
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro x
  apply isOpen_lt continuous_const
  apply continuous_norm.comp
  apply ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_coupling i j).pow 2).sub continuous_const).mul_const _

lemma augmented_weighted_operator_rare {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (β : ℝ) (G : X × X → ℝ) (hG : Continuous G) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ x : Fin n → X, u < euclideanOpNorm
        (fun i j => squareError β (augmentedDisorder β g) i j*G (x i,x j))}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := weighted_square_operator_rare β G hG hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  rw [(augmentedDisorder_hasLaw hn0 β).measure_eq (weighted_operator_event_measurable β u G)]
  exact hn

lemma squareError_row (β : ℝ) (g : Disorder n) (f : Fin n → ℝ) (i : Fin n) :
    (∑ j, squareError β g i j*f j) =
      (∑ e : incidentEdges i, (g e^2-β^2/(n:ℝ))*f (otherEnd i e))-β^2/(n:ℝ)*f i := by
  have he := squareError_decomposition β g
  simp_rw [show (fun i j => squareError β g i j)=
    (fun i j => coupling (fun e => g e^2-β^2/(n:ℝ)) i j-
      Matrix.diagonal (fun _ => β^2/(n:ℝ)) i j) from congrArg (fun m => fun i j => m i j) he]
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [sum_coupling_weighted_row]
  simp only [←Finset.sum_attach (s := incidentEdges i)]
  congr 1
  · simp only [sub_mul,Finset.sum_sub_distrib, Finset.attach_eq_univ]
  · simp [Matrix.diagonal_apply,ite_mul]

lemma diagonal_weight_bound (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight)
    (p ζ : Fin n → ℝ) {u : ℝ} (hζ : ∀ i, |ζ i| ≤ u)
    (hG : ∀ a : FieldWeight, |G (a,a)| ≤ 1) :
    |weightedForm (Matrix.diagonal ζ) G x p| ≤ u*∑ i, p i^2 := by
  have hf : weightedForm (Matrix.diagonal ζ) G x p = ∑ i, ζ i*G (x i,x i)*p i^2 := by
    simp only [weightedForm,quadratic,Matrix.diagonal_apply,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, u*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (hG (x i)) (abs_nonneg _)).trans (by simpa only [mul_one] using hζ i))
        (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

lemma compactF_le_eight (a b : FieldWeight) : |compactF (a,b)|≤8 := by
  rw [abs_of_nonneg (compactF_nonneg _)]
  exact (compactF_bound _).trans (by nlinarith [b.2.2])

def reducedForm (β : ℝ) (g : (Fin n × Fin n) → ℝ) (p : Fin n → ℝ) : ℝ :=
  let x := fun i => compactWeight (augmentedField β g i)
  weightedForm (augmented β g) varianceKernel x p +
    2*weightedForm (fun _ _ => β^2/(n:ℝ)) meanVarianceKernel x p +
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF x p +
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK x p

lemma compactForm_reduced_error (β : ℝ) (g : (Fin n × Fin n) → ℝ)
    (p : Fin n → ℝ) {a d : ℝ}
    (hdiag : ∀ i, |augmentedDiagonal β g i|≤a)
    (hm : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*meanVarianceKernel (x i,x j)) ≤ a)
    (hk : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*compactK (x i,x j)) ≤ a)
    (hf : ∀ i, |∑ e : incidentEdges i, (augmentedDisorder β g e^2-β^2/(n:ℝ))*
      compactF (compactWeight (augmentedField β g i),compactWeight (augmentedField β g (otherEnd i e)))| ≤ d) :
    |compactForm (coupling (augmentedDisorder β g))
      (fun i => compactWeight (augmentedField β g i)) p-reducedForm β g p| ≤
      (4*a+d+8*β^2/(n:ℝ))*(∑ i, p i^2) := by
  let J := coupling (augmentedDisorder β g)
  let x := fun i => compactWeight (augmentedField β g i)
  let L := weightedForm J varianceKernel x p-weightedForm (augmented β g) varianceKernel x p
  let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => J i j^2)
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => β^2/(n:ℝ))
  let M := weightedForm Q meanVarianceKernel x p-weightedForm B meanVarianceKernel x p
  let D := diagonalForm Q compactF x p-diagonalForm B compactF x p
  let K := weightedForm Q compactK x p-weightedForm B compactK x p
  have hL : |L|≤a*(∑ i, p i^2) := by
    have hd := diagonal_weight_bound varianceKernel x p (augmentedDiagonal β g) hdiag
      (fun b => by simpa only [varianceKernel,abs_of_nonneg (compactV_nonneg b)] using compactV_le_one b)
    have he : weightedForm (augmented β g) varianceKernel x p =
        weightedForm J varianceKernel x p+weightedForm (Matrix.diagonal (augmentedDiagonal β g)) varianceKernel x p := by
      have hmat : augmented β g = (Matrix.of J)+Matrix.diagonal (augmentedDiagonal β g) := by
        dsimp only [J]
        rw [coupling_augmentedDisorder]
        change augmented β g = (augmented β g - Matrix.diagonal (augmentedDiagonal β g)) + Matrix.diagonal (augmentedDiagonal β g)
        exact (sub_add_cancel _ _).symm
      rw [hmat]
      simp only [weightedForm,quadratic,Matrix.add_apply,add_mul,Finset.sum_add_distrib,Matrix.of_apply]
    dsimp [L]
    rw [he,sub_add_cancel_left,abs_neg]
    exact hd
  have hM : |M|≤a*(∑ i, p i^2) := by
    dsimp only [M]
    rw [weightedForm_sub]
    exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right (hm x)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hK : |K|≤a*(∑ i, p i^2) := by
    dsimp only [K]
    rw [weightedForm_sub]
    exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right (hk x)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hD : |D|≤(d+8*β^2/(n:ℝ))*(∑ i, p i^2) := by
    dsimp only [D]
    rw [diagonalForm_sub]
    apply diagonalForm_abs_le
    intro i
    change |∑ j, squareError β (augmentedDisorder β g) i j*compactF (x i,x j)|≤_
    rw [squareError_row]
    apply (abs_sub _ _).trans
    apply add_le_add (hf i)
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ))]
    have hh := mul_le_mul_of_nonneg_left (compactF_le_eight (x i) (x i))
      (show 0≤β^2/(n:ℝ) by positivity)
    convert hh using 1
    ring
  have hid : compactForm J x p-reducedForm β g p=L+2*M+D+K := by
    dsimp [compactForm,reducedForm,L,M,D,K,x,Q,B]
    simp only [weightedForm,diagonalForm,Matrix.of_apply]
    ring
  change |compactForm J x p-reducedForm β g p| ≤ _
  rw [hid]
  have ht := (abs_add_le (L+2*M+D) K).trans
    (add_le_add ((abs_add_le (L+2*M) D).trans (add_le_add (abs_add_le L (2*M)) le_rfl)) le_rfl)
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
  nlinarith only [ht,hL,hM,hD,hK]

theorem reduced_error_rare {β : ℝ} (hβ : 0<β) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ p : Fin n → ℝ, u*(∑ i, p i^2)<
        |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p|}) := by
  let K := 2*β+β^2+1
  have hK : 0≤K := by dsimp [K]; positivity
  let a := u/8
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨δ,hδ,hfield⟩ := compactForm_uniform_field_change (sq_nonneg K) hK ha
  have hN := augmented_norm_rare hβ (by norm_num : (0:ℝ)<1)
  have hD := augmented_diagonal_rare β (lt_min hδ ha)
  have hM := augmented_weighted_operator_rare β meanVarianceKernel continuous_meanVarianceKernel ha
  have hC := augmented_weighted_operator_rare β compactK continuous_compactK ha
  have hF := augmented_weighted_diagonal_rare compactF continuous_compactF compactWeight compactWeight_lipschitz β ha
  apply ((((hN.union hD).union hM).union hC).union hF).mono
  have ht : ∀ᶠ n : ℕ in atTop, 8*β^2/(n:ℝ)≤a :=
    ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (8*β^2)).eventually (gt_mem_nhds ha)).mono
      (fun _ hn => hn.le)
  filter_upwards [ht] with n hn
  rintro g ⟨p,hp⟩
  by_contra hb
  have hnorm : euclideanOpNorm (coupling (augmentedDisorder β g))≤K :=
    le_of_not_gt (fun h => hb (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  have hdiag : ∀ i, |augmentedDiagonal β g i|≤ min δ a :=
    fun i => le_of_not_gt (fun h => hb (Or.inl (Or.inl (Or.inl (Or.inr ⟨i,h⟩)))))
  have hm : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*meanVarianceKernel (x i,x j))≤a :=
    fun x => le_of_not_gt (fun h => hb (Or.inl (Or.inl (Or.inr ⟨x,h⟩))))
  have hk : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*compactK (x i,x j))≤a :=
    fun x => le_of_not_gt (fun h => hb (Or.inl (Or.inr ⟨x,h⟩)))
  have hf : ∀ i, |∑ e : incidentEdges i, (augmentedDisorder β g e^2-β^2/(n:ℝ))*
      compactF (compactWeight (augmentedField β g i),compactWeight (augmentedField β g (otherEnd i e)))|≤a :=
    fun i => le_of_not_gt (fun h => hb (Or.inr ⟨i,h⟩))
  let J := coupling (augmentedDisorder β g)
  have hefield (i : Fin n) : |(∑ j, J i j)-augmentedField β g i|≤δ := by
    rw [←diagonalField_augmented]
    change |(∑ j, J i j)-(augmentedDiagonal β g i+(∑ j, J i j))|≤δ
    rw [sub_add_cancel_right,abs_neg]
    exact (hdiag i).trans (min_le_left _ _)
  have h₁ := hfield J (coupling_symm _) hnorm
    (row_squares_le_opNorm J (coupling_symm _) hK hnorm) _ _ p hefield
  have h₂ := compactForm_reduced_error β g p (fun i => (hdiag i).trans (min_le_right _ _)) hm hk hf
  have hgrad := gradientForm_eq_compactForm J (coupling_symm _) (coupling_diag _) p
  rw [hgrad] at hp
  have habs := abs_sub_le (compactForm J (fun i => compactWeight (∑ j, J i j)) p)
    (compactForm J (fun i => compactWeight (augmentedField β g i)) p) (reducedForm β g p)
  have hnorm0 : 0≤∑ i, p i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hn hnorm0
  dsimp [a] at h₁ h₂ hh
  nlinarith only [hp,habs,h₁,h₂,hh,hu,hnorm0]

end SKRatio.Planted

end

end OAI
