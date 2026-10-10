import OAI.MathematicalPhysics.CriticalSK.CubeRestriction
import OAI.MathematicalPhysics.CriticalSK.GOESpectrum
import OAI.MathematicalPhysics.CriticalSK.Gibbs

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set

namespace CriticalSK

section

lemma symmetric_sum_upper {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i)+2*∑ e : Edge n, f e.val.1 e.val.2 := by
  classical
  have hu : (∑ e : Edge n, f e.val.1 e.val.2) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Fintype.sum_prod_type' (fun i j : Fin n => if i < j then f i j else 0)]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (by intro p; simp) (fun p : Fin n × Fin n => f p.1 p.2)).symm
  rw [hu]
  have hl : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [hf j i]
  have hd : (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by simp
  calc
    _ = (∑ i, ∑ j, if i = j then f i j else 0)+
        (∑ i, ∑ j, if i < j then f i j else 0)+(∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h,ne_of_lt h,not_lt_of_ge h.le]
      · subst j; simp
      · simp [h,ne_of_gt h,not_lt_of_ge h.le]
    _ = _ := by rw [hd,hl]; ring

def matrixDisorder {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Disorder n := fun e => A e.val.1 e.val.2

def matrixEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, A i j*spinValue (x i)*spinValue (x j)

lemma matrixEnergy_hamiltonian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x : Spin n) :
    matrixEnergy A x = hamiltonian (matrixDisorder A) x+(1/2:ℝ)*∑ i, A i i := by
  unfold matrixEnergy
  rw [symmetric_sum_upper _ (by intro i j; rw [hA.apply i j]; ring)]
  have hd : (∑ i, A i i*spinValue (x i)*spinValue (x i)) = ∑ i, A i i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc,← pow_two,spinValue_sq,mul_one]
  rw [hd]
  unfold hamiltonian matrixDisorder
  ring

lemma matrixEnergy_inner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    matrixEnergy A x = (1/2:ℝ)*inner ℝ (cubeVector x) (A.toEuclideanLin (cubeVector x)) := by
  simp only [matrixEnergy,EuclideanSpace.inner_eq_star_dotProduct,Matrix.toLpLin_apply,star_trivial]
  change (1/2:ℝ)*(∑ i, ∑ j, A i j*spinValue (x i)*spinValue (x j)) =
    (1/2:ℝ)*∑ i, (∑ j, A i j*spinValue (x j))*spinValue (x i)
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def matrixGibbs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  Real.exp (matrixEnergy A x)/(∑ y, Real.exp (matrixEnergy A y))

lemma matrixGibbs_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x : Spin n) :
    matrixGibbs A x = gibbs (matrixDisorder A) x := by
  simp only [matrixGibbs,matrixEnergy_hamiltonian A hA,Real.exp_add,← Finset.sum_mul]
  unfold gibbs partition
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

lemma gibbs_continuous {n : ℕ} (x : Spin n) : Continuous (fun W : Disorder n => gibbs W x) := by
  apply Continuous.div
  · unfold hamiltonian; fun_prop
  · unfold partition hamiltonian; fun_prop
  · exact fun W => (partition_pos W).ne'

def linearSmallBall {n : ℕ} (W : Disorder n) (a : Fin n → ℝ) (b : ℝ) : ℝ :=
  ∑ x, if |linearObservable a x| ≤ b then gibbs W x else 0

lemma linearSmallBall_nonneg {n : ℕ} (W : Disorder n) (a : Fin n → ℝ) (b : ℝ) :
    0 ≤ linearSmallBall W a b := by
  unfold linearSmallBall
  exact Finset.sum_nonneg fun x _ => by split_ifs; exact gibbs_nonneg W x; rfl

lemma linearSmallBall_le_one {n : ℕ} (W : Disorder n) (a : Fin n → ℝ) (b : ℝ) :
    linearSmallBall W a b ≤ 1 := by
  rw [← gibbs_sum W]
  apply Finset.sum_le_sum
  intro x _
  split_ifs; rfl; exact gibbs_nonneg W x

lemma linearSmallBall_continuous {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    Continuous (fun W : Disorder n => linearSmallBall W a b) := by
  unfold linearSmallBall
  apply continuous_finsetSum
  intro x _
  split_ifs
  · exact gibbs_continuous x
  · exact continuous_const

def smallBallObstruction (n : ℕ) (b δ : ℝ) : Set (Disorder n) :=
  {W | ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → δ ≤ linearSmallBall W a b}

lemma smallBallObstruction_closed (n : ℕ) (b δ : ℝ) : IsClosed (smallBallObstruction n b δ) := by
  unfold smallBallObstruction
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (linearSmallBall_continuous _ _)

lemma linearObservable_inner {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) (x : Spin n) :
    linearObservable a x = inner ℝ a (cubeVector x) := by
  simp only [linearObservable,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  change a i*spinValue (x i) = spinValue (x i)*a i
  ring

def rotatedDirection {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  (orthogonalIsometry U).symm (EuclideanSpace.basisFun (Fin n) ℝ i)

lemma rotatedDirection_norm {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    ‖rotatedDirection U i‖ = 1 := by
  rw [rotatedDirection,LinearIsometryEquiv.norm_map]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i

lemma rotatedDirection_observable {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) (x : Spin n) :
    linearObservable (rotatedDirection U i) x = (orthogonalIsometry U (cubeVector x)) i := by
  rw [linearObservable_inner,← (orthogonalIsometry U).inner_map_map]
  simp only [rotatedDirection,LinearIsometryEquiv.apply_symm_apply,EuclideanSpace.basisFun_inner]

lemma gibbs_exp_shift {n : ℕ} {W : Disorder n} (E : Spin n → ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = E x+c) (x : Spin n) :
    gibbs W x = Real.exp (E x)/(∑ y, Real.exp (E y)) := by
  simp only [gibbs,partition,h,Real.exp_add,← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

lemma rotatedCubeSmallBall_eq {n : ℕ} {W : Disorder n} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+c)
    (b : ℝ) (i : Fin n) :
    rotatedCubeSmallBall lam b i U = linearSmallBall W (rotatedDirection U i) b := by
  have hg := gibbs_exp_shift _ c h
  unfold rotatedCubeSmallBall rotatedCubeRestricted rotatedCubePartition linearSmallBall
  simp only [one_div,rotatedDirection_observable,hg]
  rw [mul_div_mul_left _ _ (inv_ne_zero (by positivity : (Fintype.card (Spin n):ℝ) ≠ 0))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

lemma smallBallObstruction_rotation {n : ℕ} {W : Disorder n} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+c)
    (b δ : ℝ) (i : Fin n) (hW : W ∈ smallBallObstruction n b δ) :
    δ ≤ rotatedCubeSmallBall lam b i U := by
  rw [rotatedCubeSmallBall_eq lam U c h]
  exact hW _ (rotatedDirection_norm U i)

lemma orthogonalIsometry_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    orthogonalIsometry (1 : Matrix.orthogonalGroup ι ℝ) x = x := euclideanMatrix_one_apply x

lemma orthogonalIsometry_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.orthogonalGroup ι ℝ) : orthogonalIsometry U⁻¹ = (orthogonalIsometry U).symm := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (orthogonalIsometry U).injective
  rw [LinearIsometryEquiv.apply_symm_apply,← orthogonalIsometry_mul,mul_inv_cancel,orthogonalIsometry_one]

lemma continuous_pair_transform {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X × Y → Z} {g : X → X} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => f (g p.1,p.2)) :=
  hf.comp ((hg.comp continuous_fst).prodMk continuous_snd)

lemma orthogonalIsometry_symm_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι => (orthogonalIsometry p.1).symm p.2) := by
  have h : Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι =>
      orthogonalIsometry (p.1⁻¹) p.2) :=
    continuous_pair_transform orthogonalIsometry_continuous continuous_inv
  convert h using 1
  funext p
  exact congrArg (fun V : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι => V p.2)
    (orthogonalIsometry_inv p.1).symm

def haarConjugate {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : GaussianMatrix (Fin n)) : GaussianMatrix (Fin n) :=
  conjugateGaussianMatrix (orthogonalIsometry U).symm A

lemma haarConjugate_measurable (n : ℕ) :
    Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × GaussianMatrix (Fin n) => haarConjugate p.1 p.2) :=
  by
    have h := conjugateGaussianMatrix_measurable
      (fun U : Matrix.orthogonalGroup (Fin n) ℝ => (orthogonalIsometry U).symm)
      (orthogonalIsometry_symm_continuous (ι := Fin n)).measurable
    exact h

lemma gaussian_matrix_energy_eigenbasis {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    ∃ V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x, diagonalEnergy (matrixOrderedEigenvalues A) (V x) = inner ℝ x (gaussianMatrixCLM A x) := by
  let hT := gaussianMatrixCLM_symmetric A hA
  let hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  refine ⟨(hT.eigenvectorBasis hn).repr,?_⟩
  intro x
  rw [matrixOrderedEigenvalues_eq A hA]
  exact eigenbasisQuadratic_eq hT hn x

lemma haarConjugate_energy {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : GaussianMatrix (Fin n)) (x : Spin n) :
    matrixEnergy (matrixOfGaussian (haarConjugate U A)) x =
      (1/2:ℝ)*inner ℝ (orthogonalIsometry U (cubeVector x))
        (gaussianMatrixCLM A (orthogonalIsometry U (cubeVector x))) := by
  rw [matrixEnergy_inner]
  have hc := congrArg (fun L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => L (cubeVector x))
    (gaussianMatrixCLM_conjugate (orthogonalIsometry U).symm A)
  change gaussianMatrixCLM (haarConjugate U A) (cubeVector x) =
    (orthogonalIsometry U).symm (gaussianMatrixCLM A (orthogonalIsometry U (cubeVector x))) at hc
  change (1/2:ℝ)*inner ℝ (cubeVector x) (gaussianMatrixCLM (haarConjugate U A) (cubeVector x)) = _
  rw [hc,← (orthogonalIsometry U).inner_map_map,LinearIsometryEquiv.apply_symm_apply]

lemma haarConjugate_hamiltonian {n : ℕ} (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i)
    (V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hV : ∀ x, diagonalEnergy (matrixOrderedEigenvalues A) (V x) = inner ℝ x (gaussianMatrixCLM A x))
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Spin n) :
    hamiltonian (matrixDisorder (matrixOfGaussian (haarConjugate U A))) x =
      (1/2:ℝ)*diagonalEnergy (matrixOrderedEigenvalues A)
        (orthogonalIsometry (matrixOfIsometry V*U) (cubeVector x))-
        (1/2:ℝ)*∑ i, haarConjugate U A i i := by
  rw [orthogonalIsometry_mul,orthogonalIsometry_matrixOfIsometry,hV,← haarConjugate_energy]
  have hB : (matrixOfGaussian (haarConjugate U A)).IsSymm := by
    ext i j
    exact conjugate_symmetric (orthogonalIsometry U).symm A hA j i
  rw [matrixEnergy_hamiltonian _ hB]
  change _ = _ - (1/2:ℝ)*∑ i, matrixOfGaussian (haarConjugate U A) i i
  ring

lemma goe_haar_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun p : Matrix.orthogonalGroup (Fin n) ℝ × GaussianMatrix (Fin n) => haarConjugate p.1 p.2)
      ((orthogonalHaar (Fin n)).prod (goeLaw (Fin n) s)) (goeLaw (Fin n) s) := by
  exact measurePreserving_snd.comp (random_goe_conjugation_preserving (orthogonalHaar (Fin n)) s
    (fun U => (orthogonalIsometry U).symm) orthogonalIsometry_symm_continuous.measurable)

lemma preserving_product_event_real {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (T : X × Y → Z) (hT : MeasurePreserving T (μ.prod ν) ρ)
    {E : Set Z} (hE : MeasurableSet E) :
    ρ.real E = ∫ y, μ.real {x | T (x,y) ∈ E} ∂ν := by
  let f : Z → ℝ := E.indicator 1
  have hf : Measurable f := measurable_const.indicator hE
  let F := fun p : X × Y => f (T p)
  have hF : Measurable F := hf.comp hT.measurable
  have hi : Integrable F (μ.prod ν) := by
    apply (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable
    filter_upwards [] with p
    simp only [F,f]
    by_cases hp : T p ∈ E <;> simp [hp]
  have he := integral_map (μ := μ.prod ν) hT.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq,integral_indicator_one hE,integral_prod_symm F hi] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with y
  have hs : MeasurableSet {x | T (x,y) ∈ E} :=
    hE.preimage (hT.measurable.comp (measurable_id.prodMk measurable_const))
  exact integral_indicator_one hs

lemma goe_haar_event_identity (n : ℕ) (s : ℝ) {E : Set (GaussianMatrix (Fin n))} (hE : MeasurableSet E) :
    (goeLaw (Fin n) s).real E =
      ∫ A, (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ∂goeLaw (Fin n) s :=
  preserving_product_event_real _ _ _ _ (goe_haar_preserving n s) hE

open scoped NNReal

def gaussianDisorder {n : ℕ} (A : GaussianMatrix (Fin n)) : Disorder n :=
  matrixDisorder (matrixOfGaussian A)

lemma gaussianDisorder_measurable (n : ℕ) : Measurable (gaussianDisorder (n := n)) := by
  apply Measurable.of_eval
  intro e
  change Measurable (fun A : GaussianMatrix (Fin n) => A e.val.1 e.val.2)
  fun_prop

lemma goe_disorder_law (n : ℕ) : (goeLaw (Fin (n+1)) (goeScale n)).map gaussianDisorder = disorderLaw (n+1) := by
  let e : Edge (n+1) → UpperEntry (Fin (n+1)) := fun p => ⟨p.val,p.property.le⟩
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun r : UpperEntry (Fin (n+1)) => r.val) hpq
  have hi := (goe_entries_independent (ι := Fin (n+1)) (goeScale n)).precomp he
  have hm := hi.map_fun_eq_pi_map (fun _ => by fun_prop)
  change (goeLaw (Fin (n+1)) (goeScale n)).map gaussianDisorder = _ at hm
  rw [hm]
  unfold disorderLaw
  congr 1
  funext p
  rw [goe_entry_law,ite_eq_right (ne_of_lt p.property)]
  congr 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_inv,NNReal.coe_natCast,goeScale_square]
  norm_num only [Nat.cast_add,Nat.cast_one]

end

open Set MeasureTheory

lemma haar_smallBallObstruction_bound {n : ℕ} (hn : 0 < n)
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i)
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : Fin n) :
    (orthogonalHaar (Fin n)).real {U | gaussianDisorder (haarConjugate U A) ∈ smallBallObstruction n b δ} ≤
      (2*(sphereTilted (matrixOrderedEigenvalues A) 1 (Real.sqrt n)).real
        {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b}+
        4*(∫ U, (rotatedCubePartition (matrixOrderedEigenvalues A) 1 U /
          spherePartition (matrixOrderedEigenvalues A) 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n)))/δ := by
  obtain ⟨V,hV⟩ := gaussian_matrix_energy_eigenbasis A hA
  let lam := matrixOrderedEigenvalues A
  let R := matrixOfIsometry V
  have hmeas : Measurable (fun U => rotatedCubeSmallBall lam b i (R*U)) :=
    (rotatedCubeSmallBall_measurable lam b i).comp ((continuous_const.mul continuous_id).measurable)
  have hi : Integrable (fun U => rotatedCubeSmallBall lam b i (R*U)) (orthogonalHaar (Fin n)) := by
    apply (integrable_const (1:ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with U
    rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeSmallBall_nonneg lam b i (R*U))]
    exact rotatedCubeSmallBall_le_one lam b i (R*U)
  have hh := integral_dominates_event (E := {U | gaussianDisorder (haarConjugate U A) ∈ smallBallObstruction n b δ})
    (hi.div_const δ) (fun U => div_nonneg (rotatedCubeSmallBall_nonneg lam b i (R*U)) hδ.le) (fun U hU => by
      apply (le_div_iff₀ hδ).mpr
      rw [one_mul]
      exact smallBallObstruction_rotation lam (R*U) (-(1/2:ℝ)*∑ j, haarConjugate U A j j)
        (fun x => by simpa only [gaussianDisorder,lam,R,sub_eq_add_neg,neg_mul] using haarConjugate_hamiltonian A hA V hV U x) b δ i hU)
  rw [integral_div,integral_mul_left_eq_self] at hh
  exact hh.trans (div_le_div_of_nonneg_right (rotatedCubeSmallBall_expectation hn lam b i) hδ.le)

lemma goe_event_from_orbit_bound {n : ℕ} (s : ℝ) {E G : Set (GaussianMatrix (Fin n))}
    (hE : MeasurableSet E) (hG : MeasurableSet G) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ A ∈ G, (∀ i j, A i j = A j i) →
      (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ≤ C) :
    (goeLaw (Fin n) s).real E ≤ (goeLaw (Fin n) s).real Gᶜ+C := by
  rw [goe_haar_event_identity n s hE]
  have hi : Integrable (fun A => Gᶜ.indicator (1 : GaussianMatrix (Fin n) → ℝ) A+C) (goeLaw (Fin n) s) :=
    ((integrable_const (1:ℝ)).indicator hG.compl).add (integrable_const C)
  have hh := integral_mono_of_nonneg
    (show ∀ᵐ A ∂goeLaw (Fin n) s, 0 ≤ (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} from
      ae_of_all _ (fun _ => measureReal_nonneg)) hi
    (show ∀ᵐ A ∂goeLaw (Fin n) s, (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ≤
      Gᶜ.indicator (1 : GaussianMatrix (Fin n) → ℝ) A+C from by
      filter_upwards [goe_symmetric_ae s] with A hA
      by_cases hAG : A ∈ G
      · simpa only [Set.indicator_of_notMem (show A ∉ Gᶜ from not_not.mpr hAG),zero_add] using hbound A hAG hA
      · rw [Set.indicator_of_mem hAG]
        exact (measureReal_le_one).trans (le_add_of_nonneg_right hC))
  change (∫ A, (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ∂goeLaw (Fin n) s) ≤
    (∫ A, Gᶜ.indicator (fun _ => (1:ℝ)) A+C ∂goeLaw (Fin n) s) at hh
  rw [integral_add ((integrable_const (1:ℝ)).indicator hG.compl) (integrable_const C),
    integral_indicator_const _ hG.compl,integral_const] at hh
  simpa using hh

end CriticalSK

end

end OAI
