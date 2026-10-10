import OAI.Analysis.KadisonSimilarity.FreeProduct.StrongCompressionTransfer
import OAI.Analysis.KadisonSimilarity.Representation.FiniteAmplificationReduction
import OAI.Analysis.KadisonSimilarity.Tracial.UltrapowerCommutators
import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace OAI

/-! Finite standard multiplicities exhaust the countable standard
representation.  The first-coordinate projections and all intertwining
identities below are constructed on the actual Hilbert direct sum. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The countable Hilbert direct sum of a fixed Hilbert space. -/
abbrev CountableCopies (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

private def countableOperatorValue (T : H →L[ℂ] H) (x : CountableCopies H) :
    CountableCopies H :=
  ⟨fun i => T (x i), ((lp.memℓp x).norm.const_smul ‖T‖).mono
    (fun i => T.le_opNorm (x i))⟩

private theorem countableOperatorValue_norm (T : H →L[ℂ] H) (x : CountableCopies H) :
    ‖countableOperatorValue T x‖ ≤ ‖T‖ * ‖x‖ := by
  have h := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (x := countableOperatorValue T x) (y := (‖T‖ : ℝ) • x) (fun i => by
      change ‖T (x i)‖ ≤ ‖(‖T‖ : ℝ) • x i‖
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
        using T.le_opNorm (x i))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using h

/-- The actual coordinatewise countable amplification of an operator. -/
def countableAmplify (T : H →L[ℂ] H) : CountableCopies H →L[ℂ] CountableCopies H :=
  LinearMap.mkContinuous
    { toFun := countableOperatorValue T
      map_add' x y := by apply Subtype.ext; funext i; exact map_add T (x i) (y i)
      map_smul' c x := by apply Subtype.ext; funext i; exact map_smul T c (x i) }
    ‖T‖ (countableOperatorValue_norm T)

@[simp] theorem countableAmplify_apply (T : H →L[ℂ] H) (x : CountableCopies H) (i : ℕ) :
    countableAmplify T x i = T (x i) := rfl

theorem norm_countableAmplify_le (T : H →L[ℂ] H) : ‖countableAmplify T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

variable [CompleteSpace H]

theorem countableAmplify_adjoint (T : H →L[ℂ] H) :
    (countableAmplify T).adjoint = countableAmplify T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, countableAmplify_apply, adjoint_inner_left]

/-- Insert the first `n` coordinates, with zero in every later coordinate. -/
def firstCopiesInclusion (n : ℕ) : HilbertCopies H n →L[ℂ] CountableCopies H :=
  sumColumns (fun i : Fin n => lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i.val)

omit [CompleteSpace H] in
@[simp] theorem firstCopiesInclusion_apply (n : ℕ) (x : HilbertCopies H n) :
    firstCopiesInclusion n x = ∑ i : Fin n, lp.single 2 i.val (x i) :=
  sumColumns_apply _ _

@[simp] theorem firstCopiesInclusion_adjoint_apply (n : ℕ)
    (x : CountableCopies H) (i : Fin n) : (firstCopiesInclusion n).adjoint x i = x i.val := by
  rw [firstCopiesInclusion, sumColumns_adjoint_apply]
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right]
  exact lp.inner_single_left _ _ _

theorem firstCopiesInclusion_adjoint_self (n : ℕ) :
    (firstCopiesInclusion (H := H) n).adjoint.comp (firstCopiesInclusion n) =
      ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
  ext x i
  simp only [comp_apply, firstCopiesInclusion_adjoint_apply, firstCopiesInclusion_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply, id_apply]
  simp only [Fin.val_inj]
  simp

/-- The coordinate insertion preserves the Hilbert norm. -/
def firstCopiesIsometry (n : ℕ) : HilbertCopies H n →ₗᵢ[ℂ] CountableCopies H where
  toLinearMap := (firstCopiesInclusion n).toLinearMap
  norm_map' := (norm_map_iff_adjoint_comp_self _).mpr
    (firstCopiesInclusion_adjoint_self n)

theorem norm_firstCopiesInclusion_le (n : ℕ) : ‖firstCopiesInclusion (H := H) n‖ ≤ 1 :=
  (firstCopiesIsometry (H := H) n).norm_toContinuousLinearMap_le

/-- The orthogonal projection onto the first `n` copies. -/
def firstCopiesProjection (n : ℕ) : CountableCopies H →L[ℂ] CountableCopies H :=
  (firstCopiesInclusion n).comp (firstCopiesInclusion n).adjoint

@[simp] theorem firstCopiesProjection_adjoint (n : ℕ) :
    (firstCopiesProjection (H := H) n).adjoint = firstCopiesProjection n := by
  simp only [firstCopiesProjection, adjoint_comp, adjoint_adjoint]

theorem firstCopiesProjection_tendsto (x : CountableCopies H) :
    Tendsto (fun n => firstCopiesProjection n x) atTop (𝓝 x) := by
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat
  convert h using 1
  funext n
  simp only [firstCopiesProjection, comp_apply, firstCopiesInclusion_apply,
    firstCopiesInclusion_adjoint_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => lp.single 2 i (x i)) n

omit [CompleteSpace H] in
theorem countableAmplify_firstCopiesInclusion (T : H →L[ℂ] H) (n : ℕ) :
    (countableAmplify T).comp (firstCopiesInclusion n) =
      (firstCopiesInclusion n).comp (amplify T n) := by
  ext x k
  simp only [comp_apply, firstCopiesInclusion_apply, map_sum, lp.coeFn_sum,
    Finset.sum_apply, countableAmplify_apply, lp.single_apply, Pi.single_apply,
    amplify_apply, apply_ite, map_zero]

theorem firstCopiesInclusion_adjoint_countableAmplify (T : H →L[ℂ] H) (n : ℕ) :
    (firstCopiesInclusion n).adjoint.comp (countableAmplify T) =
      (amplify T n).comp (firstCopiesInclusion n).adjoint := by
  ext x i
  simp only [comp_apply, firstCopiesInclusion_adjoint_apply,
    countableAmplify_apply, amplify_apply]

/-- Scalar commutators can only decrease on the first finite block. -/
theorem norm_firstCopies_compression_commutator_le
    (Y : CountableCopies H →L[ℂ] CountableCopies H) (T : H →L[ℂ] H) (r : ℕ)
    {c : ℝ} (h : ‖commutator Y (countableAmplify T)‖ ≤ c) :
    ‖commutator ((firstCopiesInclusion r).adjoint.comp
      (Y.comp (firstCopiesInclusion r))) (amplify T r)‖ ≤ c := by
  apply norm_reducing_compression_commutator_le (firstCopiesIsometry r)
    Y (countableAmplify T) (amplify T r)
  · exact countableAmplify_firstCopiesInclusion T r
  · change (countableAmplify T).adjoint.comp (firstCopiesInclusion r) =
      (firstCopiesInclusion r).comp (amplify T r).adjoint
    rw [countableAmplify_adjoint, adjoint_amplify]
    exact countableAmplify_firstCopiesInclusion T.adjoint r
  · exact h

omit [CompleteSpace H] in
private theorem matrix_firstCopies_intertwines (r n : ℕ)
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    (mapCopies (firstCopiesInclusion r) n).comp
      (matrixOperator (fun i j => amplify (X i j) r)) =
    (matrixOperator (fun i j => countableAmplify (X i j))).comp
      (mapCopies (firstCopiesInclusion r) n) :=
  mapCopies_intertwines_matrix (K := HilbertCopies H r) (F := CountableCopies H)
    (n := n) (firstCopiesInclusion (H := H) r)
    (fun i j => amplify (X i j) r) (fun i j => countableAmplify (X i j))
    (fun i j => (countableAmplify_firstCopiesInclusion (X i j) r).symm)

private theorem matrix_firstCopies_adjoint_intertwines (r n : ℕ)
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    (mapCopies (firstCopiesInclusion r).adjoint n).comp
      (matrixOperator (fun i j => countableAmplify (X i j))) =
    (matrixOperator (fun i j => amplify (X i j) r)).comp
      (mapCopies (firstCopiesInclusion r).adjoint n) :=
  mapCopies_intertwines_matrix (K := CountableCopies H) (F := HilbertCopies H r)
    (n := n) (firstCopiesInclusion (H := H) r).adjoint
    (fun i j => countableAmplify (X i j)) (fun i j => amplify (X i j) r)
    (fun i j => firstCopiesInclusion_adjoint_countableAmplify (X i j) r)

/-- Extending the compressed matrix commutator by zero preserves its norm. -/
theorem norm_firstCopies_matrix_compression (r n : ℕ)
    (Y : CountableCopies H →L[ℂ] CountableCopies H)
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖commutator (amplify ((firstCopiesProjection r).comp
      (Y.comp (firstCopiesProjection r))) n)
      (matrixOperator (fun i j => countableAmplify (X i j)))‖ =
    ‖commutator (amplify ((firstCopiesInclusion r).adjoint.comp
      (Y.comp (firstCopiesInclusion r))) n)
      (matrixOperator (fun i j => amplify (X i j) r))‖ := by
  let J := mapCopies (firstCopiesInclusion (H := H) r) n
  let R := mapCopies (firstCopiesInclusion (H := H) r).adjoint n
  have hJ : ‖J‖ ≤ 1 := (norm_mapCopies_le _ _).trans (norm_firstCopiesInclusion_le r)
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using norm_firstCopiesInclusion_le (H := H) r)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies (HilbertCopies H r) n) := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    exact congrArg (fun T => T (x i)) (firstCopiesInclusion_adjoint_self r)
  have hext : amplify ((firstCopiesProjection r).comp (Y.comp (firstCopiesProjection r))) n =
      J.comp ((amplify ((firstCopiesInclusion r).adjoint.comp
        (Y.comp (firstCopiesInclusion r))) n).comp R) := by
    ext x i
    rfl
  rw [hext, commutator_split_extension J R _ _ _
    (matrix_firstCopies_intertwines r n X)
    (matrix_firstCopies_adjoint_intertwines r n X), norm_split_extension J R hJ hR hRJ]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The countable standard amplification of a represented algebra. -/
def countableRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (CountableCopies H →L[ℂ] CountableCopies H) where
  toFun a := countableAmplify (σ a)
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_mul' a b := by ext x i; simp [mul_apply_eq_comp]
  commutes' c := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    change countableAmplify (σ (star a)) = (countableAmplify (σ a)).adjoint
    rw [countableAmplify_adjoint, map_star, ContinuousLinearMap.star_eq_adjoint]

@[simp] theorem countableRepresentation_apply (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    countableRepresentation σ a = countableAmplify (σ a) := rfl

/-- The first-finite-copy estimates imply the same estimate on the countable
standard representation.  The finite-copy premise is a downstream estimate,
not an additional published input. -/
theorem countable_amplification_bound_of_finite
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies H r →L[ℂ] HilbertCopies H r)
      (d : ℝ), 0 ≤ d →
      (∀ a, ‖commutator T (amplify (σ a) r)‖ ≤ d * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤ C * d * ‖X‖)
    (Y : CountableCopies H →L[ℂ] CountableCopies H) {d : ℝ} (hd : 0 ≤ d)
    (hscalar : ∀ a, ‖commutator Y (countableRepresentation σ a)‖ ≤ d * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix (countableRepresentation σ) X)‖ ≤
      C * d * ‖X‖ := by
  refine matrix_commutator_bound_of_selfadjoint_compressions
    (H := CountableCopies H) (l := (atTop : Filter ℕ))
    (firstCopiesProjection (H := H)) (firstCopiesProjection_adjoint (H := H))
    (firstCopiesProjection_tendsto (H := H)) Y n
    (representedMatrix (countableRepresentation σ) X) (by positivity) ?_
  filter_upwards with r
  change ‖commutator (amplify ((firstCopiesProjection r).comp
    (Y.comp (firstCopiesProjection r))) n)
    (matrixOperator (fun i j => countableAmplify (σ (X i j))))‖ ≤ _
  rw [norm_firstCopies_matrix_compression (H := H) r n Y (fun i j => σ (X i j))]
  apply hfinite r _ d hd
  intro a
  exact norm_firstCopies_compression_commutator_le Y (σ a) r (hscalar a)

/-- The actual GNS representation is a direct instance of the countable
amplification transfer, with its original finite-copy constant. -/
theorem gns_countable_amplification_bound (τ : A →ₚ[ℂ] ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
      (d : ℝ), 0 ≤ d →
      (∀ a, ‖commutator T (amplify (τ.gnsStarAlgHom a) r)‖ ≤ d * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
        C * d * ‖X‖)
    (Y : CountableCopies τ.GNS →L[ℂ] CountableCopies τ.GNS)
    {d : ℝ} (hd : 0 ≤ d)
    (hscalar : ∀ a, ‖commutator Y (countableRepresentation τ.gnsStarAlgHom a)‖ ≤ d * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix (countableRepresentation τ.gnsStarAlgHom) X)‖ ≤
      C * d * ‖X‖ :=
  countable_amplification_bound_of_finite τ.gnsStarAlgHom hC hfinite Y hd hscalar n X

end KadisonSimilarity

end

end OAI
