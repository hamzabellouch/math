import OAI.Dynamics.SmoothObstruction.InvariantMeasure
import OAI.Dynamics.SmoothObstruction.Coordinates

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.QR
open InnerProductSpace Finset
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ}

/-- Continuity of the actual Gram--Schmidt algorithm on independent lists. -/
theorem continuous_gramSchmidt (f : X → Fin d → E) (hf : Continuous f)
    (hind : ∀ x,LinearIndependent ℝ (f x)) (j : Fin d) :
    Continuous (fun x => gramSchmidt ℝ (f x) j) := by
  apply wellFounded_lt.induction j
  intro j ih
  have he : (fun x => gramSchmidt ℝ (f x) j)=
      (fun x => f x j-∑ i∈Iio j,
        (inner ℝ (gramSchmidt ℝ (f x) i) (f x j)/‖gramSchmidt ℝ (f x) i‖^2) •
          gramSchmidt ℝ (f x) i) := by
    funext x
    rw [gramSchmidt_def]
    simp [Submodule.starProjection_singleton]
  rw [he]
  apply ((continuous_apply j).comp hf).sub
  apply continuous_finsetSum
  intro i hi
  have hlt := Finset.mem_Iio.mp hi
  exact (((ih i hlt).inner ((continuous_apply j).comp hf)).div
    ((ih i hlt).norm.pow 2) (fun x => pow_ne_zero 2
      (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i (hind x))))).smul (ih i hlt)

theorem continuous_gramSchmidtNormed (f : X → Fin d → E) (hf : Continuous f)
    (hind : ∀ x,LinearIndependent ℝ (f x)) :
    Continuous (fun x => gramSchmidtNormed ℝ (f x)) := by
  apply continuous_pi
  intro j
  exact ((continuous_gramSchmidt f hf hind j).norm.inv₀
    (fun x => norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hind x)))).smul
      (continuous_gramSchmidt f hf hind j)


end SmoothObstruction.QR

namespace SmoothObstruction.QR
open InnerProductSpace Finset Set

/-- Finite orthonormal frames; the zero-dimensional case is included. -/
abbrev Frame (d : ℕ) := {f : Fin d → EuclideanSpace ℝ (Fin d) // Orthonormal ℝ f}

instance (d : ℕ) : Nonempty (Frame d) :=
  ⟨⟨EuclideanSpace.basisFun (Fin d) ℝ, (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal⟩⟩

instance (d : ℕ) : CompactSpace (Frame d) := by
  have hc : IsClosed {f : Fin d → EuclideanSpace ℝ (Fin d) | Orthonormal ℝ f} := by
    simp only [orthonormal_iff_ite,Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const))
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Fin d → EuclideanSpace ℝ (Fin d)) 1).of_isClosed_subset hc
  intro f hf
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact (hf.norm_eq_one i).le

variable {d : ℕ}

/-- The QR frame of the image of an orthonormal frame under an invertible map. -/
noncomputable def step (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) : Frame d :=
  ⟨gramSchmidtNormed ℝ (fun i => A (e.val i)),
    gramSchmidtNormed_orthonormal (e.property.linearIndependent.map' A.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective))⟩

lemma continuous_step {X : Type*} [TopologicalSpace X]
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (e : X → Frame d) (he : Continuous e) : Continuous (fun x => step (A x) (e x)) := by
  apply Continuous.subtype_mk
  apply continuous_gramSchmidtNormed
  · apply continuous_pi
    intro i
    exact hA.clm_apply ((continuous_apply i).comp (continuous_subtype_val.comp he))
  · intro x
    exact (e x).property.linearIndependent.map' (A x).toLinearMap (LinearMap.ker_eq_bot.mpr (A x).injective)

end SmoothObstruction.QR

namespace SmoothObstruction.QR
open InnerProductSpace Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

lemma inner_gramSchmidt_self (f : Fin d → E) (i : Fin d) :
    inner ℝ (gramSchmidt ℝ f i) (f i)=‖gramSchmidt ℝ f i‖^2 := by
  have h := congrArg (fun z => inner ℝ (gramSchmidt ℝ f i) z) (gramSchmidt_def' ℝ f i)
  rw [inner_add_right,inner_sum] at h
  have hz : (∑ j∈Iio i,inner ℝ (gramSchmidt ℝ f i)
      ((ℝ ∙ gramSchmidt ℝ f j).starProjection (f i)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_singleton,inner_smul_right,
      gramSchmidt_orthogonal ℝ f (ne_of_gt (Finset.mem_Iio.mp hj)),mul_zero]
  simpa only [hz,add_zero,real_inner_self_eq_norm_sq] using h

lemma positive_diagonal (f : Fin d → E) (hf : LinearIndependent ℝ f) (i : Fin d) :
    0 < inner ℝ (gramSchmidtNormed ℝ f i) (f i) := by
  rw [gramSchmidtNormed,inner_smul_left,inner_gramSchmidt_self]
  simp only [RCLike.conj_to_real]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)))
    (sq_pos_of_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)))

variable {d : ℕ}
noncomputable def triangular (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => inner ℝ ((step A e).val i) (A (e.val j))

lemma diagonal_pos (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) (i : Fin d) : 0<triangular A e i i :=
  positive_diagonal _ (e.property.linearIndependent.map' A.toLinearMap
    (LinearMap.ker_eq_bot.mpr A.injective)) i

lemma triangular_upper (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) : (triangular A e).IsUpperTriangular := by
  have hf := e.property.linearIndependent.map' A.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective)
  have hn (i : Fin d) : gramSchmidtNormed ℝ (fun j => A (e.val j)) i ≠ 0 := by
    have hh := gramSchmidtNormed_unit_length i hf
    change ‖gramSchmidtNormed ℝ (fun j => A (e.val j)) i‖=1 at hh
    intro hz
    rw [hz,norm_zero] at hh
    exact zero_ne_one hh
  intro i j hj
  change inner ℝ (gramSchmidtNormed ℝ (fun j => A (e.val j)) i) (A (e.val j))=0
  rw [←gramSchmidtOrthonormalBasis_apply
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=Fintype.card (Fin d)) (hn i)]
  exact gramSchmidtOrthonormalBasis_inv_triangular
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=Fintype.card (Fin d))
    (fun j => A (e.val j)) hj


end SmoothObstruction.QR

namespace SmoothObstruction.QR
open MeasureTheory Filter Topology InnerProductSpace
variable {d : ℕ}

noncomputable def basis (e : Frame d) : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  gramSchmidtOrthonormalBasis (by simp) e.val

lemma basis_apply (e : Frame d) (i : Fin d) : basis e i=e.val i := by
  rw [basis,gramSchmidtOrthonormalBasis_apply_of_orthogonal]
  · simp [e.property.norm_eq_one]
  · exact e.property.2
  · exact e.property.ne_zero i

lemma qr_factor (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) (j : Fin d) :
    ∑ i : Fin d,triangular A e i j • (step A e).val i=A (e.val j) := by
  simpa only [OrthonormalBasis.repr_apply_apply,basis_apply,triangular] using
    (basis (step A e)).sum_repr' (A (e.val j))

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def skew (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    X × Frame d → X × Frame d := fun z => (T z.1,step (A z.1) z.2)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_skew (T : X → X) (hT : Continuous T)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))) :
    Continuous (skew T A) :=
  (hT.comp continuous_fst).prodMk (continuous_step _ (hA.comp continuous_fst) _ continuous_snd)

/-- The QR frame process carries a stationary law whose base marginal is
exactly the given measure. The lift is constructed, not hypothesized. -/
theorem exists_stationary_qr (T : X → X) (hT : Continuous T)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (μ : ProbabilityMeasure X) (hμ : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    ∃ ν : ProbabilityMeasure (X × Frame d),
      MeasurePreserving (skew T A) (ν : Measure (X × Frame d)) (ν : Measure (X × Frame d)) ∧
      (ν : Measure (X × Frame d)).map Prod.fst=(μ : Measure X) := by
  have hsur : Function.Surjective (Prod.fst : X × Frame d → X) :=
    fun x => ⟨(x,Classical.choice inferInstance),rfl⟩
  exact CompactInvariant.exists_invariant_lift Prod.fst continuous_fst hsur
    (skew T A) (continuous_skew T hT A hA) T (fun _ => rfl) μ hμ

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_diagonal (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (i : Fin d) : Continuous (fun z : X × Frame d => triangular (A z.1) z.2 i i) := by
  exact ((continuous_apply i).comp (continuous_subtype_val.comp
    (continuous_step _ (hA.comp continuous_fst) _ continuous_snd))).inner
      ((hA.comp continuous_fst).clm_apply
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_log_diagonal (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (i : Fin d) : Continuous (fun z : X × Frame d => Real.log (triangular (A z.1) z.2 i i)) :=
  (continuous_diagonal A hA i).log (fun z => (diagonal_pos (A z.1) z.2 i).ne')

end SmoothObstruction.QR

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

abbrev Path := ℤ → X × CompactMatrix.Alphabet d K

noncomputable def code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) :
    Path (X:=X) (d:=d) (K:=K) := fun j => ((S^j) x,A ((S^j) x))

def shift : Path (X:=X) (d:=d) (K:=K) → Path (X:=X) (d:=d) (K:=K) :=
  fun p j => p (j+1)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_shift : Continuous (shift (X:=X) (d:=d) (K:=K)) := by
  apply continuous_pi
  intro j
  exact continuous_apply (j+1)

omit [CompactSpace X] in
lemma measurable_code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) : Measurable (code S A) := by
  apply Measurable.of_eval
  intro j
  exact (S^j).continuous.measurable.prodMk (hA.comp (S^j).continuous.measurable)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma code_shift (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) :
    code S A (S x)=shift (code S A x) := by
  funext j
  dsimp only [code,shift]
  rw [zpow_add_one,Homeomorph.mul_apply]

/-- Coding even a merely measurable bounded cocycle produces a genuine
stationary law on a compact path space. -/
theorem stationary_code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X)) :
    MeasurePreserving shift ((μ : Measure X).map (code S A))
      ((μ : Measure X).map (code S A)) := by
  have hc := measurable_code S A hA
  refine ⟨continuous_shift.measurable,?_⟩
  rw [Measure.map_map continuous_shift.measurable hc]
  have he : shift ∘ code S A=code S A ∘ S := by
    funext x
    exact (code_shift S A x).symm
  rw [he,←Measure.map_map hc hS.measurable,hS.map_eq]

end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

/-- This Borel set remembers the entire genuine orbit, and the actual
cocycle value at every integer index, despite measurable trivializations. -/
def Actual (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) :
    Set (Path (X:=X) (d:=d) (K:=K)) := {p | p=code S A (p 0).1}

lemma actual_measurable (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) : MeasurableSet (Actual S A) := by
  let : SecondCountableTopology X := inferInstance
  let : SecondCountableTopology (CompactMatrix.Alphabet d K) := inferInstance
  let : SecondCountableTopology (Path (X:=X) (d:=d) (K:=K)) := inferInstance
  let : BorelSpace (Path (X:=X) (d:=d) (K:=K)) := inferInstance
  let : MeasurableEq (Path (X:=X) (d:=d) (K:=K)) :=
    ⟨isClosed_diagonal.measurableSet⟩
  exact measurableSet_eq_fun measurable_id ((measurable_code S A hA).comp
    (measurable_fst.comp (measurable_pi_apply 0)))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma code_actual (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) :
    code S A x ∈ Actual S A := by simp [Actual,code]

noncomputable def matrix (p : Path (X:=X) (d:=d) (K:=K)) := CompactMatrix.equiv (p 0).2

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_matrix : Continuous (fun p : Path (X:=X) (d:=d) (K:=K) =>
    (matrix p).toContinuousLinearMap) :=
  continuous_subtype_val.comp (continuous_snd.comp (continuous_apply 0))

/-- A stationary QR process for the genuine measurable cocycle. The path
law, its original marginal, and concentration on actual orbits are proved. -/
theorem stationary_qr_code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X)) :
    ∃ ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d),
      MeasurePreserving (QR.skew shift matrix) (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)) (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)) ∧
      (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map Prod.fst=(μ : Measure X).map (code S A) ∧
      ∀ᵐ z ∂(ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)), z.1∈Actual S A := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  let μc := μ.map (code S A)
  obtain ⟨ν,hν,hπ⟩ := QR.exists_stationary_qr shift continuous_shift matrix continuous_matrix μc
    (stationary_code S A hA μ hS)
  refine ⟨ν,hν,hπ,?_⟩
  have hμa : ∀ᵐ p ∂((μ : Measure X).map (code S A)), p∈Actual S A := by
    apply (ae_map_iff (measurable_code S A hA).aemeasurable (actual_measurable S A hA)).mpr
    exact Filter.Eventually.of_forall (code_actual S A)
  change (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map Prod.fst=
    (μ : Measure X).map (code S A) at hπ
  rw [←hπ] at hμa
  exact ae_of_ae_map measurable_fst.aemeasurable hμa

omit [CompactSpace X] [BorelSpace X] in
lemma preserving_pow (S : X ≃ₜ X) {μ : Measure X} (hS : MeasurePreserving S μ μ) (n : ℕ) :
    MeasurePreserving (S^n) μ μ := by
  induction n with
  | zero => exact MeasurePreserving.id μ
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hS

omit [CompactSpace X] in
/-- Every deterministic-time observation has exactly the original base law. -/
lemma marginal_at (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X))
    (ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
    (hπ : (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map Prod.fst=(μ : Measure X).map (code S A)) (n : ℕ) :
    (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map (fun z => (z.1 (n : ℤ)).1)=(μ : Measure X) := by
  let p : Path (X:=X) (d:=d) (K:=K) → X := fun q => (q (n : ℤ)).1
  have hp : Measurable p := measurable_fst.comp (measurable_pi_apply _)
  change (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map (p ∘ Prod.fst)=_
  rw [←Measure.map_map hp measurable_fst,hπ,
    Measure.map_map hp (measurable_code S A hA)]
  have he : p ∘ code S A=(S^n : X ≃ₜ X) := by
    funext x; simp [p,code]
  rw [he]
  exact (preserving_pow S hS n).map_eq

end SmoothObstruction.OrbitCocycle

end

end OAI
