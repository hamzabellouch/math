import OAI.Geometry.ComplexBundle.ProjectionBundle
import OAI.Geometry.ComplexBundle.Projective
import OAI.Geometry.ComplexBundle.Pullback

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

/-- Restrict an ambient linear functional to each actual tautological line,
viewed as a section of its dual, the hyperplane bundle. -/
def hyperplaneFunctionalSection (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) : (projectionDualLineCore d).Fiber p :=
  L (unitProjectionColumn p ((projectionLineCore d).indexAt p))

theorem hyperplaneFunctionalSection_chart (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) (i : Fin d) (hi : p ∈ projectionChartSet i) :
    ((projectionDualLineCore d).localTriv i ⟨p,hyperplaneFunctionalSection L p⟩).2 =
      L (unitProjectionColumn p i) := by
  let j := (projectionLineCore d).indexAt p
  have hj : p ∈ projectionChartSet j := (projectionLineCore d).mem_baseSet_at p
  have hv := unitProjectionColumn_reconstruct p i hi
    (unitProjectionColumn p j) (unitProjectionColumn_mem p j)
  have he : L (unitProjectionColumn p j) =
      projectionLineTransition j i p * L (unitProjectionColumn p i) := by
    rw [← hv,map_smul]
    rfl
  change star (projectionLineTransition j i p) * L (unitProjectionColumn p j) = _
  rw [he,← mul_assoc,projectionLineTransition_unitary j i p hj hi,one_mul]

theorem continuous_hyperplaneFunctionalSection (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ) :
    Continuous (fun p => TotalSpace.mk' ℂ p (hyperplaneFunctionalSection L p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [FiberBundle.continuousAt_section]
  let i := (projectionLineCore d).indexAt p
  have hi : p ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at p
  have hc := L.toContinuousLinearMap.continuous.continuousAt.comp
    ((continuousOn_unitProjectionColumn i p hi).continuousAt
      ((isOpen_projectionChartSet i).mem_nhds hi))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_projectionChartSet i).mem_nhds hi] with q hq
  exact hyperplaneFunctionalSection_chart L q i hq

/-- The section's actual dual-line realization is exactly restriction of L. -/
theorem hyperplaneFunctionalSection_realization (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) (v : projectionLine p) :
    projectionDualLineFiberEquiv p (hyperplaneFunctionalSection L p) v = L v.val := by
  let i := (projectionLineCore d).indexAt p
  have hi : p ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at p
  change L (unitProjectionColumn p i) * inner ℂ (unitProjectionColumn p i) v.val = L v.val
  conv_rhs => rw [← unitProjectionColumn_reconstruct p i hi v.val v.property,map_smul]
  exact mul_comm _ _

theorem hyperplaneFunctionalSection_eq_zero_iff (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) : hyperplaneFunctionalSection L p=0 ↔
      ∀ v ∈ projectionLine p, L v=0 := by
  constructor
  · intro h v hv
    have he := hyperplaneFunctionalSection_realization L p ⟨v,hv⟩
    rw [h,map_zero,LinearMap.zero_apply] at he
    exact he.symm
  · intro h
    exact h _ (unitProjectionColumn_mem p _)

def coordinateFunctional (i : Fin d) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp (EuclideanSpace.equiv (Fin d) ℂ).toLinearEquiv.toLinearMap

@[simp] theorem coordinateFunctional_apply (i : Fin d) (v : EuclideanSpace ℂ (Fin d)) :
    coordinateFunctional i v=v i := rfl

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

def positiveCoordinate (k : ℕ) (i : Fin k) : Fin (1+k) := ⟨i.val+1,by omega⟩

def firstCoordinateVector (k : ℕ) : EuclideanSpace ℂ (Fin (1+k)) :=
  WithLp.toLp 2 (Pi.single 0 (1 : ℂ))

theorem firstCoordinateVector_ne_zero (k : ℕ) : firstCoordinateVector k≠0 := by
  intro h
  have he := congrArg (fun v : EuclideanSpace ℂ (Fin (1+k)) => v 0) h
  simp [firstCoordinateVector] at he

def firstCoordinateProjection (k : ℕ) : projectionSpace (1+k) 1 :=
  nonzeroVectorProjection (firstCoordinateVector k) (firstCoordinateVector_ne_zero k)

theorem firstCoordinateProjection_line (k : ℕ) :
    projectionLine (firstCoordinateProjection k)=Submodule.span ℂ {firstCoordinateVector k} :=
  nonzeroVectorProjection_line _ _

theorem vector_eq_firstCoordinate_of_positive_zero {k : ℕ}
    (v : EuclideanSpace ℂ (Fin (1+k))) (hv : ∀ i : Fin k, v (positiveCoordinate k i)=0) :
    v=(v 0) • firstCoordinateVector k := by
  ext j
  by_cases hj : j=0
  · subst j
    simp [firstCoordinateVector]
  · have hpos : 0<j.val := by
      have : j.val≠0 := fun h => hj (Fin.ext h)
      omega
    let i : Fin k := ⟨j.val-1,by omega⟩
    have hi : positiveCoordinate k i=j := Fin.ext (by dsimp [positiveCoordinate,i]; omega)
    have hzero := hv i
    rw [hi] at hzero
    simp [firstCoordinateVector,hj,hzero]

/-- The K coordinate sections of O(1) on CP^K have exactly one common zero,
the first coordinate line. This is an actual zero-set statement, not yet
an identification or nonvanishing theorem for the top Chern class. -/
theorem hyperplaneCoordinateSections_common_zero {k : ℕ} (p : projectionSpace (1+k) 1) :
    (∀ i : Fin k, hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate k i)) p=0) ↔
      p=firstCoordinateProjection k := by
  constructor
  · intro h
    have hle : projectionLine p ≤ Submodule.span ℂ {firstCoordinateVector k} := by
      intro v hv
      have hz (i : Fin k) : v (positiveCoordinate k i)=0 :=
        (hyperplaneFunctionalSection_eq_zero_iff _ p).mp (h i) v hv
      rw [vector_eq_firstCoordinate_of_positive_zero v hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    apply projectionLine_injective
    rw [firstCoordinateProjection_line]
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [projectionLine_finrank,finrank_span_singleton (firstCoordinateVector_ne_zero k)]
  · rintro rfl i
    rw [hyperplaneFunctionalSection_eq_zero_iff,firstCoordinateProjection_line]
    intro v hv
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hi : positiveCoordinate k i≠0 := by
      intro h
      have := congrArg Fin.val h
      simp [positiveCoordinate] at this
    simp [coordinateFunctional_apply,firstCoordinateVector,hi]

end Kaplansky

open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

/-- Evaluation at any nonzero vector is a genuine coordinate on the dual
of its one-dimensional line. -/
def hyperplaneEvaluationEquiv (p : projectionSpace d 1) (v : projectionLine p) (hv : v≠0) :
    (projectionDualLineCore d).Fiber p ≃ₗ[ℂ] ℂ := by
  let c : ℂ := (projectionLineFiberEquiv p).symm v
  have hc : c≠0 := by
    intro h
    apply hv
    exact (projectionLineFiberEquiv p).symm.injective (h.trans (map_zero _).symm)
  exact {
    toFun := fun z => (show ℂ from z)*c
    invFun := fun z => (show (projectionDualLineCore d).Fiber p from z/c)
    left_inv := fun z => mul_div_cancel_right₀ (show ℂ from z) hc
    right_inv := fun z => div_mul_cancel₀ z hc
    map_add' := fun z w => add_mul (show ℂ from z) (show ℂ from w) c
    map_smul' := fun t z => by change (t*(show ℂ from z))*c=t*((show ℂ from z)*c); ring }

@[simp] theorem hyperplaneEvaluationEquiv_apply (p : projectionSpace d 1)
    (v : projectionLine p) (hv : v≠0) (z : (projectionDualLineCore d).Fiber p) :
    hyperplaneEvaluationEquiv p v hv z = projectionDualLineFiberEquiv p z v := rfl

/-- In every chart the actual pairing is chart coefficient times the
coordinate of v in the unit local line frame. -/
theorem hyperplaneEvaluation_chart (p : projectionSpace d 1) (v : projectionLine p)
    (z : (projectionDualLineCore d).Fiber p) (i : Fin d) (hi : p ∈ projectionChartSet i) :
    projectionDualLineFiberEquiv p z v =
      ((projectionDualLineCore d).localTriv i ⟨p,z⟩).2 * inner ℂ (unitProjectionColumn p i) v.val := by
  let w := (projectionLineFiberEquiv p).symm v
  have h := projectionDualLine_pairing_chart p z w i hi
  have hw : ((projectionLineCore d).localTriv i ⟨p,w⟩).2 =
      inner ℂ (unitProjectionColumn p i) v.val := by
    have he := projectionLine_realization_chart p w i hi
    rw [LinearEquiv.apply_symm_apply] at he
    have hh := congrArg (inner ℂ (unitProjectionColumn p i)) he
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K,unitProjectionColumn_norm p i hi] at hh
    simpa using hh.symm
  rw [hw] at h
  exact h.symm

/-- Pairing is continuous for actual continuously varying dual fibers and
line vectors. The line-membership premise only identifies its genuine domain. -/
theorem continuous_hyperplaneEvaluation {X : Type*} [TopologicalSpace X]
    (p : X → projectionSpace d 1) (hp : Continuous p)
    (v : X → EuclideanSpace ℂ (Fin d)) (hvm : ∀ x, v x ∈ projectionLine (p x))
    (hv : Continuous v) (z : ∀ x, (projectionDualLineCore d).Fiber (p x))
    (hz : Continuous (fun x => TotalSpace.mk' ℂ (p x) (z x))) :
    Continuous (fun x => projectionDualLineFiberEquiv (p x) (z x) ⟨v x,hvm x⟩) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let i := (projectionLineCore d).indexAt (p x)
  have hi : p x ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at (p x)
  have hc := (FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := x)).mp hz.continuousAt |>.2
  have hu := ((continuousOn_unitProjectionColumn i (p x) hi).continuousAt
    ((isOpen_projectionChartSet i).mem_nhds hi)).comp hp.continuousAt
  apply (hc.mul (hu.inner hv.continuousAt)).congr_of_eventuallyEq
  filter_upwards [hp.continuousAt ((isOpen_projectionChartSet i).mem_nhds hi)] with y hy
  exact hyperplaneEvaluation_chart (p y) ⟨v y,hvm y⟩ (z y) i hy

end Kaplansky

end

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {X : Type*} [TopologicalSpace X] {d : ℕ}
variable (p : C(X,projectionSpace d 1)) (v : X → EuclideanSpace ℂ (Fin d))
variable (hvm : ∀ x, v x ∈ projectionLine (p x)) (hvn : ∀ x, v x≠0)

abbrev evaluationPullbackCore := pullbackLineCore (projectionDualLineCore d) p

def pullbackEvaluationEquiv (x : X) : (evaluationPullbackCore p).Fiber x ≃ₗ[ℂ] ℂ :=
  hyperplaneEvaluationEquiv (p x) ⟨v x,hvm x⟩ (fun h => hvn x (congrArg Subtype.val h))

include hvm hvn in
theorem evaluation_inner_ne_zero (x : X) (i : Fin d) (hi : p x ∈ projectionChartSet i) :
    inner ℂ (unitProjectionColumn (p x) i) (v x)≠0 := by
  intro h
  have he := unitProjectionColumn_reconstruct (p x) i hi (v x) (hvm x)
  rw [h,zero_smul] at he
  exact hvn x he.symm

theorem pullbackEvaluation_inverse_chart (x : X) (c : ℂ) (i : Fin d)
    (hi : p x ∈ projectionChartSet i) :
    ((evaluationPullbackCore p).localTriv i ⟨x,(pullbackEvaluationEquiv p v hvm hvn x).symm c⟩).2 =
      c / inner ℂ (unitProjectionColumn (p x) i) (v x) := by
  apply (eq_div_iff (evaluation_inner_ne_zero p v hvm hvn x i hi)).mpr
  change ((projectionDualLineCore d).localTriv i
    ⟨p x,(pullbackEvaluationEquiv p v hvm hvn x).symm c⟩).2 *
      inner ℂ (unitProjectionColumn (p x) i) (v x)=c
  exact (hyperplaneEvaluation_chart (p x) ⟨v x,hvm x⟩
    ((pullbackEvaluationEquiv p v hvm hvn x).symm c) i hi).symm.trans
      ((pullbackEvaluationEquiv p v hvm hvn x).apply_symm_apply c)

theorem continuous_evaluationPullback_toOriginal :
    Continuous (fun z : TotalSpace ℂ (evaluationPullbackCore p).Fiber =>
      TotalSpace.mk' ℂ (p z.proj) (show (projectionDualLineCore d).Fiber (p z.proj) from z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(p.continuous.comp (FiberBundle.continuous_proj _ _)).continuousAt,?_⟩
  exact ((FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := z)).mp
    (continuous_id (X := TotalSpace ℂ (evaluationPullbackCore p).Fiber)).continuousAt).2

variable (hv : Continuous v)

/-- Evaluation at a nonvanishing continuous line vector trivializes the
actual pullback hyperplane bundle, with its ordinary bundle topology. -/
def hyperplaneEvaluationHomeomorph : TotalSpace ℂ (evaluationPullbackCore p).Fiber ≃ₜ X × ℂ where
  toFun z := (z.proj,pullbackEvaluationEquiv p v hvm hvn z.proj z.2)
  invFun z := ⟨z.1,(pullbackEvaluationEquiv p v hvm hvn z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨x,c⟩ := z
    exact congrArg (TotalSpace.mk' ℂ x) ((pullbackEvaluationEquiv p v hvm hvn x).symm_apply_apply c)
  right_inv z := Prod.ext rfl ((pullbackEvaluationEquiv p v hvm hvn z.1).apply_symm_apply z.2)
  continuous_toFun := by
    have hp := FiberBundle.continuous_proj ℂ (evaluationPullbackCore p).Fiber
    exact hp.prodMk (continuous_hyperplaneEvaluation (fun z : TotalSpace ℂ (evaluationPullbackCore p).Fiber => p z.proj) (p.continuous.comp hp)
      (fun z => v z.proj) (fun z => hvm z.proj) (hv.comp hp)
      (fun z : TotalSpace ℂ (evaluationPullbackCore p).Fiber =>
        (show (projectionDualLineCore d).Fiber (p z.proj) from z.2))
      (continuous_evaluationPullback_toOriginal p))
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuous_fst.continuousAt,?_⟩
    let i := (projectionLineCore d).indexAt (p z.1)
    have hi : p z.1 ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at (p z.1)
    have hu : ContinuousAt (fun w : X × ℂ => unitProjectionColumn (p w.1) i) z := ((continuousOn_unitProjectionColumn i (p z.1) hi).continuousAt
      ((isOpen_projectionChartSet i).mem_nhds hi)).comp p.continuous.continuousAt |>.comp continuous_fst.continuousAt
    have hc : ContinuousAt (fun w : X × ℂ => w.2 / inner ℂ (unitProjectionColumn (p w.1) i) (v w.1)) z := continuous_snd.continuousAt.div (hu.inner (hv.comp continuous_fst).continuousAt)
      (evaluation_inner_ne_zero p v hvm hvn z.1 i hi)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(p.continuous.comp continuous_fst).continuousAt
      ((isOpen_projectionChartSet i).mem_nhds hi)] with w hw
    exact pullbackEvaluation_inverse_chart p v hvm hvn w.1 w.2 i hw

@[simp] theorem hyperplaneEvaluationHomeomorph_base
    (z : TotalSpace ℂ (evaluationPullbackCore p).Fiber) :
    (hyperplaneEvaluationHomeomorph p v hvm hvn hv z).1=z.proj := rfl

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def graphVerticalFunctional (F : GraphFrame 1 k) (j : Fin k) :
    EuclideanSpace ℂ (Fin (1+k)) →ₗ[ℂ] ℂ :=
  (LinearMap.proj j).comp ((LinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical k)).comp
    (F.toLinearMap.comp (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearEquiv.toLinearMap))

theorem graphVerticalFunctional_vector (F : GraphFrame 1 k) (A : GraphSlope 1 k) (j : Fin k) :
    graphVerticalFunctional F j (graphLineVector F A)=A (fun _ => 1) j := by
  change (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A))).2 j=_
  rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply]

def graphHyperplaneBase (F : GraphFrame 1 k) : C(GraphSlope 1 k,projectionSpace (1+k) 1) :=
  ⟨graphLineProjection F,continuous_graphLineProjection F⟩

theorem graphLineVector_mem (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphLineVector F A ∈ projectionLine (graphLineProjection F A) := by
  rw [graphLineProjection,nonzeroVectorProjection_line]
  exact Submodule.subset_span (Set.mem_singleton _)

/-- Genuine bundle coordinates obtained by evaluating a dual-line vector
on the nonvanishing graph representative. -/
def graphHyperplaneTrivialization (F : GraphFrame 1 k) :
    TotalSpace ℂ (evaluationPullbackCore (graphHyperplaneBase F)).Fiber ≃ₜ GraphSlope 1 k × ℂ :=
  hyperplaneEvaluationHomeomorph (graphHyperplaneBase F) (graphLineVector F)
    (graphLineVector_mem F) (graphLineVector_ne_zero F) (continuous_graphLineVector F)

/-- The actual K hyperplane sections, expressed in the genuine evaluation
trivialization over a projective graph chart. -/
def graphHyperplaneSectionCoordinates (F : GraphFrame 1 k) (A : GraphSlope 1 k) : GraphVertical k :=
  fun j => (graphHyperplaneTrivialization F
    ⟨A,hyperplaneFunctionalSection (graphVerticalFunctional F j) (graphLineProjection F A)⟩).2

theorem graphHyperplaneSectionCoordinates_eq (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphHyperplaneSectionCoordinates F A=A (fun _ => 1) := by
  funext j
  change projectionDualLineFiberEquiv (graphLineProjection F A)
    (hyperplaneFunctionalSection (graphVerticalFunctional F j) (graphLineProjection F A))
    ⟨graphLineVector F A,graphLineVector_mem F A⟩ = _
  rw [hyperplaneFunctionalSection_realization,graphVerticalFunctional_vector]

def slopeEvaluationOneEquiv (k : ℕ) : GraphSlope 1 k ≃L[ℂ] GraphVertical k :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun A => A (fun _ => 1)
    invFun := fun z => (ContinuousLinearMap.proj (0 : Fin 1)).smulRight z
    left_inv := by
      intro A
      apply ContinuousLinearMap.ext
      intro v
      have hv : v=v 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
        funext i
        have hi : i=0 := Subsingleton.elim _ _
        simp [hi]
      change v 0 • A (fun _ => 1)=A v
      rw [← map_smul,← hv]
    right_inv := by intro z; simp
    map_add' := by intro A B; rfl
    map_smul' := by intro c A; rfl }

/-- In these actual local bundle coordinates, the derivative at the sole
zero is a complex-linear isomorphism. This supplies regular-zero data;
its Euler/Chern interpretation remains a separate topological theorem. -/
theorem graphHyperplaneSectionCoordinates_hasFDerivAt (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    HasFDerivAt (graphHyperplaneSectionCoordinates F)
      (slopeEvaluationOneEquiv k).toContinuousLinearMap A := by
  have he : graphHyperplaneSectionCoordinates F=slopeEvaluationOneEquiv k :=
    funext (graphHyperplaneSectionCoordinates_eq F)
  rw [he]
  exact (slopeEvaluationOneEquiv k).toContinuousLinearMap.hasFDerivAt

theorem graphHyperplaneSectionCoordinates_zero_iff (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphHyperplaneSectionCoordinates F A=0 ↔ A=0 := by
  rw [graphHyperplaneSectionCoordinates_eq]
  exact (slopeEvaluationOneEquiv k).map_eq_zero_iff

end Kaplansky.ComplexGrassmann

namespace Kaplansky
variable {A S : Type} [TopologicalSpace A] [Fintype S] {d : S → ℕ}
  (p : ∀ s, C(A,projectionSpace (d s) 1))
  (v : ∀ s, A → EuclideanSpace ℂ (Fin (d s)))
  (hm : ∀ s a, v s a ∈ projectionLine (p s a))
  (hn : ∀ s a, v s a ≠ 0) (hc : ∀ s, Continuous (v s))

def finiteLineEvaluationEquiv (a : A) :
    (finiteLineSumCore (fun s => evaluationPullbackCore (p s))).Fiber a ≃ₗ[ℂ] (S → ℂ) :=
  (EuclideanSpace.equiv S ℂ).toLinearEquiv.trans
    (LinearEquiv.piCongrRight (fun s => pullbackEvaluationEquiv (p s) (v s) (hm s) (hn s) a))

/-- Simultaneous evaluation trivializes the actual finite sum of dual
lines, with the original finite-sum topology and linear fibers. -/
def finiteLineEvaluationHomeomorph :
    TotalSpace (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun s => evaluationPullbackCore (p s))).Fiber ≃ₜ A × (S → ℂ) where
  toFun z := (z.proj,finiteLineEvaluationEquiv p v hm hn z.proj z.2)
  invFun z := ⟨z.1,(finiteLineEvaluationEquiv p v hm hn z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨a,w⟩ := z
    exact congrArg (TotalSpace.mk' _ a) ((finiteLineEvaluationEquiv p v hm hn a).symm_apply_apply w)
  right_inv z := Prod.ext rfl ((finiteLineEvaluationEquiv p v hm hn z.1).apply_symm_apply z.2)
  continuous_toFun := by
    apply (FiberBundle.continuous_proj _ _).prodMk
    apply continuous_pi
    intro s
    exact continuous_snd.comp ((hyperplaneEvaluationHomeomorph (p s) (v s)
      (hm s) (hn s) (hc s)).continuous.comp
        (continuous_finiteLineSumComponent (fun s => evaluationPullbackCore (p s)) s))
  continuous_invFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨continuous_fst, fun s => ?_⟩
    exact (hyperplaneEvaluationHomeomorph (p s) (v s) (hm s) (hn s) (hc s)).symm.continuous.comp
      (continuous_fst.prodMk ((continuous_apply s).comp continuous_snd))

theorem finiteLineEvaluationHomeomorph_base (z : TotalSpace (EuclideanSpace ℂ S)
    (finiteLineSumCore (fun s => evaluationPullbackCore (p s))).Fiber) :
    (finiteLineEvaluationHomeomorph p v hm hn hc z).1 = z.proj := rfl

theorem finiteLineEvaluationHomeomorph_zero_iff (z : TotalSpace (EuclideanSpace ℂ S)
    (finiteLineSumCore (fun s => evaluationPullbackCore (p s))).Fiber) :
    (finiteLineEvaluationHomeomorph p v hm hn hc z).2 = 0 ↔ z.2 = 0 :=
  (finiteLineEvaluationEquiv p v hm hn z.proj).map_eq_zero_iff

end Kaplansky

end

open Bundle Topology
namespace Kaplansky.ComplexGrassmann

def standardLineGraphFrame (k : ℕ) : GraphFrame 1 k :=
  (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin (1+k) => ℂ) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin k) ℂ ℂ)

@[simp] theorem standardLineGraphFrame_vertical (k : ℕ) (v : Components 1 k) (i : Fin k) :
    (standardLineGraphFrame k v).2 i=v (positiveCoordinate k i) := by
  change v (Fin.natAdd 1 i)=v (positiveCoordinate k i)
  congr 1
  apply Fin.ext
  simp [positiveCoordinate,Nat.add_comm]

@[simp] theorem standardLineGraphFrame_horizontal (k : ℕ) (v : Components 1 k) (i : Fin 1) :
    (standardLineGraphFrame k v).1 i=v 0 := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

theorem standard_verticalFunctional (k : ℕ) (i : Fin k) :
    graphVerticalFunctional (standardLineGraphFrame k) i=coordinateFunctional (positiveCoordinate k i) := by
  apply LinearMap.ext
  intro v
  exact standardLineGraphFrame_vertical k _ i

theorem standard_graphVector_zero (k : ℕ) :
    graphLineVector (standardLineGraphFrame k) 0=firstCoordinateVector k := by
  apply (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective
  apply (standardLineGraphFrame k).injective
  rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    simp [firstCoordinateVector]
  · funext i
    have hi : positiveCoordinate k i≠0 := by
      intro h
      have := congrArg Fin.val h
      simp [positiveCoordinate] at this
    simp [firstCoordinateVector,hi]

/-- The graph-chart origin is exactly the unique zero previously identified
in the canonical coordinate sections of the actual hyperplane bundle. -/
theorem standard_graphProjection_zero (k : ℕ) :
    graphLineProjection (standardLineGraphFrame k) 0=firstCoordinateProjection k := by
  apply projectionLine_injective
  rw [graphLineProjection,nonzeroVectorProjection_line,standard_graphVector_zero,firstCoordinateProjection_line]

/-- The canonical sections used in the global zero-set theorem, expressed
in a genuine bundle trivialization, have an invertible complex derivative. -/
theorem canonical_hyperplaneSections_regular (k : ℕ) :
    HasFDerivAt (fun A : GraphSlope 1 k => fun i : Fin k =>
      (graphHyperplaneTrivialization (standardLineGraphFrame k)
        ⟨A,hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate k i))
          (graphLineProjection (standardLineGraphFrame k) A)⟩).2)
      (slopeEvaluationOneEquiv k).toContinuousLinearMap 0 ∧
      Function.Bijective (slopeEvaluationOneEquiv k) := by
  refine ⟨?_,(slopeEvaluationOneEquiv k).bijective⟩
  have he : (fun A : GraphSlope 1 k => fun i : Fin k =>
      (graphHyperplaneTrivialization (standardLineGraphFrame k)
        ⟨A,hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate k i))
          (graphLineProjection (standardLineGraphFrame k) A)⟩).2)=
      graphHyperplaneSectionCoordinates (standardLineGraphFrame k) := by
    funext A i
    rw [graphHyperplaneSectionCoordinates,standard_verticalFunctional]
  rw [he]
  exact graphHyperplaneSectionCoordinates_hasFDerivAt _ _

end Kaplansky.ComplexGrassmann

end

end OAI
