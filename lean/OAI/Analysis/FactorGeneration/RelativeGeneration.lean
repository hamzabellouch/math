import OAI.Analysis.FactorGeneration.HilbertProjections
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

inductive RelativePolynomial (A : Type*) where
  | coeff : A → RelativePolynomial A
  | indeterminate : RelativePolynomial A
  | add : RelativePolynomial A → RelativePolynomial A → RelativePolynomial A
  | mul : RelativePolynomial A → RelativePolynomial A → RelativePolynomial A
  | smul : ℂ → RelativePolynomial A → RelativePolynomial A
  | adjoint : RelativePolynomial A → RelativePolynomial A

namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
namespace RelativePolynomial

def eval : Generator.RelativePolynomial N.toStarSubalgebra → TraceUnitary τ → M.toStarSubalgebra
  | .coeff a, _ => coordinateInclusion hNM a
  | .indeterminate, u => u.algebra τ
  | .add p q, u => eval p u+eval q u
  | .mul p q, u => eval p u*eval q u
  | .smul z p, u => z • eval p u
  | .adjoint p, u => star (eval p u)

theorem norm_bound (p : Generator.RelativePolynomial N.toStarSubalgebra) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TraceUnitary τ, ‖eval τ hNM p u‖ ≤ C := by
  induction p with
  | coeff a => exact ⟨‖a‖,norm_nonneg _,fun _ => le_rfl⟩
  | indeterminate => exact ⟨1,zero_le_one,TraceUnitary.algebra_norm_le τ⟩
  | add p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C+D,add_nonneg hC hD,fun u => (norm_add_le _ _).trans (add_le_add (hp u) (hq u))⟩
  | mul p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C*D,mul_nonneg hC hD,fun u => (norm_mul_le _ _).trans
      (mul_le_mul (hp u) (hq u) (norm_nonneg _) hC)⟩
  | smul z p hp =>
    obtain ⟨C,hC,hp⟩ := hp
    refine ⟨‖z‖*C,mul_nonneg (norm_nonneg _) hC,fun u => ?_⟩
    simpa only [eval,norm_smul] using mul_le_mul_of_nonneg_left (hp u) (norm_nonneg z)
  | adjoint p hp =>
    obtain ⟨C,hC,hp⟩ := hp
    refine ⟨C,hC,fun u => ?_⟩
    change ‖star (eval τ hNM p u).val‖ ≤ C
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint.norm_map]
    exact hp u

def sectionVector (p : Generator.RelativePolynomial N.toStarSubalgebra) (u : TraceUnitary τ) : H :=
  (eval τ hNM p u).val τ.vector

theorem continuous_sectionVector (p : Generator.RelativePolynomial N.toStarSubalgebra) :
    Continuous (sectionVector τ hNM p) := by
  induction p with
  | coeff a =>
    change Continuous (fun _ : TraceUnitary τ => (coordinateInclusion hNM a).val τ.vector)
    exact continuous_const
  | indeterminate => exact (TraceUnitary.vector_isometry τ).continuous
  | add p q hp hq => exact hp.add hq
  | smul z p hp => exact continuous_const.smul hp
  | adjoint p hp =>
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mpr
    exact norm₂_limit_star τ _ _ ((tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mp hp.continuousAt)
  | mul p q hp hq =>
    obtain ⟨C,_,hC⟩ := norm_bound τ hNM p
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mpr
    exact norm₂_limit_mul τ _ _ _ _ C hC
      ((tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mp hp.continuousAt)
      ((tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mp hq.continuousAt)

end RelativePolynomial
end Tracial

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeGenerators (u : TraceUnitary τ) : Set (H →L[ℂ] H) :=
  (N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}

def relativeGenerated (u : TraceUnitary τ) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (wstar (relativeGenerators (N := N) τ u)) (wstar_closed _)

include hNM in
theorem relativeGenerated_le (u : TraceUnitary τ) : relativeGenerated (N := N) τ u ≤ M := by
  apply wstar_le (vonNeumann_wotClosed M)
  intro a ha
  rcases ha with ha | ha
  · exact hNM ha
  · rcases Set.mem_singleton_iff.mp ha with rfl
    exact (u.algebra τ).property

theorem le_relativeGenerated (u : TraceUnitary τ) : N ≤ relativeGenerated (N := N) τ u :=
  fun _ ha => subset_wstar _ (Or.inl ha)

theorem unitary_mem_relativeGenerated (u : TraceUnitary τ) :
    (u.algebra τ).val ∈ relativeGenerated (N := N) τ u :=
  subset_wstar _ (Or.inr rfl)

namespace RelativePolynomial

def valueAlgebra (u : TraceUnitary τ) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarAlgebra.adjoin ℂ (relativeGenerators (N := N) τ u)

theorem eval_mem (p : Generator.RelativePolynomial N.toStarSubalgebra) (u : TraceUnitary τ) :
    (eval τ hNM p u).val ∈ valueAlgebra (N := N) τ u := by
  induction p with
  | coeff a => exact StarAlgebra.subset_adjoin ℂ _ (Or.inl a.property)
  | indeterminate => exact StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)
  | add p q hp hq => exact (valueAlgebra (N := N) τ u).add_mem hp hq
  | mul p q hp hq => exact (valueAlgebra (N := N) τ u).mul_mem hp hq
  | smul z p hp => exact (valueAlgebra (N := N) τ u).smul_mem hp z
  | adjoint p hp => exact (valueAlgebra (N := N) τ u).star_mem' hp

theorem exists_eval (u : TraceUnitary τ) (a : valueAlgebra (N := N) τ u) :
    ∃ p : Generator.RelativePolynomial N.toStarSubalgebra, (eval τ hNM p u).val=a.val := by
  rcases a with ⟨a,ha⟩
  induction ha using StarAlgebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact ⟨.coeff ⟨a,ha⟩,rfl⟩
    · rcases Set.mem_singleton_iff.mp ha with rfl
      exact ⟨.indeterminate,rfl⟩
  | algebraMap z => exact ⟨.smul z (.coeff 1),by simp [eval,Algebra.algebraMap_eq_smul_one]⟩
  | add a b _ _ ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    exact ⟨.add p q,by change (eval τ hNM p u).val+(eval τ hNM q u).val=a+b; rw [hp,hq]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    exact ⟨.mul p q,by change (eval τ hNM p u).val*(eval τ hNM q u).val=a*b; rw [hp,hq]⟩
  | star a _ ha =>
    obtain ⟨p,hp⟩ := ha
    exact ⟨.adjoint p,by change star (eval τ hNM p u).val=star a; rw [hp]⟩

theorem valueAlgebra_le (u : TraceUnitary τ) :
    valueAlgebra (N := N) τ u ≤ (relativeGenerated (N := N) τ u).toStarSubalgebra :=
  StarAlgebra.adjoin_le (subset_wstar _)

theorem generated_eq_wstar_values (u : TraceUnitary τ) :
    (relativeGenerated (N := N) τ u).toStarSubalgebra =
      wstar (valueAlgebra (N := N) τ u : Set (H →L[ℂ] H)) := by
  apply le_antisymm
  · exact wstar_mono (StarAlgebra.subset_adjoin ℂ _)
  · exact wstar_le (wstar_closed _) (valueAlgebra_le τ u)

theorem exists_vector_approximation (u : TraceUnitary τ)
    (a : (relativeGenerated (N := N) τ u).toStarSubalgebra) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Generator.RelativePolynomial N.toStarSubalgebra,
      ‖a.val τ.vector-sectionVector τ hNM p u‖ < ε := by
  classical
  have ha : a.val ∈ Set.centralizer (Set.centralizer
      (valueAlgebra (N := N) τ u : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    change a.val ∈ (bicommutantVonNeumann (valueAlgebra (N := N) τ u)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,← generated_eq_wstar_values]
    exact a.property
  obtain ⟨b,hb⟩ := bicommutant_finite_strong_approximation _ a.val ha {τ.vector} ε hε
  obtain ⟨p,hp⟩ := exists_eval τ hNM u b
  exact ⟨p,by simpa only [sectionVector,hp] using hb τ.vector (Finset.mem_singleton_self _)⟩

end RelativePolynomial

def relativeTraceSpace (u : TraceUnitary τ) : Submodule ℂ H :=
  vectorOrbitClosure (relativeGenerated (N := N) τ u).toStarSubalgebra τ.vector

instance relativeTraceSpace_complete (u : TraceUnitary τ) :
    CompleteSpace (relativeTraceSpace (N := N) τ u) :=
  inferInstanceAs (CompleteSpace (vectorOrbitClosure _ _))

theorem polynomialVector_mem (p : Generator.RelativePolynomial N.toStarSubalgebra)
    (u : TraceUnitary τ) : RelativePolynomial.sectionVector τ hNM p u ∈
      relativeTraceSpace (N := N) τ u :=
  Submodule.le_topologicalClosure _ ⟨⟨(RelativePolynomial.eval τ hNM p u).val,
    RelativePolynomial.valueAlgebra_le τ u (RelativePolynomial.eval_mem τ hNM p u)⟩,rfl⟩

theorem polynomialVector_dense (u : TraceUnitary τ) :
    DenseRange (fun p : Generator.RelativePolynomial N.toStarSubalgebra =>
      (⟨RelativePolynomial.sectionVector τ hNM p u,polynomialVector_mem τ hNM p u⟩ :
        relativeTraceSpace (N := N) τ u)) := by
  intro ξ
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hξ : ξ.val ∈ closure (Set.range (fun a : (relativeGenerated (N := N) τ u).toStarSubalgebra =>
      a.val τ.vector)) := ξ.property
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp hξ (ε/2) (half_pos hε)
  obtain ⟨p,hp⟩ := RelativePolynomial.exists_vector_approximation τ hNM u a (ε/2) (half_pos hε)
  refine ⟨_,⟨p,rfl⟩,?_⟩
  change dist ξ.val (RelativePolynomial.sectionVector τ hNM p u) < ε
  have hdist := dist_triangle ξ.val (a.val τ.vector) (RelativePolynomial.sectionVector τ hNM p u)
  rw [dist_eq_norm (a.val τ.vector)] at hdist
  linarith

end Tracial

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeUnitaryWord (u : TraceUnitary τ) (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    M.toStarSubalgebra :=
  coordinateInclusion hNM (t 0 : N.toStarSubalgebra)*
    ((List.range ell).map (fun j => u.algebra τ*
      coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod

theorem relativeUnitaryWord_mem_unitary (u : TraceUnitary τ)
    (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    relativeUnitaryWord τ hNM u t ell ∈ unitary M.toStarSubalgebra := by
  apply (unitary M.toStarSubalgebra).mul_mem
  · exact Unitary.map_mem (coordinateInclusion hNM) (t 0).property
  · apply (unitary M.toStarSubalgebra).list_prod_mem
    intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact (unitary M.toStarSubalgebra).mul_mem u.toUnitary.property
      (Unitary.map_mem (coordinateInclusion hNM) (t (j+1)).property)

theorem relativeUnitaryWord_mem_generated (u : TraceUnitary τ)
    (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    (relativeUnitaryWord τ hNM u t ell).val ∈ relativeGenerated (N := N) τ u := by
  let S := (relativeGenerated (N := N) τ u).toStarSubalgebra
  have hn (j : ℕ) : (coordinateInclusion hNM (t j : N.toStarSubalgebra)).val ∈ S :=
    le_relativeGenerated τ u (t j).val.property
  apply S.mul_mem (hn 0)
  change ((List.range ell).map (fun j => u.algebra τ*
    coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod ∈
      insideAlgebra (M := M) (P := relativeGenerated (N := N) τ u)
  apply (insideAlgebra (M := M) (P := relativeGenerated (N := N) τ u)).list_prod_mem
  intro a ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
  exact S.mul_mem (unitary_mem_relativeGenerated τ u) (hn (j+1))

theorem norm₂_unitary (u : unitary M.toStarSubalgebra) :
    τ.norm₂ (u : M.toStarSubalgebra)=1 := by
  have h := norm₂_sq_trace τ (u : M.toStarSubalgebra)
  rw [u.property.1,τ.trace_one,Complex.one_re] at h
  nlinarith [show 0 ≤ τ.norm₂ (u : M.toStarSubalgebra) from norm_nonneg _]

theorem relativeUnitaryWord_correlation_le (u : TraceUnitary τ)
    (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) (xi : M.toStarSubalgebra) :
    ‖τ.trace (star xi*relativeUnitaryWord τ hNM u t ell)‖ ≤
      projectionNorm (relativeTraceSpace (N := N) τ u) (baseVector τ xi) := by
  rw [← baseVector_inner_trace]
  apply correlation_le_projectionNorm
  · exact Submodule.le_topologicalClosure _ ⟨⟨(relativeUnitaryWord τ hNM u t ell).val,
      relativeUnitaryWord_mem_generated τ hNM u t ell⟩,rfl⟩
  · exact norm₂_unitary τ ⟨_,relativeUnitaryWord_mem_unitary τ hNM u t ell⟩

theorem perturbation_size_tendsto (α : ℝ) :
    Tendsto (fun n : ℕ => α/Real.sqrt (2*((n+1 : ℕ) : ℝ))+1/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ => 2*((n+1 : ℕ) : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hs := (Real.tendsto_sqrt_atTop.comp ht).const_div_atTop α
  have hi := hn.const_div_atTop (1 : ℝ)
  simpa only [add_zero,Function.comp_def] using hs.add hi

end Tracial

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

include hNM in
theorem relative_projection_lowerSemicontinuous (ξ : H) :
    LowerSemicontinuous (fun u : TraceUnitary τ =>
      projectionNorm (relativeTraceSpace (N := N) τ u) ξ) :=
  projectionNorm_lowerSemicontinuous (relativeTraceSpace (N := N) τ)
    (RelativePolynomial.sectionVector τ hNM) (polynomialVector_mem τ hNM)
    (RelativePolynomial.continuous_sectionVector τ hNM) (polynomialVector_dense τ hNM) ξ

include hNM in
theorem common_relative_projection_continuity
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, ∀ ξ : traceCyclicSpace τ,
        ContinuousAt (fun v => projectionNorm (relativeTraceSpace (N := N) τ v) ξ.val) u := by
  let := traceCyclicSpace_separable τ hsep
  exact common_continuity_of_lipschitz
    (fun (ξ : traceCyclicSpace τ) u => projectionNorm (relativeTraceSpace (N := N) τ u) ξ.val)
    (fun ξ => relative_projection_lowerSemicontinuous τ hNM ξ.val)
    (fun u ξ η => projectionNorm_lipschitz (relativeTraceSpace (N := N) τ u) ξ.val η.val)

include hNM in
theorem common_relative_projection_continuity_algebra
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, ∀ x : M.toStarSubalgebra,
        ContinuousAt (fun v => projectionNorm (relativeTraceSpace (N := N) τ v) (baseVector τ x)) u := by
  obtain ⟨C,hC,hd,hcont⟩ := common_relative_projection_continuity τ hNM hsep
  exact ⟨C,hC,hd,fun u hu x => hcont u hu
    ⟨baseVector τ x,Submodule.le_topologicalClosure _ ⟨x,rfl⟩⟩⟩

/-! The bounded conditional expectation agrees with the actual Hilbert
projection. Proper subalgebras have a unitary outside them, yielding the
nonzero represented residual used by thm:relative-generation. -/

theorem conditionalExpectation_vector_projection (x : M.toStarSubalgebra) :
    (vectorOrbitClosure N.toStarSubalgebra τ.vector).starProjection (baseVector τ x) =
      baseVector τ (conditionalExpectation τ hNM x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.le_topologicalClosure _
      ⟨⟨(conditionalExpectation τ hNM x).val,conditionalExpectation_mem τ hNM x⟩,rfl⟩
  · intro w hw
    rw [← map_sub]
    apply inner_eq_zero_symm.mp
    have hc : IsClosed {y : H | inner ℂ y (baseVector τ (x-conditionalExpectation τ hNM x))=0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    apply closure_minimal (t := {y : H | inner ℂ y (baseVector τ (x-conditionalExpectation τ hNM x))=0})
      ?_ hc hw
    rintro _ ⟨a,rfl⟩
    change inner ℂ (baseVector τ (coordinateInclusion hNM a))
      (baseVector τ (x-conditionalExpectation τ hNM x))=0
    rw [baseVector_inner_trace]
    exact conditionalExpectation_orthogonal τ hNM x
      ⟨star (coordinateInclusion hNM a),N.toStarSubalgebra.star_mem' a.property⟩

include hNM in
theorem exists_unitary_outside (hne : N ≠ M) :
    ∃ z : unitary M.toStarSubalgebra, (z : M.toStarSubalgebra).val ∉ N := by
  classical
  by_contra h
  have hu : ∀ z : unitary M.toStarSubalgebra, (z : M.toStarSubalgebra).val ∈ N := by
    simpa only [not_exists,not_not] using h
  let : CStarAlgebra M.toStarSubalgebra := {}
  let S := (insideAlgebra (M := M) (P := N)).toSubalgebra.toSubmodule
  have hs : (⊤ : Submodule ℂ M.toStarSubalgebra) ≤ S := by
    rw [← CStarAlgebra.span_unitary M.toStarSubalgebra]
    exact Submodule.span_le.mpr (fun z hz => hu ⟨z,hz⟩)
  apply hne
  apply le_antisymm hNM
  intro a ha
  exact hs (show (⟨a,ha⟩ : M.toStarSubalgebra) ∈ (⊤ : Submodule ℂ M.toStarSubalgebra) from trivial)

def subalgebraResidual (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  x-conditionalExpectation τ hNM x

theorem subalgebraResidual_vector (x : M.toStarSubalgebra) :
    baseVector τ (subalgebraResidual τ hNM x) =
      residual (vectorOrbitClosure N.toStarSubalgebra τ.vector) (baseVector τ x) := by
  rw [residual,conditionalExpectation_vector_projection τ hNM]
  exact map_sub (baseVector τ) _ _

theorem subalgebraResidual_projection (x : M.toStarSubalgebra) :
    (vectorOrbitClosure N.toStarSubalgebra τ.vector).starProjection
      (baseVector τ (subalgebraResidual τ hNM x))=0 := by
  rw [subalgebraResidual_vector]
  exact residual_projection_zero _ _

theorem subalgebraResidual_correlation (x : M.toStarSubalgebra) :
    τ.trace (star (subalgebraResidual τ hNM x)*x)=
      (τ.norm₂ (subalgebraResidual τ hNM x) : ℂ)^2 := by
  rw [← baseVector_inner_trace]
  change inner ℂ (baseVector τ (subalgebraResidual τ hNM x)) (baseVector τ x)=
    (‖baseVector τ (subalgebraResidual τ hNM x)‖ : ℂ)^2
  rw [subalgebraResidual_vector]
  exact residual_correlation _ _

theorem subalgebraResidual_norm_pos (x : M.toStarSubalgebra) (hx : x.val ∉ N) :
    0 < τ.norm₂ (subalgebraResidual τ hNM x) := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro h
  have hz := (τ.norm₂_eq_zero_iff _).mp h.symm
  have he : x=conditionalExpectation τ hNM x := sub_eq_zero.mp hz
  exact hx (he ▸ conditionalExpectation_mem τ hNM x)

end Tracial

end Generator

end

end OAI
