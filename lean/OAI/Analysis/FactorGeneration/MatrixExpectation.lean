import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

noncomputable section

namespace Generator

/-! Construct contractive expectations onto the actual finite matrix stages.
For every element of their weak closure, these expectations converge in L2
and remain in its operator norm ball. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem conditionalExpectation_best_approximation (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x y : M.toStarSubalgebra) (hy : y.val ∈ N) :
    τ.norm₂ (x-conditionalExpectation τ hNM x) ≤ τ.norm₂ (x-y) := by
  have he : conditionalExpectation τ hNM (x-y)=conditionalExpectation τ hNM x-y := by
    change conditionalExpectationCLM τ hNM (x-y)=_
    rw [map_sub]
    change conditionalExpectation τ hNM x-conditionalExpectation τ hNM y=_
    rw [conditionalExpectation_fixed τ hNM y hy]
  have h := conditionalExpectation_pythagoras τ hNM (x-y)
  rw [he,show x-y-(conditionalExpectation τ hNM x-y)=x-conditionalExpectation τ hNM x by abel] at h
  nlinarith [sq_nonneg (τ.norm₂ (conditionalExpectation τ hNM x-y)),
    show 0 ≤ τ.norm₂ (x-y) from norm_nonneg _]

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def stageVonNeumann (E : FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed E.units.concreteAlgebra E.units.concreteAlgebra_wotClosed

theorem stageVonNeumann_le (E : FiniteMatrixStage N) : E.stageVonNeumann ≤ N :=
  E.units.concreteAlgebra_le

def stageExpectation (E : FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  conditionalExpectation τ (E.stageVonNeumann_le.trans hNM) x

theorem stageExpectation_mem (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    (E.stageExpectation τ hNM x).val ∈ E.units.concreteAlgebra :=
  conditionalExpectation_mem τ (E.stageVonNeumann_le.trans hNM) x

theorem stageExpectation_norm_le (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) : ‖E.stageExpectation τ hNM x‖ ≤ ‖x‖ :=
  conditionalExpectation_norm_le τ (E.stageVonNeumann_le.trans hNM) x

theorem stageExpectation_norm₂_tendsto (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) :
    Tendsto (fun n => τ.norm₂ (x-(A n).stageExpectation τ hNM x)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n,y,hy,he⟩ := exists_stage_norm₂_approximation A hA τ hNM x hx ε hε
  refine ⟨n,?_⟩
  intro m hm
  have h := conditionalExpectation_best_approximation τ
    ((A m).stageVonNeumann_le.trans hNM) x y (hA hm hy)
  change τ.norm₂ (x-(A m).stageExpectation τ hNM x) ≤ τ.norm₂ (x-y) at h
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (show 0 ≤ τ.norm₂ _ from norm_nonneg _)]
    using h.trans_lt he

theorem exists_bounded_stage_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) :
    ∃ a : ℕ → M.toStarSubalgebra,
      (∀ n,(a n).val ∈ (A n).units.concreteAlgebra) ∧
      (∀ n,‖a n‖ ≤ ‖x‖) ∧ Tendsto (fun n => τ.norm₂ (x-a n)) atTop (𝓝 0) :=
  ⟨fun n => (A n).stageExpectation τ hNM x,fun n => (A n).stageExpectation_mem τ hNM x,
    fun n => (A n).stageExpectation_norm_le τ hNM x,stageExpectation_norm₂_tendsto A hA τ hNM x hx⟩

end FiniteMatrixStage

/-! Construct scalarizing partitions for an actual finite matrix algebra
inside a diffuse finite factor. No chain or pinching hypothesis is assumed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_scalar_pinching_for_matrixUnits
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    {n : ℕ} (hn : 0 < n) (E : MatrixUnitSystem (Fin n) M.toStarSubalgebra) :
    ∃ Q : CornerPartition (identityProjection M),
      ∀ x : M.toStarSubalgebra,x ∈ E.algebra → Q.pinch x=τ.trace x • (1 : M.toStarSubalgebra) := by
  let : NeZero n := ⟨hn.ne'⟩
  let e : ZMod n ≃ Fin n := Fintype.equivOfCardEq (by simp)
  let E' := E.reindex e
  obtain ⟨F,hc,_,_,_,_⟩ := exists_commuting_matrix_extension τ E' 0 hfactor hdiff n hn
  let F' := F.reindex e
  have hc' : ∀ i j k l,Commute (E'.entry i j) (F'.entry k l) :=
    fun i j k l => hc i j (e k) (e l)
  refine ⟨E'.bellPartition F' hc',fun x hx => ?_⟩
  apply E'.bellPartition_pinch_algebra F' hc' τ x
  rwa [MatrixUnitSystem.reindex_algebra]

end Tracial

/-! Finite matrix approximation and Bell partitions give actual small
pinching energy. The commuting matrix factor is constructed, not assumed. -/
open Filter
open scoped BigOperators Topology
namespace FiniteMatrixStage

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

theorem exists_matrix_approximated_centered_partition (τ : TracialRepresentation N)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    {ι : Type*} (F : Finset ι) (x : ι → N.toStarSubalgebra)
    (hx : ∀ i ∈ F,(x i).val ∈ generated A)
    (ht : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection N),
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  have hi (i : ι) (hi : i ∈ F) : Tendsto
      (fun n => τ.norm₂ (x i-(A n).stageExpectation τ le_rfl (x i))^2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      (stageExpectation_norm₂_tendsto A hA τ le_rfl (x i) (hx i hi)).pow 2
  have hlim : Tendsto
      (fun n => ∑ i ∈ F,τ.norm₂ (x i-(A n).stageExpectation τ le_rfl (x i))^2)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum F hi
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨Q,hQ⟩ := exists_scalar_pinching_for_matrixUnits τ hfactor hdiff
    (A n).positive (A n).units
  refine ⟨Q,lt_of_le_of_lt (Finset.sum_le_sum fun i hi => ?_) hn⟩
  have hm : (A n).stageExpectation τ le_rfl (x i) ∈ (A n).units.algebra :=
    ((A n).units.mem_concreteAlgebra _).mp ((A n).stageExpectation_mem τ le_rfl (x i))
  have hz : Q.pinch ((A n).stageExpectation τ le_rfl (x i))=0 := by
    rw [hQ _ hm]
    change τ.trace (conditionalExpectation τ _ (x i)) • (1 : N.toStarSubalgebra)=0
    rw [conditionalExpectation_trace,ht i hi,zero_smul]
  have he : Q.pinch (x i)=Q.pinch (x i-(A n).stageExpectation τ le_rfl (x i)) := by
    rw [Q.pinch_sub,hz,sub_zero]
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (Q.pinch_norm₂_le τ _) 2

/-- View the same finite matrix stage inside any algebra containing it. -/
def restrictStage (E : FiniteMatrixStage N) (R : VonNeumannAlgebra H)
    (hER : E.units.concreteAlgebra ≤ R.toStarSubalgebra) : FiniteMatrixStage R where
  size := E.size
  positive := E.positive
  units := {
    entry := fun i j => ⟨(E.units.entry i j).val,
      hER ((E.units.mem_concreteAlgebra _).mpr (E.units.entry_mem i j))⟩
    star_entry := fun i j => Subtype.ext (congrArg (fun x : N.toStarSubalgebra => x.val) (E.units.star_entry i j))
    mul_entry := fun i j k l => by
      apply Subtype.ext
      simpa only [MulMemClass.coe_mul,ZeroMemClass.coe_zero,Subtype.coe_mk,
        apply_ite Subtype.val] using congrArg (fun x : N.toStarSubalgebra => x.val) (E.units.mul_entry i j k l)
    total := by
      apply Subtype.ext
      have h := congrArg (fun x : N.toStarSubalgebra => x.val) E.units.total
      change R.toStarSubalgebra.subtype (∑ i,_) = 1
      rw [map_sum]
      change N.toStarSubalgebra.subtype (∑ i,E.units.entry i i)=1 at h
      rw [map_sum] at h
      exact h }

theorem restrictStage_concreteAlgebra (E : FiniteMatrixStage N) (R : VonNeumannAlgebra H)
    (hER : E.units.concreteAlgebra ≤ R.toStarSubalgebra) :
    (E.restrictStage R hER).units.concreteAlgebra=E.units.concreteAlgebra := by
  have hh (a : Matrix (Fin E.size) (Fin E.size) ℂ) :
      (E.restrictStage R hER).units.concreteHom a = E.units.concreteHom a := by
    change R.toStarSubalgebra.subtype ((E.restrictStage R hER).units.hom a) =
      N.toStarSubalgebra.subtype (E.units.hom a)
    change R.toStarSubalgebra.subtype
        (∑ i, ∑ j, a i j • (E.restrictStage R hER).units.entry i j) =
      N.toStarSubalgebra.subtype (∑ i, ∑ j, a i j • E.units.entry i j)
    simp only [map_sum,map_smul]
    rfl
  change (E.restrictStage R hER).units.concreteHom.range=E.units.concreteHom.range
  congr 1
  exact DFunLike.ext _ _ hh

theorem exists_matrix_generated_centered_partition (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation (generatedVonNeumann A))
    (hfactor : IsII1Factor (generated A))
    {ι : Type*} (F : Finset ι) (x : ι → (generatedVonNeumann A).toStarSubalgebra)
    (ht : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection (generatedVonNeumann A)),
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  let B (n : ℕ) := (A n).restrictStage (generatedVonNeumann A) (stage_le_generated A n)
  have hB (n : ℕ) : (B n).units.concreteAlgebra=(A n).units.concreteAlgebra :=
    (A n).restrictStage_concreteAlgebra _ _
  have hmono : Monotone (fun n => (B n).units.concreteAlgebra) := by
    simpa only [hB] using hA
  have hgen : generated B=generated A := by simp only [generated,hB]
  apply exists_matrix_approximated_centered_partition τ
    (fun c hc => by
      obtain ⟨z,hz⟩ := hfactor.factor c hc
      refine ⟨z,?_⟩
      apply Subtype.ext
      exact congrArg (fun x : generated A => (x : H →L[ℂ] H)) hz)
    hfactor.diffuse B hmono F x (fun i _ => ?_) ht ε hε
  rw [hgen]
  exact (x i).property

end

/-! Countably many finite matrix algebras give L2 separability of their weak closure. -/
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem stage_vector_range_separable (E : FiniteMatrixStage N) (ξ : H) :
    TopologicalSpace.IsSeparable (Set.range (fun a : E.units.concreteAlgebra => a.val ξ)) := by
  let : FiniteDimensional ℂ E.units.concreteAlgebra := E.units.concrete_finiteDimensional
  exact TopologicalSpace.isSeparable_range (by fun_prop)

theorem generated_vector_range_separable (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (ξ : H) :
    TopologicalSpace.IsSeparable (Set.range (fun a : generated A => a.val ξ)) := by
  classical
  let S : ℕ → Set H := fun n => Set.range (fun a : (A n).units.concreteAlgebra => a.val ξ)
  have hs : TopologicalSpace.IsSeparable (⋃ n,S n) :=
    TopologicalSpace.IsSeparable.iUnion (fun n => stage_vector_range_separable (A n) ξ)
  apply hs.closure.mono
  rintro _ ⟨x,rfl⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n,a,ha⟩ := exists_stage_strong_approximation A hA x {ξ} ε hε
  exact ⟨a.val ξ,Set.mem_iUnion.mpr ⟨n,⟨a,rfl⟩⟩,
    by simpa only [dist_eq_norm] using ha ξ (Finset.mem_singleton_self ξ)⟩

theorem generated_norm₂_separable (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) :
    TopologicalSpace.IsSeparable (Set.range (baseVector (generatedTrace A τ hNM))) :=
  generated_vector_range_separable A hA τ.vector

end FiniteMatrixStage

/-! The actual finite-stage conditional expectations converge strongly and
adjoint-strongly on every vector in the given representation. The generated
algebra also has a constructed separable faithful cyclic Hilbert representation. -/
open Filter
open scoped Topology
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem stageExpectation_strong_tendsto (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) (y : H) :
    Tendsto (fun n => ((A n).stageExpectation τ hNM x).val y) atTop (𝓝 (x.val y)) := by
  apply norm₂_limit_strong τ _ x ‖x‖
    (fun n => (A n).stageExpectation_norm_le τ hNM x) _ y
  simpa only [TracialRepresentation.norm₂_sub,norm_sub_rev] using
    stageExpectation_norm₂_tendsto A hA τ hNM x hx

theorem stageExpectation_strong_star_tendsto (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) (y : H) :
    Tendsto (fun n => (star ((A n).stageExpectation τ hNM x)).val y) atTop (𝓝 ((star x).val y)) := by
  apply norm₂_limit_strong_star τ _ x ‖x‖
    (fun n => (A n).stageExpectation_norm_le τ hNM x) _ y
  simpa only [TracialRepresentation.norm₂_sub,norm_sub_rev] using
    stageExpectation_norm₂_tendsto A hA τ hNM x hx

theorem exists_bounded_strong_stage_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) :
    ∃ a : ℕ → M.toStarSubalgebra,
      (∀ n,(a n).val ∈ (A n).units.concreteAlgebra) ∧ (∀ n,‖a n‖ ≤ ‖x‖) ∧
      (∀ y : H,Tendsto (fun n => (a n).val y) atTop (𝓝 (x.val y))) ∧
      (∀ y : H,Tendsto (fun n => (star (a n)).val y) atTop (𝓝 ((star x).val y))) :=
  ⟨fun n => (A n).stageExpectation τ hNM x,fun n => (A n).stageExpectation_mem τ hNM x,
    fun n => (A n).stageExpectation_norm_le τ hNM x,
    stageExpectation_strong_tendsto A hA τ hNM x hx,
    stageExpectation_strong_star_tendsto A hA τ hNM x hx⟩

theorem generated_cyclicSpace_separable (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) :
    TopologicalSpace.SeparableSpace (traceCyclicSpace (generatedTrace A τ hNM)) :=
  traceCyclicSpace_separable _ (generated_norm₂_separable A hA τ hNM)

end FiniteMatrixStage

end Generator

end

end OAI
