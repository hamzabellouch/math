import Mathlib
import OAI.Analysis.SymmetricDomains.EtaleDerivationExtensionUnique

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Algebra KaehlerDifferential
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def meromorphicDirectionalDerivation (v : E) :
    Derivation ℂ (MeromorphicGermField E) (MeromorphicGermField E) := by
  let A := AnalyticGerm E
  let K := MeromorphicGermField E
  letI : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := K) (nonZeroDivisors A)
  exact etaleDerivationExtension ℂ A K
    ((Algebra.linearMap A K).compDer (analyticDirectionalDerivation E v))

@[simp] theorem meromorphicDirectionalDerivation_algebraMap (v : E) (a : AnalyticGerm E) :
    meromorphicDirectionalDerivation E v (algebraMap (AnalyticGerm E) (MeromorphicGermField E) a) =
      algebraMap (AnalyticGerm E) (MeromorphicGermField E)
        (analyticDirectionalDerivation E v a) := by
  exact etaleDerivationExtension_algebraMap ℂ _ _ _ a

@[simp] theorem analyticDirectionalDerivation_coordinate {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    analyticDirectionalDerivation (Fin n → ℂ) v (analyticCoordinate i) =
      algebraMap ℂ (AnalyticGerm (Fin n → ℂ)) (v i) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun x => by
    change fderiv ℂ (fun z : Fin n → ℂ => z i) x v = v i
    exact congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v)
      (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).hasFDerivAt.fderiv

noncomputable def meromorphicCoordinate {n : ℕ} (i : Fin n) :
    MeromorphicGermField (Fin n → ℂ) :=
  algebraMap (AnalyticGerm (Fin n → ℂ)) (MeromorphicGermField (Fin n → ℂ)) (analyticCoordinate i)

@[simp] theorem meromorphicDirectionalDerivation_coordinate {n : ℕ}
    (v : Fin n → ℂ) (i : Fin n) :
    meromorphicDirectionalDerivation (Fin n → ℂ) v (meromorphicCoordinate i) =
      algebraMap ℂ (MeromorphicGermField (Fin n → ℂ)) (v i) := by
  simp only [meromorphicCoordinate,meromorphicDirectionalDerivation_algebraMap,
    analyticDirectionalDerivation_coordinate,←IsScalarTower.algebraMap_apply]

theorem algebraicIndependent_meromorphicCoordinate {n : ℕ} :
    AlgebraicIndependent ℂ (meromorphicCoordinate (n := n)) := by
  exact (algebraicIndependent_analyticCoordinate (n := n)).map'
    (f := IsScalarTower.toAlgHom ℂ (AnalyticGerm (Fin n → ℂ))
      (MeromorphicGermField (Fin n → ℂ)))
    (IsFractionRing.injective _ _)

end

open Set Algebra KaehlerDifferential Module
open scoped IntermediateField.algebraAdjoinAdjoin

theorem differential_mem_span_of_isAlgebraic_adjoin
    {R F ι : Type*} [Field R] [CharZero R] [Field F] [Algebra R F]
    (x : ι → F) (hx : AlgebraicIndependent R x) (y : F)
    (hy : IsAlgebraic (IntermediateField.adjoin R (range x)) y) :
    D R F y ∈ Submodule.span F (range (fun i => D R F (x i))) := by
  let A := Algebra.adjoin R (range x)
  let L := IntermediateField.adjoin R (range x)
  let C := algebraicClosure L F
  have hA : IsTranscendenceBasis R (hx.aevalEquiv ∘ MvPolynomial.X) :=
    hx.aevalEquiv.isTranscendenceBasis (IsTranscendenceBasis.mvPolynomial ι R)
  have hL := IsTranscendenceBasis.algebraMap_comp (A := L) hA
  have : FaithfulSMul L C := (faithfulSMul_iff_algebraMap_injective L C).mpr
    (algebraMap L C).injective
  have : IsScalarTower R C F := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hC := IsTranscendenceBasis.algebraMap_comp (A := C) hL
  let yC : C := ⟨y,mem_algebraicClosure_iff.mpr hy⟩
  convert differential_mem_span_transcendenceBasis
    (K := F) _ hC yC using 1
  · congr 2
    funext i
    change D R F (x i) = D R F ((hx.aevalEquiv (MvPolynomial.X i) : A) : F)
    simp only [AlgebraicIndependent.aevalEquiv_apply_coe,MvPolynomial.aeval_X]
  · rfl

theorem partials_injective_on_differential_span
    {R F ι : Type*} [Field R] [Field F] [Algebra R F] [Fintype ι] [DecidableEq ι]
    (x : ι → F) (δ : ι → Derivation R F F)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    {z : Ω[F⁄R]} (hz : z ∈ Submodule.span F (range (fun i => D R F (x i))))
    (hzero : ∀ i, (δ i).liftKaehlerDifferential z = 0) : z = 0 := by
  obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hz
  have hc : ∀ i, c i = 0 := by
    intro i
    simpa only [map_sum,_root_.map_smul,Derivation.liftKaehlerDifferential_comp_D,
      hδ,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      using hzero i
  simp only [hc,zero_smul,Finset.sum_const_zero]

theorem algebraicIndependent_nash_partials
    {R F ι κ : Type*} [Field R] [CharZero R] [Field F] [Algebra R F]
    [Fintype ι] [DecidableEq ι]
    (x : ι → F) (hx : AlgebraicIndependent R x)
    (δ : ι → Derivation R F F)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    (q : κ → F) (hqalg : ∀ j, IsAlgebraic (IntermediateField.adjoin R (range x)) (q j))
    (hq : AlgebraicIndependent R q) :
    LinearIndependent F (fun j i => δ i (q j)) := by
  rw [linearIndependent_iff']
  intro s c hc j hj
  have hD : ∑ k ∈ s, c k • D R F (q k) = 0 := by
    apply partials_injective_on_differential_span x δ hδ
    · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (differential_mem_span_of_isAlgebraic_adjoin x hx _ (hqalg k))
    · intro i
      have hi := congrFun hc i
      simpa only [map_sum,_root_.map_smul,Derivation.liftKaehlerDifferential_comp_D,
        Finset.sum_apply,Pi.smul_apply,Pi.zero_apply] using hi
  exact (linearIndependent_iff'.mp (algebraicIndependent_differentials q hq)) s c hD j hj

end Release061

end

end OAI
