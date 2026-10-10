import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicGlobalization

namespace OAI

/-! Compact support and exact boundary jets of the actual finite ansatz. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

/-- A zero-coefficient collar gives equality with the baseline on a whole
neighborhood, not just at the selected point. -/
lemma finiteAnsatz_eventuallyEq_on_zero (F : A → E) (U : ℕ → Family O E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {Z : Set A} (hZ : IsOpen Z)
    (hzero : ∀ i p, p ∈ Z → (U i).val p = 0) {p : A} (hp : p ∈ Z) :
    finiteAnsatz F U ℓ L z =ᶠ[𝓝 p] F := by
  filter_upwards [hZ.mem_nhds hp] with q hq
  simp only [finiteAnsatz,Family.fastValue,hzero _ q hq,
    ContinuousMap.zero_apply,smul_zero,Finset.sum_const_zero,add_zero]

lemma finiteAnsatz_eventuallyEq_off_support (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hK : IsClosed K) (hzero : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {p : A} (hp : p ∉ K) :
    finiteAnsatz F U ℓ L z =ᶠ[𝓝 p] F :=
  finiteAnsatz_eventuallyEq_on_zero F U ℓ L z hK.isOpen_compl hzero hp

/-- All jets agree exactly away from the fixed closed coefficient support. -/
lemma finiteAnsatz_jets_eq_off_support (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hK : IsClosed K) (hzero : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L m : ℕ) (z : ℝ) {p : A} (hp : p ∉ K) :
    iteratedFDeriv ℝ m (finiteAnsatz F U ℓ L z) p = iteratedFDeriv ℝ m F p :=
  ((finiteAnsatz_eventuallyEq_off_support F U hK hzero ℓ L z hp).iteratedFDeriv ℝ m).eq_of_nhds

lemma finiteAnsatz_tsupport_sub (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hK : IsClosed K) (hzero : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    tsupport (fun p => finiteAnsatz F U ℓ L z p-F p) ⊆ K := by
  apply closure_minimal _ hK
  intro p hp
  by_contra hpK
  apply (Function.mem_support.mp hp)
  rw [finiteAnsatz_eq_off_support F U hzero ℓ L z hpK,sub_self]

/-- The same compact set supports each actual jet correction. -/
lemma finiteAnsatz_tsupport_jets_sub (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hK : IsClosed K) (hzero : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L m : ℕ) (z : ℝ) :
    tsupport (fun p => iteratedFDeriv ℝ m (finiteAnsatz F U ℓ L z) p-
      iteratedFDeriv ℝ m F p) ⊆ K := by
  apply closure_minimal _ hK
  intro p hp
  by_contra hpK
  apply (Function.mem_support.mp hp)
  rw [finiteAnsatz_jets_eq_off_support F U hK hzero ℓ L m z hpK,sub_self]

/-- Compact coefficient support gives one globally smooth perturbation with
compactly supported corrections in every derivative order. -/
theorem finiteAnsatz_compact_support {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E) {K : Set A} (hK : IsCompact K) (hKO : K ⊆ O)
    (hzero : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) ∧
      HasCompactSupport (fun p => finiteAnsatz F U ℓ L z p-F p) ∧
      tsupport (fun p => finiteAnsatz F U ℓ L z p-F p) ⊆ K ∧
      (∀ m, HasCompactSupport (fun p =>
        iteratedFDeriv ℝ m (finiteAnsatz F U ℓ L z) p-iteratedFDeriv ℝ m F p)) ∧
      ∀ p, p ∉ K → finiteAnsatz F U ℓ L z =ᶠ[𝓝 p] F := by
  have hs := finiteAnsatz_tsupport_sub F U hK.isClosed hzero ℓ L z
  refine ⟨finiteAnsatz_smooth_global hF U hK.isClosed hKO
    (fun i p _ hp => hzero i p hp) ℓ L z,
    hK.of_isClosed_subset (isClosed_tsupport _) hs,hs,?_,?_⟩
  · intro m
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (finiteAnsatz_tsupport_jets_sub F U hK.isClosed hzero ℓ L m z)
  · intro p hp
    exact finiteAnsatz_eventuallyEq_off_support F U hK.isClosed hzero ℓ L z hp

namespace Geometry
variable [FiniteDimensional ℝ A] [CompleteSpace E]
  {dy : A} (g : Geometry (E := E) O dy)

/-- The support conclusion of the proved coefficient recursion immediately
gives exact boundary germs wherever its initial primitive vanishes. -/
lemma finiteAnsatz_eventuallyEq_on_initial_zero (F : A → E) (U : ℕ → Family O E)
    (hcoeff : ∀ Z : Set A, IsOpen Z → Z ⊆ O →
      (∀ p ∈ Z, g.initial.val p = 0) → ∀ i p, p ∈ Z → (U i).val p = 0)
    {Z : Set A} (hZ : IsOpen Z) (hZO : Z ⊆ O)
    (hzero : ∀ p ∈ Z, g.initial.val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {p : A} (hp : p ∈ Z) :
    finiteAnsatz F U ℓ L z =ᶠ[𝓝 p] F :=
  finiteAnsatz_eventuallyEq_on_zero F U ℓ L z hZ (hcoeff Z hZ hZO hzero) hp

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
