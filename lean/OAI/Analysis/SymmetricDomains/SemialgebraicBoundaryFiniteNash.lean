import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicFiniteAnalyticNash

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open SignElimination
open scoped Classical

noncomputable def realCoordinatesEquiv (n : ℕ) : Affine n ≃L[ℝ] (Fin n ⊕ Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := realCoordinates
    invFun := fun x j => ⟨x (.inl j),x (.inr j)⟩
    left_inv := by intro z; ext j; rfl
    right_inv := by intro x; funext j; cases j <;> rfl
    map_add' := by intro x y; funext j; cases j <;> rfl
    map_smul' := by intro r x; funext j; cases j <;> simp [realCoordinates] }

noncomputable def complexRealEquiv (n : ℕ) : Affine n ≃L[ℝ] (Fin (n+n) → ℝ) :=
  (realCoordinatesEquiv n).trans
    (LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv.symm).toContinuousLinearEquiv

lemma complexRealEquiv_apply {n : ℕ} (z : Affine n) (j : Fin (n+n)) :
    complexRealEquiv n z j = realCoordinates z (finSumFinEquiv.symm j) := rfl

lemma complexRealEquiv_symm_re {n : ℕ} (x : Fin (n+n) → ℝ) (j : Fin n) :
    ((complexRealEquiv n).symm x j).re = x (finSumFinEquiv (.inl j)) := rfl

lemma complexRealEquiv_symm_im {n : ℕ} (x : Fin (n+n) → ℝ) (j : Fin n) :
    ((complexRealEquiv n).symm x j).im = x (finSumFinEquiv (.inr j)) := rfl

lemma isSemialgebraic_real_image {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    PolynomialSignSet id (complexRealEquiv n '' S) := by
  have hh := (isSemialgebraic_iff_polynomialSignSet.mp hS).coordinate_preimage
    (complexRealEquiv n).symm finSumFinEquiv
    (d := id) (by intro x j; cases j <;> rfl)
  convert hh using 1
  ext x
  simp only [mem_image,mem_preimage]
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa using hz
  · intro hx
    exact ⟨_,hx,(complexRealEquiv n).apply_symm_apply x⟩

lemma isSemialgebraic_of_real_image {n : ℕ} {S : Set (Affine n)}
    (hS : PolynomialSignSet id (complexRealEquiv n '' S)) : IsSemialgebraic S := by
  apply isSemialgebraic_iff_polynomialSignSet.mpr
  have hh := hS.coordinate_preimage (complexRealEquiv n) finSumFinEquiv.symm
    (d := realCoordinates) (by intros; rfl)
  simpa only [Set.preimage_image_eq _ (complexRealEquiv n).injective] using hh

lemma IsSemialgebraic.closure {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (closure S) := by
  apply isSemialgebraic_of_real_image
  change PolynomialSignSet id ((complexRealEquiv n).toHomeomorph '' _root_.closure S)
  rw [(complexRealEquiv n).toHomeomorph.image_closure]
  exact (isSemialgebraic_real_image hS).closure

lemma IsSemialgebraic.inter {n : ℕ} {S T : Set (Affine n)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∩ T) := by
  exact isSemialgebraic_iff_polynomialSignSet.mpr
    ((isSemialgebraic_iff_polynomialSignSet.mp hS).inter
      (isSemialgebraic_iff_polynomialSignSet.mp hT))

lemma IsSemialgebraic.diff {n : ℕ} {S T : Set (Affine n)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S \ T) :=
  hS.inter hT.compl

lemma IsSemialgebraic.interior {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (interior S) := by
  rw [interior_eq_compl_closure_compl]
  exact hS.compl.closure.compl

lemma IsSemialgebraic.frontier {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (frontier S) := hS.closure.diff hS.interior

namespace SemialgebraicOn
lemma coordinate_graph {ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}
    (hf : SemialgebraicOn B f) (j : κ) :
    PolynomialSignSet (id : (Option ι → ℝ) → (Option ι → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i)) j} := by
  have hh := (hf.reindex (fun _ : Fin 1 => j)).coordinate_preimage
    (fun x : Option ι → ℝ => ((fun i => x (some i)),fun _ : Fin 1 => x none))
    (Sum.elim some (fun _ => none)) (d := id) (by intro x i; cases i <;> rfl)
  convert hh using 1
  ext x
  simp only [mem_ofPred_eq,mem_preimage]
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨hx,funext (fun _ => he)⟩
  · rintro ⟨hx,he⟩
    exact ⟨hx,congrFun he 0⟩
end SemialgebraicOn

namespace NashPatch
variable {n : ℕ}

noncomputable def complexMap (p : NashPatch (n+n)) : (Fin p.dim → ℝ) → Affine n :=
  (complexRealEquiv n).symm ∘ p.toFun

lemma analytic_complexMap (p : NashPatch (n+n)) : AnalyticOnNhd ℝ p.complexMap p.domain := by
  intro x hx
  exact ((complexRealEquiv n).symm.analyticAt _).comp (p.analytic_toFun x hx)

lemma injective_fderiv_complexMap (p : NashPatch (n+n)) {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) :
    Function.Injective (fderiv ℝ p.complexMap x) := by
  have he := ((complexRealEquiv n).symm.hasFDerivAt.comp x
    (p.analytic_toFun x hx).differentiableAt.hasFDerivAt).fderiv
  change Function.Injective (fderiv ℝ ((complexRealEquiv n).symm ∘ p.toFun) x)
  rw [he]
  exact (complexRealEquiv n).symm.injective.comp (p.injective_fderiv x hx)

lemma semialgebraic_complexMap_re (p : NashPatch (n+n)) (j : Fin n) :
    PolynomialSignSet (id : (Option (Fin p.dim) → ℝ) → (Option (Fin p.dim) → ℝ))
      {x | (fun i => x (some i)) ∈ p.domain ∧ x none = (p.complexMap (fun i => x (some i)) j).re} :=
  p.semialgebraic_toFun.coordinate_graph (finSumFinEquiv (.inl j))

lemma semialgebraic_complexMap_im (p : NashPatch (n+n)) (j : Fin n) :
    PolynomialSignSet (id : (Option (Fin p.dim) → ℝ) → (Option (Fin p.dim) → ℝ))
      {x | (fun i => x (some i)) ∈ p.domain ∧ x none = (p.complexMap (fun i => x (some i)) j).im} :=
  p.semialgebraic_toFun.coordinate_graph (finSumFinEquiv (.inr j))

end NashPatch

theorem isSemialgebraic_finite_nash_cover {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    ∃ P : Finset (NashPatch (n+n)), ∀ z, z ∈ S ↔
      ∃ p ∈ P, z ∈ p.complexMap '' p.domain := by
  obtain ⟨P,hP⟩ := polynomialSignSet_finite_nash_cover (n+n) _ (isSemialgebraic_real_image hS)
  refine ⟨P,fun z => ?_⟩
  rw [← (complexRealEquiv n).injective.mem_set_image,hP]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  change (∃ x ∈ p.domain, p.toFun x = complexRealEquiv n z) ↔
    ∃ x ∈ p.domain, (complexRealEquiv n).symm (p.toFun x) = z
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  exact (complexRealEquiv n).symm_apply_eq.symm

theorem semialgebraic_boundary_finite_nash_cover {n : ℕ} {U : Set (Affine n)}
    (hU : IsSemialgebraic U) :
    ∃ P : Finset (NashPatch (n+n)), ∀ z, z ∈ closure U \ U ↔
      ∃ p ∈ P, z ∈ p.complexMap '' p.domain :=
  isSemialgebraic_finite_nash_cover (hU.closure.diff hU)

end Release061

end

end OAI
