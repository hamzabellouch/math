import OAI.Analysis.Pureness.Stabilization.MatrixLimit
import OAI.Analysis.Pureness.Stabilization.MatrixMasks

namespace OAI
noncomputable section
open scoped ENNReal Topology CStarAlgebra
open Filter
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixFamilyMask (n : ℕ) : BoundedFamilies (FinMatrix A) →ₗ[ℂ] BoundedFamilies (FinMatrix A) where
  toFun x := ⟨fun m => matrixMask n (x m), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨m,rfl⟩
    exact (matrixMask_norm_le n (x m)).trans (BoundedFamilies.norm_coordinate_le x m)⟩⟩
  map_add' x y := by apply lp.ext; funext m; exact matrixMask_add n (x m) (y m)
  map_smul' c x := by apply lp.ext; funext m; exact matrixMask_smul n c (x m)

lemma matrixFamilyMask_vanishing (n : ℕ) {x : BoundedFamilies (FinMatrix A)}
    (hx : x ∈ BoundedFamilies.vanishing) : matrixFamilyMask n x ∈ BoundedFamilies.vanishing := by
  change Tendsto (fun m => ‖matrixMask n (x m)‖) atTop (𝓝 0)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => matrixMask_norm_le n (x m)) hx

def matrixQuotientMask (n : ℕ) : FamilyQuotient (FinMatrix A) →ₗ[ℂ] FamilyQuotient (FinMatrix A) :=
  (BoundedFamilies.vanishing (A := FinMatrix A)).mapQ BoundedFamilies.vanishing
    (matrixFamilyMask n) (fun _ hx => matrixFamilyMask_vanishing n hx)

@[simp] lemma matrixQuotientMask_mk (n : ℕ) (x : BoundedFamilies (FinMatrix A)) :
    matrixQuotientMask n (FamilyQuotient.mk x) = FamilyQuotient.mk (matrixFamilyMask n x) := rfl

lemma matrixQuotientMask_norm_le (n : ℕ) (x : FamilyQuotient (FinMatrix A)) :
    ‖matrixQuotientMask n x‖ ≤ ‖x‖ := by
  obtain ⟨x,rfl⟩ := FamilyQuotient.mk_surjective x
  rw [matrixQuotientMask_mk, FamilyQuotient.norm_mk_eq_limsup, FamilyQuotient.norm_mk_eq_limsup]
  exact limsup_le_limsup (Eventually.of_forall (fun m => matrixMask_norm_le n (x m)))
    (BoundedFamilies.norm_cobounded _) (BoundedFamilies.norm_bounded x)

def matrixQuotientMaskCLM (n : ℕ) : FamilyQuotient (FinMatrix A) →L[ℂ] FamilyQuotient (FinMatrix A) :=
  (matrixQuotientMask n).mkContinuous 1 (fun x => by simpa using matrixQuotientMask_norm_le n x)

lemma matrixQuotientMask_stage (n m : ℕ) (M : FinMatrix A m) :
    matrixQuotientMask n (matrixStage m M) = matrixStage m (matrixMask n M) := by
  apply FamilyQuotient.mk_eq_of_eventually_eq
  filter_upwards [eventually_ge_atTop m] with k hk
  change matrixMask n (if h : m ≤ k then matrixInclusion h M else 0) =
    (if h : m ≤ k then matrixInclusion h (matrixMask n M) else 0)
  simp [hk, matrixMask_inclusion]

lemma matrixQuotientMask_mem_limit (n : ℕ) (x : MatrixLimit A) :
    matrixQuotientMask n x.1 ∈ matrixLimitAlgebra A := by
  have hc : Continuous (matrixQuotientMask (A := A) n) := (matrixQuotientMaskCLM n).continuous
  apply map_mem_closure hc x.2
  rintro y ⟨m,M,rfl⟩
  exact ⟨m,matrixMask n M,(matrixQuotientMask_stage n m M).symm⟩

def matrixCompression (n : ℕ) : MatrixLimit A →ₗ[ℂ] MatrixLimit A where
  toFun x := ⟨matrixQuotientMask n x.1, matrixQuotientMask_mem_limit n x⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul _ c x.1)

lemma matrixCompression_norm_le (n : ℕ) (x : MatrixLimit A) : ‖matrixCompression n x‖ ≤ ‖x‖ :=
  matrixQuotientMask_norm_le n x.1

lemma matrixCompression_stage (n m : ℕ) (M : FinMatrix A m) :
    matrixCompression n (matrixLimitStage m M) = matrixLimitStage m (matrixMask n M) :=
  Subtype.ext (matrixQuotientMask_stage n m M)

private theorem contractions_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : ℕ → E →ₗ[ℂ] E) (hC : ∀ n x, ‖C n x‖ ≤ ‖x‖) (x : E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ y : E, ‖x-y‖ < ε ∧ ∃ m, ∀ n, m ≤ n → C n y = y) :
    Tendsto (fun n => C n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y,hy,m,hm⟩ := happrox (ε/2) (by linarith)
  refine ⟨m,fun n hn => ?_⟩
  have hid : C n x - x = C n (x-y) + (y-x) := by
    rw [map_sub,hm n hn]
    abel
  rw [dist_eq_norm,hid]
  calc
    _ ≤ ‖C n (x-y)‖ + ‖y-x‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + ‖y-x‖ := add_le_add (hC n _) le_rfl
    _ < ε := by rw [norm_sub_rev y x]; linarith

theorem matrixCompression_tendsto (x : MatrixLimit A) :
    Tendsto (fun n => matrixCompression n x) atTop (𝓝 x) := by
  apply contractions_tendsto matrixCompression matrixCompression_norm_le x
  intro ε hε
  obtain ⟨m,M,hM⟩ := matrixLimit_finite_approximation x hε
  refine ⟨matrixLimitStage m M,hM,m,fun n hn => ?_⟩
  rw [matrixCompression_stage, matrixMask_eq_self hn]
end CuntzTrace

end

end OAI
