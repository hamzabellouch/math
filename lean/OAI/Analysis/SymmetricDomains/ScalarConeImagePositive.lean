import Mathlib
import OAI.Analysis.SymmetricDomains.HolQuadraticSmul
import OAI.Analysis.SymmetricDomains.QuadraticDomainConnectedComponent
import OAI.Analysis.SymmetricDomains.ModelChartOpen

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
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {k j : ℕ}

def bilinearNormalCoordinates (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ))
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Fin j → E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  fun i => LinearMap.mk₂ ℝ (fun z w => L (fun t => B t z w) i)
    (fun x y z => by
      simp only [map_add, LinearMap.add_apply]
      change L ((fun t => B t x z)+(fun t => B t y z)) i = _
      rw [map_add]; rfl)
    (fun r x z => by
      simp only [map_smul, LinearMap.smul_apply]
      change L (r • (fun t => B t x z)) i = _
      rw [map_smul]; rfl)
    (fun x y z => by
      simp only [map_add]
      change L ((fun t => B t x y)+(fun t => B t x z)) i = _
      rw [map_add]; rfl)
    (fun r x z => by
      simp only [map_smul]
      change L (r • (fun t => B t x z)) i = _
      rw [map_smul]; rfl)

omit [IsScalarTower ℝ ℂ E] in
lemma hermQuadratic_half_sum (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) :
    hermQuadratic B z = (1/2 : ℝ) •
      ((fun i => B i z z)+(fun i => B i (I • z) (I • z))) := by
  funext i
  simp only [hermQuadratic,hermPart,add_re,ofReal_re,mul_re,I_re,I_im,
    ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,Pi.smul_apply,Pi.add_apply,
    smul_eq_mul,symmetrize_diag]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermQuadratic_bilinearNormalCoordinates
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ))
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) :
    hermQuadratic (bilinearNormalCoordinates L B) z = L (hermQuadratic B z) := by
  rw [hermQuadratic_half_sum,hermQuadratic_half_sum,map_smul,map_add]
  rfl

omit [IsScalarTower ℝ ℂ E] in
lemma supportLinearCoordinates_hermitian_residual {k : ℕ}
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    (B : Fin (k+1) → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin (k+1) → ℂ)) :
    (fun i => ((supportLinearCoordinates e p).2 i).im -
      hermQuadratic (bilinearNormalCoordinates e.toLinearMap B) (supportLinearCoordinates e p).1 i) =
    e (fun i => (p.2 i).im-hermQuadratic B p.1 i) := by
  rw [supportLinearCoordinates_fst,hermQuadratic_bilinearNormalCoordinates]
  change _ = e ((fun i => (p.2 i).im)-hermQuadratic B p.1)
  rw [map_sub]
  funext i
  rw [supportLinearCoordinates_im]
  rfl

omit [IsScalarTower ℝ ℂ E] in
lemma supportLinearCoordinates_hermitian_mem {k : ℕ}
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    (B : Fin (k+1) → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin (k+1) → ℝ))
    (p : E × (Fin (k+1) → ℂ)) :
    supportLinearCoordinates e p ∈
      quadraticDomain (hermQuadratic (bilinearNormalCoordinates e.toLinearMap B)) (e '' C) ↔
      p ∈ quadraticDomain (hermQuadratic B) C := by
  change (fun i => ((supportLinearCoordinates e p).2 i).im -
      hermQuadratic (bilinearNormalCoordinates e.toLinearMap B) (supportLinearCoordinates e p).1 i)
        ∈ e '' C ↔ _
  rw [supportLinearCoordinates_hermitian_residual]
  exact e.injective.mem_set_image

lemma scalar_cone_image_eq_positive
    (C : Set (Fin 1 → ℝ)) (hC : C.Nonempty)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (e : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ))
    (hpos : ∀ y ∈ C, 0 < e y 0) :
    e '' C = {y | 0 < y 0} := by
  obtain ⟨a,ha⟩ := hC
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hpos x hx
  · intro hy
    let r := y 0/e a 0
    have hr : 0 < r := div_pos hy (hpos a ha)
    refine ⟨r • a,hcone r hr a ha,?_⟩
    rw [map_smul]
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change (y 0/e a 0) * e a 0 = y 0
    exact div_mul_cancel₀ _ (hpos a ha).ne'

end Release061.Hermitian

end

end OAI
