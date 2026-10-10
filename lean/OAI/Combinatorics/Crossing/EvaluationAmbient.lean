import OAI.Combinatorics.Crossing.PolynomialFiltration

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ)

def constrainedInclusion {Z₁ Z₂ : Submodule ℝ W} (hZ : Z₁ ≤ Z₂) (k : ℕ) :
    constrained U node Z₁ k →ₗ[ℝ] constrained U node Z₂ k where
  toFun p := ⟨PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val, by
    constructor
    · intro n hn
      change Submodule.inclusion hZ (p.val.coeff n) = 0
      rw [p.property.1 n hn, map_zero]
    · intro i
      rw [show eval (node i) (PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val) =
        Submodule.inclusion hZ (eval (node i) p.val) by
          simpa using PolynomialModule.eval_map ℝ (Submodule.inclusion hZ) p.val (node i)]
      exact p.property.2 i⟩
  map_add' p q := Subtype.ext ((PolynomialModule.map ℝ (Submodule.inclusion hZ)).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((PolynomialModule.map ℝ (Submodule.inclusion hZ)).map_smul c p.val)

theorem constrainedInclusion_eval {Z₁ Z₂ : Submodule ℝ W} (hZ : Z₁ ≤ Z₂) (k : ℕ)
    (t : ℝ) (p : constrained U node Z₁ k) :
    Z₂.subtype (eval t (constrainedInclusion U node hZ k p).val) = Z₁.subtype (eval t p.val) := by
  change Z₂.subtype (eval t (PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val)) = _
  rw [show eval t (PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val) =
    Submodule.inclusion hZ (eval t p.val) by
      simpa using PolynomialModule.eval_map ℝ (Submodule.inclusion hZ) p.val t]
  rfl

def ambientEval (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) : constrained U node Z k →ₗ[ℝ] W :=
  Z.subtype.comp (constrainedEval U node Z k t)

def ambientEvalRange (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) : Submodule ℝ W :=
  LinearMap.range (ambientEval U node Z k t)

theorem finrank_ambientEvalRange (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) :
    finrank ℝ (ambientEvalRange U node Z k t) = finrank ℝ (evaluationFiltration U node Z t k) := by
  unfold ambientEvalRange ambientEval evaluationFiltration
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_subtype_eq Z _

theorem finrank_ambientEvalRange_off_node [FiniteDimensional ℝ W]
    (Z : Submodule ℝ W) (h : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    finrank ℝ (ambientEvalRange U node Z (h+1) t) = rankIncrement U node Z h := by
  rw [finrank_ambientEvalRange]
  exact finrank_eval_range U node Z h t ht

theorem ambientEvalRange_mono_coeff {Z₁ Z₂ : Submodule ℝ W} (hZ : Z₁ ≤ Z₂) (k : ℕ) (t : ℝ) :
    ambientEvalRange U node Z₁ k t ≤ ambientEvalRange U node Z₂ k t := by
  intro z hz
  obtain ⟨p, hp⟩ := hz
  refine ⟨constrainedInclusion U node hZ k p, ?_⟩
  exact (constrainedInclusion_eval U node hZ k t p).trans hp

theorem ambientEvalRange_le_coeff (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) :
    ambientEvalRange U node Z k t ≤ Z := by
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  exact (eval t p.val).property

theorem ambientEvalRange_at_node_le (Z : Submodule ℝ W) (k : ℕ) (i : ι) :
    ambientEvalRange U node Z k (node i) ≤ U i := by
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  exact p.property.2 i

end Zarankiewicz

end

end OAI
