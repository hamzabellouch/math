import OAI.RepresentationTheory.FoulkesHowe.DegreeOne
import OAI.RepresentationTheory.FoulkesHowe.Functoriality

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

@[simp] theorem foulkesFormula_one (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin 1 → V) :
    foulkesFormula 1 b V v =
      symMonomial 1 (SymPow b V) (fun _ => symMonomial b V (fun j => v j 0)) := by
  classical
  simp [foulkesFormula, Fin.eq_zero]

/-- The canonical Foulkes--Howe equivalence when the inner degree is one. -/
def foulkesOneEquiv (b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    SymPow b (SymPow 1 V) ≃ₗ[ℂ] SymPow 1 (SymPow b V) :=
  (symPowEquiv b (symPowOneEquiv V)).trans (symPowOneEquiv (SymPow b V)).symm

theorem foulkesOneEquiv_isFoulkesMap (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    IsFoulkesMap 1 b V (foulkesOneEquiv b V).toLinearMap := by
  intro v
  simp [foulkesOneEquiv]

/-- Degree-one stabilization, with no finite-dimensionality requirement. -/
theorem canonical_foulkes_howe_a_one_aux (V : Type u)
    [AddCommGroup V] [Module ℂ V] (b : ℕ) :
    ∃ μ : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V),
      IsFoulkesMap 1 b V μ ∧ Function.Bijective μ ∧
      ∀ ν : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V),
        IsFoulkesMap 1 b V ν → ν = μ := by
  refine ⟨(foulkesOneEquiv b V).toLinearMap, foulkesOneEquiv_isFoulkesMap b V,
    (foulkesOneEquiv b V).bijective, ?_⟩
  intro ν hν
  have hspan : Submodule.span ℂ (Set.range (symMonomial b (SymPow 1 V))) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff (symPowSubmodule b (SymPow 1 V))
      (fun v => Submodule.subset_span (Set.mem_range_self v))).mpr rfl
  apply LinearMap.ext_on_range hspan
  intro v
  have h := (hν (fun j _ => symPowOneEquiv V (v j))).trans
    ((foulkesOneEquiv_isFoulkesMap b V (fun j _ => symPowOneEquiv V (v j))).symm)
  simpa only [← symPowOneEquiv_symm_apply, LinearEquiv.symm_apply_apply] using h

end Problem346

end

end OAI
