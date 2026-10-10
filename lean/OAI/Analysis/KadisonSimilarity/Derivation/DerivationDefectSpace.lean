import OAI.Analysis.KadisonSimilarity.Derivation.RectangularDerivations

namespace OAI

/-! The reducing defect space of a factorized derivation. It will provide
the sharp implementing operator in the commutant-distance formula. -/

noncomputable section
namespace KadisonSimilarity
open scoped Topology

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def derivationDefect (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) : H →L[ℂ] K :=
  (π a).comp W - W.comp (σ a)

def derivationDefectSpace (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) : ClosedSubmodule ℂ K :=
  (Submodule.span ℂ (Set.range fun p : A × H => derivationDefect σ π W p.1 p.2)).closure

theorem derivationDefect_mem (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) (x : H) :
    derivationDefect σ π W a x ∈ derivationDefectSpace σ π W := by
  apply (Submodule.span ℂ (Set.range fun p : A × H =>
    derivationDefect σ π W p.1 p.2)).le_topologicalClosure
  exact Submodule.subset_span ⟨(a, x), rfl⟩

theorem derivationDefect_mul (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (b a : A) :
    (π b).comp (derivationDefect σ π W a) =
      derivationDefect σ π W (b * a) - (derivationDefect σ π W b).comp (σ a) := by
  ext x
  simp only [derivationDefect, ContinuousLinearMap.comp_apply, _root_.sub_apply,
    map_sub, map_mul, mul_apply_eq_comp]
  abel

theorem derivationDefectSpace_invariant (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
    (b : A) (x : K) (hx : x ∈ derivationDefectSpace σ π W) :
    π b x ∈ derivationDefectSpace σ π W := by
  let Q := derivationDefectSpace σ π W
  have hspan : Submodule.span ℂ (Set.range fun p : A × H =>
      derivationDefect σ π W p.1 p.2) ≤ Q.toSubmodule.comap (π b).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨a, z⟩, rfl⟩
    change π b (derivationDefect σ π W a z) ∈ Q
    have he := congrArg (fun T : H →L[ℂ] K => T z) (derivationDefect_mul σ π W b a)
    change π b (derivationDefect σ π W a z) =
      derivationDefect σ π W (b * a) z - derivationDefect σ π W b (σ a z) at he
    rw [he]
    exact Q.sub_mem (derivationDefect_mem σ π W _ _) (derivationDefect_mem σ π W _ _)
  exact closure_minimal hspan (Q.isClosed.preimage (π b).continuous) hx

/-- The left factor intertwines the two representations on the defect space. -/
theorem derivationDefectSpace_intertwines
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : K →L[ℂ] H) (W : H →L[ℂ] K) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    (hF : ∀ a, U.comp ((π a).comp W) = δ a) (hUW : U.comp W = 0)
    (b : A) (x : K) (hx : x ∈ derivationDefectSpace σ π W) :
    U (π b x) = σ b (U x) := by
  have hUd (a : A) : U.comp (derivationDefect σ π W a) = δ a := by
    simp only [derivationDefect, ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc, hUW, ContinuousLinearMap.zero_comp, sub_zero]
    exact hF a
  have hgen (a : A) :
      U.comp ((π b).comp (derivationDefect σ π W a)) = (σ b).comp (δ a) := by
    rw [derivationDefect_mul, ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc U (derivationDefect σ π W b) (σ a),
      hUd, hUd, hδ]
    abel
  have hspan : Submodule.span ℂ (Set.range fun p : A × H =>
      derivationDefect σ π W p.1 p.2) ≤
      (U.comp (π b) - (σ b).comp U).ker := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨a, z⟩, rfl⟩
    change U (π b (derivationDefect σ π W a z)) -
      σ b (U (derivationDefect σ π W a z)) = 0
    have hg := congrArg (fun T : H →L[ℂ] H => T z) (hgen a)
    have hd := congrArg (fun T : H →L[ℂ] H => T z) (hUd a)
    change U (π b (derivationDefect σ π W a z)) = σ b (δ a z) at hg
    change U (derivationDefect σ π W a z) = δ a z at hd
    rw [hg, hd, sub_self]
  have hc := closure_minimal hspan
    (U.comp (π b) - (σ b).comp U).isClosed_ker hx
  exact sub_eq_zero.mp hc

end KadisonSimilarity

end

end OAI
