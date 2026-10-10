import OAI.Analysis.Nuclearity.CPWeakOperatorUltralimit
import OAI.Analysis.OperatorAlgebra.FiniteOperatorExtension

namespace OAI

/-! Cpc maps into Hilbert-space operators extend along faithful unital
inclusions. Finite-dimensional compressions extend by the matrix theorem;
a weak operator ultralimit preserves complete positivity and all matrix
coefficients of the original map. -/

noncomputable section
open Filter Topology
open scoped InnerProductSpace CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma compression_contractive {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : E →L[ℂ] K) (hV : ‖V‖ ≤ 1) :
    ‖hilbertCompression (NonUnitalStarAlgHom.id ℂ (K →L[ℂ] K)) V‖ ≤ 1 := by
  exact (hilbertCompression_norm_le _ V).trans
    ((mul_le_mul hV hV (norm_nonneg V) zero_le_one).trans_eq (one_mul 1))

private lemma cpc_comp_norm {C D E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : C →L[ℂ] D) (g : D →L[ℂ] E) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    ‖g.comp f‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hg hf (norm_nonneg f) zero_le_one).trans_eq (one_mul 1))

private theorem finiteCorner_cpc_extension (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι)
    (φ : A →L[ℂ] (H →L[ℂ] H)) (hφ : CompletelyPositive φ) (hφn : ‖φ‖ ≤ 1)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] [Nontrivial E] :
    ∃ Φ : B →L[ℂ] (H →L[ℂ] H), CompletelyPositive Φ ∧ ‖Φ‖ ≤ 1 ∧
      ∀ a x y, x ∈ E → y ∈ E → inner ℂ (Φ (ι a) x) y = inner ℂ (φ a x) y := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let V := E.subtypeL
  let C := hilbertCompression (NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)) V
  have hCn : ‖C‖ ≤ 1 := compression_contractive V (Submodule.norm_subtypeL_le E)
  obtain ⟨ψ, hψ, hψn, hψe⟩ := finiteOperator_cpc_extension ι hι (C.comp φ)
    (completelyPositive_comp _ _ hφ (hilbertCompression_cp _ _))
    (cpc_comp_norm _ _ hφn hCn)
  let R := hilbertCompression (A := E →L[ℂ] E) (NonUnitalStarAlgHom.id ℂ (E →L[ℂ] E)) V.adjoint
  have hRn : ‖R‖ ≤ 1 := compression_contractive V.adjoint (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using Submodule.norm_subtypeL_le E)
  refine ⟨R.comp ψ, completelyPositive_comp _ _ hψ (hilbertCompression_cp _ _),
    cpc_comp_norm _ _ hψn hRn, ?_⟩
  intro a x y hx hy
  change inner ℂ (V.adjoint.adjoint (ψ (ι a) (V.adjoint x))) y = _
  rw [ContinuousLinearMap.adjoint_adjoint, hψe]
  change inner ℂ (V (V.adjoint (φ a (V (V.adjoint x))))) y = _
  have hPx : V (V.adjoint x) = x := by
    change E.subtypeL (E.subtypeL.adjoint x) = x
    rw [Submodule.adjoint_subtypeL]
    exact E.starProjection_eq_self_iff.mpr hx
  have hPy : V (V.adjoint y) = y := by
    change E.subtypeL (E.subtypeL.adjoint y) = y
    rw [Submodule.adjoint_subtypeL]
    exact E.starProjection_eq_self_iff.mpr hy
  rw [hPx, ← ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left, hPy]

/-- The Hilbert-operator cpc extension theorem, obtained from finite matrix
extensions and weak operator compactness. -/
theorem hilbertOperator_cpc_extension [Nontrivial H]
    (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι)
    (φ : A →L[ℂ] (H →L[ℂ] H)) (hφ : CompletelyPositive φ) (hφn : ‖φ‖ ≤ 1) :
    ∃ Φ : B →L[ℂ] (H →L[ℂ] H), CompletelyPositive Φ ∧ ‖Φ‖ ≤ 1 ∧
      ∀ a, Φ (ι a) = φ a := by
  classical
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H)
  let E (s : Finset H) := Submodule.span ℂ ((insert ξ s : Finset H) : Set H)
  have hE (s : Finset H) : Nontrivial (E s) := by
    have hm : ξ ∈ E s := Submodule.subset_span (by simp)
    exact ⟨⟨⟨ξ, hm⟩, 0, fun h => hξ (congrArg Subtype.val h)⟩⟩
  have hfin (s : Finset H) : FiniteDimensional ℂ (E s) := inferInstance
  have hex (s : Finset H) := @finiteCorner_cpc_extension A B H _ _ _ _ _ _ _ _ _
    ι hι φ hφ hφn (E s) (hfin s) (hE s)
  choose F hFcp hFn hFe using hex
  let U := Ultrafilter.of (atTop : Filter (Finset H))
  let Φ := cpOperatorUltraLimit U F hFn
  refine ⟨Φ, cpOperatorUltraLimit_completelyPositive U F hFn hFcp,
    cpOperatorUltraLimit_norm_le U F hFn, ?_⟩
  intro a
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  have he : ∀ᶠ s in (U : Filter (Finset H)),
      inner ℂ (F s (ι a) x) y = inner ℂ (φ a x) y := by
    apply (Ultrafilter.of_le (atTop : Filter (Finset H)))
    filter_upwards [eventually_ge_atTop ({x, y} : Finset H)] with s hs
    apply hFe s a x y
    · apply Submodule.subset_span
      exact Finset.mem_insert_of_mem (hs (by simp))
    · apply Submodule.subset_span
      exact Finset.mem_insert_of_mem (hs (by simp))
  exact tendsto_nhds_unique (cpOperatorUltraLimit_inner_tendsto U F hFn (ι a) x y)
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))

end WeakPureInfiniteness

end

end OAI
