import OAI.Analysis.KadisonKastler.TomitaGraphInvolution
import OAI.Analysis.KadisonKastler.GraphResolventCompression

namespace OAI

/-! # Faithfulness of the bounded Tomita graph resolvent

Both endpoints of the positive contraction have zero eigenspace. This is the
bounded starting point for recovering the modular operator by spectral calculus.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
private theorem inner_tupleSingle_left (i : Fin 2) (x : H) (v : TomitaGraphHilbert H) :
    inner ℂ (Generator.tupleSingle i x) v = inner ℂ x (v i) := by
  fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_two, Generator.tupleSingle_apply,
    Pi.single_apply]

private theorem tupleSingle_adjoint (i : Fin 2) :
    (Generator.tupleSingle (H := H) i).adjoint = PiLp.proj 2 (fun _ : Fin 2 => H) i := by
  ext v
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_tupleSingle_left i x v

theorem graphResolvent_eq_compression (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    graphResolvent M J Ω c =
      (Generator.tupleSingle (H := H) (0 : Fin 2)).adjoint ∘L
        rescaledGraphProjection M J Ω c ∘L Generator.tupleSingle 0 := by
  rw [tupleSingle_adjoint]
  rfl

theorem graphResolvent_positive (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    (graphResolvent M J Ω c).IsPositive := by
  rw [graphResolvent_eq_compression]
  apply ContinuousLinearMap.IsPositive.adjoint_conj
  exact ContinuousLinearMap.isPositive_def'.mpr
    ⟨isSelfAdjoint_starProjection _, fun x =>
      (rescaledGraphSubspace M J Ω c).re_inner_starProjection_nonneg x⟩

theorem graphResolvent_norm_le_one (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    ‖graphResolvent M J Ω c‖ ≤ 1 :=
  (norm_graph_operatorEntry_le _ 0 0).trans
    (rescaledGraphSubspace M J Ω c).starProjection_norm_le

theorem graphResolvent_eq_zero_iff (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    graphResolvent M J Ω c x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    let P := rescaledGraphSubspace M J Ω c
    have hp : P.starProjection (Generator.tupleSingle 0 x) = 0 :=
      rescaledGraph_no_vertical J Ω c hsep _ (P.starProjection_apply_mem _) hx
    have hort := P.starProjection_apply_eq_zero_iff.mp hp
    have hall (a : Algebra M) : inner ℂ x (a.val Ω) = 0 := by
      have h := (P.mem_orthogonal' _).mp hort _ (rescaledGraphVector_mem M J Ω c a)
      simpa only [inner_tupleSingle_left, rescaledGraphVector_zero] using h
    have hc : IsClosed {y : H | inner ℂ x y = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : Set.range (algebraVectorMap M Ω) ⊆ {y : H | inner ℂ x y = 0} := by
      rintro _ ⟨a, rfl⟩
      exact hall a
    have h := closure_minimal hsub hc (hcyc x)
    exact inner_self_eq_zero.mp h
  · rintro rfl
    exact map_zero _

end

end KadisonKastler

end OAI
