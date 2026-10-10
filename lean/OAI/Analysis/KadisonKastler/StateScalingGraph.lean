import OAI.Analysis.KadisonKastler.StateScalingAlgebra
import OAI.Analysis.KadisonKastler.TomitaCentralizerConjugation

namespace OAI

/-! # State scaling in the closed Tomita graph

A state-scaling operator gives an exact eigenvector of the bounded graph
resolvent. This identifies its modular square-root ratio without any
unbounded-operator domain convention.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H} {r : ℝ}

namespace StateScales

theorem tomita_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : r ≠ 0) (a : Algebra M) :
    inner ℂ (J (star v.val Ω)) (J (star a.val Ω)) =
      (r⁻¹ : ℝ) * inner ℂ (v.val Ω) (a.val Ω) := by
  rw [conjugateIsometry_inner]
  change (starRingEnd ℂ) (inner ℂ (star v.val Ω) (star a.val Ω)) = _
  rw [inner_conj_symm]
  calc
    inner ℂ (star a.val Ω) (star v.val Ω) =
        productVectorState Ω (a.val * star v.val) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      rfl
    _ = (r⁻¹ : ℝ) * productVectorState Ω (star v.val * a.val) :=
      hv.adjoint hr a.val a.property
    _ = _ := by
      change _ * inner ℂ Ω (star v.val (a.val Ω)) = _
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem graphProjection (J : H ≃ₗᵢ⋆[ℂ] H) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : 0 < r) :
    rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 (v.val Ω)) =
      ((r/(1+r) : ℝ) : ℂ) • rescaledGraphVector J Ω 1 v.val := by
  let P := rescaledGraphSubspace M J Ω 1
  apply P.eq_starProjection_of_mem_of_inner_eq_zero
  · exact P.smul_mem _ (rescaledGraphVector_mem M J Ω 1 v)
  · intro w hw
    have hc : IsClosed {w : TomitaGraphHilbert H |
        inner ℂ (Generator.tupleSingle 0 (v.val Ω) -
          ((r/(1+r) : ℝ) : ℂ) • rescaledGraphVector J Ω 1 v.val) w = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω 1)) ?_ hc hw
    rintro _ ⟨a, rfl⟩
    change inner ℂ (Generator.tupleSingle 0 (v.val Ω) -
      ((r/(1+r) : ℝ) : ℂ) • rescaledGraphVector J Ω 1 v.val)
      (rescaledGraphVector J Ω 1 a.val) = 0
    simp only [inner_sub_left, inner_smul_left, PiLp.inner_apply, Fin.sum_univ_two,
      Generator.tupleSingle_apply, Pi.single_apply, Fin.isValue, ↓reduceIte,
      rescaledGraphVector_zero, rescaledGraphVector_one, one_smul]
    rw [hv.tomita_coefficient J v (ne_of_gt hr) a]
    rw [show (starRingEnd ℂ) (((r/(1+r) : ℝ) : ℂ)) = (((r/(1+r) : ℝ) : ℂ)) from
      Complex.conj_ofReal _]
    simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false,
      inner_zero_left, add_zero, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv]
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    have hden : (1 : ℂ)+(r : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0 < 1+r by linarith))
    field_simp [hrc,hden]
    ring

theorem graphResolvent (J : H ≃ₗᵢ⋆[ℂ] H) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : 0 < r) :
    graphResolvent M J Ω 1 (v.val Ω) = ((r/(1+r) : ℝ) : ℂ) • v.val Ω := by
  exact congrArg (fun w : TomitaGraphHilbert H => w 0) (hv.graphProjection J v hr)

theorem polarCoordinates (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (v : Algebra M)
    (hv : StateScales M Ω r v.val) (hr : 0 < r) :
    (Real.sqrt (r/(1+r)) : ℂ) • (tomitaPolarCoordinates J Ω hsep hcyc (v.val Ω)).val =
      ((r/(1+r) : ℝ) : ℂ) • rescaledGraphVector J Ω 1 v.val := by
  have h := tomitaPolarCoordinates_root J Ω hsep hcyc (v.val Ω)
  rw [tomitaGraphRoot_eigen J Ω (v.val Ω)
    (div_pos hr (by linarith)) (hv.graphResolvent J v hr),map_smul] at h
  have he := congrArg (fun w : rescaledGraphSubspace M J Ω 1 => w.val) h
  rw [tomitaGraphFirst_adjoint_apply,hv.graphProjection J v hr] at he
  exact he

end StateScales

end

end KadisonKastler

end OAI
