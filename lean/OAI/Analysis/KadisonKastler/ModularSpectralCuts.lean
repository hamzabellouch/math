import OAI.Analysis.KadisonKastler.GraphScaleFunctionalCalculus
import OAI.Analysis.KadisonKastler.GraphIdentificationIndependence
import OAI.Analysis.KadisonKastler.ModularStrongContinuity

namespace OAI

/-! # Concrete upper cuts for the logarithmic modular spectrum

An upper logarithmic cut is the support of the positive part of a scalar
minus the graph resolvent. These are actual orthogonal projections on the
original Hilbert space, with no assumed spectral measure.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def resolventCutGenerator (R : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  cfc (fun s : ℝ => max (r - s) 0) R

def resolventLowerCut (R : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  (resolventCutGenerator R r).range.topologicalClosure.starProjection

theorem resolventLowerCut_projection (R : H →L[ℂ] H) (r : ℝ) :
    IsStarProjection (resolventLowerCut R r) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem resolventLowerCut_mul_generator (R : H →L[ℂ] H) (r : ℝ) :
    resolventLowerCut R r * resolventCutGenerator R r = resolventCutGenerator R r := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem mul_resolventLowerCut_eq_zero (R A : H →L[ℂ] H) (r : ℝ)
    (h : A * resolventCutGenerator R r = 0) : A * resolventLowerCut R r = 0 := by
  have hs : (resolventCutGenerator R r).range.topologicalClosure ≤ A.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun T : H →L[ℂ] H => T x) h
    · exact A.isClosed_ker
  ext x
  exact hs ((resolventCutGenerator R r).range.topologicalClosure.starProjection_apply_mem x)

private theorem cut_range_invariant (R T : H →L[ℂ] H) (r : ℝ)
    (h : Commute (resolventCutGenerator R r) T) {x : H}
    (hx : x ∈ (resolventCutGenerator R r).range.topologicalClosure) :
    T x ∈ (resolventCutGenerator R r).range.topologicalClosure := by
  have hs : (resolventCutGenerator R r).range.topologicalClosure ≤
      ((resolventCutGenerator R r).range.topologicalClosure).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨y, rfl⟩
      apply Submodule.le_topologicalClosure
      exact ⟨T y, congrArg (fun A : H →L[ℂ] H => A y) h.eq⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact hs hx

theorem resolventLowerCut_commutes (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (r : ℝ) :
    Commute (resolventLowerCut R r) R := by
  have hc : Commute (resolventCutGenerator R r) R := (Commute.refl R).cfc_real _
  exact Generator.starProjection_commutes_of_invariant _ R
    (fun _ hx => cut_range_invariant R R r hc hx)
    (fun _ hx => cut_range_invariant R (star R) r (by rwa [hR.star_eq]) hx)

theorem resolventLowerCut_commutes_cfc (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (r : ℝ) (f : ℝ → ℝ) : Commute (resolventLowerCut R r) (cfc f R) :=
  ((resolventLowerCut_commutes R hR r).symm.cfc_real f).symm

def modularCutThreshold (a : ℝ) : ℝ := (1 + Real.exp a)⁻¹

theorem modularCutThreshold_pos (a : ℝ) : 0 < modularCutThreshold a := by
  unfold modularCutThreshold
  positivity

theorem modularCutThreshold_lt_one (a : ℝ) : modularCutThreshold a < 1 := by
  unfold modularCutThreshold
  exact inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos a])

def modularUpperCut (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (a : ℝ) : H →L[ℂ] H :=
  resolventLowerCut (graphResolvent M J Ω 1) (modularCutThreshold a)

theorem modularUpperCut_projection (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    IsStarProjection (modularUpperCut M J Ω a) := resolventLowerCut_projection _ _

theorem modularUpperCut_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ‖modularUpperCut M J Ω a‖ ≤ 1 := (modularUpperCut_projection J Ω a).norm_le _

theorem modularUpperCut_complement_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ‖1 - modularUpperCut M J Ω a‖ ≤ 1 := (modularUpperCut_projection J Ω a).one_sub.norm_le _

theorem modularUpperCut_identification_independent (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    modularUpperCut M J Ω a = modularUpperCut M K Ω a := by
  unfold modularUpperCut
  rw [graphResolvent_identification_independent J K]

theorem modularUpperCut_commutes_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a c : ℝ)
    (hc : c ≠ 0) : Commute (modularUpperCut M J Ω a) (graphResolvent M J Ω c) := by
  rw [graphResolvent_eq_cfc_scale J Ω hc]
  exact resolventLowerCut_commutes_cfc _ (graphResolvent_positive J Ω 1).isSelfAdjoint _ _

variable [TopologicalSpace.SeparableSpace H]

theorem modularUpperCut_commutes_group (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (a t : ℝ) :
    Commute (modularUpperCut M J Ω a)
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  apply commute_of_strong_tendsto _ _ (fun n => modularApproximation M J Ω n t)
    (modularApproximation_tendsto J Ω hsep hcyc t)
  intro n
  rw [modularApproximation, regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n)]
  exact ((graphResolvent_positive J Ω 1).isSelfAdjoint.commute_cfc
    (resolventLowerCut_commutes _ (graphResolvent_positive J Ω 1).isSelfAdjoint _).symm _).symm

end

end KadisonKastler

end OAI
