import OAI.Analysis.KadisonKastler.ModularStrongContinuity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! # Fixed vectors of the constructed modular group

The half-eigenspace of the bounded graph resolvent is fixed by every
regularized group and by its strong limit. It contains the state vector
and the vectors obtained from elements of the vector-state centralizer.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem cfcHom_half_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (x : H) (hx : A x = (1 / 2 : ℂ) • x) (hs : (1 / 2 : ℂ) ∈ spectrum ℂ A)
    (f : C(spectrum ℂ A, ℂ)) : (cfcHom (R := ℂ) hA.isStarNormal f) x = f ⟨1 / 2, hs⟩ • x := by
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    change (cfcHom (R := ℂ) hA.isStarNormal (algebraMap ℂ C(spectrum ℂ A, ℂ) r)) x = r • x
    rw [AlgHomClass.commutes]
    rfl
  | id =>
    rw [cfcHom_id]
    exact hx
  | star_id =>
    rw [map_star, cfcHom_id, hA.star_eq]
    simpa only [ContinuousMap.star_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply, star_div₀, star_one, star_ofNat] using hx
  | add f g hf hg =>
    rw [map_add, add_apply, hf, hg, ← add_smul]
    rfl
  | mul f g hf hg =>
    rw [map_mul, mul_apply_eq_comp, hg, map_smul, hf, smul_smul, mul_comm]
    rfl
  | frequently f hf =>
    have hc : IsClosed {g : C(spectrum ℂ A, ℂ) |
        (cfcHom (R := ℂ) hA.isStarNormal g) x = g ⟨1 / 2, hs⟩ • x} :=
      isClosed_eq ((cfcHom_continuous hA.isStarNormal).clm_apply continuous_const)
        ((continuous_eval_const _).smul continuous_const)
    have hm := mem_closure_iff_frequently.mpr hf
    change f ∈ closure {g : C(spectrum ℂ A, ℂ) |
      (cfcHom (R := ℂ) hA.isStarNormal g) x = g ⟨1 / 2, hs⟩ • x} at hm
    rwa [hc.closure_eq] at hm

private theorem cfc_half_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (x : H) (hx : A x = (1 / 2 : ℂ) • x) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ A)) : (cfc f A) x = f (1 / 2) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hs : (1 / 2 : ℂ) ∈ spectrum ℂ A := by
    apply spectrum.mem_iff.mpr
    intro hu
    have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    have hz : (algebraMap ℂ (H →L[ℂ] H) (1 / 2) - A) x = 0 := by
      rw [sub_apply, ContinuousLinearMap.algebraMap_apply, hx, sub_self]
    exact hx0 (hinj (hz.trans (map_zero _).symm))
  rw [cfc_apply f A hA.isStarNormal hf]
  exact cfcHom_half_eigen A hA x hx hs ⟨_, hf.domRestrict⟩

theorem regularizedModularGroup_fixes_half_eigen (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : H)
    (hx : graphResolvent M J Ω 1 x = (1 / 2 : ℂ) • x) :
    (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) x = x := by
  rw [regularizedModularGroup_eq_cfc J Ω t hε,
    cfc_half_eigen _ (graphResolvent_positive J Ω 1).isSelfAdjoint x hx _
      (modularPhaseScalar_continuousOn J Ω t hε)]
  have hh : modularPhaseScalar t ε (1 / 2) = 1 := by
    have he : regularizedLogScalar ε (1 / 2) = 0 := by
      unfold regularizedLogScalar
      rw [show 1 - (1 / 2 : ℝ) + ε = 1 / 2 + ε by ring, sub_self]
    have hre : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
    unfold modularPhaseScalar
    rw [hre, he]
    simp
  rw [hh, one_smul]

variable [SeparableSpace H]

theorem modularStrongGroup_fixes_half_eigen (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (x : H)
    (hx : graphResolvent M J Ω 1 x = (1 / 2 : ℂ) • x) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x = x := by
  have ht := modularApproximation_tendsto J Ω hsep hcyc t x
  have he (n : ℕ) : modularApproximation M J Ω n t x = x :=
    regularizedModularGroup_fixes_half_eigen J Ω (modularRegularizationScale_pos n) t x hx
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem modularStrongGroup_fixes_state (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω = Ω :=
  modularStrongGroup_fixes_half_eigen J Ω hsep hcyc t Ω (graphResolvent_state J Ω)

theorem modularStrongGroup_fixes_centralizer_vector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) (r.val Ω) = r.val Ω :=
  modularStrongGroup_fixes_half_eigen J Ω hsep hcyc t _ (graphResolvent_centralizer J Ω r hr)

end

end KadisonKastler

end OAI
