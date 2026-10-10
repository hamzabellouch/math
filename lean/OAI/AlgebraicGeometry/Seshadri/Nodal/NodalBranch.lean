import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.CoordinateEquivalences
import OAI.AlgebraicGeometry.Seshadri.Jets.NodalTaylor
import OAI.AlgebraicGeometry.Seshadri.Nodal.BranchFaithfulness

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open FormalCoordinates NodalLocal IsLocalRing
open scoped Topology

lemma binary_second_jet_witness {R : Type*} [CommRing R] [Algebra ℂ R]
    (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp τ.toRingHom)) (i : Fin 2) :
    ∃ a : R, MvPowerSeries.constantCoeff (τ a) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single i 1) (τ a) = 1 := by
  obtain ⟨a,ha⟩ := hs (Ideal.Quotient.mk _ (MvPowerSeries.X i))
  have hm := (mem_maximal_sq_iff (τ a - MvPowerSeries.X i)).mp
    (Ideal.Quotient.eq.mp ha)
  refine ⟨a, ?_, ?_⟩
  · simpa using hm.1
  · simpa [sub_eq_zero] using hm.2 i

lemma bivariate_branch_witnesses {R : Type*} [CommRing R] [Algebra ℂ R]
    (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp τ.toRingHom)) :
    (∃ a : R, PowerSeries.constantCoeff (restrictX ℂ ((binaryEquiv ℂ) (τ a))) = 0 ∧
      restrictX ℂ ((binaryEquiv ℂ) (τ a)) ≠ 0) ∧
    (∃ a : R, PowerSeries.constantCoeff (restrictZ ℂ ((binaryEquiv ℂ) (τ a))) = 0 ∧
      restrictZ ℂ ((binaryEquiv ℂ) (τ a)) ≠ 0) := by
  constructor
  · obtain ⟨a,ha0,ha1⟩ := binary_second_jet_witness τ hs 1
    refine ⟨a, ?_, ?_⟩
    · exact (binaryEquiv_constantCoeff _).trans ha0
    · intro h
      have H := congrArg (PowerSeries.coeff 1) h
      have he : Finsupp.cons 0 (Finsupp.cons 1 (0 : Fin 0 →₀ ℕ)) =
          Finsupp.single (1 : Fin 2) 1 := by
        ext j
        fin_cases j
        · simp
        · change (Finsupp.cons _ (Finsupp.cons _ 0)) (Fin.succ (0 : Fin 1)) = _
          rw [Finsupp.cons_succ]
          simp
      simp only [map_zero, restrictX_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at H
      change PowerSeries.coeff 1 (PowerSeries.coeff 0 ((binaryEquiv ℂ) (τ a))) = 0 at H
      rw [binaryEquiv_coeff,he,ha1] at H
      exact one_ne_zero H
  · obtain ⟨a,ha0,ha1⟩ := binary_second_jet_witness τ hs 0
    refine ⟨a, ?_, ?_⟩
    · rw [← restrict_constants]
      exact (binaryEquiv_constantCoeff _).trans ha0
    · intro h
      have H := congrArg (PowerSeries.coeff 1) h
      have he : Finsupp.cons 1 (Finsupp.cons 0 (0 : Fin 0 →₀ ℕ)) =
          Finsupp.single (0 : Fin 2) 1 := by
        ext j
        fin_cases j
        · simp
        · change (Finsupp.cons _ (Finsupp.cons _ 0)) (Fin.succ (0 : Fin 1)) = _
          rw [Finsupp.cons_succ]
          simp
      change PowerSeries.coeff 1 (PowerSeries.map PowerSeries.constantCoeff
        ((binaryEquiv ℂ) (τ a))) = 0 at H
      rw [PowerSeries.coeff_map] at H
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at H
      change PowerSeries.coeff 0 (PowerSeries.coeff 1 ((binaryEquiv ℂ) (τ a))) = 0 at H
      rw [binaryEquiv_coeff,he,ha1] at H
      exact one_ne_zero H

theorem nodal_branch_kernels {R : Type*} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp (analyticTaylor q hq).toRingHom))
    (g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) :
    RingHom.ker ((restrictX ℂ).comp (bivariateTaylor q hq)).toRingHom = Ideal.span {g} ∧
    RingHom.ker ((restrictZ ℂ).comp (bivariateTaylor q hq)).toRingHom = Ideal.span {g} := by
  obtain ⟨U,hU,hgU⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hw := bivariate_branch_witnesses (analyticTaylor q hq) hs
  have he (a : R) : (binaryEquiv ℂ) (analyticTaylor q hq a) = bivariateTaylor q hq a := by
    rw [bivariateTaylor_eq]; rfl
  simp only [he] at hw
  constructor
  · apply formal_branch_kernel hd g hg0 _ _ hw.1
    change restrictX ℂ (bivariateTaylor q hq g) = 0
    simp [hgU, nodeEquation]
  · apply formal_branch_kernel hd g hg0 _ _ hw.2
    change restrictZ ℂ (bivariateTaylor q hq g) = 0
    simp [hgU, nodeEquation]

theorem integral_nodal_colength {R : Type*} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hjets : ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
    [hprime : (RingHom.ker (q 0)).IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]
    [IsLocalization.AtPrime A (RingHom.ker (q 0))] [IsLocalRing A] [IsNoetherianRing A]
    (f g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : f ∉ Ideal.span {g}) :
    FiniteDimensional ℂ (A ⧸ Ideal.span {algebraMap R A f, algebraMap R A g}) ∧
    Module.finrank ℂ (A ⧸ Ideal.span {algebraMap R A f, algebraMap R A g}) =
      (restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
        (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat := by
  have hk := nodal_branch_kernels hd q hq (hjets 2).2 g hg0 u hu hu0 hg
  apply local_nodal_colength q hq hjets A f g u hu hu0 hg
  · intro h
    apply hf
    rw [← hk.1]
    exact h
  · intro h
    apply hf
    rw [← hk.2]
    exact h

end
end MaximalSeshadri.AnalyticCoordinates

end


end
end

end OAI
