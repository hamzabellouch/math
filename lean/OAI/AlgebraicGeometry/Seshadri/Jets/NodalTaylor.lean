import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.LocalQuotients
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalIntersection

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open AlgebraicJets FormalCoordinates LocalComparison NodalLocal IsLocalRing
open scoped Topology

lemma localEquiv_comap_pow {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃ₐ[K] B) (n : ℕ) :
    (maximalIdeal B ^ n).comap e.toRingHom = maximalIdeal A ^ n := by
  have hm : (maximalIdeal A).map e.toRingHom = maximalIdeal B := by
    apply IsLocalRing.eq_maximalIdeal
    change (Ideal.map e.toRingEquiv (maximalIdeal A)).IsMaximal
    infer_instance
  rw [← hm, ← Ideal.map_pow, Ideal.comap_map_of_bijective e.toRingHom e.bijective]

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def bivariateTaylor (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) : R →ₐ[ℂ] Bivariate ℂ :=
  analyticFormal.comp (analyticPullback q hq)

lemma bivariateTaylor_eq (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) :
    bivariateTaylor q hq = (binaryEquiv ℂ).toAlgHom.comp (analyticTaylor q hq) := by
  apply AlgHom.ext
  intro s
  exact ((binaryEquiv ℂ).apply_symm_apply _).symm

lemma bivariateTaylor_exactJets (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (n : ℕ)
    (hk : RingHom.ker ((Ideal.Quotient.mk (maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n)
    (hs : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom)) :
    RingHom.ker ((Ideal.Quotient.mk (maximalIdeal (Bivariate ℂ)^n)).comp
      (bivariateTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal (Bivariate ℂ)^n)).comp
      (bivariateTaylor q hq).toRingHom) := by
  rw [bivariateTaylor_eq]
  constructor
  · rw [← RingHom.comap_ker, Ideal.mk_ker] at hk ⊢
    change ((maximalIdeal (Bivariate ℂ)^n).comap (binaryEquiv ℂ).toRingHom).comap
      (analyticTaylor q hq).toRingHom = _
    rwa [localEquiv_comap_pow]
  · intro y
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s,hs⟩ := hs (Ideal.Quotient.mk _ ((binaryEquiv ℂ).symm f))
    refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
    have hm : analyticTaylor q hq s - (binaryEquiv ℂ).symm f ∈
        maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n := Ideal.Quotient.eq.mp hs
    rw [← localEquiv_comap_pow (binaryEquiv ℂ) n] at hm
    change (binaryEquiv ℂ) (analyticTaylor q hq s - (binaryEquiv ℂ).symm f) ∈
      maximalIdeal (Bivariate ℂ)^n at hm
    change (binaryEquiv ℂ) (analyticTaylor q hq s) - f ∈ maximalIdeal (Bivariate ℂ)^n
    simpa only [map_sub, AlgEquiv.apply_symm_apply] using hm

lemma bivariateTaylor_comap_maximal (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) :
    (maximalIdeal (Bivariate ℂ)).comap (bivariateTaylor q hq).toRingHom =
      RingHom.ker (q 0) := by
  rw [bivariateTaylor_eq]
  change ((maximalIdeal (Bivariate ℂ)).comap (binaryEquiv ℂ).toRingHom).comap
    (analyticTaylor q hq).toRingHom = _
  have hm := localEquiv_comap_pow (binaryEquiv ℂ) 1
  simp only [pow_one] at hm
  rw [hm]
  exact formalTaylor_comap_maximalIdeal (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq)

lemma bivariateTaylor_node (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (g : R)
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) :
    ∃ U : Bivariate ℂ, IsUnit U ∧
      bivariateTaylor q hq g = U * nodeEquation ℂ := by
  let a : analyticFunctionAlgebra := ⟨u,hu⟩
  refine ⟨analyticFormal a, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.isUnit_iff_constantCoeff,
      analyticFormal_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hu0
  · have he := analyticFormal_congr (analyticPullback q hq g)
      (a*analyticFirst*analyticSecond) hg
    change analyticFormal (analyticPullback q hq g) = _
    rw [he, map_mul, map_mul, analyticFormal_first, analyticFormal_second, nodeEquation]
    exact mul_assoc _ _ _

theorem local_nodal_colength (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hjets : ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
    [hprime : (RingHom.ker (q 0)).IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]
    [IsLocalization.AtPrime A (RingHom.ker (q 0))] [IsLocalRing A] [IsNoetherianRing A]
    (f g : R) (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hx : restrictX ℂ (bivariateTaylor q hq f) ≠ 0)
    (hz : restrictZ ℂ (bivariateTaylor q hq f) ≠ 0) :
    FiniteDimensional ℂ (A ⧸ Ideal.span {algebraMap R A f, algebraMap R A g}) ∧
    Module.finrank ℂ (A ⧸ Ideal.span {algebraMap R A f, algebraMap R A g}) =
      (restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
        (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat := by
  let T := localTaylorLift (RingHom.ker (q 0)) A (bivariateTaylor q hq)
    (bivariateTaylor_comap_maximal q hq)
  have hT : T.toRingHom.comp (algebraMap R A) = (bivariateTaylor q hq).toRingHom :=
    localTaylorLift_comp _ _ _ _
  have hTs (n : ℕ) := localizedJet_surjective (bivariateTaylor q hq).toRingHom
    T.toRingHom hT (maximalIdeal (Bivariate ℂ)) n
      (bivariateTaylor_exactJets q hq n (hjets n).1 (hjets n).2).2
  have hTk (n : ℕ) := localizedJet_kernel (RingHom.ker (q 0)) (bivariateTaylor q hq).toRingHom
    T.toRingHom hT (maximalIdeal (Bivariate ℂ)) n
      (bivariateTaylor_exactJets q hq n (hjets n).1 (hjets n).2).1
  obtain ⟨U,hU,hgU⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hTg : T (algebraMap R A g) = U * nodeEquation ℂ := by
    rw [← hgU]
    exact RingHom.congr_fun hT g
  have hTf : T (algebraMap R A f) = bivariateTaylor q hq f := RingHom.congr_fun hT f
  refine ⟨actual_nodal_intersection_finite T hTs hTk _ _ hU hTg
    (by rwa [hTf]) (by rwa [hTf]), ?_⟩
  have H := actual_nodal_intersection_colength T hTs hTk _ _ hU hTg
    (by rwa [hTf]) (by rwa [hTf])
  rw [hTf] at H
  exact H
end
end MaximalSeshadri.AnalyticCoordinates
end


end
end

end OAI
