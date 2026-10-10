import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalBranch

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.LocalComparison
noncomputable section
open IsLocalRing MaximalSeshadri.NodalLocal
variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

theorem formal_quotient_finrank_le [IsNoetherianRing S] [IsLocalRing S]
    (τ : R →ₐ[K] S) (I : Ideal R) [FiniteDimensional K (R ⧸ I)]
    [FiniteDimensional K (S ⧸ I.map τ.toRingHom)]
    (hs : ∀ n : ℕ, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ n)).comp τ.toRingHom)) :
    Module.finrank K (S ⧸ I.map τ.toRingHom) ≤ Module.finrank K (R ⧸ I) := by
  obtain ⟨N,hN⟩ := exists_pow_le_of_finite (K := K) (I.map τ.toRingHom)
  let q : (R ⧸ I) →ₐ[K] (S ⧸ I.map τ.toRingHom) :=
    Ideal.quotientMapₐ (I.map τ.toRingHom) τ Ideal.le_comap_map
  exact LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap)
    (quotientMap_surjective_of_finiteJet τ.toRingHom (maximalIdeal S) I N (hs N) hN)

theorem nodal_branch_sum_le_affine (τ : R →ₐ[K] Bivariate K)
    (hs : ∀ n : ℕ, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (Bivariate K) ^ n)).comp τ.toRingHom))
    (f g : R) [FiniteDimensional K (R ⧸ Ideal.span {f,g})]
    {u : Bivariate K} (hu : IsUnit u) (hg : τ g = u * nodeEquation K)
    (hx : restrictX K (τ f) ≠ 0) (hz : restrictZ K (τ f) ≠ 0) :
    (restrictX K (τ f)).order.toNat + (restrictZ K (τ f)).order.toNat ≤
      Module.finrank K (R ⧸ Ideal.span {f,g}) := by
  have he := map_nodal_intersection_ideal τ f g hu hg
  let : FiniteDimensional K (Bivariate K ⧸ (Ideal.span {f,g}).map τ.toRingHom) := by
    rw [he]
    exact finite_intersection_quotient K (τ f) hx hz
  have hb := formal_quotient_finrank_le τ (Ideal.span {f,g}) hs
  rw [he,nodal_intersection_colength K (τ f) hx hz] at hb
  exact hb
end
end MaximalSeshadri.LocalComparison

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open AlgebraicJets FormalCoordinates LocalComparison NodalLocal IsLocalRing
open scoped Topology

theorem integral_nodal_branch_sum_le_affine {R : Type*} [CommRing R]
    [Algebra ℂ R] [IsDomain R] (hd : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hjets : ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
    (f g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    [FiniteDimensional ℂ (R ⧸ Ideal.span {f,g})]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (hf : f ∉ Ideal.span {g}) :
    (restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat ≤
        Module.finrank ℂ (R ⧸ Ideal.span {f,g}) := by
  have hk := nodal_branch_kernels hd q hq (hjets 2).2 g hg0 u hu hu0 hg
  obtain ⟨U,hU,hgU⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  apply nodal_branch_sum_le_affine (bivariateTaylor q hq)
    (fun n => (bivariateTaylor_exactJets q hq n (hjets n).1 (hjets n).2).2) f g hU hgU
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
