import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.CoordinateEquivalences

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology

open AlgebraicJets FormalCoordinates MvPolynomial
variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma analyticTaylor_coeff_zero (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.coeff (Finsupp.single 0 1) (analyticTaylor q hq s) =
      deriv (fun z => q (0,z) s) 0 := by
  have he : (Finsupp.cons 1 (Finsupp.cons 0 0) : Fin 2 →₀ ℕ) =
      Finsupp.single 0 1 := by
    ext i
    fin_cases i
    · simp
    · change (Finsupp.cons 1 (Finsupp.cons 0 0)) (Fin.succ (0 : Fin 1)) = _
      rw [Finsupp.cons_succ]
      simp
  have h := binaryEquiv_coeff (analyticTaylor q hq s) 0 1
  rw [he] at h
  rw [←h]
  have hb : binaryEquiv ℂ (analyticTaylor q hq s) = analyticFormal (analyticPullback q hq s) := by
    exact (binaryEquiv ℂ).apply_symm_apply _
  rw [hb]
  have hc : PowerSeries.coeff 0 (PowerSeries.coeff 1 (analyticFormal (analyticPullback q hq s))) =
      analyticCoefficients (analyticPullback q hq s) (0,1) := by
    change PowerSeries.coeff _ (PowerSeries.coeff _ (biSeries (analyticCoefficients _))) = _
    simp [biSeries]
  rw [hc]
  have hd := analyticCoefficients_eq_derivative (analyticPullback q hq s) 0 1
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, analyticPullback] using hd

lemma analyticTaylor_coeff_one (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.coeff (Finsupp.single 1 1) (analyticTaylor q hq s) =
      deriv (fun x => q (x,0) s) 0 := by
  have he : (Finsupp.cons 0 (Finsupp.cons 1 0) : Fin 2 →₀ ℕ) =
      Finsupp.single 1 1 := by
    ext i
    fin_cases i
    · simp
    · change (Finsupp.cons 0 (Finsupp.cons 1 0)) (Fin.succ (0 : Fin 1)) = _
      rw [Finsupp.cons_succ]
      simp
  have h := binaryEquiv_coeff (analyticTaylor q hq s) 1 0
  rw [he] at h
  rw [←h]
  have hb : binaryEquiv ℂ (analyticTaylor q hq s) = analyticFormal (analyticPullback q hq s) := by
    exact (binaryEquiv ℂ).apply_symm_apply _
  rw [hb]
  have hc : PowerSeries.coeff 1 (PowerSeries.coeff 0 (analyticFormal (analyticPullback q hq s))) =
      analyticCoefficients (analyticPullback q hq s) (1,0) := by
    change PowerSeries.coeff _ (PowerSeries.coeff _ (biSeries (analyticCoefficients _))) = _
    simp [biSeries]
  rw [hc]
  have hd := analyticCoefficients_eq_derivative (analyticPullback q hq s) 1 0
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, analyticPullback] using hd

lemma analyticTaylor_fullRank
    [Algebra (MvPolynomial (Fin 2) ℂ) S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
    (he : HasFDerivAt (fun z =>
      (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
       q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0)))) (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) :
    ∃ b : Fin 2 → Fin 2 → ℂ, ∀ i j,
      ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
        (analyticTaylor q hq (algebraMap (MvPolynomial (Fin 2) ℂ) S (X l))) =
      if i = j then 1 else 0 := by
  have hv : HasDerivAt (fun z : ℂ => ((0 : ℂ),z)) (0,1) 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id (0 : ℂ))
  have hh : HasDerivAt (fun z : ℂ => (z,(0 : ℂ))) (1,0) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  have h00 := (he.snd.comp_hasDerivAt (f := fun z : ℂ => ((0 : ℂ),z)) 0 hv).deriv
  have h01 := (he.snd.comp_hasDerivAt (f := fun z : ℂ => (z,(0 : ℂ))) 0 hh).deriv
  have h10 := (he.fst.comp_hasDerivAt (f := fun z : ℂ => ((0 : ℂ),z)) 0 hv).deriv
  have h11 := (he.fst.comp_hasDerivAt (f := fun z : ℂ => (z,(0 : ℂ))) 0 hh).deriv
  change deriv (fun z => q (0,z) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))) 0 = (e (0,1)).2 at h00
  change deriv (fun z => q (z,0) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))) 0 = (e (1,0)).2 at h01
  change deriv (fun z => q (0,z) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1))) 0 = (e (0,1)).1 at h10
  change deriv (fun z => q (z,0) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1))) 0 = (e (1,0)).1 at h11
  have hfin : (1 : Fin 2) ≠ 0 := by decide
  have hi (z : ℂ × ℂ) : z.1 • e.symm (1,0) + z.2 • e.symm (0,1) = e.symm z := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  refine ⟨fun i l => if i = 0 then
    (if l = 0 then (e.symm (0,1)).2 else (e.symm (1,0)).2)
    else (if l = 0 then (e.symm (0,1)).1 else (e.symm (1,0)).1), ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.sum_univ_two, Fin.mk_zero, Fin.isValue, hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_zero, analyticTaylor_coeff_zero]
    rw [h00,h10]
    simpa [Prod.snd_add, Prod.snd_smul, mul_comm, add_comm] using congrArg Prod.snd (hi (e (0,1)))
  · simp only [Fin.sum_univ_two, Fin.mk_zero, Fin.mk_one, Fin.isValue, hfin, Ne.symm hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_one, analyticTaylor_coeff_one]
    rw [h01,h11]
    simpa [Prod.snd_add, Prod.snd_smul, mul_comm, add_comm] using congrArg Prod.snd (hi (e (1,0)))
  · simp only [Fin.sum_univ_two, Fin.mk_zero, Fin.mk_one, Fin.isValue, hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_zero, analyticTaylor_coeff_zero]
    rw [h00,h10]
    simpa [Prod.fst_add, Prod.fst_smul, mul_comm, add_comm] using congrArg Prod.fst (hi (e (0,1)))
  · simp only [Fin.sum_univ_two, Fin.mk_one, Fin.isValue, hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_one, analyticTaylor_coeff_one]
    rw [h01,h11]
    simpa [Prod.fst_add, Prod.fst_smul, mul_comm, add_comm] using congrArg Prod.fst (hi (e (1,0)))

theorem analyticTaylor_exactJets
    [Algebra (MvPolynomial (Fin 2) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
    (he : HasFDerivAt (fun z =>
      (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
       q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))))
       (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
        (RingHom.ker (q 0))^n ∧
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) := by
  obtain ⟨b,hb⟩ := analyticTaylor_fullRank q hq e he
  exact ⟨fullRankTaylor_localJet_kernel (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) b hb n,
    fullRankTaylor_surjective_localJet (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) b hb n⟩

lemma exactJets_injective [IsNoetherianRing S] [IsDomain S]
    (ρ : S →ₐ[ℂ] ℂ) (τ : S →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hk : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp τ.toRingHom) =
        (RingHom.ker ρ)^n) : Function.Injective τ := by
  apply (injective_iff_map_eq_zero τ).mpr
  intro s hs
  have hm : s ∈ ⨅ n : ℕ, (RingHom.ker ρ)^n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [← hk n]
    change Ideal.Quotient.mk _ (τ s) = 0
    rw [hs, map_zero]
  rwa [Ideal.iInf_pow_eq_bot_of_isDomain (I := RingHom.ker ρ)
    (RingHom.ker_ne_top _)] at hm

end
end MaximalSeshadri.AnalyticCoordinates

end


end
end

end OAI
