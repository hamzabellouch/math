import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LocalBinaryPrime
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtalePointChart

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing MvPolynomial
open MaximalSeshadri.AlgebraicJets

local instance residueKernelIsPrime {Scalar CoordinateRing : Type}
    [Field Scalar] [CommRing CoordinateRing] [Algebra Scalar CoordinateRing]
    (residue : CoordinateRing →ₐ[Scalar] Scalar) : (RingHom.ker residue).IsPrime :=
  RingHom.ker_isPrime residue

theorem standard_smooth_binary_maximal {K S : Type} [Field K] [CommRing S] [Algebra K S]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K) :
    ∃ a b : Localization.AtPrime (RingHom.ker ρ),
      maximalIdeal (Localization.AtPrime (RingHom.ker ρ)) = Ideal.span {a,b} := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2 (R := K) (S := S)
  let q := RingHom.ker ρ
  have hp : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  have H := unramified_map_under_local (R := MvPolynomial (Fin 2) K) q
  rw [hp,IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q),
    Ideal.map_span,← Set.range_comp] at H
  have hr : Set.range ((algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q)) ∘ X) =
      {algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q) (X 0),
       algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q) (X 1)} := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with h | h
      · exact ⟨0,h.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp h).symm⟩
  rw [hr] at H
  exact ⟨_,_,H.symm⟩

theorem spread_principal_prime {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I q : Ideal S) [I.IsPrime] [q.IsPrime]
    (hI : (I.map (algebraMap S (Localization.AtPrime q))).IsPrincipal) :
    ∃ c : S, c ∈ I ∧ ∃ s : S, s ∉ q ∧
      I.map (algebraMap S (Localization.Away s)) =
      Ideal.span {algebraMap S (Localization.Away s) c} := by
  obtain ⟨u,hu⟩ := hI
  have hum : u ∈ I.map (algebraMap S (Localization.AtPrime q)) := by
    rw [hu]; exact Ideal.subset_span (by simp)
  obtain ⟨⟨c,d⟩,hcd⟩ := (IsLocalization.mem_map_algebraMap_iff q.primeCompl
    (Localization.AtPrime q)).mp hum
  have he : I.map (algebraMap S (Localization.AtPrime q)) =
      (Ideal.span {c.val}).map (algebraMap S (Localization.AtPrime q)) := by
    rw [hu,Ideal.map_span,Set.image_singleton,← hcd,
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units (Localization.AtPrime q) d)]
  obtain ⟨s,hs,hseq⟩ := exists_away_map_eq_of_le I (Ideal.span {c.val}) q
    (Ideal.fg_of_isNoetherianRing I) (Ideal.span_le.mpr (by simp)) he
  exact ⟨c.val,c.property,s,hs,by simpa only [Ideal.map_span,Set.image_singleton] using hseq⟩

theorem standard_smooth_prime_principal_neighborhood {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) (I : Ideal S) [hI : I.IsPrime]
    (hle : I ≤ RingHom.ker ρ) (hne : I ≠ RingHom.ker ρ) :
    ∃ c : S, c ∈ I ∧ ∃ s : S, ρ s ≠ 0 ∧
      I.map (algebraMap S (Localization.Away s)) =
      Ideal.span {algebraMap S (Localization.Away s) c} := by
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2 (R := K) (S := S)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let q := RingHom.ker ρ
  have hdis : Disjoint (q.primeCompl : Set S) I :=
    Set.disjoint_left.mpr (fun _ hq hi => hq (hle hi))
  let : (I.map (algebraMap S (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) I hI hdis
  obtain ⟨a,b,hm⟩ := standard_smooth_binary_maximal ρ
  have hneq : I.map (algebraMap S (Localization.AtPrime q)) ≠ maximalIdeal (Localization.AtPrime q) := by
    intro H
    apply hne
    have HH := congrArg (Ideal.comap (algebraMap S (Localization.AtPrime q))) H
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)] at HH
    change (I.map _).under S = (q.map _).under S at HH
    rw [IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) hI hdis,
      IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q)
        (inferInstance : q.IsPrime) (Set.disjoint_left.mpr (fun _ hx hy => hx hy))] at HH
    exact HH
  have hp := prime_principal_of_binary_maximal a b hm
    (I.map (algebraMap S (Localization.AtPrime q))) hneq
  obtain ⟨c,hc,s,hs,he⟩ := spread_principal_prime I q hp
  exact ⟨c,hc,s,hs,he⟩
end
end MaximalSeshadri.LocalCurve

end

end OAI
