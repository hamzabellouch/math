import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusSplitting
import OAI.NumberTheory.PrimePackets.SplitEuler

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.Unfinished

theorem actual_frobenius_nonprincipal
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (hχ : χ ≠ 1) (N : ℕ) (hN : 0 < N) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsCoprime P.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) ∧
      χ (GaloisIdealCharacter.primeFrobenius F E P) ≠ 1 := by
  classical
  by_contra h
  push Not at h
  let L : IntermediateField F E := IntermediateField.fixedField χ.ker
  have hL : IsGalois F L := inferInstance
  have hχL : L ≠ ⊥ := by
    intro he
    have hk := IntermediateField.fixingSubgroup_fixedField χ.ker
    change L.fixingSubgroup = χ.ker at hk
    rw [he, IntermediateField.fixingSubgroup_bot] at hk
    apply hχ
    apply DFunLike.ext
    intro σ
    have hm : σ ∈ χ.ker := hk ▸ Subgroup.mem_top σ
    exact hm
  let D := (NumberField.discr L).natAbs
  have hD : D ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)
  let S : Finset Nat.Primes := (N * D).primeFactors.subtype Nat.Prime
  have hloc (p : Nat.Primes) (hp : p ∉ S) (s : ℂ) (_hs : 1 < s.re) :
      primeIdealEulerFactor L p s = primeIdealEulerFactor F p s ^ finrank F L := by
    have hpd : ¬ p.val ∣ N * D := by
      intro hd
      apply hp
      exact (Finset.mem_subtype (a := (⟨p.val, p.property⟩ : Subtype Nat.Prime))).mpr
        (Nat.mem_primeFactors.mpr ⟨p.property, hd, mul_ne_zero (ne_of_gt hN) hD⟩)
    have hpN : p.val.Coprime N := p.property.coprime_iff_not_dvd.mpr
      (fun hd => hpd (dvd_mul_of_dvd_left hd D))
    have hpD : p.val.Coprime D := p.property.coprime_iff_not_dvd.mpr
      (fun hd => hpd (dvd_mul_of_dvd_right hd N))
    have hsplit (P : idealsOverPrime F p) :
        Nat.card (Ideal.primesOver P.val (𝓞 L)) = finrank F L ∧
        ∀ Q : Ideal.primesOver P.val (𝓞 L), Ideal.absNorm Q.val = Ideal.absNorm P.val := by
      have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
      let : P.val.IsPrime := hP.1
      have hP0 : P.val ≠ ⊥ := by
        intro he
        rw [he, Ideal.mem_bot] at hP
        exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)
      let PP : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P.val, hP.1, hP0⟩
      have hcop : IsCoprime PP.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
        apply Ideal.isCoprime_iff_codisjoint.mpr
        apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
        exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hpN.cast).codisjoint
      have hχP := h PP hcop
      let Q := GaloisIdealCharacter.primeAbove F L PP
      let : Q.val.IsPrime := Q.property.1
      let : Q.val.LiesOver PP.asIdeal := Q.property.2
      have hf := GaloisIdealCharacter.inertiaDeg_eq_one_kernelFixedField F E χ PP hχP Q.val
      let : Algebra.IsUnramifiedAt (𝓞 F) Q.val :=
        unramified_of_absDiscr_not_mem F L PP.asIdeal Q.val (Q.val.over_def PP.asIdeal).symm
          (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast hP.2)
      refine ⟨GaloisIdealCharacter.card_primesOver_of_unramified_of_inertia_one F L PP Q.val hf, ?_⟩
      intro R
      let : R.val.IsPrime := R.property.1
      let : R.val.LiesOver PP.asIdeal := R.property.2
      exact GaloisIdealCharacter.norm_eq_of_inertiaDeg_eq_one F L PP Q.val hf R.val
    exact primeIdealEulerFactor_eq_pow F L p.property.ne_zero (finrank F L) s
      (fun P => (hsplit P).1) (fun P => (hsplit P).2)
  have hdegree := degree_eq_one_of_localEulerFactor_eq_pow F L (finrank F L)
    Module.finrank_pos S hloc
  exact hχL (IntermediateField.finrank_eq_one_iff.mp hdegree)

end PrimeDegreePackets.Unfinished

end

end OAI
