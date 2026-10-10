import OAI.NumberTheory.DirichletL.PrimeRows.BufferedBin
import OAI.NumberTheory.DirichletL.Detector.RayPhaseAmplitude
import OAI.NumberTheory.DirichletL.PrimeRows.PrincipalMask
import OAI.NumberTheory.DirichletL.PrimeRows.Conductor
import OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
import OAI.NumberTheory.DirichletL.Hecke.PrimeScale
import OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeRayCharacterFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def fixedTwistSupport : Finset (Ideal O) :=
  (normalizedFactors (M*Ideal.span {rowMaskElement}*Ideal.span {(72:O)})).toFinset

omit [NeZero M] in
theorem fixedTwistSupport_prime : ∀P∈fixedTwistSupport M,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_twist_base_modulus (θ : RayQuotient.Characters M H) :
    ((fixedSourcePrincipal ∅ (by simp)).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change (1:Ideal O)⊓M=M
  simp

theorem large_supported_twists_nonprincipal (u : FreeRow)
    (hs : Supported (Ideal.span {u.val}))
    (hl : (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ)<rowNorm u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hs
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by simp [r]
  let η := (fixedSourcePrincipal ∅ (by simp)).product
    (HeckeRayQuotient.character M H hH θ).inverse
  let χ := (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).inverse
  have hχ : ∀n,elementCoeff χ n=rowTwist (HeckeRowClosure.elementHom η) rowMaskElement 1 u.val n :=
    HeckePrimeNonprincipal.inverse_twist_elementCoeff _ _ _ _ _ _ (rawRow_elementCoeff u)
  intro hp
  have hprincipal : χ.residue=1 := by
    change (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue⁻¹=1
    exact congrArg Inv.inv hp |>.trans inv_one
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η χ rowMaskElement 1 u.val
    rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx hχ hprincipal
    (fun P _=>hspan.symm ▸ u.property.2 P)
  have hη : η.modulus=M := inverse_twist_base_modulus M H hH θ
  rw [hη] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (fixedTwistSupport M) (fixedTwistSupport_prime M) hfixed
  rw [hspan] at hn
  exact not_lt_of_ge (show rowNorm u≤(HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ) by unfold rowNorm;exact_mod_cast hn) hl

theorem raw_twisted_conductor (u : FreeRow) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm≤
      conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm := by
  have ht := HeckePrimeScale.twisted_modulus_bound M H hH (rawRow u).inverse θ
  change _≤(rawRow u).modulus.absNorm*M.absNorm at ht
  exact ht.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using
    Nat.mul_le_mul_right M.absNorm (rawRow_conductor u))
omit [NeZero M] in
theorem canonical_amplitude_raw (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (W : ℝ→ℂ) (a b D : ℝ)
    (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hsmall : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (rawRow u).inverse W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hp := (Finset.mem_filter.mp hP).2.1
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp [hw]
  have hPS : P∉S := by
    intro hPS
    have hh := (lt_div_iff₀ hD).mp (hW hw).1
    have := hsmall P hPS
    linarith
  rw [idealCoeff_inverse_conj,rawRow_prime_outside S hS hbad u ⟨P,hp⟩ hPS]
  exact mul_assoc _ _ _

omit H hH in
theorem large_supported_twists_eventually (d : ℝ) (hd : 0<d) :
    ∀ᶠZ : ℝ in Filter.atTop,∀u : FreeRow,Z^d≤rowNorm u →
      Supported (Ideal.span {u.val}) → ∀(H : Subgroup (O ⧸ M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H) (θ : RayQuotient.Characters M H),
      (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (Filter.eventually_gt_atTop (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ))]
    with Z hZ u hu hs H hH θ
  exact large_supported_twists_nonprincipal M H hH u hs (hZ.trans_le hu) θ

omit M H hH in
theorem source_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→Character) (T : ℝ) :
    detectorMaximum ψ T≤detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum ψ T) with hm|hm
  · obtain ⟨j,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained ψ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum (sourceDetectorFamily S hS η u ψ) T (Sum.inr j)
      (by rw [heq];exact hm.le) ht hz hpole
  · exact hm.trans (detectorMaximum_bounds _ T).1

omit M H hH in
theorem source_nonprincipal_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→Character) (hψ : ∀j,(ψ j).residue≠1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum ψ hψ T≤detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rw [←detectorMaximum_eq_nonprincipal ψ hψ T]
  exact source_maximum_dominates S hS η u ψ T

end SevenEighths.ProbeRayCharacterFamily

end

end OAI
