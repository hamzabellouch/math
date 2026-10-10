import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem minimalPrimeCutSum_quotient (I : Ideal A) (x : A) :
    minimalPrimeCutSum I x =
      minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) := by
  classical
  let : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  let : Fintype (minimalPrimes (A ⧸ I)) :=
    ((⊥ : Ideal (A ⧸ I)).finite_minimalPrimes_of_isNoetherianRing (A ⧸ I)).fintype
  symm
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (quotientMinimalPrimesEquiv I)
  intro Q
  let P := (quotientMinimalPrimesEquiv I Q).val
  let : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : P.map (Ideal.Quotient.mk I) = Q.val :=
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hc := quotient_prime_cut_length I P hIP x
  rw [hmap] at hc
  exact congrArg₂ HMul.hMul (quotient_minimal_local_length I Q).symm hc.symm

omit [IsNoetherianRing A] in
theorem quotient_parameter_mem_nonZeroDivisors (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Ideal.Quotient.mk I x ∈ nonZeroDivisors (A ⧸ I) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro y hy
  apply hregular
  change x • y = x • (0 : A ⧸ I)
  rw [smul_zero, Algebra.smul_def]
  exact hy

theorem local_onecut_length [IsLocalRing A]
    (I : Ideal A) (x : A) (hdim : ringKrullDim (A ⧸ I) = 1)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x := by
  have hnot : ¬ Subsingleton (A ⧸ I) := by
    intro hsub
    let := hsub
    have hbot : ringKrullDim (A ⧸ I) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
    rw [hdim] at hbot
    exact WithBot.one_ne_bot hbot
  let : Nontrivial (A ⧸ I) := not_subsingleton_iff_nontrivial.mp hnot
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 (A ⧸ I) := Ring.krullDimLE_iff.mpr hdim.le
  calc
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
        Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) :=
      quotient_principal_cut_length I x
    _ = minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) :=
      regular_ring_onecut_length _ (quotient_parameter_mem_nonZeroDivisors I x hregular)
    _ = minimalPrimeCutSum I x := (minimalPrimeCutSum_quotient I x).symm

theorem localOneCutLengthStatement_proved [IsLocalRing A] :
    LocalOneCutLengthStatement A := by
  intro I x hdim hregular _hprimary _hradical
  exact local_onecut_length I x hdim hregular

end PiExponentJets.W28.LocalIntersection

end OAI
