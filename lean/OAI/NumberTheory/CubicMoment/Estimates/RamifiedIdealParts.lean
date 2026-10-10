import OAI.NumberTheory.CubicMoment.Estimates.ConductorLocal
import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower

namespace OAI

/-! Exact separation of the finitely many primes above three in the
complete ideal lattice. No ramified Euler term is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def ramifiedPart (ν : EisensteinIdealExponent) : EisensteinIdealExponent :=
  ν.filter (fun p => p ∈ ramifiedIdealPrimes)

def unramifiedPart (ν : EisensteinIdealExponent) : EisensteinIdealExponent :=
  ν.filter (fun p => p ∉ ramifiedIdealPrimes)

lemma ramified_add_unramified (ν : EisensteinIdealExponent) :
    ramifiedPart ν+unramifiedPart ν = ν := Finsupp.filter_add_filter_not _ _

lemma unramifiedPart_primary (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator (unramifiedPart ν)) := by
  rw [idealPrimaryGenerator_primary_iff]
  intro p hp
  simp [unramifiedPart,hp]

lemma ramifiedPart_le (ν : EisensteinIdealExponent) : ramifiedPart ν ≤ ν := by
  intro p
  simp only [ramifiedPart,Finsupp.filter_apply]
  split <;> simp

lemma unramifiedPart_le (ν : EisensteinIdealExponent) : unramifiedPart ν ≤ ν := by
  intro p
  simp only [unramifiedPart,Finsupp.filter_apply]
  split <;> simp

lemma ramifiedPart_norm_le (ν : EisensteinIdealExponent) :
    idealExponentNorm (ramifiedPart ν) ≤ idealExponentNorm ν := by
  simpa only [idealExponentNorm,normNat_cast] using
    norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
      (idealExponentGenerator_dvd_of_le (ramifiedPart_le ν))

lemma idealExponent_exponent_bound {ν : EisensteinIdealExponent} {J : ℝ}
    (hν : idealExponentNorm ν ≤ J) (p : EisensteinIdealPrime) :
    ν p ≤ Nat.log 2 ⌊J⌋₊ := by
  have hsingle : Finsupp.single p (ν p) ≤ ν := Finsupp.single_le_iff.mpr le_rfl
  have hN := norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
    (idealExponentGenerator_dvd_of_le hsingle)
  have hpow : (2:ℝ)^(ν p) ≤ idealExponentNorm ν := by
    calc
      _ ≤ (normNat (idealPrimeRepresentative p):ℝ)^(ν p) :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast idealPrimeRepresentative_normNat_ge_two p) _
      _ = idealExponentNorm (Finsupp.single p (ν p)) := (idealExponentNorm_single _ _).symm
      _ ≤ idealExponentNorm ν := by simpa only [idealExponentNorm,normNat_cast] using hN
  apply Nat.le_log_of_pow_le (by norm_num)
  apply Nat.le_floor
  exact_mod_cast hpow.trans hν

lemma ramifiedPart_support (ν : EisensteinIdealExponent) {p : EisensteinIdealPrime}
    (hp : p ∉ ramifiedIdealPrimes) : ramifiedPart ν p = 0 := by
  simp [ramifiedPart,hp]

/-- The number of ramified parts in a full norm ball grows only as a
fixed power of the logarithm. -/
theorem ramified_parts_card_le {J : ℝ} :
    ((fullIdealBall J).image ramifiedPart).card ≤
      (Nat.log 2 ⌊J⌋₊+1)^ramifiedIdealPrimes.card := by
  let S := (fullIdealBall J).image ramifiedPart
  let M := Nat.log 2 ⌊J⌋₊+1
  let f : S → (ramifiedIdealPrimes → Fin M) := fun ν p =>
    ⟨ν.val p, Nat.lt_succ_of_le (idealExponent_exponent_bound
      (by
        obtain ⟨κ,hκ,hκν⟩ := Finset.mem_image.mp ν.property
        rw [← hκν]
        exact (ramifiedPart_norm_le κ).trans (mem_fullIdealBall.mp hκ)) p)⟩
  have hf : Function.Injective f := by
    intro ν κ he
    apply Subtype.ext
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ ramifiedIdealPrimes
    · exact congrArg Fin.val (congrFun he ⟨p,hp⟩)
    · obtain ⟨ν',hν',hν⟩ := Finset.mem_image.mp ν.property
      obtain ⟨κ',hκ',hκ⟩ := Finset.mem_image.mp κ.property
      rw [← hν,← hκ,ramifiedPart_support ν' hp,ramifiedPart_support κ' hp]
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hcard

def ramifiedParts (S : Finset EisensteinIdealExponent) : Finset EisensteinIdealExponent :=
  S.image ramifiedPart

def unramifiedFiber (S : Finset EisensteinIdealExponent) (ρ : EisensteinIdealExponent) :
    Finset EisensteinIdealExponent :=
  (S.filter (fun ν => ramifiedPart ν = ρ)).image unramifiedPart

lemma sum_unramifiedFiber (S : Finset EisensteinIdealExponent)
    (ρ : EisensteinIdealExponent) (f : EisensteinIdealExponent → ℂ) :
    (∑ κ ∈ unramifiedFiber S ρ, f (ρ+κ)) =
      ∑ ν ∈ S.filter (fun ν => ramifiedPart ν = ρ), f ν := by
  unfold unramifiedFiber
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ν hν
    rw [← (Finset.mem_filter.mp hν).2,ramified_add_unramified]
  · intro ν hν κ hκ he
    have hn := ramified_add_unramified ν
    have hk := ramified_add_unramified κ
    rw [(Finset.mem_filter.mp hν).2,he] at hn
    rw [(Finset.mem_filter.mp hκ).2] at hk
    exact hn.symm.trans hk

lemma ideal_sum_ramified_partition (S : Finset EisensteinIdealExponent)
    (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ S, f ν) = ∑ ρ ∈ ramifiedParts S, ∑ κ ∈ unramifiedFiber S ρ, f (ρ+κ) := by
  simp_rw [sum_unramifiedFiber]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun ν hν => Finset.mem_image_of_mem ramifiedPart hν) _).symm

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

/-- Exact separation of the ramified part in a normalized dual polynomial.
Each ramified character value is a row scalar; the inner support is prime
to three, with its precise rescaled normalization length. -/
theorem normalizedDualPolynomial_ramified_partition
    (S : Finset EisensteinIdealExponent) (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (J u : ℝ) :
    normalizedDualPolynomial S χ idealExponentNorm J u =
      ∑ ρ ∈ ramifiedParts S, (χ ρ*mellinPhase u (idealExponentNorm ρ))*
        normalizedDualPolynomial (unramifiedFiber S ρ) χ idealExponentNorm
          (J/idealExponentNorm ρ) u := by
  unfold normalizedDualPolynomial
  rw [ideal_sum_ramified_partition]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [hχ,idealExponentNorm_add,div_mul_eq_div_div,
    mellinPhase_mul_pos u (idealExponentNorm_pos ρ) (idealExponentNorm_pos κ)]
  ring

lemma unramifiedFiber_primary {S : Finset EisensteinIdealExponent}
    {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ unramifiedFiber S ρ) :
    primary (idealPrimaryGenerator κ) := by
  obtain ⟨ν,_,rfl⟩ := Finset.mem_image.mp hκ
  exact unramifiedPart_primary ν

lemma ramifiedParts_card_le {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ J) :
    (ramifiedParts S).card ≤ (Nat.log 2 ⌊J⌋₊+1)^ramifiedIdealPrimes.card := by
  apply (Finset.card_le_card (Finset.image_subset_image (fun ν hν => mem_fullIdealBall.mpr (hS ν hν)))).trans
  exact ramified_parts_card_le

lemma unramifiedFiber_norm {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*J)
    {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ unramifiedFiber S ρ) :
    J/idealExponentNorm ρ ≤ idealExponentNorm κ ∧
      idealExponentNorm κ ≤ (2*J)/idealExponentNorm ρ := by
  obtain ⟨ν,hν,hκν⟩ := Finset.mem_image.mp hκ
  obtain ⟨hνS,hνρ⟩ := Finset.mem_filter.mp hν
  have hn : idealExponentNorm ν = idealExponentNorm ρ*idealExponentNorm κ := by
    rw [← ramified_add_unramified ν,idealExponentNorm_add,hνρ,hκν]
  constructor
  · exact (div_le_iff₀ (idealExponentNorm_pos ρ)).mpr (by simpa [mul_comm,← hn] using (hS ν hνS).1)
  · exact (le_div_iff₀ (idealExponentNorm_pos ρ)).mpr (by simpa [mul_comm,← hn] using (hS ν hνS).2)

lemma ramifiedPart_norm_le_upper {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ 2*J)
    {ρ : EisensteinIdealExponent} (hρ : ρ ∈ ramifiedParts S) :
    1 ≤ (2*J)/idealExponentNorm ρ := by
  obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hρ
  apply (le_div_iff₀ (idealExponentNorm_pos _)).mpr
  simpa only [one_mul] using (ramifiedPart_norm_le ν).trans (hS ν hν)

end CubicFirstMoment

end

end OAI
