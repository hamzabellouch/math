import OAI.NumberTheory.CubicMoment.Estimates.SmallPrimeParts

namespace OAI

/-! Exact separation of the primes of an arbitrary nonzero modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma supportedIdealPart_norm_le (v : Eisenstein) (ν : EisensteinIdealExponent) :
    idealExponentNorm (supportedIdealPart v ν) ≤ idealExponentNorm ν := by
  simpa only [idealExponentNorm,normNat_cast] using
    norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
      (idealExponentGenerator_dvd_of_le (supportedIdealPart_le v ν))

lemma outsideIdealPart_primary {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    (ν : EisensteinIdealExponent) : primary (idealPrimaryGenerator (outsideIdealPart v ν)) := by
  rw [idealPrimaryGenerator_primary_iff]
  intro p hp
  have hle := idealExponentOf_le_of_dvd (by norm_num : (3:Eisenstein) ≠ 0) hv h3
  have hpin : p ∈ (idealExponentOf v).support := Finsupp.mem_support_iff.mpr (by
    have hp3 := Finsupp.mem_support_iff.mp hp
    have h := hle p
    omega)
  have hne := Finsupp.mem_support_iff.mp hpin
  simp [outsideIdealPart,hne]

lemma outsideIdealPart_coprime {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    (ν : EisensteinIdealExponent) : IsCoprime (idealPrimaryGenerator (outsideIdealPart v ν)) v := by
  rw [isCoprime_iff_idealExponent_disjoint
    (primary_ne_zero (outsideIdealPart_primary hv h3 ν)) hv,idealExponentOf_primaryGenerator]
  intro p
  by_cases hp : p ∈ (idealExponentOf v).support
  · left
    have hne := Finsupp.mem_support_iff.mp hp
    simp [outsideIdealPart,hne]
  · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

def supportedParts (v : Eisenstein) (S : Finset EisensteinIdealExponent) : Finset EisensteinIdealExponent :=
  S.image (supportedIdealPart v)

def outsideFiber (v : Eisenstein) (S : Finset EisensteinIdealExponent) (ρ : EisensteinIdealExponent) :
    Finset EisensteinIdealExponent :=
  (S.filter (fun ν => supportedIdealPart v ν = ρ)).image (outsideIdealPart v)

lemma sum_outsideFiber (v : Eisenstein) (S : Finset EisensteinIdealExponent)
    (ρ : EisensteinIdealExponent) (f : EisensteinIdealExponent → ℂ) :
    (∑ κ ∈ outsideFiber v S ρ, f (ρ+κ)) =
      ∑ ν ∈ S.filter (fun ν => supportedIdealPart v ν = ρ), f ν := by
  unfold outsideFiber
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ν hν
    rw [← (Finset.mem_filter.mp hν).2,supported_add_outside]
  · intro ν hν κ hκ he
    have hn := supported_add_outside v ν
    have hk := supported_add_outside v κ
    rw [(Finset.mem_filter.mp hν).2,he] at hn
    rw [(Finset.mem_filter.mp hκ).2] at hk
    exact hn.symm.trans hk

lemma ideal_sum_supported_partition (v : Eisenstein) (S : Finset EisensteinIdealExponent)
    (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ S, f ν) = ∑ ρ ∈ supportedParts v S, ∑ κ ∈ outsideFiber v S ρ, f (ρ+κ) := by
  simp_rw [sum_outsideFiber]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun ν hν => Finset.mem_image_of_mem (supportedIdealPart v) hν) _).symm

 theorem normalizedDualPolynomial_supported_partition
    (v : Eisenstein) (S : Finset EisensteinIdealExponent) (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (J u : ℝ) :
    normalizedDualPolynomial S χ idealExponentNorm J u =
      ∑ ρ ∈ supportedParts v S, (χ ρ*mellinPhase u (idealExponentNorm ρ))*
        normalizedDualPolynomial (outsideFiber v S ρ) χ idealExponentNorm
          (J/idealExponentNorm ρ) u := by
  unfold normalizedDualPolynomial
  rw [ideal_sum_supported_partition v]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [hχ,idealExponentNorm_add,div_mul_eq_div_div,
    mellinPhase_mul_pos u (idealExponentNorm_pos ρ) (idealExponentNorm_pos κ)]
  ring

lemma outsideFiber_primary {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    {S : Finset EisensteinIdealExponent} {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ outsideFiber v S ρ) :
    primary (idealPrimaryGenerator κ) := by
  obtain ⟨ν,_,rfl⟩ := Finset.mem_image.mp hκ
  exact outsideIdealPart_primary hv h3 ν

lemma outsideFiber_coprime {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    {S : Finset EisensteinIdealExponent} {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ outsideFiber v S ρ) :
    IsCoprime (idealPrimaryGenerator κ) v := by
  obtain ⟨ν,_,rfl⟩ := Finset.mem_image.mp hκ
  exact outsideIdealPart_coprime hv h3 ν

lemma outsideFiber_norm {v : Eisenstein} {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*J)
    {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ outsideFiber v S ρ) :
    J/idealExponentNorm ρ ≤ idealExponentNorm κ ∧
      idealExponentNorm κ ≤ (2*J)/idealExponentNorm ρ := by
  obtain ⟨ν,hν,hκν⟩ := Finset.mem_image.mp hκ
  obtain ⟨hνS,hνρ⟩ := Finset.mem_filter.mp hν
  have hn : idealExponentNorm ν = idealExponentNorm ρ*idealExponentNorm κ := by
    rw [← supported_add_outside v ν,idealExponentNorm_add,hνρ,hκν]
  constructor
  · exact (div_le_iff₀ (idealExponentNorm_pos ρ)).mpr (by simpa [mul_comm,← hn] using (hS ν hνS).1)
  · exact (le_div_iff₀ (idealExponentNorm_pos ρ)).mpr (by simpa [mul_comm,← hn] using (hS ν hνS).2)

lemma supportedPart_norm_le_upper {v : Eisenstein} {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ 2*J)
    {ρ : EisensteinIdealExponent} (hρ : ρ ∈ supportedParts v S) :
    1 ≤ (2*J)/idealExponentNorm ρ := by
  obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hρ
  apply (le_div_iff₀ (idealExponentNorm_pos _)).mpr
  simpa only [one_mul] using (supportedIdealPart_norm_le v ν).trans (hS ν hν)

end CubicFirstMoment

end

end OAI
