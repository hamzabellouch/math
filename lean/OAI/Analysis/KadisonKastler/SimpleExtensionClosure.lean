import OAI.Analysis.KadisonKastler.CommutantScalarFromNorm
import OAI.Analysis.KadisonKastler.FaithfulReducingNorm
import OAI.Analysis.KadisonKastler.DerivationExtensionFactor

namespace OAI

/-! # A spatially split simple extension lies in the source weak closure -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

universe u

variable {A B H : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem extension_implementer_mem_of_spatial_split
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hdsa : IsSelfAdjoint d)
    (hgen : NormGeneratedExtension φ d)
    (hB : ∀ (C : Type u) [CStarAlgebra C] [Nontrivial C]
      (ψ : B →⋆ₐ[ℂ] C), Function.Injective ψ)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hN : ScalarCenter (generatedVonNeumannAlgebra (π.comp φ).range))
    (a : H →L[ℂ] H) (ha : a ∈ generatedVonNeumannAlgebra (π.comp φ).range)
    (hasa : IsSelfAdjoint a)
    (hb : π d - a ∈ (generatedVonNeumannAlgebra (π.comp φ).range).commutant) :
    π d ∈ generatedVonNeumannAlgebra (π.comp φ).range := by
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  let b := π d - a
  have hbsa : IsSelfAdjoint b := (hdsa.map π).sub hasa
  let x := a + ‖a‖ • (1 : H →L[ℂ] H)
  let y := b + ‖b‖ • (1 : H →L[ℂ] H)
  have hx : 0 ≤ x := by
    have hh := hasa.neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one] at hh
    simpa only [add_comm] using neg_le_iff_add_nonneg.mp hh
  have hy : 0 ≤ y := by
    have hh := hbsa.neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one] at hh
    simpa only [add_comm] using neg_le_iff_add_nonneg.mp hh
  have hxN : x ∈ N := N.add_mem ha (real_smul_one_mem_vonNeumann N ‖a‖)
  have hyN : y ∈ N.commutant := N.commutant.add_mem hb (real_smul_one_mem_vonNeumann N.commutant ‖b‖)
  have hscalar : y = ‖y‖ • 1 := by
    apply positive_commutant_scalar_of_corner_norm N hN x y hxN hyN hx hy
    intro p hp0 hpy
    let E := typeIIIInitialSpace p
    have hp : IsStarProjection p.val.val := p.property.map N.commutant.toStarSubalgebra.subtype
    have hpv : p.val.val ≠ 0 := fun h => hp0 (Subtype.ext h)
    let : Nontrivial E := nontrivial_projection_range p.val.val hp hpv
    have hpa : Commute p.val.val a :=
      (VonNeumannAlgebra.mem_commutant_iff.mp p.val.property a ha).symm
    have hpb : Commute p.val.val b := by
      change p.val.val * (b + ‖b‖ • 1) = (b + ‖b‖ • 1) * p.val.val at hpy
      change p.val.val * b = b * p.val.val
      simpa only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
        add_left_inj] using hpy
    have hpd : Commute p.val.val (π d) := by
      have he : π d = a + b := by dsimp [b]; abel
      rw [he]
      exact hpa.add_right hpb
    have hpA : ∀ c, Commute p.val.val (π (φ c)) := by
      intro c
      exact (VonNeumannAlgebra.mem_commutant_iff.mp p.val.property _
        (subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨c, rfl⟩)).symm
    have hpB := commutes_of_normGeneratedExtension φ d hgen π p.val.val
      hp.isSelfAdjoint hpA hpd
    have hE : ∀ c, E.starProjection * π c = π c * E.starProjection := by
      intro c
      rw [← typeIIIInitialSpace_projection p]
      exact (hpB c).eq
    let d₀ := d + ((‖a‖ + ‖b‖ : ℝ) : ℂ) • (1 : B)
    have hvalue : π d₀ = x + y := by
      dsimp only [d₀, x, y, b]
      rw [map_add, map_smul, map_one, Complex.coe_smul, add_smul]
      abel
    have hn := norm_reducingRepresentation E π hE hB d₀
    simpa only [hvalue] using hn
  have hyM : y ∈ N := by
    rw [hscalar]
    exact real_smul_one_mem_vonNeumann N ‖y‖
  have hbM : b ∈ N := by
    have hh := N.sub_mem hyM (real_smul_one_mem_vonNeumann N ‖b‖)
    have he : y - ‖b‖ • 1 = b := by dsimp [y]; abel
    rwa [he] at hh
  have hh := N.add_mem ha hbM
  have he : a + b = π d := by dsimp [b]; abel
  rwa [he] at hh

end

end KadisonKastler

end OAI
