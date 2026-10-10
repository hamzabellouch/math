import OAI.Analysis.KadisonKastler.SimpleExtensionClosure
import OAI.Analysis.KadisonKastler.GeneratedDerivationExtension
import OAI.Analysis.KadisonKastler.HermitianSeparation
import OAI.Analysis.KadisonKastler.SignedCyclicFunctional
import OAI.Analysis.KadisonKastler.ExtremeDerivationFactor
import OAI.Analysis.KadisonKastler.DerivationCyclicPowers

namespace OAI

/-! # Innerness of bounded derivations of simple unital C-star algebras

The maximal simple extension, extreme Hermitian separator, spatial factor
splitting and faithful-corner norm argument together prove the precise
unital input used in the stability application.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial
open scoped InnerProductSpace

universe u

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]

theorem simple_extension_implementer_mem_range
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (d : B) (hdsa : IsSelfAdjoint d) (hgen : NormGeneratedExtension φ d)
    (hB : ∀ (C : Type u) [CStarAlgebra C] [Nontrivial C]
      (ψ : B →⋆ₐ[ℂ] C), Function.Injective ψ)
    (D : A →L[ℂ] A) (hd : ∀ a, φ (D a) = d * φ a - φ a * d) :
    d ∈ Set.range φ := by
  by_contra hnot
  obtain ⟨F, hF, hFn, hFd⟩ := exists_extreme_hermitian_separator φ hφ d hdsa hnot
  have hFm := (mem_extremePoints.mp hF).1
  obtain ⟨H, hHn, hHi, hHc, π, ξ, S, hξ, hcyc, hS, hSS, hSπ, hcoeff⟩ :=
    exists_signed_cyclic_functional F.toStrongDual hFm.2.1 hFn
  let : NormedAddCommGroup H := hHn
  let : InnerProductSpace ℂ H := hHi
  let : CompleteSpace H := hHc
  let : Nontrivial H := by
    by_contra h
    have : Subsingleton H := not_nontrivial_iff_subsingleton.mp h
    have he : ξ = 0 := Subsingleton.elim _ _
    simp only [he, norm_zero] at hξ
    norm_num at hξ
  have hrep : F.toStrongDual = signedVectorFunctional π S ξ := by
    ext b
    exact hcoeff b
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  have hN : ScalarCenter N := factor_of_extreme_signed_derivation_extension
    φ d hgen D hd F hF π ξ hξ hcyc S hS hSS hSπ hrep
  have hfamilies := derivation_extension_commutant_countable φ d hdsa hgen D hd π ξ hcyc
  have hsource : ∀ a : (π.comp φ).range,
      π d * a.val - a.val * π d ∈ N := by
    intro a
    obtain ⟨b, hb⟩ := a.property
    change π (φ b) = a.val at hb
    rw [← hb, ← map_mul, ← map_mul, ← map_sub, ← hd]
    exact subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨D b, rfl⟩
  have hnorm : ∀ a ∈ N, π d * a - a * π d ∈ N :=
    spatial_commutator_mem_generated (π.comp φ).range (π d) hsource
  obtain ⟨a, ha, hasa, _, hb⟩ := exists_selfAdjoint_split_of_factor N hN hfamilies
    (π d) (hdsa.map π) hnorm
  have hdN := extension_implementer_mem_of_spatial_split φ d hdsa hgen hB π hN a ha hasa hb
  have hann : ∀ a : (π.comp φ).range, inner ℂ (S ξ) (a.val ξ) = 0 := by
    intro a
    obtain ⟨b, hb⟩ := a.property
    change π (φ b) = a.val at hb
    rw [← hb, ← hcoeff]
    exact hFm.2.2 b
  have hz := coefficient_zero_generated (π.comp φ).range ξ (S ξ) hann (π d) hdN
  exact hFd ((hcoeff d).trans hz)

theorem antiStar_derivation_inner_of_simple [Nontrivial A]
    (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ a : A, ∀ x, D x = a * x - x * a := by
  obtain ⟨B, hBc, hBn, φ, d, hφ, hdsa, hd, hgen, hB⟩ :=
    exists_generated_derivation_extension hA D hD hstar
  let : CStarAlgebra B := hBc
  let : Nontrivial B := hBn
  obtain ⟨a, ha⟩ := simple_extension_implementer_mem_range φ hφ d hdsa hgen hB D hd
  refine ⟨a, fun x => hφ ?_⟩
  rw [hd, map_sub, map_mul, map_mul, ha]

theorem publishedSimpleDerivationInner : PublishedSimpleDerivationInner.{u} := by
  intro A _ _ hA D hD
  exact inner_derivation_of_antiStar_inner
    (fun F hF hFs => antiStar_derivation_inner_of_simple hA F hF hFs) D hD

end

end KadisonKastler

end OAI
