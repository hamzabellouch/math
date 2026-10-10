import OAI.NumberTheory.DirichletL.Moments.Bridge

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentInitial
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentBridge

variable {ι : Type*}

abbrev activeModulus (P : ι → Ideal O) (B : Finset ι) (c d : ι → ℕ) : O :=
  finitePrimeModulus (fun i : CenteredMomentActive.activeSupport B c d => P i.val)

def commonCharacter (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (B : Finset ι) (c d : ι → ℕ) : MulChar (Residue (activeModulus P B c d)) ℂ :=
  primitiveCharacter (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))

theorem activeModulus_ne_zero (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) : activeModulus P B c d ≠ 0 :=
  finitePrimeModulus_ne_zero _

theorem activeModulus_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) (v : O)
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {v})) :
    IsCoprime (activeModulus P B c d) v := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [activeModulus, span_finitePrimeModulus]
  apply IsCoprime.prod_left
  intro i _
  exact hcop i.val (Finset.mem_filter.mp i.property).1

theorem allocated_pair_factor (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (z : O) :
    idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b})) =
      rowCoprimeMask P (CenteredMomentActive.principalSupport B c d) z *
      (commonCharacter P hinj hg B c d (Ideal.Quotient.mk _ z) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ z) *
        star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ z))) := by
  calc
    _ = (idealRowHom z (∏ i ∈ B, P i ^ c i) *
        star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
        (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) := by
      rw [map_mul, map_mul, star_mul]
      ring
    _ = _ := by
      rw [CenteredMomentActive.common_ideal_pair_active P hg hchar B c d hc hd]
      simp only [commonCharacter, primitiveCharacter_mk, supportedModulusCharacter_mk]
      ring

theorem allocated_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {a * b})) (hab : IsCoprime a b)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let r := activeModulus P B c d
    let ξ := commonCharacter P hinj hg B c d
    let χa := supportedModulusCharacter a ha
    let χb := supportedModulusCharacter b hb
    (∑' z : O, (idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b}))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ (CenteredMomentActive.principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r (activeModulus_ne_zero P B c d) ξ (Ideal.Quotient.mk _ j) *
          residueGauss a (supported_element_ne_zero a ha) χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b (supported_element_ne_zero b hb) χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  simp_rw [allocated_pair_factor P hinj hg hchar B c d hc hd a b ha hb]
  exact masked_triple_pair_poisson P hinj (CenteredMomentActive.principalSupport B c d)
    (activeModulus P B c d) a b (activeModulus_ne_zero P B c d)
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (activeModulus_coprime P B c d (a * b) hcop) hab
    (commonCharacter P hinj hg B c d) (supportedModulusCharacter a ha)
    (supportedModulusCharacter b hb) W K hK

theorem common_gauss_norm_le_one (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ) (h : O) :
    ‖normalizedResidueGauss (activeModulus P B c d) (activeModulus_ne_zero P B c d)
      (commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h)‖ ≤ 1 :=
  normalized_primitive_gauss_norm_le_one
    (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))
    (CenteredMomentActive.netExponent_ne_zero B c d)
    (fun _i => CenteredMomentActive.netExponent_lt_six _ _) h

end SevenEighths.CenteredMomentInitial
end

end OAI
