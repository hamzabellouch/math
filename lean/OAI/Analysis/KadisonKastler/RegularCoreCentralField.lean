import OAI.Analysis.KadisonKastler.RegularFourierTransport
import OAI.Analysis.KadisonKastler.RegularFieldMembership
import OAI.Analysis.KadisonKastler.PublishedRegularDiagonal
import OAI.Analysis.KadisonKastler.RegularCoreIntersection
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition

namespace OAI

/-! # Fourier fields of central elements in the actual regular core -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
  (P : VonNeumannAlgebra H)

/-- Centrality supplies diagonal decomposition after Fourier transform;
countable commutant tests put its fibers in the original algebra. The
only inputs are the separate published spectral and diagonal theorems. -/
theorem regularCore_central_fourier_field
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU P)
    (hcentral : ∀ S ∈ regularCoreAlgebra U hU P, S * T = T * S) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ᵐ t ∂volume, ‖F t‖ ≤ ‖T‖) ∧ (∀ᵐ t ∂volume, F t ∈ P) ∧
      RepresentsOperatorField volume F ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T) := by
  let Φ := (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
  have hchar (a : ℝ) : Commute (Φ T)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    let s : ℝ := a / (2 * Real.pi)
    have hs : 2 * Real.pi * s = a := by dsimp [s]; field_simp
    have he := congrArg Φ (hcentral _ (regularTranslation_mem_core U hU P
      (Multiplicative.ofAdd s)))
    simp only [map_mul, Φ, fourierConj_regularTranslation, hs] at he
    exact he.symm
  obtain ⟨F, hFm, hFn, hFT⟩ := hDiagonal H (Φ T) (hSpectral H (Φ T) hchar)
  have htensor : Φ T ∈ regularTensorAlgebra P := by
    apply (mem_regularTensorAlgebra_iff P _).mpr
    intro b hb
    have he := congrArg Φ ((mem_regularTensorAlgebra_iff P T).mp
      (regularCoreAlgebra_le_tensor U hU P hP hT) b hb)
    simpa only [map_mul, Φ, fourierConj_regularConstantHom] using he
  refine ⟨F, hFm, ?_, hFT.mem_algebra_ae P htensor, hFT⟩
  have hn : ‖Φ T‖ = ‖T‖ := StarAlgEquiv.norm_map Φ T
  rwa [hn] at hFn

omit [TopologicalSpace.SeparableSpace H] in
/-- Fixed operators have constant regular embeddings. -/
theorem regularCoreEmbedding_eq_constant_of_fixed (b : H →L[ℂ] H)
    (hfixed : ∀ s, unitaryConj (U s) b = b) :
    regularCoreEmbedding U hU b = regularConstantHom volume b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU b f,
    regularConstantHom_apply_ae volume b f] with t h₁ h₂
  rw [h₁, h₂]
  have he : unitaryConj (star (U (Multiplicative.ofAdd t))) b = b := by
    rw [regularGroup_star_eq U t]
    exact hfixed _
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    using congrArg (fun A : H →L[ℂ] H => A (f t)) he

omit [TopologicalSpace.SeparableSpace H] in
/-- A fixed base element commutes with the Fourier transform of a central
core element, in its constant representation. -/
theorem regularCore_central_fourier_commutes_fixed
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hcentral : ∀ S ∈ regularCoreAlgebra U hU P, S * T = T * S)
    (b : H →L[ℂ] H) (hb : b ∈ P) (hfixed : ∀ s, unitaryConj (U s) b = b) :
    Commute ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
      (regularConstantHom volume b) := by
  have he := hcentral _ (regularCoreEmbedding_mem_core U hU P hb)
  rw [regularCoreEmbedding_eq_constant_of_fixed U hU b hfixed] at he
  have hf := congrArg (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv he
  simp only [map_mul, fourierConj_regularConstantHom] at hf
  exact hf.symm

/-- Commutation with a constant operator in the regular representation
recovers commutation at time zero by continuity of the modular action. -/
theorem constant_commutes_regularEmbedding
    (A x : H →L[ℂ] H)
    (hc : Commute (regularConstantHom volume A) (regularCoreEmbedding U hU x)) :
    Commute A x := by
  have hf : RepresentsOperatorField volume
      (fun t : ℝ => unitaryConj (star (U (Multiplicative.ofAdd t))) x)
      (regularCoreEmbedding U hU x) := by
    intro f
    simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
      using regularCoreEmbedding_apply_ae U hU x f
  have ha := hf.commute_constant_ae A hc.symm
  change A * x = x * A
  ext ξ
  have hae : (fun t : ℝ =>
      A (unitaryConj (star (U (Multiplicative.ofAdd t))) x ξ)) =ᵐ[volume]
      (fun t : ℝ => unitaryConj (star (U (Multiplicative.ofAdd t))) x (A ξ)) := by
    filter_upwards [ha] with t ht
    exact congrArg (fun B : H →L[ℂ] H => B ξ) ht.eq.symm
  have he := Measure.eq_of_ae_eq hae
    (A.continuous.comp (regularCoreEmbedding_field_continuous U hU x ξ))
    (regularCoreEmbedding_field_continuous U hU x (A ξ))
  have hzero := congrFun he 0
  simpa only [ofAdd_zero, map_one, star_one, unitaryConj_one,
    mul_apply_eq_comp] using hzero

/-- A constant central operator in the core of a factor is scalar. -/
theorem regularCore_constant_central_scalar
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P) (hfactor : ScalarCenter P)
    (A : H →L[ℂ] H)
    (hA : regularConstantHom volume A ∈ regularCoreAlgebra U hU P)
    (hcentral : ∀ S ∈ regularCoreAlgebra U hU P,
      S * regularConstantHom volume A = regularConstantHom volume A * S) :
    ∃ c : ℂ, regularConstantHom volume A = c •
      (1 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hAmem : A ∈ P := by
    rw [← P.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro b hb
    have he := (mem_regularTensorAlgebra_iff P _).mp
      (regularCoreAlgebra_le_tensor U hU P hP hA) b hb
    apply real_regularConstantHom_injective
    simpa only [map_mul] using he
  have hac : ∀ x ∈ P, x * A = A * x := by
    intro x hx
    exact (constant_commutes_regularEmbedding U hU A x
      (hcentral _ (regularCoreEmbedding_mem_core U hU P hx)).symm).eq.symm
  obtain ⟨c, hc⟩ := hfactor A hAmem hac
  refine ⟨c, ?_⟩
  rw [hc, map_smul, map_one]

end

end KadisonKastler

end OAI
