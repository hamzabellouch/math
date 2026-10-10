import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGenerators
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeights
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomogeneousGenerators

namespace OAI

/-! # A homogeneous bracket-word basis of the Cartan ideal

This supplies actual nonzero-root letters and strictly positive integral
letter multiplicities for the nilpotent box data.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

def cartanGeneratorPool : Set (cartanRootIdeal H) :=
  {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ (v : L) ∈ rootSpace H χ}

theorem cartanGeneratorPool_lieSpan [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) = ⊤ := by
  let N := cartanRootIdeal H
  let U := LieSubalgebra.lieSpan ℝ N (cartanGeneratorPool H)
  have himage : N.incl '' cartanGeneratorPool H =
      {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hv
      have hN : v ∈ N := LieSubmodule.subset_lieSpan hv
      exact ⟨⟨v, hN⟩, hv, rfl⟩
  have hmap : U.map N.incl = N.toLieSubalgebra := by
    rw [LieSubalgebra.map_lieSpan, himage]
    change cartanRootSubalgebra H = N.toLieSubalgebra
    apply SetLike.coe_injective
    exact congrArg (fun V : Submodule ℝ L => (V : Set L))
      (cartanRootSubalgebra_eq_ideal H T)
  apply top_unique
  intro v _
  have hv : (v : L) ∈ U.map N.incl := by rw [hmap]; exact v.property
  obtain ⟨w, hw, heq⟩ := hv
  have : w = v := Subtype.ext heq
  change v ∈ U
  exact this ▸ hw

abbrev cartanRootAbelianization :=
  (cartanRootIdeal H) ⧸ (LieModule.lowerCentralSeries ℝ
    (cartanRootIdeal H) (cartanRootIdeal H) 1).toSubmodule

/-- Retain the actual abelianization basis along with its homogeneous lifts.
This gives positivity for every later choice of a word basis. -/
theorem exists_cartan_abelianization_generators [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ (m : ℕ) (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
      (b : Basis (Fin m) ℝ (cartanRootAbelianization H)),
      (∀ i, (χ i).IsNonZero ∧ (X i : L) ∈ rootSpace H (χ i)) ∧
      (∀ i, (LieModule.lowerCentralSeries ℝ (cartanRootIdeal H)
        (cartanRootIdeal H) 1).toSubmodule.mkQ (X i) = b i) ∧
      LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤ := by
  let := cartanRootIdeal_nilpotent H T
  let C := (LieModule.lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule
  obtain ⟨b, X, hXS, hXq, hspan⟩ := exists_quotient_basis_lifts C (cartanGeneratorPool H)
    (span_sup_lowerCentralSeries_one_of_lieSpan _ (cartanGeneratorPool_lieSpan H T))
  choose χ hχ using hXS
  refine ⟨Module.finrank ℝ (cartanRootAbelianization H), X, χ, b, hχ, hXq, ?_⟩
  apply lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
  apply top_unique
  rw [← hspan]
  apply sup_le_sup_right
  exact Submodule.span_le.mpr LieSubalgebra.subset_lieSpan

/-- The actual Cartan ideal has a basis of bracket words in finitely many
nonzero generalized root vectors, with every letter occurring positively. -/
theorem exists_cartan_word_basis [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ (m : ℕ) (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
      (b : Basis (Fin (Module.finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
      (words : Fin (Module.finrank ℝ (cartanRootIdeal H)) → FreeMagma (Fin m)),
      (∀ i, (χ i).IsNonZero ∧ (X i : L) ∈ rootSpace H (χ i)) ∧
      (∀ j, evalBracketWord X (words j) = b j) ∧
      (∀ i, 0 < ∑ j, bracketWordCount (words j) i) := by
  let := cartanRootIdeal_nilpotent H T
  obtain ⟨m, X, b, words, hXS, hwords, hpositive⟩ :=
    exists_positive_word_basis (cartanGeneratorPool H) (cartanGeneratorPool_lieSpan H T)
  choose χ hχ using hXS
  exact ⟨m, X, χ, b, words, hχ, hwords, hpositive⟩

/-- The weights of a generating family in the Cartan ideal already separate
canonical height; one need not retain the full set of adjoint weights. -/
theorem cartan_generator_weights_separate [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) {I : Type*}
    (X : I → cartanRootIdeal H) (χ : I → Weight ℝ H L)
    (hX : ∀ i, (X i : L) ∈ rootSpace H (χ i))
    (hgen : LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤)
    (w : HeightSpace T.character)
    (hw : ∀ i, cartanHeightWeight T H (χ i) w = 0) : w = 0 := by
  let h := cartanHeightSection T H w
  let V := (LieAlgebra.ad ℝ L h).maxGenEigenspace 0
  have hletter (i : I) : (X i : L) ∈ V := by
    have hi := genWeightSpace_le_genWeightSpaceOf L h (χ i : H → ℝ) (hX i)
    have hχ : χ i h = 0 := hw i
    change (X i : L) ∈ (toEnd ℝ H L h).maxGenEigenspace (χ i h) at hi
    rw [hχ] at hi
    exact hi
  have hbracket {x y : L} (hx : x ∈ V) (hy : y ∈ V) : ⁅x, y⁆ ∈ V := by
    simpa only [V, LieAlgebra.ad, zero_add] using
      LieModule.lie_mem_maxGenEigenspace_toEnd hx hy
  have hN (x : cartanRootIdeal H) : (x : L) ∈ V := by
    have hx : x ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) := by
      rw [hgen]
      trivial
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hletter i
    | zero => exact V.zero_mem
    | add x y _ _ hx hy => exact V.add_mem hx hy
    | smul r x _ hx => exact V.smul_mem r hx
    | lie x y _ _ hx hy => exact hbracket hx hy
  have hH (x : H) : (x : L) ∈ V := by
    have hx : (x : L) ∈ rootSpace H (0 : H → ℝ) := by
      rw [rootSpace_zero_eq]
      exact x.property
    exact genWeightSpace_le_genWeightSpaceOf L h (0 : H → ℝ) hx
  have htop : V = ⊤ := by
    apply top_unique
    rw [← triangular_cartan_spanning T H]
    exact sup_le (fun x hx => hN ⟨x, hx⟩) (fun x hx => hH ⟨x, hx⟩)
  have hnil : _root_.IsNilpotent (LieAlgebra.ad ℝ L h) := by
    dsimp only [V] at htop
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.genEigenspace_nat, zero_smul, sub_zero, LinearMap.ker_eq_top] at htop
    exact ⟨Module.finrank ℝ L, htop⟩
  have hp := (Submodule.Quotient.mk_eq_zero _).mpr
    (T.mem_kernelIdeal_of_ad_nilpotent h hnil)
  change heightProjection T.character (h : L) = 0 at hp
  simpa only [h, cartanHeightSection_height] using hp

end PolycyclicRecognition

end

end OAI
