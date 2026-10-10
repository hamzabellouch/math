import OAI.Analysis.KadisonKastler.PublishedRegularDiagonal
import OAI.Analysis.KadisonKastler.RegularCoreAlgebra
import OAI.Analysis.KadisonKastler.RegularCoreFixed
import OAI.Analysis.KadisonKastler.CharacterAverageDescent
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # The joint fixed algebra in the concrete regular representation

The reverse tensor membership is proved from the actual multiplier
representation. The joint fixed-point identification then uses only the
two separate published spectral and diagonal decomposition inputs.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strong continuity of a unitary field permits a continuously varying
vector argument, because every member is an isometry. -/
theorem continuous_unitary_field_apply {X : Type*} [TopologicalSpace X]
    (V : X → unitary (H →L[ℂ] H))
    (hV : ∀ ξ, Continuous (fun x => (V x : H →L[ℂ] H) ξ))
    (f : X → H) (hf : Continuous f) :
    Continuous (fun x => (V x : H →L[ℂ] H) (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [(Metric.tendsto_nhds.mp (hf.tendsto x)) (ε / 2) hhalf,
    (Metric.tendsto_nhds.mp ((hV (f x)).tendsto x)) (ε / 2) hhalf]
    with y hy hxy
  have hi : dist ((V y : H →L[ℂ] H) (f y)) ((V y : H →L[ℂ] H) (f x)) =
      dist (f y) (f x) :=
    (Unitary.linearIsometryEquiv (V y)).isometry.dist_eq _ _
  calc
    dist ((V y : H →L[ℂ] H) (f y)) ((V x : H →L[ℂ] H) (f x)) ≤
        dist ((V y : H →L[ℂ] H) (f y)) ((V y : H →L[ℂ] H) (f x)) +
        dist ((V y : H →L[ℂ] H) (f x)) ((V x : H →L[ℂ] H) (f x)) :=
      dist_triangle _ _ _
    _ < ε := by rw [hi]; linarith

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
theorem regularCoreEmbedding_field_continuous (A : H →L[ℂ] H) (ξ : H) :
    Continuous (fun t : ℝ =>
      unitaryConj (star (U (Multiplicative.ofAdd t))) A ξ) := by
  have hs (η : H) : Continuous (fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) η) := by
    have he : (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) η) =
        (fun t : ℝ => (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) η) := by
      funext t
      exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H) η)
        (regularGroup_star_eq U t)
    rw [he]
    exact (hU η).comp continuous_neg
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp] using
    continuous_unitary_field_apply (fun t : ℝ => star (U (Multiplicative.ofAdd t)))
      hs (fun t : ℝ => A ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
      (A.continuous.comp (hU ξ))

/-- Membership in the tensor algebra reflects membership in the original
algebra. The coefficient identity is continuous, so its almost-everywhere
validity also gives its value at zero. -/
theorem regularCoreEmbedding_mem_tensorAlgebra_iff (P : VonNeumannAlgebra H)
    (hP : ∀ s A, A ∈ P → unitaryConj (U s) A ∈ P) (A : H →L[ℂ] H) :
    regularCoreEmbedding U hU A ∈ regularTensorAlgebra P ↔ A ∈ P := by
  constructor
  · intro hA
    rw [← VonNeumannAlgebra.commutant_commutant P]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    have he := (mem_regularTensorAlgebra_iff P _).mp hA z hz
    let F : ℝ → H →L[ℂ] H := fun t =>
      unitaryConj (star (U (Multiplicative.ofAdd t))) A
    have hl : RepresentsOperatorField volume (fun t => z * F t)
        (regularConstantHom volume z * regularCoreEmbedding U hU A) := by
      intro f
      filter_upwards [regularConstantHom_apply_ae volume z (regularCoreEmbedding U hU A f),
        regularCoreEmbedding_apply_ae U hU A f] with t hc hp
      change regularConstantHom volume z (regularCoreEmbedding U hU A f) t = _
      rw [hc, hp]
      simp only [F, unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    have hr : RepresentsOperatorField volume (fun t => F t * z)
        (regularConstantHom volume z * regularCoreEmbedding U hU A) := by
      rw [he]
      intro f
      filter_upwards [regularCoreEmbedding_apply_ae U hU A (regularConstantHom volume z f),
        regularConstantHom_apply_ae volume z f] with t hp hc
      change regularCoreEmbedding U hU A (regularConstantHom volume z f) t = _
      rw [hp, hc]
      simp only [F, unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    apply ContinuousLinearMap.ext
    intro ξ
    have hae := hl.eval_eq_ae_real hr ξ
    have heq := Measure.eq_of_ae_eq hae
      (z.continuous.comp (regularCoreEmbedding_field_continuous U hU A ξ))
      (regularCoreEmbedding_field_continuous U hU A (z ξ))
    have hzero := congrFun heq 0
    simpa only [F, ofAdd_zero, map_one, star_one,
      unitaryConj_one, mul_apply_eq_comp] using hzero
  · exact regularCoreEmbedding_mem_tensorAlgebra U hU P hP

/-- The exact joint fixed algebra of the two concrete regular actions.
The spectral and diagonal decomposition inputs are used separately; the
algebra identification itself is the conclusion of the proof. -/
theorem mem_regular_jointFixed_iff [TopologicalSpace.SeparableSpace H]
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (P : VonNeumannAlgebra H)
    (hP : ∀ s A, A ∈ P → unitaryConj (U s) A ∈ P)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    T ∈ fixedPointAlgebra (regularCharacterRepresentation (H := H))
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) ↔
      ∃ A ∈ P, T = regularCoreEmbedding U hU A := by
  constructor
  · intro hT
    obtain ⟨hinner, hchar⟩ := (mem_fixedPointAlgebra_iff _ _ _).mp hT
    obtain ⟨htensor, haction⟩ := (mem_fixedPointAlgebra_iff _ _ _).mp hinner
    have hcomm (a : ℝ) : Commute T
        (regularCharacterUnitary (H := H) a :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
      exact ((commute_unitary_iff_star_right_conjugate
        (regularCharacterUnitary (H := H) a).property).mpr
        (hchar (Multiplicative.ofAdd a))).symm
    obtain ⟨F, hFm, _, hFT⟩ := hDiagonal H T (hSpectral H T hcomm)
    obtain ⟨A, hA⟩ := exists_regularCoreEmbedding_of_field_fixed U hU hFT hFm haction
    exact ⟨A, (regularCoreEmbedding_mem_tensorAlgebra_iff U hU P hP A).mp
      (hA ▸ htensor), hA⟩
  · rintro ⟨A, hA, rfl⟩
    apply (mem_fixedPointAlgebra_iff _ _ _).mpr
    refine ⟨(mem_fixedPointAlgebra_iff _ _ _).mpr
      ⟨regularCoreEmbedding_mem_tensorAlgebra U hU P hP hA,
        fun s => regularCoreEmbedding_fixed U hU s A⟩, ?_⟩
    intro a
    exact regularCharacter_fixes_embedding U hU a.toAdd A

end

end KadisonKastler

end OAI
