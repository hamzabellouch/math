import OAI.Analysis.KadisonKastler.BoundaryPolarMeasurable
import OAI.Analysis.KadisonKastler.StandardTracialPosition
import OAI.Analysis.KadisonKastler.NonsingularBoundary
import OAI.Analysis.KadisonKastler.HilbertCoefficientMeasurable
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Diagonal comparison from almost-everywhere cocycle data

A countable group has a common invariant conull set for the cocycle laws
and approximation bounds. Outside that set the generating family is filled
with one good value. This provides global bounds for the least-vector and
polar constructions; covariance is required only on the conull set.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

section Local

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

local instance aeDiagonalOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance aeDiagonalStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- Global boundedness suffices for the measurable least field. The
cocycle laws need hold only on the set where covariance is asserted. -/
theorem exists_measurable_diagonal_unitary_on_set
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (S : Set D) (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, x ∈ S → (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ a : D → D → unitary (Algebra M),
      AEStronglyMeasurable (fun p : D × D => J (a p.1 p.2 : Algebra M)) μ ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, x ∈ S → y ∈ S → (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  have hex (x y : D) : ∃ b : Algebra M,
      J b ∈ diagonalTraceHull J (diagonalGenerators W x y) ∧ ‖b‖ ≤ 1 ∧
        ‖b - 1‖ ≤ r ∧
        ∀ z ∈ diagonalTraceHull J (diagonalGenerators W x y), ‖J b‖ ≤ ‖z‖ := by
    apply (exists_unique_diagonal_least J hJ hτ (Set.range_nonempty _) hr0 ?_ ?_).exists
    · rintro _ ⟨t, rfl⟩
      simpa only [Submonoid.coe_mul, Unitary.coe_star] using
        norm_unitary_le_one (W t x * star (W t y))
    · rintro _ ⟨t, rfl⟩
      exact hnear t x y
  choose c hc using hex
  have hcm : AEStronglyMeasurable (fun p : D × D => J (c p.1 p.2)) μ :=
    aestronglyMeasurable_diagonal_least J
      (fun t (p : D × D) => (W t p.1 : Algebra M) * star (W t p.2 : Algebra M))
      hWmeas (fun p => c p.1 p.2)
      (fun p => (hc p.1 p.2).1) (fun p => (hc p.1 p.2).2.2.2)
  have hcov (g : G) (x y : D) (hx : x ∈ S) (hy : y ∈ S) :
      c x y = (W g x : Algebra M) * c (shift g x) (shift g y) * star (W g y : Algebra M) := by
    have hgen (t : G) :
        (W g x : Algebra M) *
          ((W t (shift g x) : Algebra M) * star (W t (shift g y) : Algebra M)) *
          star (W g y : Algebra M) =
        (W (g * t) x : Algebra M) * star (W (g * t) y : Algebra M) := by
      rw [hW g t x hx, hW g t y hy, star_mul]
      noncomm_ring
    apply diagonal_least_covariance J hJ (W g x) (W g y)
      (s := diagonalGenerators W (shift g x) (shift g y))
      (t := diagonalGenerators W x y) ?_ ?_
      (hc (shift g x) (shift g y)).1 (hc x y).1
      (hc (shift g x) (shift g y)).2.2.2 (hc x y).2.2.2
    · rintro _ ⟨t, rfl⟩
      exact ⟨g * t, (hgen t).symm⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨g⁻¹ * t, ?_⟩
      have heq := hgen (g⁻¹ * t)
      rw [mul_inv_cancel_left] at heq
      dsimp only
      rw [← heq]
      symm
      calc
        _ = (star (W g x : Algebra M) * (W g x : Algebra M)) *
            ((W (g⁻¹ * t) (shift g x) : Algebra M) *
              star (W (g⁻¹ * t) (shift g y) : Algebra M)) *
            (star (W g y : Algebra M) * (W g y : Algebra M)) := by noncomm_ring
        _ = _ := by
          rw [Unitary.star_mul_self_of_mem (W g x).property,
            Unitary.star_mul_self_of_mem (W g y).property, one_mul, mul_one]
  have hunit (x y : D) : IsUnit (c x y) := by
    nontriviality Algebra M
    exact (Units.ofNearby 1 (c x y) (by simpa using ((hc x y).2.2.1).trans_lt hr)).isUnit
  have hp (x y : D) := exists_polar_unitary_near_one (c x y) (((hc x y).2.2.1).trans_lt hr)
  choose a ha han using hp
  refine ⟨a, ?_, ?_, ?_⟩
  · exact aestronglyMeasurable_polar_trace τ J hJ
      (fun p : D × D => c p.1 p.2) (fun p : D × D => a p.1 p.2) hr
      (fun p => (hc p.1 p.2).2.2.1) (fun p => ha p.1 p.2) hcm
  · intro x y
    exact (han x y).trans (mul_le_mul_of_nonneg_left (hc x y).2.2.1 (by norm_num))
  · intro g x y hx hy
    exact polar_unitary_sandwich (hunit x y) (W g x) (W g y)
      (a x y) (a (shift g x) (shift g y)) (ha x y) (ha _ _) (hcov g x y hx hy)

end Local

section AE

variable {H E G D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E] [Group G] [Countable G] [MeasurableSpace D]
  {μ : Measure D} [SFinite μ] [NeZero μ]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- The unitary-pair displacement equals the distance between the pair. -/
theorem norm_unitary_mul_star_sub_one (u v : unitary (Algebra M)) :
    ‖(u : Algebra M) * star (v : Algebra M) - 1‖ = ‖(u : Algebra M) - v‖ := by
  have he : (u : Algebra M) * star (v : Algebra M) - 1 =
      ((u : Algebra M) - v) * star (v : Algebra M) := by
    rw [sub_mul, Unitary.mul_star_self_of_mem v.property]
  rw [he]
  exact CStarRing.norm_mul_coe_unitary ((u : Algebra M) - v) (star v)

/-- Countably many almost-everywhere laws give the diagonal comparison,
with its explicit `4δ` displacement and almost-everywhere covariance. -/
theorem exists_ae_measurable_diagonal_unitary_comparison
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (α : NonsingularAction G D μ)
    (W : G → D → unitary (Algebra M))
    (hW : ∀ g t, ∀ᵐ x ∂μ, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (α.toPerm g⁻¹ x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) (μ.prod μ))
    (U : G → unitary (H →L[ℂ] H)) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 2 * δ < 1)
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ) :
    ∃ a : D → D → unitary (Algebra M),
      AEStronglyMeasurable (fun p : D × D => J (a p.1 p.2 : Algebra M)) (μ.prod μ) ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 4 * δ) ∧
      (∀ g, ∀ᵐ p ∂μ.prod μ, (a p.1 p.2 : Algebra M) =
        (W g p.1 : Algebra M) *
          (a (α.toPerm g⁻¹ p.1) (α.toPerm g⁻¹ p.2) : Algebra M) *
            star (W g p.2 : Algebra M)) := by
  classical
  let P : (G × G) ⊕ G → D → Prop := fun i x => match i with
    | Sum.inl gh => (W (gh.1 * gh.2) x : Algebra M) =
        (W gh.1 x : Algebra M) * (W gh.2 (α.toPerm gh.1⁻¹ x) : Algebra M)
    | Sum.inr g => ‖(W g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ
  have hP (i) : ∀ᵐ x ∂μ, P i x := by
    cases i with
    | inl gh => exact hW gh.1 gh.2
    | inr g => exact hclose g
  obtain ⟨S, hS, hSinv, hSP⟩ := α.exists_invariant_conull P hP
  obtain ⟨x₀, hx₀⟩ := hS.exists
  let pick : D → D := fun x => if x ∈ S then x else x₀
  have hpick (x : D) : pick x ∈ S := by
    dsimp only [pick]
    split_ifs with hx
    · exact hx
    · exact hx₀
  have hpick_eq {x : D} (hx : x ∈ S) : pick x = x := ite_eq_left hx
  let W' : G → D → unitary (Algebra M) := fun g x => W g (pick x)
  have heq (g : G) {x : D} (hx : x ∈ S) : W' g x = W g x := by
    dsimp only [W']
    rw [hpick_eq hx]
  have hW' (g t : G) (x : D) (hx : x ∈ S) :
      (W' (g * t) x : Algebra M) =
        (W' g x : Algebra M) * (W' t (α.toPerm g⁻¹ x) : Algebra M) := by
    rw [heq _ hx, heq _ hx, heq _ (hSinv g⁻¹ x hx)]
    exact hSP x hx (.inl (g, t))
  have hW'meas (t : G) : AEStronglyMeasurable
      (fun p : D × D => J ((W' t p.1 : Algebra M) * star (W' t p.2 : Algebra M))) (μ.prod μ) := by
    apply (hWmeas t).congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hS,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hS] with p hx hy
    rw [heq _ hx, heq _ hy]
  have hW'close (g : G) (x : D) :
      ‖(W' g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ :=
    hSP (pick x) (hpick x) (.inr g)
  have hnear (g : G) (x y : D) :
      ‖(W' g x : Algebra M) * star (W' g y : Algebra M) - 1‖ ≤ 2 * δ := by
    rw [norm_unitary_mul_star_sub_one]
    change ‖(W' g x : Algebra M).val - (W' g y : Algebra M).val‖ ≤ 2 * δ
    calc
      _ ≤ ‖(W' g x : Algebra M).val - (U g : H →L[ℂ] H)‖ +
          ‖(U g : H →L[ℂ] H) - (W' g y : Algebra M).val‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖(W' g x : Algebra M).val - (U g : H →L[ℂ] H)‖ +
          ‖(W' g y : Algebra M).val - (U g : H →L[ℂ] H)‖ := by
        rw [norm_sub_rev (U g : H →L[ℂ] H)]
      _ ≤ δ + δ := add_le_add (hW'close g x) (hW'close g y)
      _ = 2 * δ := (two_mul δ).symm
  obtain ⟨a, ham, han, hac⟩ := exists_measurable_diagonal_unitary_on_set J hJ hτ S
    (fun g x => α.toPerm g⁻¹ x) W' hW' hW'meas (by positivity) hsmall hnear
  refine ⟨a, ham, ?_, ?_⟩
  · intro x y
    calc
      _ ≤ 2 * (2 * δ) := han x y
      _ = 4 * δ := by ring
  · intro g
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hS,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hS] with p hx hy
    simpa only [heq _ hx, heq _ hy] using hac g p.1 p.2 hx hy

end AE

section Standard

variable {H G D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [Group G] [Countable G] [MeasurableSpace D]
  {μ : Measure D} [SFinite μ] [NeZero μ] {M : VonNeumannAlgebra H}

/-- The standard-position version needs only measurable operator evaluations
of the original cocycle. Its diagonal unitary field is likewise measurable
on every vector of the ambient Hilbert space. -/
theorem StandardTracialPosition.exists_ae_diagonal_unitary_comparison
    (p : StandardTracialPosition M) (α : NonsingularAction G D μ)
    (W : G → D → unitary (Algebra M))
    (hW : ∀ g t, ∀ᵐ x ∂μ, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (α.toPerm g⁻¹ x) : Algebra M))
    (hWmeas : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : Algebra M).val ξ) μ)
    (U : G → unitary (H →L[ℂ] H)) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 2 * δ < 1)
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ) :
    ∃ a : D → D → unitary (Algebra M),
      (∀ ξ, AEStronglyMeasurable
        (fun x : D × D => (a x.1 x.2 : Algebra M).val ξ) (μ.prod μ)) ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 4 * δ) ∧
      (∀ g, ∀ᵐ x ∂μ.prod μ, (a x.1 x.2 : Algebra M) =
        (W g x.1 : Algebra M) *
          (a (α.toPerm g⁻¹ x.1) (α.toPerm g⁻¹ x.2) : Algebra M) *
            star (W g x.2 : Algebra M)) := by
  borelize H
  have hgen (g : G) : AEStronglyMeasurable
      (fun x : D × D => algebraVectorMap M p.vector
        ((W g x.1 : Algebra M) * star (W g x.2 : Algebra M))) (μ.prod μ) := by
    exact aestronglyMeasurable_field_apply
      (fun x : D × D => (W g x.1 : Algebra M).val)
      (fun ξ => (hWmeas g ξ).comp_fst)
      (fun x : D × D => star (W g x.2 : Algebra M).val p.vector)
      ((operator_adjoint_eval_aestronglyMeasurable
        (fun x => (W g x : Algebra M).val) (hWmeas g) p.vector).comp_snd)
  obtain ⟨a, ham, han, hac⟩ := exists_ae_measurable_diagonal_unitary_comparison
    (algebraVectorMap M p.vector) p.vectorMap_norm p.finiteVectorTrace
    α W hW hgen U hδ hsmall hclose
  refine ⟨a, ?_, han, hac⟩
  intro ξ
  exact aestronglyMeasurable_operator_eval_of_trace (algebraVectorMap M p.vector)
    p.vectorMap_norm p.finiteVectorTrace
    (fun x : D × D => (a x.1 x.2 : Algebra M)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => norm_unitary_le_one (a x.1 x.2)) ham ξ

end Standard

end

end KadisonKastler

end OAI
