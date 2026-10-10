import OAI.Analysis.KadisonKastler.TracialQuotientRepresentation
import OAI.Analysis.KadisonKastler.TraceLimits

namespace OAI

/-! # Scalar center of the tracial quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

theorem scalarCenter_of_starAlgEquiv {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
    (e : A ≃⋆ₐ[ℂ] C)
    (hA : ∀ x : A, (∀ y, y * x = x * y) → ∃ c : ℂ, x = c • 1)
    (x : C) (hx : ∀ y, y * x = x * y) : ∃ c : ℂ, x = algebraMap ℂ C c := by
  have hcentral : ∀ y, y * e.symm x = e.symm x * y := by
    intro y
    have h := congrArg e.symm (hx (e y))
    simpa only [map_mul, StarAlgEquiv.symm_apply_apply] using h
  obtain ⟨c, hc⟩ := hA (e.symm x) hcentral
  refine ⟨c, ?_⟩
  calc
    x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = e (c • 1) := congrArg e hc
    _ = algebraMap ℂ C c := by rw [map_smul, map_one, Algebra.algebraMap_eq_smul_one]

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

/-- Only a uniform commutator test for the scalar part of each coordinate
is needed for the factor property. -/
def CoordinateVarianceControl : Prop :=
  ∀ j (x : B j), ∃ u : unitary (B j),
    traceTwoNorm (τ j) (x - (τ j).toLinearMap x • (1 : B j)) ≤
      2 * traceTwoNorm (τ j) ((u : B j) * x - x * u)

theorem tracialQuotient_scalarCenter (hcontrol : CoordinateVarianceControl τ)
    (x : TracialSequenceQuotient τ ω)
    (hx : ∀ y, y * x = x * y) :
    ∃ c : ℂ, x = c • 1 := by
  classical
  let q := tracialSequenceQuotientMap τ ω
  obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
  choose u hu using fun j => hcontrol j (a j)
  let v : VaryingBoundedSequence B := ⟨fun j => (u j : B j),
    memℓp_infty ⟨1, by rintro _ ⟨j, rfl⟩; exact (CStarRing.norm_coe_unitary (u j)).le⟩⟩
  have hcomm : q (v * a - a * v) = 0 := by
    simpa only [map_sub, map_mul] using sub_eq_zero.mpr (hx (q v))
  have hnull := (tracialSequenceQuotientMap_eq_zero_iff τ ω _).mp hcomm
  let c := tracialSequenceValue τ ω a
  have hscalar : Tendsto (fun j => ‖(τ j).toLinearMap (a j) - c‖) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [c, sub_self, norm_zero] using ((tendsto_tracialSequenceValue τ ω a).sub_const c).norm
  have hbound (j : ℕ) : traceTwoNorm (τ j) ((a - c • 1) j) ≤
      2 * traceTwoNorm (τ j) ((v * a - a * v) j) + ‖(τ j).toLinearMap (a j) - c‖ := by
    change traceTwoNorm (τ j) (a j - c • 1) ≤
      2 * traceTwoNorm (τ j) ((u j : B j) * a j - a j * u j) + _
    have he : a j - c • (1 : B j) =
        (a j - (τ j).toLinearMap (a j) • 1) +
          ((τ j).toLinearMap (a j) - c) • 1 := by rw [sub_smul]; abel
    rw [he]
    apply (traceTwoNorm_add_le _ _ _).trans
    apply add_le_add (hu j)
    exact (traceTwoNorm_le_norm _ _).trans (by rw [norm_smul, norm_one, mul_one])
  have hy : TraceNullSequence τ ω (a - c • 1) := by
    apply squeeze_zero (fun j => traceTwoNorm_nonneg _ _) hbound
    simpa only [mul_zero, zero_add] using (hnull.const_mul 2).add hscalar
  have he := (tracialSequenceQuotientMap_eq_zero_iff τ ω _).mpr hy
  refine ⟨c, sub_eq_zero.mp ?_⟩
  simpa only [map_sub, map_smul, map_one] using he

attribute [local irreducible] tracialSequenceAlgebra

theorem tracialSequenceAlgebra_scalarCenter (hω : (ω : Filter ℕ) ≤ atTop)
    (hcontrol : CoordinateVarianceControl τ)
    (x : Algebra (tracialSequenceAlgebra τ ω)) (hx : ∀ y, y * x = x * y) :
    ∃ c : ℂ, x = algebraMap ℂ _ c :=
  scalarCenter_of_starAlgEquiv (tracialSequenceEquiv τ ω hω)
    (tracialQuotient_scalarCenter τ ω hcontrol) x hx

end

end KadisonKastler

end OAI
