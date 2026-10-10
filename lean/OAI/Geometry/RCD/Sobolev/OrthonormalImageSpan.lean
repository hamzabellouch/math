import OAI.Geometry.RCD.Sobolev.OrthonormalHarmonicLipschitz
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace OAI

/-! # An orthonormal Sobolev frame has a full-dimensional coordinate image -/

open Set Filter MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem orthonormal_linear_constant_zero (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ Q) (v : X → Euclidean n)
    (Ω : Set X) (hΩ : MeasurableSet Ω) (hμΩ : μ Ω≠0)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict Ω] fun x => v x i)
    (hgram : ∀ i j, localGamma μ Q (u i) (u j) =ᵐ[μ.restrict Ω]
      fun _ => if i=j then 1 else 0)
    (a : Euclidean n) (c : ℝ) (hc : ∀ x∈Ω, ⟪v x,a⟫_ℝ=c) : a=0 := by
  let f := sobolevColumnMap μ Q u a
  have hf : SobolevSpace.toLp μ Q f =ᵐ[μ.restrict Ω] fun _ => c := by
    filter_upwards [sobolevColumnMap_representative μ Q u Ω v hu a,ae_restrict_mem hΩ]
      with x hx hxm
    exact hx.trans (hc x hxm)
  have he : ∀ᵐ x ∂μ.restrict Ω, ‖a‖^2=0 := by
    filter_upwards [hf,ae_restrict_of_ae (localGamma_zero_on_level μ Q f f c),
      localGamma_column_orthonormal μ Q u Ω hgram a] with x hx hz hg
    exact hg.symm.trans (hz hx)
  by_contra ha
  have hn : ‖a‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hh : ∀ᵐ x ∂μ.restrict Ω, False := he.mono (fun _ hx => hn hx)
  have hm := ae_iff.mp hh
  exact hμΩ (by simpa only [not_false_eq_true,ofPred_true,Measure.restrict_apply_univ] using hm)

theorem affineSpan_eq_top_of_linear_constants {n : ℕ} (S : Set (Euclidean n))
    (hS : S.Nonempty)
    (h : ∀ (a : Euclidean n) (c : ℝ), (∀ z∈S, ⟪z,a⟫_ℝ=c) → a=0) :
    affineSpan ℝ S=⊤ := by
  obtain ⟨p,hp⟩ := hS
  let K := (affineSpan ℝ S).direction
  have hK : Kᗮ=⊥ := by
    apply le_antisymm ?_ bot_le
    intro a ha
    change a=0
    apply h a ⟪p,a⟫_ℝ
    intro z hz
    have hv : z-p∈K := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ S hz) (subset_affineSpan ℝ S hp)
    have he := (Submodule.mem_orthogonal K a).mp ha (z-p) hv
    rw [inner_sub_left] at he
    linarith
  have hd : (affineSpan ℝ S).direction=⊤ := (Submodule.orthogonal_eq_bot_iff).mp hK
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty
    ⟨p,subset_affineSpan ℝ S hp⟩).mp hd

theorem orthonormal_image_has_interior (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ Q) (v : X → Euclidean n)
    (Ω : Set X) (hΩ : MeasurableSet Ω) (hμΩ : μ Ω≠0)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict Ω] fun x => v x i)
    (hgram : ∀ i j, localGamma μ Q (u i) (u j) =ᵐ[μ.restrict Ω]
      fun _ => if i=j then 1 else 0)
    (hconv : Convex ℝ (v '' Ω)) : (interior (v '' Ω)).Nonempty := by
  apply hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
  apply affineSpan_eq_top_of_linear_constants (v '' Ω)
  · apply Set.Nonempty.image
    by_contra hempty
    have hΩ0 : Ω=∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    exact hμΩ (by rw [hΩ0,measure_empty])
  · intro a c hc
    exact orthonormal_linear_constant_zero μ Q u v Ω hΩ hμΩ hu hgram a c
      (fun x hx => hc (v x) ⟨x,hx,rfl⟩)

end RegularPointCoordinates

end

end OAI
