import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Tactic

namespace OAI

noncomputable section

namespace Invariant233.AffiliatedTransport

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def imageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) : Submodule ℂ E :=
  (p.comap H.domain.subtype).map H.toFun

def closedImageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) : Submodule ℂ E :=
  (imageOn H p).topologicalClosure

instance [CompleteSpace E] (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) :
    CompleteSpace (closedImageOn H p) := by
  unfold closedImageOn
  infer_instance

@[simp] theorem mem_imageOn {H : E →ₗ.[ℂ] E} {p : Submodule ℂ E} {y : E} :
    y ∈ imageOn H p ↔ ∃ x : H.domain, (x : E) ∈ p ∧ H x = y := by
  rfl

theorem imageOn_le_closedImageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) :
    imageOn H p ≤ closedImageOn H p :=
  Submodule.le_topologicalClosure _

theorem image_mem_closedImageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (x : H.domain) (hx : (x : E) ∈ p) : H x ∈ closedImageOn H p :=
  imageOn_le_closedImageOn H p ((mem_imageOn).2 ⟨x, hx, rfl⟩)

theorem imageOn_invariant (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (A B : E →L[ℂ] E)
    (hD : ∀ x : H.domain, A (x : E) ∈ H.domain)
    (hI : ∀ x : H.domain, H ⟨A (x : E), hD x⟩ = B (H x))
    (hp : ∀ x ∈ p, A x ∈ p) :
    ∀ y ∈ imageOn H p, B y ∈ imageOn H p := by
  rintro y ⟨x, hx, rfl⟩
  exact (mem_imageOn).2 ⟨⟨A (x : E), hD x⟩, hp x hx, hI x⟩

theorem closedImageOn_invariant (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (A B : E →L[ℂ] E)
    (hD : ∀ x : H.domain, A (x : E) ∈ H.domain)
    (hI : ∀ x : H.domain, H ⟨A (x : E), hD x⟩ = B (H x))
    (hp : ∀ x ∈ p, A x ∈ p) :
    ∀ y ∈ closedImageOn H p, B y ∈ closedImageOn H p := by
  have hmap : (imageOn H p).map B.toLinearMap ≤ imageOn H p := by
    rintro y ⟨x, hx, rfl⟩
    exact imageOn_invariant H p A B hD hI hp x hx
  intro y hy
  change B y ∈ (imageOn H p).topologicalClosure
  apply Submodule.topologicalClosure_mono hmap
  apply Submodule.topologicalClosure_map B (imageOn H p)
  exact ⟨y, hy, rfl⟩

theorem closedImageOn_invariant_of_commuting (H : E →ₗ.[ℂ] E)
    (p : Submodule ℂ E) (W : E →L[ℂ] E)
    (hD : ∀ x : H.domain, W (x : E) ∈ H.domain)
    (hC : ∀ x : H.domain, H ⟨W (x : E), hD x⟩ = W (H x))
    (hp : ∀ x ∈ p, W x ∈ p) :
    ∀ y ∈ closedImageOn H p, W y ∈ closedImageOn H p :=
  closedImageOn_invariant H p W W hD hC hp

theorem mem_orthogonal_closedImageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (hH : H.IsFormalAdjoint H) (z : H.domain)
    (hz : H z ∈ pᗮ) : (z : E) ∈ (closedImageOn H p)ᗮ := by
  rw [closedImageOn, Submodule.orthogonal_closure]
  rw [Submodule.mem_orthogonal]
  rintro y ⟨x, hx, rfl⟩
  change inner ℂ (H x) (z : E) = 0
  exact (hH x z).trans (Submodule.inner_right_of_mem_orthogonal hx hz)

theorem inverse_imageOn_le_orthogonal (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (hH : H.IsFormalAdjoint H) (hinj : H.toFun.ker = ⊥) :
    imageOn H.inverse pᗮ ≤ (closedImageOn H p)ᗮ := by
  rintro y ⟨η, hη, rfl⟩
  have hηrange : (η : E) ∈ LinearMap.range H.toFun := by
    rw [← LinearPMap.inverse_domain]
    exact η.property
  obtain ⟨z, hz⟩ := hηrange
  have hker : H.ker = ⊥ := by simp [LinearPMap.ker, hinj]
  have heq : H.inverse η = (z : E) := LinearPMap.inverse_apply_eq hker hz
  change H.inverse η ∈ (closedImageOn H p)ᗮ
  rw [heq]
  apply mem_orthogonal_closedImageOn H p hH z
  change H.toFun z ∈ pᗮ
  rw [hz]
  exact hη

theorem inverse_closedImageOn_le_orthogonal (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (hH : H.IsFormalAdjoint H) (hinj : H.toFun.ker = ⊥) :
    closedImageOn H.inverse pᗮ ≤ (closedImageOn H p)ᗮ := by
  exact (imageOn H.inverse pᗮ).topologicalClosure_minimal
    (inverse_imageOn_le_orthogonal H p hH hinj)
    (closedImageOn H p).isClosed_orthogonal

theorem orthogonal_invariant_of_inverse (p : Submodule ℂ E)
    (W : E ≃ₗᵢ[ℂ] E) (hp : ∀ x ∈ p, W.symm x ∈ p) :
    ∀ y ∈ pᗮ, W y ∈ pᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  have h := W.inner_map_map (W.symm x) y
  rw [W.apply_symm_apply] at h
  exact h.trans (Submodule.inner_right_of_mem_orthogonal (hp x hx) hy)

theorem starProjection_commutes_of_reducing (p : Submodule ℂ E)
    [p.HasOrthogonalProjection] (W : E ≃ₗᵢ[ℂ] E)
    (hp : ∀ x ∈ p, W x ∈ p) (hp' : ∀ x ∈ p, W.symm x ∈ p) :
    ∀ x, p.starProjection (W x) = W (p.starProjection x) := by
  intro x
  apply p.eq_starProjection_of_mem_orthogonal
  · exact hp _ (p.starProjection_apply_mem x)
  · have h := orthogonal_invariant_of_inverse p W hp' _
      (p.sub_starProjection_mem_orthogonal x)
    simpa only [map_sub] using h

theorem closedImageOn_map_eq (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (W : E ≃L[ℂ] E)
    (hD : ∀ x : H.domain, W (x : E) ∈ H.domain)
    (hD' : ∀ x : H.domain, W.symm (x : E) ∈ H.domain)
    (hC : ∀ x : H.domain, H ⟨W (x : E), hD x⟩ = W (H x))
    (hC' : ∀ x : H.domain, H ⟨W.symm (x : E), hD' x⟩ = W.symm (H x))
    (hp : ∀ x ∈ p, W x ∈ p) (hp' : ∀ x ∈ p, W.symm x ∈ p) :
    (closedImageOn H p).map W.toLinearMap = closedImageOn H p := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact closedImageOn_invariant_of_commuting H p W.toContinuousLinearMap hD hC hp x hx
  · intro y hy
    refine ⟨W.symm y, ?_, W.apply_symm_apply y⟩
    exact closedImageOn_invariant_of_commuting H p W.symm.toContinuousLinearMap
      hD' hC' hp' y hy

theorem closedImageOn_starProjection_commutes [CompleteSpace E]
    (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E)
    (hD : ∀ x : H.domain, W (x : E) ∈ H.domain)
    (hD' : ∀ x : H.domain, W.symm (x : E) ∈ H.domain)
    (hC : ∀ x : H.domain, H ⟨W (x : E), hD x⟩ = W (H x))
    (hC' : ∀ x : H.domain, H ⟨W.symm (x : E), hD' x⟩ = W.symm (H x))
    (hp : ∀ x ∈ p, W x ∈ p) (hp' : ∀ x ∈ p, W.symm x ∈ p) :
    ∀ x, (closedImageOn H p).starProjection (W x) =
      W ((closedImageOn H p).starProjection x) := by
  apply starProjection_commutes_of_reducing
  · exact closedImageOn_invariant_of_commuting H p W.toLinearIsometry.toContinuousLinearMap hD hC hp
  · exact closedImageOn_invariant_of_commuting H p W.symm.toLinearIsometry.toContinuousLinearMap hD' hC' hp'

theorem trace_eq_of_cutoff_estimates {t p : ℝ} {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 1))
    (hlower : ∀ n, p + e n - 1 ≤ t)
    (hupper : ∀ n, (1 - p) + e n - 1 ≤ 1 - t) : t = p := by
  have h₁ : p ≤ t := by
    have hlim : Tendsto (fun n => p + e n - 1) atTop (𝓝 p) := by
      convert (tendsto_const_nhds.add he).sub tendsto_const_nhds using 1; simp
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  have h₂ : 1 - p ≤ 1 - t := by
    have hlim : Tendsto (fun n => (1 - p) + e n - 1) atTop (𝓝 (1 - p)) := by
      convert (tendsto_const_nhds.add he).sub tendsto_const_nhds using 1; simp
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hupper)
  linarith

end Invariant233.AffiliatedTransport

end

end OAI
