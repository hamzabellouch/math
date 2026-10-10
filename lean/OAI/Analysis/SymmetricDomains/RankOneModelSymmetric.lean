import Mathlib
import OAI.Analysis.SymmetricDomains.ModelUnaveraged
import OAI.Analysis.SymmetricDomains.ScalarModelSymmetric
import OAI.Analysis.SymmetricDomains.ScalarConeImagePositive

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex

noncomputable def normalCoordinatesBiholomorph {m k : ℕ}
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    (B : Fin (k+1) → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin (k+1) → ℝ)) :
    Biholomorph
      (affineProductCoordinates m (k+1) '' quadraticDomain (hermQuadratic B) C)
      (affineProductCoordinates m (k+1) ''
        quadraticDomain (hermQuadratic (bilinearNormalCoordinates e.toLinearMap B)) (e '' C)) := by
  let a := affineProductCoordinates m (k+1)
  let s := supportLinearCoordinates (E := Affine m) e
  let f := (a.symm.trans s).trans a
  let D := quadraticDomain (hermQuadratic B) C
  let D' := quadraticDomain (hermQuadratic (bilinearNormalCoordinates e.toLinearMap B)) (e '' C)
  have hm : ∀ p, s p ∈ D' ↔ p ∈ D := supportLinearCoordinates_hermitian_mem e B C
  refine biholomorphOfAmbientInverse (a '' D) (a '' D') f f.symm
    (f.analyticOnNhd _) (f.symm.analyticOnNhd _) ?_ ?_ (fun x _ => f.symm_apply_apply x)
    (fun x _ => f.apply_symm_apply x)
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨s x,(hm x).mpr hx,by simp [f]⟩
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨s.symm x,(hm (s.symm x)).mp (by simpa using hx),?_⟩
    simp [f]

theorem actual_rank_one_model_bounded_symmetric {m : ℕ}
    (B : Fin 1 → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin 1 → ℝ)) (hC : IsOpen C) (hconn : IsConnected C)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (e : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ))
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      c*‖x.1‖^2 ≤ e (fun t => (x.2 t).im) 0) :
    ∃ D : Set (Affine (m+1)), IsBoundedSymmetricDomain D ∧
      Nonempty (Biholomorph
        (affineProductCoordinates m 1 '' quadraticDomain (hermQuadratic B) C) D) := by
  let ℓ : (Fin 1 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj 0).comp e.toContinuousLinearMap
  have hn : ℓ ≠ 0 := support_coordinate_nonzero e 0
  have hb : ∀ (z : Affine m) (v : Fin 1 → ℝ), v-hermQuadratic B z ∈ C →
      c*‖z‖^2 ≤ ℓ v := by
    intro z v hv
    have hp : (z,fun j => I*(v j : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
      change (fun i => v i-hermQuadratic B z i) ∈ C at hv
      simpa [quadraticDomain] using hv
    simpa [ℓ] using hbound (z,fun j => I*(v j : ℂ)) hp
  have hs := strict_model_supports (hermQuadratic B) (hermQuadratic_zero B)
    hC hconn.nonempty hcone ℓ hn c hb
  have hcone' : e '' C = {y | 0 < y 0} :=
    scalar_cone_image_eq_positive C hconn.nonempty hcone e hs.1
  have hpos : ∀ z, c*‖z‖^2 ≤
      hermQuadratic (bilinearNormalCoordinates e.toLinearMap B) z 0 := by
    intro z
    rw [hermQuadratic_bilinearNormalCoordinates]
    exact hs.2 z
  obtain ⟨D,hD,⟨d⟩⟩ := scalar_model_bounded_symmetric _ hc hpos
  let f := normalCoordinatesBiholomorph e B C
  rw [hcone'] at f
  exact ⟨D,hD,⟨f.trans d⟩⟩

end Release061.Hermitian

end

end OAI
