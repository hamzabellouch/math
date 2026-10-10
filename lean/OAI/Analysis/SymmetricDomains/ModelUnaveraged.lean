import Mathlib
import OAI.Analysis.SymmetricDomains.StrictModelSupports
import OAI.Analysis.SymmetricDomains.QuadraticModelDomain
import OAI.Analysis.SymmetricDomains.Model

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
open Complex Set

lemma support_coordinate_nonzero {k : ℕ}
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (i : Fin k) :
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap ≠ 0 := by
  classical
  intro h
  have hh := congrArg (fun L : (Fin k → ℝ) →L[ℝ] ℝ => L (e.symm (Pi.single i 1))) h
  simp at hh

theorem actual_model_bounded_realization {m k : ℕ}
    (B : Fin (k+1) → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin (k+1) → ℝ)) (hC : IsOpen C) (hconn : IsConnected C)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      ∀ i, c*‖x.1‖^2 ≤ e (fun t => (x.2 t).im) i) :
    ∃ D : Set (Affine (m+(k+1))), IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      Nonempty (Biholomorph
        (affineProductCoordinates m (k+1) '' quadraticDomain (hermQuadratic B) C) D) := by
  have hH := hermQuadratic_continuous B
  apply model_bounded_biholomorph e
    (quadraticDomain_isOpen _ hH C hC) (quadraticDomain_isConnected _ hH C hconn) hc
  intro x hx i
  let ℓ : (Fin (k+1) → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hn : ℓ ≠ 0 := support_coordinate_nonzero e i
  have hb : ∀ (z : Affine m) (v : Fin (k+1) → ℝ), v-hermQuadratic B z ∈ C →
      c*‖z‖^2 ≤ ℓ v := by
    intro z v hv
    have hp : (z,fun j => I*(v j : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
      change (fun i => v i-hermQuadratic B z i) ∈ C at hv
      simpa [quadraticDomain] using hv
    simpa [ℓ] using hbound (z,fun j => I*(v j : ℂ)) hp i
  have hs := strict_model_supports (hermQuadratic B) (hermQuadratic_zero B)
    hC hconn.nonempty hcone ℓ hn c hb
  have hl := hs.2 x.1
  have hp := hs.1 ((fun t => (x.2 t).im)-hermQuadratic B x.1) hx
  change c*‖x.1‖^2 ≤ e (hermQuadratic B x.1) i at hl
  change 0 < e ((fun t => (x.2 t).im)-hermQuadratic B x.1) i at hp
  rw [map_sub,Pi.sub_apply] at hp
  linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem actual_model_bounded_from_unaveraged {m k : ℕ}
    (B : Fin (k+1) → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin (k+1) → ℝ)) (hC : IsOpen C) (hconn : IsConnected C)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    (J : Affine m →ₗ[ℂ] F) (hJ : Function.Injective J)
    (P : Fin (k+1) → Affine m → ℂ) (hP : ∀ i z, P i (I • z) = -P i z)
    (hbound : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      ∀ i, ‖J x.1‖^2 ≤ e (fun t => (x.2 t).im) i+(P i x.1).re) :
    ∃ D : Set (Affine (m+(k+1))), IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      Nonempty (Biholomorph
        (affineProductCoordinates m (k+1) '' quadraticDomain (hermQuadratic B) C) D) := by
  obtain ⟨c,hc,hco⟩ := injective_squared_lower_bound J hJ
  apply actual_model_bounded_realization B C hC hconn hcone e hc
  intro x hx i
  have hi : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      (I • x.1,x.2) ∈ quadraticDomain (hermQuadratic B) C := by
    intro x hx
    exact (quadraticDomain_unit_rotation _ C I
      (fun z => hermQuadratic_unit B I norm_I z) x).mpr hx
  exact (hco x.1).trans
    (cancel_quadratic_support hi J (fun w => e (fun t => (w t).im) i)
      (P i) (hP i) (fun x hx => hbound x hx i) x hx)

end Release061.Hermitian

end

end OAI
