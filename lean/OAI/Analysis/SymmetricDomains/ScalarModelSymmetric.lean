import Mathlib
import OAI.Analysis.SymmetricDomains.QuadraticModelDomain
import OAI.Analysis.SymmetricDomains.Model
import OAI.Analysis.SymmetricDomains.ScalarPointSymmetryMap
import OAI.Analysis.SymmetricDomains.TransferSymmetries

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

theorem scalar_model_symmetries {m : ℕ}
    (B : Fin 1 → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (hB : ∀ z, 0 ≤ hermQuadratic B z 0) :
    ∀ p : affineProductCoordinates m 1 '' quadraticDomain (hermQuadratic B) {a | 0 < a 0},
      ∃ σ : Biholomorph
        (affineProductCoordinates m 1 '' quadraticDomain (hermQuadratic B) {a | 0 < a 0})
        (affineProductCoordinates m 1 '' quadraticDomain (hermQuadratic B) {a | 0 < a 0}),
        Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
        ∃ W : Set (affineProductCoordinates m 1 '' quadraticDomain (hermQuadratic B) {a | 0 < a 0}),
          IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, σ.toHomeomorph q = q → q = p := by
  let a : (Affine m × ℂ) ≃L[ℂ] Affine (m+1) :=
    scalarNormalCoordinates.symm.trans (affineProductCoordinates m 1)
  let S := scalarTube (fun z => hermQuadratic B z 0)
  have he : a '' S = affineProductCoordinates m 1 ''
      quadraticDomain (hermQuadratic B) {a | 0 < a 0} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨scalarNormalCoordinates.symm y,?_,rfl⟩
      exact (scalarNormalCoordinates_mem B _).mp (by simpa using hy)
    · rintro ⟨y,hy,rfl⟩
      refine ⟨scalarNormalCoordinates y,(scalarNormalCoordinates_mem B y).mpr hy,?_⟩
      change affineProductCoordinates m 1 (scalarNormalCoordinates.symm
        (scalarNormalCoordinates y)) = affineProductCoordinates m 1 y
      rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [← he]
  intro p
  let p' := a.symm p.val
  have hp : p' ∈ S := by
    obtain ⟨q,hq,hqp⟩ := p.property
    change a.symm p.val ∈ S
    rw [← hqp,a.symm_apply_apply]
    exact hq
  let F := scalarPointSymmetryMap B p'
  have hF : AnalyticOnNhd ℂ F S := scalarPointSymmetryMap_analytic B hB p'
  have hm : MapsTo F S S := fun _ hq => scalarPointSymmetryMap_mem B hB hp hq
  have hi : ∀ q ∈ S, F (F q) = q := fun _ hq =>
    scalarPointSymmetryMap_involutive B hB hp hq
  let σ := conjugateInvolutionBiholomorph a S F hF hm hi
  have hf : ∀ q : a '' S, σ.toHomeomorph q = q ↔ q = p := by
    intro q
    have hq : a.symm q.val ∈ S := by
      obtain ⟨u,hu,huq⟩ := q.property
      rw [← huq,a.symm_apply_apply]
      exact hu
    rw [Subtype.ext_iff,conjugateInvolutionBiholomorph_apply]
    have hqeq := scalarPointSymmetryMap_fixed_iff B hB hp hq
    change a (scalarPointSymmetryMap B p' (a.symm q.val)) = q.val ↔ _
    rw [← a.apply_symm_apply q.val,a.injective.eq_iff,a.symm_apply_apply]
    rw [hqeq]
    exact (a.symm.injective.eq_iff).trans Subtype.ext_iff.symm
  exact ⟨σ,conjugateInvolutionBiholomorph_involutive a S F hF hm hi,(hf p).mpr rfl,
    univ,isOpen_univ,mem_univ _,fun q _ hq => (hf q).mp hq⟩

theorem scalar_model_bounded_symmetric {m : ℕ}
    (B : Fin 1 → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hbound : ∀ z, c*‖z‖^2 ≤ hermQuadratic B z 0) :
    ∃ D : Set (Affine (m+1)), IsBoundedSymmetricDomain D ∧
      Nonempty (Biholomorph
        (affineProductCoordinates m 1 '' quadraticDomain (hermQuadratic B) {a | 0 < a 0}) D) := by
  let C : Set (Fin 1 → ℝ) := {a | 0 < a 0}
  have hCo : IsOpen C := isOpen_lt continuous_const (continuous_apply 0)
  have hCc : IsConnected C := by
    change IsConnected ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) ⁻¹' Ioi 0)
    exact (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toHomeomorph.isConnected_preimage.mpr
      isConnected_Ioi
  have hB : ∀ z, 0 ≤ hermQuadratic B z 0 := fun z =>
    (mul_nonneg hc.le (sq_nonneg ‖z‖)).trans (hbound z)
  obtain ⟨D,hDo,hDc,hDb,⟨e⟩⟩ := model_bounded_biholomorph
    (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))
    (quadraticDomain_isOpen _ (hermQuadratic_continuous B) C hCo)
    (quadraticDomain_isConnected _ (hermQuadratic_continuous B) C hCc) hc
    (by
      intro x hx i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hx' : hermQuadratic B x.1 0 < (x.2 0).im := sub_pos.mp hx
      exact (hbound x.1).trans_lt hx')
  exact ⟨D,⟨hDo,hDc,hDb,e.transfer_symmetries (scalar_model_symmetries B hB)⟩,⟨e⟩⟩

end Release061.Hermitian

end

end OAI
