import Mathlib
import OAI.Analysis.SymmetricDomains.ModelUnaveraged
import OAI.Analysis.SymmetricDomains.SupportedHermitianModel

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
namespace Release061
open Set Complex
open scoped Classical

theorem Hermitian.model_support_coordinates {m k : ℕ}
    (B : Fin k → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin k → ℝ)) (hC : IsOpen C) (hne : C.Nonempty)
    (hcone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ)
    (hbound : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      ∀ i, c*‖x.1‖^2 ≤ e (fun j => (x.2 j).im) i) :
    (∀ y ∈ C, ∀ i, 0 < e y i) ∧
    ∀ z, ∀ i, c*‖z‖^2 ≤ e (hermQuadratic B z) i := by
  have hh : ∀ i : Fin k, (∀ y ∈ C, 0 < e y i) ∧
      ∀ z, c*‖z‖^2 ≤ e (hermQuadratic B z) i := by
    intro i
    let ℓ : (Fin k → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
    apply strict_model_supports (hermQuadratic B) (hermQuadratic_zero B) hC hne
      hcone ℓ (support_coordinate_nonzero e i) c
    intro z v hv
    have hp : (z,fun j => I*(v j : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
      change (fun i => v i-hermQuadratic B z i) ∈ C at hv
      simpa [quadraticDomain] using hv
    simpa [ℓ] using hbound (z,fun j => I*(v j : ℂ)) hp i
  exact ⟨fun y hy i => (hh i).1 y hy,fun z i => (hh i).2 z⟩

theorem original_divisible_hermitian_model {N : ℕ} (V U : Set (Affine N))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (r k : ℕ) (B : Fin (k+1) → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ)
      (C : Set (Fin (k+1) → ℝ))
      (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (c : ℝ),
      let D := quadraticDomain (Hermitian.hermQuadratic B) C
      let M := (affineProductCoordinates r (k+1)) '' D
      IsOpen C ∧ IsConnected C ∧ (0 : Fin (k+1) → ℝ) ∉ C ∧
      (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧ 0 < c ∧
      (∀ y ∈ C, ∀ i, 0 < e y i) ∧
      (∀ z, ∀ i, c*‖z‖^2 ≤ e (Hermitian.hermQuadratic B z) i) ∧
      IsOpen D ∧ IsConnected D ∧
      (∃ a : Fin (k+1) → ℝ, (0,fun i => I*(a i : ℂ)) ∈ D) ∧
      (∀ p : Affine r × Affine (k+1), ∀ a : Fin (k+1) → ℝ,
        (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p ∈ D) ∧
      (∀ t : ℂ, ‖t‖=1 → ∀ p, (t • p.1,p.2) ∈ D ↔ p ∈ D) ∧
      (∀ t : ℝ, 0 < t → ∀ p, (Real.sqrt t • p.1,t • p.2) ∈ D ↔ p ∈ D) ∧
      (∃ A : Set (Affine (r+(k+1))), IsOpen A ∧ IsConnected A ∧
        Bornology.IsBounded A ∧ Nonempty (Biholomorph M A)) ∧
      ∃ g : Biholomorph U M,
        let _ : MulAction Γ M := conjugateMulAction g.toHomeomorph.toEquiv
        ProperSMul Γ M ∧ CompactSpace (Quotient (MulAction.orbitRel Γ M)) ∧
        ∀ γ : Γ, HolomorphicOnSubset M (fun p => (γ • p : M).val) := by
  obtain ⟨r,k,B,C,e,c,hk,hCo,hCc,hCzero,hcone,hcpos,hbound,⟨g⟩⟩ :=
    original_supported_hermitian_model V U hV hUV hU hc hn hb hs Γ hhol
  cases k with
  | zero => omega
  | succ k =>
    have hconep : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C :=
      fun t ht y hy => (hcone t ht y).mpr hy
    obtain ⟨hpositive,hherm⟩ := Hermitian.model_support_coordinates B C hCo hCc.nonempty hconep e c hbound
    obtain ⟨hDo,hDc,ha⟩ := Hermitian.actual_quadratic_model_domain B C hCo hCc
    obtain ⟨htrans,hunit,hdilation⟩ := Hermitian.actual_quadratic_model_invariances B C hcone
    have hbounded := Hermitian.actual_model_bounded_realization B C hCo hCc hconep e hcpos hbound
    refine ⟨r,k,B,C,e,c,hCo,hCc,hCzero,hcone,hcpos,hpositive,hherm,
      hDo,hDc,ha,htrans,hunit,hdilation,hbounded,g,?_,?_,?_⟩
    · exact conjugateMulAction_proper g.toHomeomorph
    · exact conjugateMulAction_compact_quotient g.toHomeomorph
    · exact g.conjugate_action_holomorphic hhol

end Release061

end

end OAI
