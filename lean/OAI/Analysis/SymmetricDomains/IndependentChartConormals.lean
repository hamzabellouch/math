import Mathlib
import OAI.Analysis.SymmetricDomains.VanishingIdealPrime
import OAI.Analysis.SymmetricDomains.IndependentConormals
import OAI.Analysis.SymmetricDomains.PrimeBoundaryGenericFiber

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
open Set Filter Topology MeasureTheory
open scoped Classical

theorem original_boundary_generic_fiber {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (P : MvPolynomial (Fin n) ℂ) (C : Finset (NashPatch (n+n))),
      (∃ u ∈ U, MvPolynomial.eval u P ≠ 0) ∧
      (∀ p ∈ C, 0 ∈ p.domain ∧ ∀ x ∈ p.domain,
        p.complexMap x ∈ closure U \ U ∧
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) → Affine n) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
          ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) ∧
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
          x ∈ p.val.domain ∧ x ∈ c.base ∧ m ≤ p.val.complexRank x ∧
          MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
          volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0 := by
  have hsm := cocompact_bounded_affine_smooth V U hV hUV hU hc hb Γ hhol
  let I := MvPolynomial.vanishingIdeal ℂ U
  have : I.IsPrime := hsm.vanishingIdeal_isPrime hc
  have hIV : MvPolynomial.zeroLocus ℂ I ⊆ V := by
    obtain ⟨R,hR⟩ := hV
    intro x hx
    rw [hR]
    intro p hp
    apply hx p
    intro y hy
    exact (hR ▸ hUV hy) p hp
  exact prime_boundary_generic_fiber I rfl (hU.preimage (continuous_inclusion hIV))
    hc.isPreconnected hn hb hs

theorem affine_conormal_pullback_range
    {E F X K : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup K] [Module ℝ K]
    (L : E →ₗ[ℝ] F) (hL : Function.Injective L) (M : X →ₗ[ℝ] E)
    (A : K →ᵃ[ℝ] Module.Dual ℝ F)
    (hA : range A = ((LinearMap.range (L.comp M)).dualAnnihilator : Set (Module.Dual ℝ F))) :
    range (L.dualMap.toAffineMap.comp A) =
      ((LinearMap.range M).dualAnnihilator : Set (Module.Dual ℝ E)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨k,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro y ⟨x,rfl⟩
    have ha : A k ∈ (LinearMap.range (L.comp M)).dualAnnihilator := by
      change A k ∈ ((LinearMap.range (L.comp M)).dualAnnihilator : Set (Module.Dual ℝ F))
      rw [← hA]
      exact mem_range_self k
    exact (Submodule.mem_dualAnnihilator _).mp ha _ ⟨x,rfl⟩
  · intro l hl
    obtain ⟨g,hg⟩ := LinearMap.dualMap_surjective_of_injective hL l
    have hgA : g ∈ (LinearMap.range (L.comp M)).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      rintro y ⟨x,rfl⟩
      have he := congrArg (fun f : Module.Dual ℝ E => f (M x)) hg
      change g (L (M x)) = l (M x) at he
      exact he.trans ((Submodule.mem_dualAnnihilator _).mp hl _ ⟨x,rfl⟩)
    have hgAr : g ∈ range A := hA.symm ▸ hgA
    obtain ⟨k,rfl⟩ := hgAr
    exact ⟨k,hg⟩

namespace ActualCriticalChart
variable {d m N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

theorem independent_chart_conormals (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    (L : Affine m →L[ℝ] Affine N) (hL : Function.Injective L)
    (M : (Fin d → ℝ) →L[ℝ] Affine m) (hM : L.comp M = fderiv ℝ q x)
    {S : Set (Fin c.fiberDim → ℝ)} (hS : volume S ≠ 0) :
    ∃ v : Fin (Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator) →
        (Fin c.fiberDim → ℝ),
      (∀ i, v i ∈ S) ∧
      LinearIndependent ℝ (fun i => (c.ambientCovector x (v i)).comp L.toLinearMap) := by
  let W := (LinearMap.range M.toLinearMap).dualAnnihilator
  let A := L.toLinearMap.dualMap.toAffineMap.comp (c.ambientCovector x)
  have hA : range A = (W : Set (Module.Dual ℝ (Affine m))) := by
    apply affine_conormal_pullback_range L.toLinearMap hL M.toLinearMap (c.ambientCovector x)
    have he : L.toLinearMap.comp M.toLinearMap = (fderiv ℝ q x).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap hM
    rw [he]
    exact c.ambientCovector_range hx hq hP
  have hav (k : Fin c.fiberDim → ℝ) : A k ∈ W := by
    change A k ∈ (W : Set (Module.Dual ℝ (Affine m)))
    rw [← hA]
    exact mem_range_self k
  let A' := affineMapCodRestrict A W hav
  have hs : Function.Surjective A' := by
    intro l
    have hl : l.val ∈ range A := by rw [hA]; exact l.property
    obtain ⟨v,hv⟩ := hl
    exact ⟨v,Subtype.ext hv⟩
  obtain ⟨v,hv,hi⟩ := exists_independent_affine_images_of_positive_measure volume hS A' hs
  refine ⟨v,hv,?_⟩
  exact hi.map' W.subtype (Submodule.ker_subtype _)
end ActualCriticalChart
end Release061

end

end OAI
