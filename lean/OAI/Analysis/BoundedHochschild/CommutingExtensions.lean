import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CommutingAverages

namespace OAI

/-! Extending commuting invariance through finite averages. -/

noncomputable section

open Filter Topology
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {T : Type*} (u : T → unitary M) (S : Set (unitary M))

include e in
lemma exists_finite_commuting_extension {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hcomm : ∀ t t', Commute (u t) (u t'))
    (hS : ∀ t v, v ∈ S → Commute (u t) v)
    (F : Cochain M (n+1)) (hfix : ∀ v ∈ S, translateLast F v=F)
    (c : (Fin (n+1) → M) → M)
    (hr : ∀ v x, residualCLM x (translateLast F v)=c x) (s : Finset T) :
    ∃ G : Cochain M (n+1), ‖G‖≤‖F‖ ∧
      (∀ v ∈ S, translateLast G v=G) ∧
      (∀ t ∈ s, translateLast G (u t)=G) ∧
      ∀ v x, residualCLM x (translateLast G v)=c x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨F,le_rfl,hfix,by simp,hr⟩
  | @insert t s ht ih =>
      obtain ⟨H,hH,hHS,hHs,hHr⟩ := ih
      let B : Set (unitary M) := S ∪ u '' (s : Set T)
      have hB : ∀ v ∈ B, Commute (u t) v := by
        intro v hv
        rcases hv with hv | ⟨t',ht',rfl⟩
        · exact hS t v hv
        · exact hcomm t t'
      have hHB : ∀ v ∈ B, translateLast H v=H := by
        intro v hv
        rcases hv with hv | ⟨t',ht',rfl⟩
        · exact hHS v hv
        · exact hHs t' ht'
      obtain ⟨G,hG,hGB,hGr⟩ := exists_translate_fixed_preserving e hL hR (u t) B hB H hHB c hHr
      refine ⟨G,hG.trans hH,?_,?_,hGr⟩
      · intro v hv
        exact hGB v (Set.mem_insert_of_mem _ (Or.inl hv))
      · intro t' ht'
        rcases Finset.mem_insert.mp ht' with rfl | ht'
        · exact hGB (u t') (Set.mem_insert _ _)
        · exact hGB (u t') (Set.mem_insert_of_mem _ (Or.inr ⟨t',ht',rfl⟩))

include e in
theorem exists_commuting_extension {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hcomm : ∀ t t', Commute (u t) (u t'))
    (hS : ∀ t v, v ∈ S → Commute (u t) v)
    (F : Cochain M (n+1)) (hfix : ∀ v ∈ S, translateLast F v=F)
    (c : (Fin (n+1) → M) → M)
    (hr : ∀ v x, residualCLM x (translateLast F v)=c x) :
    ∃ G : Cochain M (n+1), ‖G‖≤‖F‖ ∧
      (∀ v ∈ S, translateLast G v=G) ∧
      (∀ t, translateLast G (u t)=G) ∧
      ∀ v x, residualCLM x (translateLast G v)=c x := by
  classical
  choose A hA hAS hAu hAr using exists_finite_commuting_extension e u S hL hR hcomm hS F hfix c hr
  let U : Ultrafilter (Finset T) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset T))≤atTop := Ultrafilter.of_le _
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U A ‖F‖ (norm_nonneg _) hA
  refine ⟨G,hG,?_,?_,?_⟩
  · intro v hv
    ext x
    have hlim := predual_tendsto_translate e hR ht v x
    have he (s : Finset T) : translateLast (A s) v=A s := hAS s v hv
    simp only [he] at hlim
    exact predual_tendsto_unique e hlim (ht x)
  · intro t
    ext x
    have hlim := predual_tendsto_translate e hR ht (u t) x
    have he : (fun s => translateLast (A s) (u t) x)=ᶠ[U] (fun s => A s x) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({t} : Finset T)] with s hs
      rw [hAu s t (hs (Finset.mem_singleton_self t))]
    have hlim' : PredualTendsto e (fun s => translateLast (A s) (u t) x) U (G x) := by
      intro z
      exact (ht x z).congr' (he.mono (fun s h => congrArg (fun a : M => e.symm a z) h.symm))
    exact predual_tendsto_unique e hlim hlim'
  · intro v x
    have hlim := predual_tendsto_residual e hL
      (fun y => predual_tendsto_translate e hR ht v y) x
    simp only [hAr] at hlim
    exact predual_tendsto_unique e hlim (predual_tendsto_const e (c x) (U : Filter (Finset T)))

end BoundedHochschild

end

end OAI
