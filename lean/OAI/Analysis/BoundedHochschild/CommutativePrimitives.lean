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

/-! Bounded primitives for commutative dual algebras. -/

noncomputable section

open Filter Topology
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma exists_finite_commuting_invariant {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hcomm : ∀ u v : unitary M, Commute u v)
    (f : Cochain M (n+1)) (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (s : Finset (unitary M)) :
    ∃ G : Cochain M (n+1), ‖G‖≤‖f‖ ∧
      (∀ v ∈ s, translateLast G v=G) ∧
      ∀ v x, residualCLM x (translateLast G v)=((-1:ℂ)^(n+1)) • f x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨f,le_rfl,by simp,residual_translate_cocycle f hf⟩
  | @insert u s hu ih =>
      obtain ⟨F,hF,hfix,hr⟩ := ih
      obtain ⟨G,hG,hfixG,hrG⟩ := exists_translate_fixed_preserving e hL hR
        u (s : Set (unitary M)) (fun v _ => hcomm u v) F hfix _ hr
      refine ⟨G,hG.trans hF,?_,hrG⟩
      intro v hv
      exact hfixG v (by simpa only [Finset.mem_insert,Set.mem_insert_iff,Finset.mem_coe] using hv)

theorem exists_commuting_invariant {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hcomm : ∀ u v : unitary M, Commute u v)
    (f : Cochain M (n+1)) (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ G : Cochain M (n+1), ‖G‖≤‖f‖ ∧
      (∀ v, translateLast G v=G) ∧
      ∀ x, residualCLM x G=((-1:ℂ)^(n+1)) • f x := by
  classical
  choose F hF hfix hr using exists_finite_commuting_invariant e hL hR hcomm f hf
  let U : Ultrafilter (Finset (unitary M)) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset (unitary M)))≤atTop := Ultrafilter.of_le _
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hF
  refine ⟨G,hG,?_,?_⟩
  · intro v
    ext x
    have hlim := predual_tendsto_translate e hR ht v x
    have he : (fun s => translateLast (F s) v x)=ᶠ[U] (fun s => F s x) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({v} : Finset (unitary M))] with s hs
      rw [hfix s v (hs (Finset.mem_singleton_self v))]
    have hlim' : PredualTendsto e (fun s => translateLast (F s) v x) U (G x) := by
      intro z
      exact (ht x z).congr' (he.mono (fun s h => congrArg (fun a : M => e.symm a z) h.symm))
    exact predual_tendsto_unique e hlim hlim'
  · intro x
    have hlim := predual_tendsto_residual e hL ht x
    have he (s : Finset (unitary M)) : residualCLM x (F s)=((-1:ℂ)^(n+1)) • f x := by
      simpa only [translateLast_one] using hr s 1 x
    simp only [he] at hlim
    exact predual_tendsto_unique e hlim
      (predual_tendsto_const e (((-1:ℂ)^(n+1)) • f x) (U : Filter (Finset (unitary M))))

lemma right_module_of_all_translates {n : ℕ} (F : Cochain M (n+1))
    (hfix : ∀ v : unitary M, translateLast F v=F) :
    ∀ (a : Fin n → M) (x : M), F (Fin.snoc a x)=F (Fin.snoc a 1)*x := by
  intro a x
  let L := F.curryRight a
  have hu (u : unitary M) : L (u:M)=L 1*(u:M) := by
    have h := congrArg (fun H : Cochain M (n+1) => H (Fin.snoc a 1)) (hfix u)
    simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,one_mul] at h
    have hh := congrArg (fun y : M => y*(u:M)) h
    simpa only [L,ContinuousMultilinearMap.curryRight_apply,mul_assoc,Unitary.star_mul_self_of_mem u.prop,mul_one] using hh
  have hx : x ∈ Submodule.span ℂ (unitary M : Set M) := by
    rw [CStarAlgebra.span_unitary]; trivial
  change L x=L 1*x
  induction hx using Submodule.span_induction with
  | mem y hy => exact hu ⟨y,hy⟩
  | zero => simp
  | add y z hy hz ihy ihz => simp only [map_add,ihy,ihz,mul_add]
  | smul r y hy ih => simp only [map_smul,ih,mul_smul_comm]

include e in

theorem primitive_of_commutative [CompleteSpace X] [PartialOrder M] [StarOrderedRing M]
    (hcomm : ∀ a b : M, a*b=b*a)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  have hc (u v : unitary M) : Commute u v := by
    apply Subtype.ext
    exact hcomm (u:M) (v:M)
  obtain ⟨F,hF,hfix,hr⟩ := exists_commuting_invariant e
    (HochschildSakai.mul_hasPreadjoint e) (HochschildSakai.mul_right_hasPreadjoint e) hc f hf
  exact primitive_from_average f F hF hr (right_module_of_all_translates F hfix)

theorem primitive_of_commutative_wstar [WStarAlgebra M]
    (hcomm : ∀ a b : M, a*b=b*a)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  obtain ⟨Y,hY,hN,hC,⟨d⟩⟩ := WStarAlgebra.exists_predual (M:=M)
  let := hY
  let := hN
  let := hC
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact primitive_of_commutative d hcomm f hf

end BoundedHochschild

end

end OAI
