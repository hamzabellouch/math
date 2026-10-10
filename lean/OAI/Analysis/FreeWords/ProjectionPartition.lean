import Mathlib
import OAI.Analysis.FreeWords.ProjectionSubdivision

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem projection_partition (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) (n : ℕ) (p : ConcreteAlgebra M) (hp : IsStarProjection p)
    (t : ℝ) (ht : 0 ≤ t) (hτ : τ.map p=(n : ℂ)*(t : ℂ)) :
    ∃ f : Fin n → ConcreteAlgebra M, (∀ i, IsStarProjection (f i)) ∧
      (∀ i, f i ≤ p) ∧ (∀ i j, i≠j → f i*f j=0) ∧
      (∑ i, f i)=p ∧ (∀ i, τ.map (f i)=(t : ℂ)) := by
  classical
  induction n generalizing p with
  | zero =>
    have hp0 : p=0 := by
      by_contra h
      exact trace_projection_ne_zero τ hp h (by simpa using hτ)
    exact ⟨Fin.elim0,(by intro i; exact Fin.elim0 i),(by intro i; exact Fin.elim0 i),
      (by intro i; exact Fin.elim0 i),(by simp [hp0]),(by intro i; exact Fin.elim0 i)⟩
  | succ n ih =>
    have htp : t ≤ (τ.map p).re := by
      rw [hτ]
      norm_num only [Nat.cast_add,Nat.cast_one,Complex.add_re,Complex.natCast_re,
        Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,Complex.natCast_im,
        Complex.one_re,Complex.one_im,mul_zero,sub_zero,zero_add]
      nlinarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]
    obtain ⟨q,hq,hqp,hτq⟩ := projection_with_trace M τ hD p hp t ht htp
    have hle : q ≤ p := (hq.le_iff_mul_eq_left hp).mpr hqp
    have hr : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hle
    have hτr : τ.map (p-q)=(n:ℂ)*(t:ℂ) := by
      rw [map_sub,hτ,hτq,Nat.cast_add,Nat.cast_one]
      ring
    obtain ⟨f,hf,hfp,hff,hfs,hfτ⟩ := ih (p-q) hr hτr
    have hqf (i : Fin n) : q*f i=0 := by
      calc
        q*f i = q*((p-q)*f i) := by rw [((hf i).le_iff_mul_eq_right hr).mp (hfp i)]
        _ = (q*(p-q))*f i := (mul_assoc _ _ _).symm
        _ = 0 := by rw [mul_sub,hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
    have hfq (i : Fin n) : f i*q=0 := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq,(hf i).isSelfAdjoint.star_eq,star_zero] using congrArg star (hqf i)
    refine ⟨Fin.cons q f,?_,?_,?_,?_,?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨hq,hf⟩
    · exact Fin.forall_fin_succ.mpr ⟨hle,fun i => (hfp i).trans (sub_le_self _ hq.nonneg)⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa only [Fin.cons_zero,Fin.cons_succ] using hqf j
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa only [Fin.cons_zero,Fin.cons_succ] using hfq i
        | succ j => exact hff i j (fun h => hij (congrArg Fin.succ h))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hfs]
      abel
    · exact Fin.forall_fin_succ.mpr ⟨hτq,hfτ⟩

end

end KKProjectionSupport
end

end OAI
