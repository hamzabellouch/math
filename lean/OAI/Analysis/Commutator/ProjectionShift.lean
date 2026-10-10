import Mathlib
import OAI.Analysis.Commutator.ProjectionStrong

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.ProjectionShift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (w p : H →L[ℂ] H)

def partialSum : ℕ → H →L[ℂ] H
  | 0 => 0
  | n+1 => p+w*partialSum n*star w

variable {w p} {e : H →L[ℂ] H}

lemma conjugate_projection (he : IsStarProjection e) (hw : star w*w=e)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqe : q≤e) :
    IsStarProjection (w*q*star w) := by
  have heq : e*q=q := (hq.le_iff_mul_eq_right he).mp hqe
  constructor
  · calc
      _=w*q*(star w*w)*q*star w := by noncomm_ring
      _=w*q*star w := by rw [hw,mul_assoc (w*q) e q,heq,mul_assoc w q q,hq.isIdempotentElem.eq]
  · simp only [star_mul,star_star,hq.isSelfAdjoint.star_eq,IsSelfAdjoint,mul_assoc]

lemma partial_projection_le (he : IsStarProjection e) (hp : IsStarProjection p)
    (hw : star w*w=e) (hwe : w*e=w) (hpw : p*w=0)
    (hbound : p+w*star w≤e) (n : ℕ) :
    IsStarProjection (partialSum w p n) ∧ partialSum w p n≤e := by
  induction n with
  | zero => exact ⟨IsStarProjection.zero _,he.nonneg⟩
  | succ n ih =>
    refine ⟨hp.add (conjugate_projection he hw ih.1 ih.2) ?_,?_⟩
    · rw [←mul_assoc,←mul_assoc,hpw,zero_mul,zero_mul]
    · exact (add_le_add le_rfl (star_right_conjugate_le_conjugate ih.2 w)).trans
        (by simpa only [hwe] using hbound)

lemma partial_mono (hp : IsStarProjection p) : Monotone (partialSum w p) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa only [partialSum,mul_zero,zero_mul,add_zero] using hp.nonneg
  | succ n ih => exact add_le_add le_rfl (star_right_conjugate_le_conjugate ih w)

lemma partial_mem (M : VonNeumannAlgebra H) (hw : w∈M) (hp : p∈M) (n : ℕ) :
    partialSum w p n∈M := by
  induction n with
  | zero => exact M.zero_mem
  | succ n ih => exact M.add_mem hp (M.mul_mem (M.mul_mem hw ih) (M.star_mem' hw))

theorem exists_fixed_projection (M : VonNeumannAlgebra H)
    (he : IsStarProjection e) (hp : IsStarProjection p)
    (hw : star w*w=e) (hwe : w*e=w) (hpw : p*w=0)
    (hbound : p+w*star w≤e) (hwM : w∈M) (hpM : p∈M) :
    ∃ q : H →L[ℂ] H,q∈M ∧ IsStarProjection q ∧ q≤e ∧ q=p+w*q*star w := by
  obtain ⟨q,hqM,hq,hle,hlim,hleast⟩ := ProjectionChains.exists_strong_sup M (partialSum w p)
    (fun n => (partial_projection_le he hp hw hwe hpw hbound n).1)
    (partial_mem M hwM hpM) (partial_mono hp)
  refine ⟨q,hqM,hq,hleast e he (fun n => (partial_projection_le he hp hw hwe hpw hbound n).2),?_⟩
  ext x
  have hs := (hlim x).comp (tendsto_add_atTop_nat 1)
  have hr := (tendsto_const_nhds (x:=p x) (f:=atTop (α:=ℕ))).add (w.continuous.tendsto (q (star w x)) |>.comp (hlim (star w x)))
  have hh : Tendsto (fun n => partialSum w p (n+1) x) atTop (𝓝 ((p+w*q*star w) x)) := by
    simpa only [Function.comp_def,partialSum,add_apply,mul_apply_eq_comp] using hr
  exact tendsto_nhds_unique hs hh

end Kadison.ProjectionShift

end

end
end

end OAI
