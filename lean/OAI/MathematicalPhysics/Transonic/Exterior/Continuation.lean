import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section
namespace SepticProfile.RegularContinuation
open Set
open scoped NNReal

/-- A strict moving lower fence and an invariant upper equilibrium suffice.
An exponential strict upper fence is constructed from the compact Lipschitz
constant, rather than assuming a continuation or a separation estimate. -/
theorem exists_between_lower_equilibrium {a b c d u0 : ℝ}
    (hab : a≤b) (hcd : c≤d)
    {f : ℝ×ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ Icc c d))
    (lo dlo : ℝ → ℝ)
    (hloder : ∀ t ∈ Icc a b, HasDerivAt lo (dlo t) t)
    (hlorange : ∀ t ∈ Icc a b, lo t ∈ Icc c d)
    (hlostrict : ∀ t ∈ Icc a b, dlo t<f (t,lo t))
    (heq : ∀ t ∈ Icc a b, f (t,d)=0)
    (hu0 : lo a≤u0) (hu0d : u0<d) :
    ∃ u : ℝ → ℝ, u a=u0 ∧ ContinuousOn u (Icc a b) ∧
      (∀ t ∈ Icc a b, lo t≤u t ∧ u t<d) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,u t)) (Icc a b) t := by
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_Icc c d)) (isCompact_Icc.prod isCompact_Icc)
  let e := (d-u0)/2
  have he : 0<e := by dsimp [e];linarith
  let L : ℝ := (K:ℝ)+1
  have hL : 0<L := by dsimp [L];positivity
  let E : ℝ → ℝ := fun t => Real.exp (-L*(t-a))
  let upper : ℝ → ℝ := fun t => d-e*E t
  let du : ℝ → ℝ := fun t => e*L*E t
  have hEpos (t:ℝ) : 0<E t := Real.exp_pos _
  have hEone (t:ℝ) (ht : a≤t) : E t≤1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL.le) (sub_nonneg.mpr ht)
  have hEder (t:ℝ) : HasDerivAt E (-L*E t) t := by
    simpa only [E,mul_one,one_mul,id_eq,mul_comm] using (((hasDerivAt_id t).sub_const a).const_mul (-L)).exp
  have huder (t:ℝ) : HasDerivAt upper (du t) t := by
    have hh := ((hEder t).const_mul e).const_sub d
    have heq : -(e * (-L * E t))=du t := by dsimp [du];ring
    rw [heq] at hh
    exact hh
  have hump (t:ℝ) (ht : t∈Icc a b) : upper t∈Icc c d := by
    have hca : c≤u0 := (hlorange a ⟨le_rfl,hab⟩).1.trans hu0
    have hm := mul_le_mul_of_nonneg_left (hEone t ht.1) he.le
    have hp := mul_pos he (hEpos t)
    change c≤d-e*E t ∧ d-e*E t≤d
    dsimp [e] at hm hp ⊢
    constructor <;> linarith
  have hull (t:ℝ) : upper t<d := by
    dsimp [upper];linarith [mul_pos he (hEpos t)]
  have hus (t:ℝ) (ht : t∈Icc a b) : f (t,upper t)<du t := by
    have hh := hK.norm_sub_le (x:=(t,upper t)) (y:=(t,d)) ⟨ht,hump t ht⟩ ⟨ht,⟨hcd,le_rfl⟩⟩
    rw [heq t ht,sub_zero] at hh
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
      Real.norm_eq_abs] at hh
    have habs : |upper t-d|=e*E t := by
      rw [abs_of_nonpos (by linarith [hull t])]
      dsimp [upper];ring
    rw [max_eq_right (abs_nonneg _),habs] at hh
    have hh' := (le_abs_self (f (t,upper t))).trans hh
    dsimp [du,L]
    nlinarith [mul_pos he (hEpos t)]
  have hstart : u0∈Icc (lo a) (upper a) := by
    refine ⟨hu0,?_⟩
    simp only [upper,E,sub_self,mul_zero,Real.exp_zero,mul_one]
    dsimp [e];linarith
  obtain ⟨u,hu,huc,hbound,hder⟩ := exists_between_strict_barriers hab hcd hf
    lo upper dlo du hloder (fun t _ => huder t) hlorange hump hlostrict hus hstart
  exact ⟨u,hu,huc,fun t ht => ⟨(hbound t ht).1,(hbound t ht).2.trans_lt (hull t)⟩,hder⟩

end SepticProfile.RegularContinuation

end
end

end OAI
