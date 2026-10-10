import Mathlib

namespace OAI
noncomputable section
open Set Filter Topology
namespace FlatSpectral
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
lemma compact_difference_pow (T R : X →L[ℂ] X) (h : IsCompactOperator (T-R)) (n : ℕ) :
    IsCompactOperator (T^n-R^n) := by
  induction n with
  | zero => simpa using (isCompactOperator_zero : IsCompactOperator (0 : X →L[ℂ] X))
  | succ n ih =>
    have hc : IsCompactOperator ((T^n-R^n)*T+R^n*(T-R)) :=
      (ih.comp_clm T).add (h.clm_comp (R^n))
    have he : T^(n+1)-R^(n+1)=(T^n-R^n)*T+R^n*(T-R) := by
      rw [pow_succ,pow_succ]
      noncomm_ring
    rw [he]
    exact hc

lemma exists_power_small (R : X →L[ℂ] X) (a C r : ℝ)
    (ha : 0≤a) (hr : 0<r) (har : a<r)
    (hb : ∀ n : ℕ, ‖R^n‖≤C*a^n) :
    ∃ n : ℕ, 0<n ∧ 4*‖R^n‖<r^n := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hr.le) ((div_lt_one hr).mpr har)
  have ht : Tendsto (fun n : ℕ => 4*C*(a/r)^n) atTop (𝓝 (0:ℝ)) := by
    simpa using tendsto_const_nhds.mul hp
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨n,hn,hsmall⟩ := ((eventually_gt_atTop (0:ℕ)).and he).exists
  refine ⟨n,hn,?_⟩
  rw [div_pow,←mul_div_assoc] at hsmall
  have hs := (div_lt_one (pow_pos hr n)).mp hsmall
  have := hb n
  nlinarith

lemma finite_preimage_pow (n : ℕ) (hn : 0<n) (S : Set ℂ) (hS : S.Finite) :
    {z : ℂ | z^n∈S}.Finite := by
  have hf (w : ℂ) : {z : ℂ | z^n=w}.Finite := by
    have h := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hn w)
    simpa only [Polynomial.IsRoot,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C,sub_eq_zero] using h
  have hh := hS.biUnion (fun w _ => hf w)
  apply hh.subset
  intro z hz
  exact mem_iUnion₂.mpr ⟨z^n,hz,rfl⟩
end FlatSpectral

end

end OAI
