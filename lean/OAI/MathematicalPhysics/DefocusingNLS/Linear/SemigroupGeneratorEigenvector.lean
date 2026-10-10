import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # A real generator eigenvector evolves by its scalar exponential -/

open Set Filter Topology
open scoped NNReal

namespace DefocusingNLS

theorem semigroup_eigenvector_of_generator
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : ℝ≥0 → V →L[ℝ] V)
    (hc : ∀ v, Continuous (fun t => S t v))
    (hzero : S 0 = ContinuousLinearMap.id ℝ V)
    (hadd : ∀ s t, S (s + t) = (S s).comp (S t))
    (u : V) (lam : ℝ)
    (hu : HasDerivWithinAt (fun t : ℝ => S t.toNNReal u) (lam • u) (Ici 0) 0)
    (t : ℝ≥0) : S t u = Real.exp (lam * (t : ℝ)) • u := by
  let f := fun s : ℝ => S s.toNNReal u
  have hf : Continuous f := (hc u).comp continuous_real_toNNReal
  have hf0 : f 0 = u := by simp only [f, Real.toNNReal_zero, hzero, ContinuousLinearMap.id_apply]
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt f (lam • f s) (Ici s) s := by
    have h := (S s.toNNReal).hasFDerivAt.comp_hasDerivWithinAt 0 hu
    have hh : HasDerivWithinAt (fun r : ℝ => r - s) 1 (Ici s) s :=
      ((hasDerivAt_id s).sub_const s).hasDerivWithinAt
    have he := h.scomp_of_eq s hh (fun r hr => show 0 ≤ r - s from sub_nonneg.mpr hr) (by simp)
    simp only [one_smul, map_smul] at he
    apply he.congr_of_mem _ (by simp only [mem_Ici]; exact le_rfl)
    intro r hr
    have hsum : s.toNNReal + (r - s).toNNReal = r.toNNReal := by
      rw [← Real.toNNReal_add hs (sub_nonneg.mpr hr), add_sub_cancel]
    change S r.toNNReal u = S s.toNNReal (S (r - s).toNNReal u)
    rw [← hsum, hadd]
    rfl
  let g := fun s : ℝ => Real.exp (-lam * s) • f s
  have hg : Continuous g := (by fun_prop : Continuous (fun s : ℝ => Real.exp (-lam * s))).smul hf
  have hgD (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt g 0 (Ici s) s := by
    have he := (((hasDerivAt_id s).const_mul (-lam)).exp).hasDerivWithinAt (s := Ici s)
    have h := he.smul (hd s hs)
    convert h using 1
    · rfl
    · simp only [id_eq, mul_one, smul_smul]
      module
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := (t : ℝ))
    hg.continuousOn (fun s hs => hgD s hs.1) t ⟨t.2, le_rfl⟩
  have hz : Real.exp (-lam * (t : ℝ)) • S t u = u := by
    simpa only [g, f, hf0, Real.toNNReal_coe, mul_zero, Real.exp_zero, one_smul] using hconst
  have he := congrArg (fun v : V => Real.exp (lam * (t : ℝ)) • v) hz
  simpa only [smul_smul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_smul] using he

end DefocusingNLS

end OAI
