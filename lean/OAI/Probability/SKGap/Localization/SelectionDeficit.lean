import Mathlib
import OAI.Probability.SKGap.Localization.LocalExtraction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma selection_deficit_l2 (hn : 0<n) (P H : Observables n) (C : ℕ→Observables n)
    (d : ℕ) (hP : ∀x,0≤P x) (hC : ∀k x,0≤C k x ∧ C k x≤1)
    {B T : ℝ} (hB : 0≤B) (hH : ∀x,|H x|≤B*Real.sqrt (n:ℝ))
    (ht : (∑x,if 0<cutoffDeficit (fun k=>C k x) d then P x else 0)≤T/(n:ℝ)) :
    (∑x,P x*(cutoffDeficit (fun k=>C k x) d*H x)^2)≤B^2*T := by
  classical
  let D:=fun x=>cutoffDeficit (fun k=>C k x) d
  have hD x : 0≤D x ∧ D x≤1:=cutoffDeficit_bounds _ _ (fun k=>hC k x)
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  calc
    _ ≤ ∑x,(if 0<D x then P x else 0)*(B^2*(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      change P x*(D x*H x)^2≤_
      by_cases hd:0<D x
      · rw [ite_eq_left hd]
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have h1 : |D x*H x|≤B*Real.sqrt (n:ℝ) := by
          rw [abs_mul,abs_of_nonneg (hD x).1]
          exact (mul_le_mul_of_nonneg_left (hH x) (hD x).1).trans
            (mul_le_of_le_one_left (mul_nonneg hB (Real.sqrt_nonneg _)) (hD x).2)
        have h2:=pow_le_pow_left₀ (abs_nonneg _) h1 2
        simpa only [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using h2
      · have hz:D x=0:=le_antisymm (le_of_not_gt hd) (hD x).1
        simp [hz]
    _ = (∑x,if 0<D x then P x else 0)*(B^2*(n:ℝ)) := (Finset.sum_mul ..).symm
    _ ≤ (T/(n:ℝ))*(B^2*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right ht (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by field_simp

lemma spin_root_direction_size (r e : Fin n→ℝ) (he : vectorNorm e≤1) (x : Spin n) :
    |∑i,(spin x i-Real.tanh (r i))*e i|≤2*Real.sqrt (n:ℝ) := by
  have hv : vectorNorm (fun i=>spin x i-Real.tanh (r i))≤2*Real.sqrt (n:ℝ) := by
    apply (vectorNorm_sub (spin x) (fun i=>Real.tanh (r i))).trans
    have hs : vectorNorm (spin x)≤Real.sqrt (n:ℝ) := by
      simpa only [vectorNorm_const,abs_one,one_mul] using
        (vectorNorm_mono (u:=spin x) (v:=fun _=>1) (fun i=>by simp [spin];split_ifs <;> norm_num))
    exact (add_le_add hs (vectorNorm_tanh r)).trans_eq (by ring)
  have hpair:=vectorPair_abs (fun _ : Spin n=>fun i=>spin x i-Real.tanh (r i)) (fun _=>e) x
  change |∑i,(spin x i-Real.tanh (r i))*e i|≤_ at hpair
  exact hpair.trans ((mul_le_mul hv he (vectorNorm_nonneg _) (by positivity)).trans_eq (mul_one _))

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ ε : ℝ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

theorem gibbs_residual_selection_deficit (m : ℕ) (hρ : 0<ρ) (hε : 0<ε)
    (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a)) :
    ∃D≥0,∀a (r e : Fin (N a)→ℝ),vectorNorm e≤1→∀G : Observables (N a),
      |∑x,fieldGibbs (J a) (h a) x*G x*
        (cutoffDeficit (fun k=>residualCutoff ρ j (J a) (h a) k x) (2*m-1)*
          (∑i,(spin x i-Real.tanh (r i))*e i))|≤D*starNorm (fieldGibbs (J a) (h a)) G := by
  obtain ⟨T,U,hT,hU,ht⟩:=gibbs_residual_selection_tail (h:=h) m hρ hε hm he hR hB hW hC hn hJ hdiag hevent
  refine ⟨Real.sqrt (2^2*T),Real.sqrt_nonneg _,?_⟩
  intro a r e he G
  apply tested_l2_to_star _ _ _ (fun x=>(fieldGibbs_pos _ _ _).le) (by positivity)
  exact selection_deficit_l2 (hn a) _ _ _ (2*m-1) (fun x=>(fieldGibbs_pos _ _ _).le)
    (fun k x=>residualCutoff_bounds ρ j (J a) (h a) k x) (by norm_num)
    (spin_root_direction_size r e he) (ht a).1

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {N : Ω→ℕ}

lemma uniform_cutoff_partition {P H : ∀a,Observables (N a)}
    {C F : ℕ→∀a,Observables (N a)} (d : ℕ)
    (hP : ∀a x,0≤P a x)
    (hmult : ∀k<d,UniformMultiplier (C k))
    (hres : ∀k<d,UniformWeak P (fun a x=>H a x-F k a x))
    (hlocal : ∀k<d,UniformWeak P (fun a x=>C k a x*F k a x))
    (hdef : UniformWeak P (fun a x=>cutoffDeficit (fun k=>C k a x) d*H a x)) :
    UniformWeak P H := by
  classical
  let Q:=fun k a x=>∏l∈Finset.range k,(1-C l a x)
  have hQ (k : ℕ) (hk : k<d) : UniformMultiplier (Q k) := by
    apply UniformMultiplier.finset_prod
    intro l hl
    exact (UniformMultiplier.const 1).add (hmult l (lt_trans (Finset.mem_range.mp hl) hk)).neg
  have hw (k : ℕ) (hk : k<d) :
      UniformWeak P (fun a x=>cutoffWeight (fun l=>C l a x) k*H a x) := by
    have hr:=(hres k hk).mul hP (cutoffWeight_uniform k (fun l hl=>hmult l (lt_of_le_of_lt hl hk)))
    have hf:=(hlocal k hk).mul hP (hQ k hk)
    apply (hr.add hf).congr
    intro a x
    dsimp [cutoffWeight,Q]
    ring
  have hs:=(UniformWeak.finset_sum (Finset.range d) (fun k hk=>hw k (Finset.mem_range.mp hk))).add hdef
  apply hs.congr
  intro a x
  rw [←Finset.sum_mul]
  dsimp [cutoffDeficit]
  ring

end SKGapCutoff.Recipe

end
end

end OAI
