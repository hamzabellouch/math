import Mathlib
import OAI.Probability.SKValue.Evolution.TestHeat

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
noncomputable def combinedJet (c:ℝ) (ψ f:ℝ → ℝ) (j:ℕ) (t x:ℝ) : ℝ :=
  if j%2=0 then baseJet c ψ (j/2) t x else responseJet c ψ f (j/2) t x
lemma combinedJet_even (c:ℝ) (ψ f:ℝ → ℝ) (j:ℕ) (t x:ℝ) :
    combinedJet c ψ f (2*j) t x=baseJet c ψ j t x := by simp [combinedJet]
lemma combinedJet_odd (c:ℝ) (ψ f:ℝ → ℝ) (j:ℕ) (t x:ℝ) :
    combinedJet c ψ f (2*j+1) t x=responseJet c ψ f j t x := by simp [combinedJet,Nat.add_div]
lemma baseJet_continuous {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0≤c) (j:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ baseJet c ψ j p.1 p.2) :=
  heat_normalizedJet_continuous ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j
lemma baseJet_time {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c t:ℝ} (hc:0≤c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (baseJet c ψ j · x)
      ((1/2:ℝ)*(baseJet c ψ (j+2) t x-baseJet c ψ j t x*baseJet c ψ 2 t x)) t :=
  heat_normalizedJet_time ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j x ht
lemma combinedJet_continuous {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (j:ℕ) : Continuous (fun p:ℝ×ℝ ↦ combinedJet c ψ f j p.1 p.2) := by
  unfold combinedJet
  split_ifs
  · exact baseJet_continuous hψ hc _
  · exact responseJet_continuous hψ hf hc _
lemma combinedJet_bound {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ t x,|combinedJet c ψ f j t x|≤C := by
  unfold combinedJet
  split_ifs
  · exact exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc _
  · exact responseJet_bound hψ hf hc _
lemma combinedJet_space {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (j:ℕ) (t x:ℝ) :
    HasDerivAt (combinedJet c ψ f j t)
      (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x := by
  change HasDerivAt (fun y ↦ combinedJet c ψ f j t y)
    (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x
  have he:(j+2)/2=j/2+1 := by omega
  have hm:(j+2)%2=j%2 := by omega
  by_cases h:j%2=0
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true] using
      baseJet_space hψ hc (j/2) t x
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true,ite_false] using
      responseJet_space hψ hf hc (j/2) t x
lemma combinedJet_time {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c t:ℝ} (hc:0≤c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (combinedJet c ψ f j · x)
      ((1/2:ℝ)*(combinedJet c ψ f (j+4) t x-combinedJet c ψ f j t x*combinedJet c ψ f 4 t x)) t := by
  have he:(j+4)/2=j/2+2 := by omega
  have hm:(j+4)%2=j%2 := by omega
  simp only [combinedJet,he,hm,show (4:ℕ)%2=0 from rfl,show (4:ℕ)/2=2 from rfl,ite_true]
  split_ifs
  · exact baseJet_time hψ hc ht (j/2) x
  · exact responseJet_time hψ hf hc ht (j/2) x
namespace JetExpr
noncomputable def responseσx (j:ℕ) : JetExpr :=
  add (coord (j+2)) (mul (const (-1)) (mul (coord j) (coord 2)))
noncomputable def responseσt (j:ℕ) : JetExpr :=
  mul (const (1/2)) (add (coord (j+4)) (mul (const (-1)) (mul (coord j) (coord 4))))
noncomputable def responseExpr : ℕ → JetExpr
  | 0 => coord 1
  | n+1 => D responseσx (responseExpr n)
lemma eval_responseσx (R:ℕ → ℝ) (j:ℕ) : eval R (responseσx j)=R (j+2)-R j*R 2 := by
  simp only [responseσx,eval];ring
lemma eval_responseσt (R:ℕ → ℝ) (j:ℕ) : eval R (responseσt j)=(1/2:ℝ)*(R (j+4)-R j*R 4) := by
  simp only [responseσt,eval];ring
end JetExpr
lemma responseJet_zero_expr {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (n:ℕ) (t:ℝ) :
    iteratedDeriv n (responseJet c ψ f 0 t)=
      fun x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) (JetExpr.responseExpr n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,JetExpr.responseExpr,JetExpr.eval];rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    apply HasDerivAt.deriv
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσx] using combinedJet_space hψ hf hc j t x
lemma responseJet_joint_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (n:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ iteratedDeriv n (responseJet c ψ f 0 p.1) p.2) := by
  simp_rw [responseJet_zero_expr hψ hf hc]
  exact JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) _
lemma responseJet_time_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (n:ℕ) :
    ∃ d:ℝ → ℝ → ℝ,Continuous (fun p:ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C:ℝ,0≤C ∧ ∀ t x,|d t x|≤C) ∧
      ∀ t x,0<t → HasDerivAt (fun s ↦ iteratedDeriv n (responseJet c ψ f 0 s) x) (d t x) t := by
  let E := JetExpr.D JetExpr.responseσt (JetExpr.responseExpr n)
  let d := fun t x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) E
  refine ⟨d,JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) E,?_,?_⟩
  · have hb (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ p:ℝ×ℝ,|combinedJet c ψ f j p.1 p.2|≤C := by
      obtain ⟨C,hC,hb⟩ := combinedJet_bound hψ hf hc j
      exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
    obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hb E
    exact ⟨C,hC,fun t x ↦ hb (t,x)⟩
  · intro t x ht
    simp_rw [responseJet_zero_expr hψ hf hc]
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσt] using combinedJet_time hψ hf hc ht j x
end SKValue

end

end OAI
