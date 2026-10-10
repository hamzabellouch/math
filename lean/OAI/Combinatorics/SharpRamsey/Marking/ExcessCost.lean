import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.RootCost

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Selection ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [FiniteDimensional K V] [Finite K]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma twoMask_log_card {N d : ℕ} (hdim : Module.finrank K V=d+3) :
    log (Fintype.card (TwoMask (K:=K) (V:=V) N):ℝ)=
      2*(N:ℝ)*log (3*((d:ℝ)+4)) := by
  unfold TwoMask
  rw [Fintype.card_prod]
  simp only [Fintype.card_fun,Fintype.card_fin,rankMask_card,Subspace.dual_finrank_eq,
    hdim,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [log_mul (by positivity) (by positivity),log_pow]
  push_cast
  ring_nf

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma twoExpensive_linear {d : ℕ} (hdim : Module.finrank K V=d+3)
    {σ : ℝ} (hlog : log (Nat.card K:ℝ)=σ) (hσ : 1≤σ) :
    expensiveBudget K V+expensiveBudget K (Module.Dual K V)≤
      (64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ := by
  have hdim' : Module.finrank K V=(d+2)+1:=hdim
  have hdual : Module.finrank K (Module.Dual K V)=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdim]
  have ha:=projective_log_card_add_one hdim' (by rwa [hlog])
  have hb:=projective_log_card_add_one hdual (by rwa [hlog])
  rw [hlog] at ha hb
  unfold expensiveBudget
  simp only [Subspace.dual_finrank_eq,hdim]
  simp only [Points] at *
  push_cast at ha hb ⊢
  have hfactor : 0≤32*((d:ℝ)+3+1)^2*(Nat.card K:ℝ):=by positivity
  have ha':=mul_le_mul_of_nonneg_left ha hfactor
  have hb':=mul_le_mul_of_nonneg_left hb hfactor
  nlinarith only [ha',hb']

variable {Ω Γ : Type} [Fintype Ω] [Fintype Γ]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem excessCost_linear {N d : ℕ} (hdim : Module.finrank K V=d+3)
    (p : Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (σ Λ Δ A B Jprev : ℝ) (hlog : log (Nat.card K:ℝ)=σ) (hσ : 1≤σ)
    (hΔ : 0≤Δ) (hB : 0≤B) (hC : entropy (p.map C)≤Λ)
    (hF : (N:ℝ)*((d+2:ℕ):ℝ)*σ-A*N≤entropy (p.map F))
    (hJ : Jprev-jointJ K (d+2)≤Δ+B) :
    excessCost p C F Jprev (jointJ K (d+2))≤
      Λ+(N:ℝ)*(log 64+2*log (3*((d:ℝ)+4))+A+B)+
        (64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ*Δ := by
  let E : ℝ:=∑ x,p.mass x*((bothExpensive (twoMask (Nat.card K) (F x))).card:ℝ)
  have hE0 : 0≤E:=sum_nonneg (fun x _=>mul_nonneg (p.nonneg x) (Nat.cast_nonneg _))
  have hEN : E≤N := by
    calc
      _ ≤ ∑ x,p.mass x*(N:ℝ) := by
        apply sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
        exact_mod_cast (show (bothExpensive (twoMask (Nat.card K) (F x))).card≤N by
          simpa only [Fintype.card_fin] using card_le_univ (bothExpensive (twoMask (Nat.card K) (F x))))
      _ = _ := by rw [←sum_mul,p.total,one_mul]
  have hEE : E≤(64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ := by
    calc
      _ ≤ ∑ x,p.mass x*(expensiveBudget K V+expensiveBudget K (Module.Dual K V)) := by
        exact sum_le_sum (fun x _=>mul_le_mul_of_nonneg_left (two_expensive_bound (F x)) (p.nonneg x))
      _ = _ := by rw [←sum_mul,p.total,one_mul]
      _ ≤ _ := twoExpensive_linear hdim hlog hσ
  have hJ0 : jointJ K (d+2)=log 64+((d+2:ℕ):ℝ)*σ := by
    have hq : (0:ℝ)<Nat.card K:=by exact_mod_cast Finite.card_pos
    unfold jointJ
    rw [log_mul (by norm_num) (pow_ne_zero _ hq.ne'),log_pow,hlog]
  have hcost : E*(Jprev-jointJ K (d+2))≤
      (64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ*Δ+(N:ℝ)*B := by
    calc
      _ ≤ E*(Δ+B) := mul_le_mul_of_nonneg_left hJ hE0
      _ = E*Δ+E*B := mul_add _ _ _
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hEE hΔ) (mul_le_mul_of_nonneg_right hEN hB)
  unfold excessCost
  rw [twoMask_log_card hdim,hJ0]
  change _ + E*(Jprev-(log 64+((d+2:ℕ):ℝ)*σ))≤_
  rw [hJ0] at hcost
  nlinarith only [hC,hF,hcost]
end
end SharpLogRamsey.Marking

end

end OAI
