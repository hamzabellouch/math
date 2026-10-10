import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OrderedExtraction
import OAI.Combinatorics.RamseyFive.Entropy.WindowReadiness
import OAI.Combinatorics.RamseyFive.Entropy.IndependentSampling

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {α β κ τ : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype τ]

lemma mean_by_fibers (p : Law (α×β)) (f : α×β→ℝ) :
    mean p f=mean (first p) (fun a=>mean (fiber p a) (fun b=>f (a,b))) := by
  simp only [mean,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mass_eq_first_mul_fiber]
  ring

lemma mean_comm (p : Law α) (q : Law β) (f : α→β→ℝ) :
    mean p (fun a=>mean q (f a))=mean q (fun b=>mean p (fun a=>f a b)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

def coveredPositions {n : ℕ} (x : Fin n→β) (D : Finset β) : Finset (Fin n) :=
  Finset.univ.filter fun i=>x i∈D

omit [Fintype β] in
lemma mem_coveredPositions {n : ℕ} (x : Fin n→β) (D : Finset β) (i : Fin n) :
    i∈coveredPositions x D ↔ x i∈D := by
  simp only [coveredPositions,Finset.mem_filter,Finset.mem_univ,true_and]

omit [Fintype β] in
lemma omitted_card_eq {n : ℕ} (x : Fin n→β) (D : Finset β) :
    ((coveredPositions x D)ᶜ.card:ℝ)=∑ i:Fin n,if x i∉D then 1 else 0 := by
  have he : (coveredPositions x D)ᶜ=Finset.univ.filter fun i=>x i∉D := by
    ext i
    simp [coveredPositions]
  rw [he]
  simp only [←Finset.sum_boole]

theorem conditional_omissions {n : ℕ} (p : Law α) (ctx : α→κ) (x : α→Fin n→β)
    (sampler : κ→Law τ) (D : τ→Finset β) :
    mean (adaptiveLaw p (fun a=>sampler (ctx a)))
      (fun z=>((coveredPositions (x z.1) (D z.2))ᶜ.card:ℝ)) =
    mean (first (pair p ctx x)) (fun c=>∑ i:Fin n,
      mean (map (fiber (pair p ctx x) c) (fun y=>y i))
        (fun b=>eventWeight (sampler c) (fun t=>b∉D t))) := by
  rw [mean_adaptive]
  have hpoint (a : α) : mean (sampler (ctx a))
      (fun t=>((coveredPositions (x a) (D t))ᶜ.card:ℝ))=
      ∑ i:Fin n,eventWeight (sampler (ctx a)) (fun t=>x a i∉D t) := by
    simp_rw [omitted_card_eq]
    rw [mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [eventWeight_mean]
    apply mean_congr
    intro t
    by_cases hh : x a i∉D t <;> simp only [hh]
  simp_rw [hpoint]
  have he : mean p (fun a=>∑ i:Fin n,eventWeight (sampler (ctx a)) (fun t=>x a i∉D t))=
      mean (pair p ctx x) (fun z=>∑ i:Fin n,eventWeight (sampler z.1) (fun t=>z.2 i∉D t)) := by
    exact (mean_map p (fun a=>(ctx a,x a))
      (fun z=>∑ i:Fin n,eventWeight (sampler z.1) (fun t=>z.2 i∉D t))).symm
  rw [he,mean_by_fibers]
  apply mean_congr
  intro c
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mean_map (fiber (pair p ctx x) c) (fun y=>y i)
    (fun b=>eventWeight (sampler c) (fun t=>b∉D t))).symm

theorem conditional_extraction {n l : ℕ} (hl : l<n) (p : Law α)
    (ctx : α→κ) (x : α→Fin n→β) (sampler : κ→Law τ) (D : τ→Finset β)
    (hm : mean (first (pair p ctx x)) (fun c=>∑ i:Fin n,
      mean (map (fiber (pair p ctx x) c) (fun y=>y i))
        (fun b=>eventWeight (sampler c) (fun t=>b∉D t)))≤((n:ℝ)-l)/10) :
    (9:ℝ)/10≤eventMass (adaptiveLaw p (fun a=>sampler (ctx a)))
      (Finset.univ.filter fun z=>l≤(coveredPositions (x z.1) (D z.2)).card) := by
  apply extraction_probability _ _ hl
  rwa [conditional_omissions]
end
end

open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β τ : Type} [Fintype κ] [Fintype β] [Fintype τ] {r n rem : ℕ} [Nonempty (Fin r)]
local instance readyExtractBlockDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance readyExtractIndexDE : DecidableEq (Slots 1 r) := Classical.decEq _

theorem preRound_ready_omissions (μ : Law κ) (p : κ→Law (Slots 1 r→β))
    (S : κ→(Fin 1×Bool)→Finset (Fin r)) (hrem : 0<rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card) (J d e L : ℝ) (hL : 0≤L)
    (c : κ→BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) β n→Slots 1 r→Slots 1 r→ℝ)
    (sampler : ((κ×BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) β n)×
      ((Fin 1×Bool)→Fin r))→Law τ) (D : τ→Finset β)
    (hb : ∀ z,0<preRoundLaw μ p S n z→∀ t,
      windowReady (preRoundBad μ p S n J d e c z) z.2 0 t→
      mean (map (historyPosterior (p z.1.1) z.1.2) (fun x=>x (Sum.inr (0,t))))
        (fun b=>eventWeight (sampler z) (fun s=>b∉D s))≤L) :
    mean (adaptiveLaw (preRoundTupleLaw μ p S n) (fun z=>sampler z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (D z.2))ᶜ.card:ℝ))≤
      5*mean (preRoundLaw μ p S n) (fun z=>
        ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d e c z i)+(2*r:ℝ)*L := by
  have hpoint : ∀ z,0<preRoundLaw μ p S n z→∀ t,
      mean (map (historyPosterior (p z.1.1) z.1.2) (fun x=>x (Sum.inr (0,t))))
        (fun b=>eventWeight (sampler z) (fun s=>b∉D s))≤
          (if windowReady (preRoundBad μ p S n J d e c z) z.2 0 t then (0:ℝ) else 1)+L := by
    intro z hz t
    by_cases hh : windowReady (preRoundBad μ p S n J d e c z) z.2 0 t
    · simpa only [ite_eq_left hh,zero_add] using hb z hz t hh
    · rw [ite_eq_right hh]
      exact (mean_mono _ (fun b=>eventWeight_le_one _ _)).trans (by rw [mean_const]; linarith)
  have he : mean (adaptiveLaw (preRoundTupleLaw μ p S n) (fun z=>sampler z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (D z.2))ᶜ.card:ℝ))=
      mean (preRoundLaw μ p S n) (fun z=>∑ t,
        mean (map (historyPosterior (p z.1.1) z.1.2) (fun x=>x (Sum.inr (0,t))))
          (fun b=>eventWeight (sampler z) (fun s=>b∉D s))) := by
    simp only [mean_adaptive,preRoundTupleLaw]
    apply mean_congr
    intro z
    simp_rw [omitted_card_eq,mean_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [mean_map]
    apply mean_congr
    intro x
    rw [eventWeight_mean]
    apply mean_congr
    intro zt
    by_cases hh : x (Sum.inr (0,t))∉D zt <;> simp only [hh]
  rw [he]
  have hh:=mean_mono_pos (preRoundLaw μ p S n) (fun z hz=>
    Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin (2*r)))) (fun t _=>hpoint z hz t))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mean_add,mean_const,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hrdy:=preRound_ready_loss μ p S hrem hr hS J d e c
  simp only [Fin.sum_univ_one] at hrdy
  exact hh.trans (add_le_add hrdy le_rfl)
end

end SharpRamseyFive.FiniteEntropy

end OAI
