import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.HighSampleRetention
import OAI.Combinatorics.RamseyFive.Entropy.ConditionalSampling

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ]

def highLossBound {m : ℕ} (p : Law (SampleFlag (K:=K) (V:=V)))
    (targets : Fin m→Law (SampleFlag (K:=K) (V:=V)))
    (G : Fin m→Finset (ℙ K (Dual K V))) (A : ℝ) (_ : ℝ) (B : Fin m→ℝ) (h : ℕ) : ℝ :=
  ∑ i,(eventMass (second (targets i)) (G i)ᶜ+64*(Nat.card K:ℝ)^5*A*(B i)+
    3*(1-1/(5*(Nat.card K:ℝ)))^h+3*h*relationMass SampleConflict p (targets i))

theorem high_conditional_omissions (hdim : finrank K V=5) {m : ℕ}
    (p : Law Ω) (ctx : Ω→κ) (x : Ω→Fin m→SampleFlag (K:=K) (V:=V))
    (rep : κ→Law (SampleFlag (K:=K) (V:=V)))
    (G : κ→Fin m→Finset (ℙ K (Dual K V))) (A C : κ→ℝ) (B : κ→Fin m→ℝ)
    (hflag : ∀ c,0<first (pair p ctx x) c→∀ i z,
      0< map (fiber (pair p ctx x) c) (fun y=>y i) z→Incident z.1 z.2)
    (hA : ∀ c,0≤A c) (hB : ∀ c i,0≤B c i) (hC : ∀ c,0≤C c)
    (hpA : ∀ c a,first (rep c) a≤A c)
    (hrB : ∀ c i b,b∈G c i→second (map (fiber (pair p ctx x) c) (fun y=>y i)) b≤B c i)
    (hpC : ∀ c b,second (rep c) b≤C c)
    (hsmall : ∀ c,2*(Nat.card K:ℝ)^2*C c≤1/(20*(Nat.card K:ℝ))) (h : ℕ) :
    mean (adaptiveLaw p (fun a=>iid (iid (rep (ctx a)) (Fin h)) (Fin 3)))
      (fun z=>((coveredPositions (x z.1) (highDomain z.2))ᶜ.card:ℝ)) ≤
    mean (first (pair p ctx x)) (fun c=>highLossBound (rep c)
      (fun i=>map (fiber (pair p ctx x) c) (fun y=>y i)) (G c) (A c) (C c) (B c) h) := by
  rw [conditional_omissions p ctx x (fun c=>iid (iid (rep c) (Fin h)) (Fin 3)) highDomain]
  apply mean_mono_pos
  intro c hc
  apply Finset.sum_le_sum
  intro i _
  exact sampled_target_loss hdim (rep c) _ (hflag c hc i) (G c i)
    (A c) (B c i) (C c) (hA c) (hB c i) (hC c)
    (hpA c) (hrB c i) (hpC c) (hsmall c) h

theorem high_conditional_partial (hdim : finrank K V=5) {m : ℕ}
    (p : Law Ω) (ctx : Ω→κ) (x : Ω→Fin m→SampleFlag (K:=K) (V:=V))
    (rep : κ→Law (SampleFlag (K:=K) (V:=V)))
    (ready : κ→Fin m→Prop)
    (G : κ→Fin m→Finset (ℙ K (Dual K V))) (A C : κ→ℝ) (B : κ→Fin m→ℝ)
    (hflag : ∀ c,0<first (pair p ctx x) c→∀ i z,
      0 < map (fiber (pair p ctx x) c) (fun y=>y i) z→Incident z.1 z.2)
    (hA : ∀ c,0≤A c) (hB : ∀ c i,0≤B c i) (hC : ∀ c,0≤C c)
    (hpA : ∀ c,0<first (pair p ctx x) c→∀ i,ready c i→∀ a,first (rep c) a≤A c)
    (hrB : ∀ c,0<first (pair p ctx x) c→∀ i,ready c i→∀ b,b∈G c i→
      second (map (fiber (pair p ctx x) c) (fun y=>y i)) b≤B c i)
    (hpC : ∀ c,0<first (pair p ctx x) c→∀ i,ready c i→∀ b,second (rep c) b≤C c)
    (hsmall : ∀ c,0<first (pair p ctx x) c→∀ i,ready c i→
      2*(Nat.card K:ℝ)^2*C c≤1/(20*(Nat.card K:ℝ))) (h : ℕ) :
    mean (adaptiveLaw p (fun a=>iid (iid (rep (ctx a)) (Fin h)) (Fin 3)))
      (fun z=>((coveredPositions (x z.1) (highDomain z.2))ᶜ.card:ℝ)) ≤
    mean (first (pair p ctx x)) (fun c=>∑ i,if ready c i then
      eventMass (second (map (fiber (pair p ctx x) c) (fun y=>y i))) (G c i)ᶜ+
        64*(Nat.card K:ℝ)^5*A c*(B c i)+3*(1-1/(5*(Nat.card K:ℝ)))^h+
        3*h*relationMass SampleConflict (rep c) (map (fiber (pair p ctx x) c) (fun y=>y i))
      else 1) := by
  rw [conditional_omissions p ctx x (fun c=>iid (iid (rep c) (Fin h)) (Fin 3)) highDomain]
  apply mean_mono_pos
  intro c hc
  apply Finset.sum_le_sum
  intro i _
  by_cases hr : ready c i
  · rw [ite_eq_left hr]
    exact sampled_target_loss hdim (rep c) _ (hflag c hc i) (G c i)
      (A c) (B c i) (C c) (hA c) (hB c i) (hC c)
      (hpA c hc i hr) (hrB c hc i hr) (hpC c hc i hr) (hsmall c hc i hr) h
  · rw [ite_eq_right hr]
    apply (mean_mono _ (fun z=>eventWeight_le_one _ _)).trans_eq
    exact mean_const _ 1

local instance highExtractionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

omit [Finite K] in
theorem high_extracted_entropy (hdim : finrank K V=5) {m l h : ℕ} (hl : l ≤ m)
    (p : Law Ω) (x : Ω→Fin m→SampleFlag (K:=K) (V:=V))
    (samples : Ω→Fin 3→Fin h→SampleFlag (K:=K) (V:=V))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(coveredPositions (x a) (highDomain (samples a))).card)) :
    entropy (map (conditionOn p _ hE) (fun a=>retainedTuple hl (x a)
      (coveredPositions (x a) (highDomain (samples a)))))≤
      3*h*Real.log (Fintype.card (SampleFlag (K:=K) (V:=V)))+
        l*Real.log (Fintype.card (ℙ K (Dual K V))) := by
  have hd : 0<finrank K (Dual K V) := by simp [hdim]
  let : Nontrivial (Dual K V) := Module.nontrivial_of_finrank_pos hd
  have hQ : 1≤Fintype.card (ℙ K (Dual K V)) := Fintype.card_pos
  apply extracted_entropy hl p x
    (fun a=>coveredPositions (x a) (highDomain (samples a))) samples highDomain
    (fun a _ i hi=>(mem_coveredPositions _ _ _).mp hi) hE
  · have hc:=entropy_le_log_card (map (conditionOn p _ hE) samples)
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,
      mul_assoc,mul_left_comm,mul_comm] using hc
  · intro t
    exact log_card_le hQ _ (highDomain_card hdim t)

end
end SharpRamseyFive.HighSamples

end OAI
