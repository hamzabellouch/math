import Mathlib
import OAI.Probability.SKBarriers.Dynamics.PathEndpoint
import OAI.Probability.SKBarriers.Dynamics.ThresholdObstruction
import OAI.Probability.SKBarriers.Dynamics.BankPool

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

def lockingUnion (n : ℕ) (μ : ProbabilityMeasure ℝ) (t ρ q b b' : ℝ) : Finset (ReplicaConfig n 3) :=
  signedLockingSet n q b ∪ signedLockingSet n b b' ∪ narrowLockingSet n μ t ρ

@[simp] theorem mem_lockingUnion (n : ℕ) (μ : ProbabilityMeasure ℝ) (t ρ q b b' : ℝ) (v : ReplicaConfig n 3) :
    v ∈ lockingUnion n μ t ρ q b b' ↔ (v ∈ signedLockingSet n q b ∨ v ∈ signedLockingSet n b b') ∨ v ∈ narrowLockingSet n μ t ρ := by
  simp only [lockingUnion,Finset.mem_union]

def bankBadVertex {n p : ℕ} (K : Fin p → ℕ) (B : ℕ) (μ : ProbabilityMeasure ℝ)
    (t ρ q b b' : ℝ) (z : BankIndex K → Config n) (x : Config n) : Prop :=
  bankCoverageBad K (blockPrior p B) t q z x ∨
    bankVertexBad (fun i : BankIndex K => i.1.val) (lockingUnion n μ t ρ q b b') z x

theorem bank_no_passage {n : ℕ} (hn : 0<n) (μ : ProbabilityMeasure ℝ)
    (B H s m : ℕ) (t ρ b b' q : ℝ)
    (G : GreedyScaleBounds n B H (B*s) t ρ (2/(n:ℝ)) b b' q)
    (hcount : (B*s)*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4)+(m+1)*(2*(6*(B*s)*ρ^20)/ρ+1/(n:ℝ))^s<1)
    (K : Fin (B*s) → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (lockingUnion n μ t ρ q b b') z)
    (x : ℕ → Config n)
    (hjump : ∀v k, k < m → |overlap v (x (k+1))-overlap v (x k)| ≤ 2/(n:ℝ))
    (hgood : ∀k ≤ m,¬bankBadVertex K B μ t ρ q b b' z (x k)) :
    0<overlap (initialBankReference (natBankPool K z) (natBankDefault K hK z) B t q (x 0)) (x m) := by
  let pool := natBankPool K z
  let fallback := natBankDefault K hK z
  have hp (i : ℕ) (hi : i<B*s) (v : Config n) (hv : v ∈ pool i) : v ∈ orientedBankPool K z ⟨i,hi⟩ := by
    simpa only [pool,natBankPool,dite_eq_left hi] using hv
  rw [initialBankReference_path]
  apply greedy_no_passage hn μ pool fallback (natBankDefault_mem K hK z) fallback x B H s m t ρ (2/(n:ℝ)) b b' q G hcount hjump
  · intro j hj v hv u hu hc
    exact bank_pool_coverage K B z t q (x u) (fun H => hgood u hu (Or.inl H)) j hj v hv hc
  · intro i j hij hj v hv w hw k hk HS
    have H := bank_pool_no_vertex K z (lockingUnion n μ t ρ q b b') (x k)
      (fun H => hgood k hk (Or.inr H)) ⟨i,hij.trans hj⟩ ⟨j,hj⟩
      (fun he => by have he' : i=j := congrArg Fin.val he; omega) v w (hp i (hij.trans hj) v hv) (hp j hj w hw) (Equiv.refl _)
    apply H
    exact (mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inl (Or.inl HS))
  · intro i k j hik hkj hj v hv u hu w hw
    have Hi := hp i (hik.trans (hkj.trans hj)) v hv
    have Hk := hp k (hkj.trans hj) u hu
    have Hj := hp j hj w hw
    have hki : (⟨k,hkj.trans hj⟩ : Fin (B*s))≠⟨i,hik.trans (hkj.trans hj)⟩ := fun he => by have he' : k=i := congrArg Fin.val he; omega
    have hkj' : (⟨k,hkj.trans hj⟩ : Fin (B*s))≠⟨j,hj⟩ := fun he => by have he' : k=j := congrArg Fin.val he; omega
    have hij' : (⟨i,hik.trans (hkj.trans hj)⟩ : Fin (B*s))≠⟨j,hj⟩ := fun he => by have he' : i=j := congrArg Fin.val he; omega
    constructor
    · intro HS
      exact bank_pool_no_triple K z _ hz _ _ _ hki hkj' hij' u v w Hk Hi Hj
        ((mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inl (Or.inr HS)))
    · intro HS
      exact bank_pool_no_triple K z _ hz _ _ _ hki hkj' hij' u v (flip w) Hk Hi (flip_mem_orientedBankPool K z _ Hj)
        ((mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inl (Or.inr HS)))
  · intro i j hij hj v hv w hw k hk HS
    have HE : ((![v,w,x k] : ReplicaConfig n 3) ∘ Equiv.swap (1:Fin 3) 2)=(![v,x k,w] : ReplicaConfig n 3) := by
      funext a; fin_cases a <;> simp [Equiv.swap_apply_def]
    have H := bank_pool_no_vertex K z (lockingUnion n μ t ρ q b b') (x k)
      (fun H => hgood k hk (Or.inr H)) ⟨i,hij.trans hj⟩ ⟨j,hj⟩
      (fun he => by have he' : i=j := congrArg Fin.val he; omega) v w (hp i (hij.trans hj) v hv) (hp j hj w hw) (Equiv.swap 1 2)
    rw [HE] at H
    exact H ((mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inr HS))

theorem bank_stationary_crossing {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (μ : ProbabilityMeasure ℝ)
    (B H s m : ℕ) (t ρ b b' q : ℝ)
    (G : GreedyScaleBounds n B H (B*s) t ρ (2/(n:ℝ)) b b' q)
    (hcount : (B*s)*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4)+(m+1)*(2*(6*(B*s)*ρ^20)/ρ+1/(n:ℝ))^s<1)
    (K : Fin (B*s) → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (lockingUnion n μ t ρ q b b') z) :
    (∑x,gibbs β J x*∑y,if overlap (initialBankReference (natBankPool K z) (natBankDefault K hK z) B t q x) y ≤ 0
      then discreteKernel β J m x y else 0)  ≤  (m+1)*(gibbsFiniteLaw β J).prob (bankBadVertex K B μ t ρ q b b' z) := by
  apply stationary_sign_crossing_bound hn β J m _ _
  intro path hpath hg
  have H := bank_no_passage hn μ B H s m t ρ b b' q G hcount K hK z hz (extendPath path)
    (extendPath_jump hn β J path hpath) (fun k hk => by simpa only [extendPath,dite_eq_left hk] using hg ⟨k,by omega⟩)
  have hz0 : (⟨0,show 0 < m+1 by omega⟩ : Fin (m+1))=0 := Fin.ext (by simp)
  simpa only [extendPath,dite_eq_left (show 0 ≤ m by omega),dite_eq_left le_rfl,hz0,Fin.last] using H

end SK.Analytic

end
end

end OAI
