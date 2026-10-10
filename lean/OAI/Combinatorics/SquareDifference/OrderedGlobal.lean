import OAI.Combinatorics.SquareDifference.OrderedBlock

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Global

variable {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma block_multilinear_identity {V : Type*} [Fintype V] [DecidableEq V]
    (Llaw : ((V → ResidueSpace p) → ℝ) →ₗ[ℝ] ℝ)
    (N K L Q : ℕ) (hN : 0<N) (hK : 0<K) (hL : 0<L) (hNKL : N≤K*L)
    (f : V → ℕ → ℝ) (hf : ∀v n,N≤n → f v n=0) :
    multilinearIntegral Llaw (fun v => actualTruncatedLift p N Q (f v))=
      ((K:ℝ)*L/N)^(Fintype.card V)*(𝔼 a : V → Fin K,
        multilinearIntegral Llaw (fun v => intervalLift p (L*(a v).val) L Q (f v))) := by
  let : NeZero K := ⟨hK.ne'⟩
  have heq : (fun v => actualTruncatedLift p N Q (f v))=
      (fun v x => ((K:ℝ)*L/N)*(𝔼 i : Fin K,intervalLift p (L*i.val) L Q (f v) x)) :=
    funext (fun v => funext (blockLift_expect p N K L Q hN hK hL hNKL (f v) (hf v)))
  rw [heq]
  exact multilinearIntegral_scale_expect (I:=Fin K) Llaw (fun v (i : Fin K) => intervalLift p (L*i.val) L Q (f v)) _

lemma ordered_global_estimate (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (L N Q H K : ℕ) (hN : 1≤N) (hL : 0<L) (hH : 1≤H) (hK : 1≤K)
    (hNKL : N≤K*L) (hfac : (K:ℝ)*L/N≤2) (hNL : (N:ℝ)/L≤K)
    (hHQ : H*K^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(K^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps))
    (hgood : ∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (R : ℝ) (hR : 1≤R)
    (hm : ∀a v t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,intervalPiece p a L (smallResidueInput (smallModulus ps) A (s v)) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => actualTruncatedLift p N Q (smallResidueInput (smallModulus ps) A (s v)))|≤
      (2:ℝ)^(Fintype.card TupleVertex)*((K:ℝ)⁻¹*(2*R^(2*Fintype.card TupleVertex))+
      ((Fintype.card TupleVertex:ℝ)*(K:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex)+
        orderedLowError (Fintype.card TupleVertex) (smallModulus ps) K H R)) := by
  let : NeZero K := ⟨by omega⟩
  let F (a : TupleVertex → Fin K) : ℝ := multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
    (fun v => intervalLift p (L*(a v).val) L Q (smallResidueInput (smallModulus ps) A (s v)))
  let E : ℝ := (Fintype.card TupleVertex:ℝ)*(K:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex)+
    orderedLowError (Fintype.card TupleVertex) (smallModulus ps) K H R
  have hE : 0≤E := add_nonneg (by positivity) (orderedLowError_nonneg _ _ _ _ _)
  have hb : ∀a,|F a|≤2*R^(2*Fintype.card TupleVertex) := by
    intro a
    exact interval_multilinear_crude p hmass (fun v => L*(a v).val) L Q _ R hR (fun v => hm _ v)
  have hg : ∀a,a (cycleVertex 0)≠a (cycleVertex 1) → |F a|≤E := by
    intro a ha
    have ha' : (a (cycleVertex 0)).val≠(a (cycleVertex 1)).val := fun h => ha (Fin.ext h)
    obtain ⟨k,hk,hasc⟩ := tuple_interval_ascent (fun v => (a v).val) ha'
    have hasc' : L*(a (cycleVertex k)).val+L≤L*(a (cycleVertex (k+1))).val := by
      calc
        _ = L*((a (cycleVertex k)).val+1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hasc)
    exact ordered_interval_full ps p hinj hp hmass (fun v => L*(a v).val) L N Q H K
      hN hH hK hHQ hD hHn hlarge hcover A hA hfree s k hasc' (hgood k hk) hNL R (by linarith)
      (fun v => hm _ v)
  have hav := choice_average_bound (cycleVertex 0) (cycleVertex 1) (cycleVertex_consecutive_ne 0)
    F (2*R^(2*Fintype.card TupleVertex)) E hE hb hg
  simp only [Fintype.card_fin] at hav
  have hid : multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => actualTruncatedLift p N Q (smallResidueInput (smallModulus ps) A (s v)))=
      ((K:ℝ)*L/N)^(Fintype.card TupleVertex)*(𝔼 a,F a) := by
    exact block_multilinear_identity p _ N K L Q (by omega) (by omega) hL hNKL
      (fun v => smallResidueInput (smallModulus ps) A (s v))
      (fun v => smallResidueInput_zero _ N A hA _)
  rw [hid,abs_mul,abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hfac _) hav (abs_nonneg _) (by positivity)

end Global

end SquareDifference

end

end OAI
