import OAI.Combinatorics.SquareDifference.CRTTransfer

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

def LiftSizeConditions (L Q : ℕ) : Prop :=
  0<L ∧ 0<Q ∧ 2*(Q:ℝ)≤L ∧ (Q:ℝ)^5≤L

lemma uniform_partial_lift_moments (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,Fact (p j).Prime],Function.Injective p →
      ∀(L Q N : ℕ),LiftSizeConditions L Q → Q≤N →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n<L,|f n|≤M) →
      ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L f U x)^(2*r))≤(C*M*(N:ℝ)^ε)^(2*r) := by
  obtain ⟨C,hC,hb⟩ := uniform_common_lift_moments (V:=TupleVertex) ε hε
  refine ⟨C,hC,?_⟩
  intro J _ _ p _ hinj L Q N hs hQN f M hM hf t ht r hr
  have hp : Pairwise fun i j => (p i).Coprime (p j) := by
    intro i j hij
    exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr
      (fun h => hij (hinj ((Nat.prime_dvd_prime_iff_eq (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mp h))))
  apply (hb p hp hinj t Q hs.2.1 (fun U hU => (mem_filter.mp (ht hU)).2)
    L hs.1 hs.2.2.1 hs.2.2.2 f M hM hf r hr).trans
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hQN) hε.le)
    (mul_nonneg hC.le hM)

lemma fiber_transfer_algebra (l K H C t m q : ℝ) (d : ℕ) :
    l^d*(K+(d:ℝ)*H*(C*t)^d)+(d:ℝ)*H*q*(C*m*t)^d=
      l^d*K+(d:ℝ)*H*(C*t)^d*(l^d+q*m^d) := by
  rw [show C*m*t=(C*t)*m by ring,mul_pow]
  ring

lemma uniform_actual_fiber_transfer (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,Fact (p j).Prime],Function.Injective p →
      (∀j,tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) →
      ∀(M : ℕ) [NeZero M],(∀j,M.Coprime (p j)) →
      ∀(N Q H L Qc : ℕ) (B : Finset J) (s : ZMod M) (z : ResidueSpace p),
      LiftSizeConditions N Q → LiftSizeConditions L Qc → Q≤N → Qc≤N →
      0<H → H*(∏j∈B,p j)≤Q → H≤Qc → N≤(M*(∏j∈B,p j))^2*L →
      ∀(A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀K : ℝ,0≤K →
      (∀A' : Finset ℕ,A'⊆range L → NatSquareFree A' → setFunctional p L Qc A'≤K) →
      diagonalIntegral (productTupleLaw p)
        (fun x => actualTruncatedLift p N Q (smallResidueInput M A s) (freezeCoordinates B z x))≤
      (((M*(∏j∈B,p j):ℕ):ℝ)^2*L/N)^(Fintype.card TupleVertex)*K+
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(C*(N:ℝ)^ε)^(Fintype.card TupleVertex)*
        ((((M*(∏j∈B,p j):ℕ):ℝ)^2*L/N)^(Fintype.card TupleVertex)+
          (∏j∈B,p j:ℝ)*(M:ℝ)^(Fintype.card TupleVertex)) := by
  obtain ⟨C,hC,hb⟩ := uniform_partial_lift_moments ε hε
  refine ⟨C,hC,?_⟩
  intro J _ _ p _ hinj hcond href M _ hM N Q H L Qc B s z hs hs' hQN hQcN hH hHQ hHQc hNL A hA hfree K hK hchild
  have hp : Pairwise fun i j => (p i).Coprime (p j) := by
    intro i j hij
    exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr
      (fun h => hij (hinj ((Nat.prime_dvd_prime_iff_eq (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mp h))))
  have hh := actual_set_fiber_transfer p hp M hM hcond href N Q H L Qc B s z
    hH hHQ hHQc hs'.1 hNL A hA hfree K (C*M*(N:ℝ)^ε) (C*(N:ℝ)^ε)
    hK (by positivity) (by positivity)
    (fun t ht r hr => hb p hinj N Q N hs hQN _ M (Nat.cast_nonneg _)
      (fun n _ => smallResidueInput_bound M A s n) t ht r hr)
    (by
      intro A' hA' t ht r hr
      simpa only [mul_one] using hb p hinj L Qc N hs' hQcN (natIndicator A') 1
        (by norm_num) (fun n _ => natIndicator_bound A' n) t ht r hr)
    hchild
  exact hh.trans_eq (fiber_transfer_algebra _ _ _ _ _ _ _ _)

end SquareDifference

end

end OAI
