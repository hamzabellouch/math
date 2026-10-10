import OAI.Combinatorics.SquareDifference.InductionParameters

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma weighted_affine_sum_bound {I : Type*} (S : Finset I) (w k : I → ℝ)
    (c e : ℝ) (hc : 0≤c) (he : 0≤e)
    (hwk : (∑i∈S,w i*k i)≤1/4) (hw : (∑i∈S,w i)≤1) :
    (∑i∈S,w i*(c*k i+e))≤c/4+e := by
  have heq : (∑i∈S,w i*(c*k i+e))=c*(∑i∈S,w i*k i)+e*(∑i∈S,w i) := by
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [heq]
  nlinarith

lemma source_inductive_step {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] (hM2 : 2 ≤ smallModulus ps) :
    ∃E : ℝ,0<E ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective (extendedPrime ps p) → (∀j,64≤p j) →
      (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) → (∀j,(smallModulus ps).Coprime (p j)) →
      (∀j,tupleEta (p j)≤1/(p j:ℝ)^4) →
      (∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r) →
      ∀a : ℝ,0≤a → 2*a≤1 → ∀D : ℝ,0≤D →
      (∀ n : ℕ,1≤n → n<N → ∀A' : Finset ℕ,A'⊆range n → NatSquareFree A' →
        setFunctional p n (powerCutoff n sourceBeta) A'≤D*(n:ℝ)^(-a)) →
      ∀A : Finset ℕ,A⊆range N → NatSquareFree A →
      setFunctional p N (powerCutoff N sourceBeta) A≤E*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex))+
        transferFactor (Fintype.card TupleVertex) (smallModulus ps) N*D*(N:ℝ)^(-a)*
          ((smallModulus ps:ℝ)^(2*a)*(1-3*goodSmallProbability ps/4)) := by
  classical
  let d := Fintype.card TupleVertex
  let M := smallModulus ps
  let : NeZero M := ⟨by omega⟩
  obtain ⟨Ct,hCt,ht⟩ := source_mixed_transfer M hM2
  obtain ⟨Cc,hCc,hc⟩ := source_mixed_crude M
  obtain ⟨Co,hCo,ho⟩ := source_ordered_contraction ps
  let E := Co+Ct+Cc
  have hE : 0<E := by dsimp [E]; linarith
  refine ⟨E,hE,?_⟩
  filter_upwards [ht,hc,ho,eventually_ge_atTop 2] with N ht hc ho hN
  intro J _ _ p _ hinj hp hmass href hcop heta hcover a ha ha1 D hD hind A hA hfree
  have hN1 : 1≤N := by omega
  have hN0 : 0<N := by omega
  have hinjp : Function.Injective p := fun i j hij => Sum.inr.inj (hinj hij)
  have hmass' (j : J) := (le_max_left _ _).trans (hmass j)
  let q : Finset J → ℕ := fun B => ∏j∈B,p j
  have hq (B : Finset J) : 0<q B := prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)
  let X := D*(M:ℝ)^(2*a)*(N:ℝ)^(-a)
  let T := transferFactor d M N
  let e := (N:ℝ)^(-sourceSigma d)
  have hX : 0≤X := mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hT : 0≤T := transferFactor_nonneg _ _ _
  have he : 0≤e := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let F : (TupleVertex → ZMod M) → TupleVertex → ResidueSpace p → ℝ :=
    fun s v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v))
  have hsmall (B : Finset J) (hB : (∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau d)) (s : TupleVertex → ZMod M) :
      |multilinearIntegral (actualMixedLaw p B) (F s)|≤exceptionalProduct p B*(T*(X*(∏j∈B,p j:ℝ)^(2*a))+Ct*e) := by
    have hL : 0<childLength N (M*q B) := childLength_pos N _ hN0 (Nat.mul_pos (by omega) (hq B))
    have hLN : childLength N (M*q B)<N := childLength_lt N _ hN (by nlinarith [hq B])
    have ht' := ht p hinjp hmass href hcop B hB s A hA hfree
      (D*(childLength N (M*q B):ℝ)^(-a))
      (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun A' hA' hf => hind _ (by omega) hLN A' hA' hf)
    apply ht'.trans
    apply mul_le_mul_of_nonneg_left _ (exceptionalProduct_nonneg p B)
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hT
    have hl := mul_le_mul_of_nonneg_left (childLength_product_rpow_bound N M (q B) hN0 (by omega) (hq B) a ha) hD
    apply hl.trans_eq
    dsimp [X,q]
    rw [Nat.cast_prod]
    ring
  have hbad (s : TupleVertex → ZMod M) :
      |multilinearIntegral (productTupleLaw p) (F s)|≤T*X+E*e := by
    have hh := hsmall ∅ (by simpa only [prod_empty] using Real.one_le_rpow (by exact_mod_cast hN1) (sourceTau_pos d).le) s
    simp only [actualMixedLaw_empty,exceptionalProduct,prod_empty,Real.one_rpow,mul_one,one_mul] at hh
    apply hh.trans
    have hCtE : Ct≤E := by dsimp [E]; linarith
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCtE he)
  have hgood (s : TupleVertex → ZMod M) (hs : goodSmallAssignment ps s) :
      |multilinearIntegral (productTupleLaw p) (F s)|≤T*X/4+E*e := by
    have ho' := ho p hinj hp hmass hcover A hA hfree s hs
    have hi := actual_exceptional_bound p hmass' (tupleEta_le_one_of_fourth p heta) (F s)
    let U : Finset (Finset J) := univ.erase ∅
    let V := U.filter (fun B => (∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau d))
    let W := U.filter (fun B => (N:ℝ)^(sourceTau d)<(∏j∈B,p j:ℝ))
    have hps (j : J) : 5≤p j := (by omega : 5≤64).trans (hp j)
    have hsw := exceptional_small_power_budget p hinjp hps heta V (filter_subset _ _) (2*a) ha1
    have hw : (∑B∈V,exceptionalProduct p B)≤1 := by
      have hh := exceptional_small_power_budget p hinjp hps heta V (filter_subset _ _) 0 (by norm_num)
      simp only [Real.rpow_zero,mul_one] at hh
      linarith
    have hvs : (∑B∈V,|multilinearIntegral (actualMixedLaw p B) (F s)|)≤T*X/4+Ct*e := by
      apply le_trans (sum_le_sum (fun B hB => hsmall B (mem_filter.mp hB).2 s))
      simpa only [mul_assoc] using weighted_affine_sum_bound V (exceptionalProduct p) (fun B => (∏j∈B,p j:ℝ)^(2*a))
        (T*X) (Ct*e) (mul_nonneg hT hX) (mul_nonneg hCt.le he) hsw hw
    have hws : (∑B∈W,|multilinearIntegral (actualMixedLaw p B) (F s)|)≤Cc*e := by
      have hh := exceptional_large_tail p hinjp hps heta N hN0 (sourceTau d)
      calc
        _ ≤ ∑B∈W,exceptionalProduct p B*(Cc*(N:ℝ)^(2*(d:ℝ)*sourceLoss d)) :=
          sum_le_sum (fun B _ => hc p hinjp hmass' B A s)
        _ = (∑B∈W,exceptionalProduct p B)*(Cc*(N:ℝ)^(2*(d:ℝ)*sourceLoss d)) := (sum_mul ..).symm
        _ ≤ ((N:ℝ)^(-sourceTau d)/4)*(Cc*(N:ℝ)^(2*(d:ℝ)*sourceLoss d)) :=
          mul_le_mul_of_nonneg_right hh (mul_nonneg hCc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _ ≤ _ := crude_tail_rate d N hN1 Cc hCc.le
    have hu : (∑B∈U,|multilinearIntegral (actualMixedLaw p B) (F s)|)=
        (∑B∈V,|multilinearIntegral (actualMixedLaw p B) (F s)|)+(∑B∈W,|multilinearIntegral (actualMixedLaw p B) (F s)|) := by
      simpa only [not_le] using (sum_filter_add_sum_filter_not U (fun B => (∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau d))
        (fun B => |multilinearIntegral (actualMixedLaw p B) (F s)|)).symm
    rw [hu] at hi
    dsimp [E]
    linarith
  rw [setFunctional_small_average p N (powerCutoff N sourceBeta) M A]
  apply (le_abs_self _).trans
  have hav := event_average_bound (goodSmallAssignment ps) (fun s => multilinearIntegral (productTupleLaw p) (F s))
    (T*X/4+E*e) (T*X+E*e) hgood (fun s _ => hbad s)
  apply hav.trans_eq
  change goodSmallProbability ps*(T*X/4+E*e)+(1-goodSmallProbability ps)*(T*X+E*e)=_
  dsimp [X,T,e]
  ring

end SquareDifference

end

end OAI
