import OAI.Combinatorics.SquareDifference.OrderedRates

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma orderedErrorConstant_nonneg (d M : ℕ) (C : ℝ) (hC : 0≤C) : 0≤orderedErrorConstant d M C := by
  unfold orderedErrorConstant
  exact add_nonneg (add_nonneg (add_nonneg (by positivity) (by positivity))
    (mul_nonneg (by positivity) kernelAbsoluteConstant_nonneg)) (by positivity)

lemma source_ordered_contraction {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective (extendedPrime ps p) → (∀j,64≤p j) →
      (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r) →
      ∀(A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀s : TupleVertex → ZMod (smallModulus ps),
      (∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1)))) →
      |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta)
          (smallResidueInput (smallModulus ps) A (s v)))|≤C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex)) := by
  let d := Fintype.card TupleVertex
  let M := smallModulus ps
  obtain ⟨C,hC,hb⟩ := uniform_interval_moments (sourceLoss d) (sourceLoss_pos d)
  let C' := (C+1)*((M:ℝ)+1)
  have hC' : 1≤C' := by dsimp [C']; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  let E := (2:ℝ)^d*orderedErrorConstant d M C'
  have hE : 0≤E := mul_nonneg (by positivity) (orderedErrorConstant_nonneg d M C' (by linarith))
  refine ⟨E+1,by linarith,?_⟩
  filter_upwards [eventual_block_scales d M] with N hscale
  intro J _ _ p _ hinj hp hmass hcover A hA hfree s hgood
  dsimp only at hscale
  obtain ⟨hN,hK,hL,hNKL,hfac,hNL,hsize,hQN,hH,hHQ,hD,hHn,hlarge,hKl,hHl⟩ := hscale
  let K := powerCutoff N (sourceTau d)
  let L := blockLength N K
  let H := powerCutoff N (sourceBeta/2)
  have hinjp : Function.Injective p := fun i j hij => Sum.inr.inj (hinj (show extendedPrime ps p (Sum.inr i)=extendedPrime ps p (Sum.inr j) from hij))
  have hR : 1≤C'*(N:ℝ)^(sourceLoss d) := one_le_mul_of_one_le_of_one_le hC'
    (Real.one_le_rpow (by exact_mod_cast hN) (sourceLoss_pos d).le)
  have hm (a : ℕ) (v : TupleVertex) (t : Finset (Finset J)) (ht : t⊆liftSupportFamily p (powerCutoff N sourceBeta))
      (r : ℕ) (hr : r=1 ∨ r+1=d) :
      (𝔼 x,(∑U∈t,intervalPiece p a L (smallResidueInput M A (s v)) U x)^(2*r))≤
        (C'*(N:ℝ)^(sourceLoss d))^(2*r) := by
    apply (hb p hinjp a L (powerCutoff N sourceBeta) N hsize hQN _ M (Nat.cast_nonneg _) (smallResidueInput_bound M A _) t ht r hr).trans
    apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg M)) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp [C']; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  have he := ordered_global_estimate ps p hinj hp hmass L N (powerCutoff N sourceBeta) H K hN hL
    hH hK hNKL hfac hNL hHQ (by simpa only [Nat.cast_mul,Nat.cast_pow] using hD) hHn hlarge hcover
    A hA hfree s hgood _ hR hm
  have hr := orderedError_bound d M N K H C' (by linarith) hN (powerCutoff_le N _) hKl hHl
  have he' : |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)))|≤
      (2:ℝ)^d*orderedError d M N K H C' := by
    simpa only [orderedError,sourceGamma,neg_div,add_assoc] using he
  calc
    _ ≤ (2:ℝ)^d*(orderedErrorConstant d M C'*(N:ℝ)^(-sourceSigma d)) :=
      he'.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    _ ≤ (E+1)*(N:ℝ)^(-sourceSigma d) := by
      dsimp [E]
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-sourceSigma d)]

end SquareDifference

end

end OAI
