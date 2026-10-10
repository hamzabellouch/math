import OAI.Combinatorics.SquareDifference.TransferRates

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma source_actual_fiber_transfer (M : ℕ) [NeZero M] (hM2 : 2≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective p → (∀j,tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) → (∀j,M.Coprime (p j)) →
      ∀(B : Finset J),(∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau (Fintype.card TupleVertex)) →
      ∀(s : ZMod M) (z : ResidueSpace p) (A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀K : ℝ,0≤K →
      (∀A' : Finset ℕ,A'⊆range (childLength N (M*(∏j∈B,p j))) → NatSquareFree A' →
        setFunctional p (childLength N (M*(∏j∈B,p j)))
          (powerCutoff (childLength N (M*(∏j∈B,p j))) sourceBeta) A'≤K) →
      diagonalIntegral (productTupleLaw p)
        (fun x => actualTruncatedLift p N (powerCutoff N sourceBeta)
          (smallResidueInput M A s) (freezeCoordinates B z x))≤
      transferFactor (Fintype.card TupleVertex) M N*K+C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex)) := by
  let d := Fintype.card TupleVertex
  obtain ⟨C,hC,hb⟩ := uniform_actual_fiber_transfer (sourceLoss d) (sourceLoss_pos d)
  let E : ℝ := (d:ℝ)*C^d*((2:ℝ)^d+(M:ℝ)^d)
  refine ⟨E+1,by dsimp [E]; positivity,?_⟩
  have he := eventual_cutoff_rpow_lower (sourceBeta/2) (sourceBeta/3)
    (by have := sourceBeta_pos; linarith) (by have := sourceBeta_pos; linarith)
  filter_upwards [eventual_transfer_scales d M hM2,he,eventually_ge_atTop 1] with N hscale he hN
  intro J _ _ p _ hinj hcond href hM B hB s z A hA hfree K hK hchild
  let q := ∏j∈B,p j
  have hq : 0<q := prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)
  have hq' : (q:ℝ)≤(N:ℝ)^(sourceTau d) := by exact_mod_cast hB
  obtain ⟨hL,hLN,hhalf,hsize,hsize',hQN,hQcN,hH,hHQ,hHQc,hcover,hl1,hl2⟩ := hscale q hq hq'
  have ht := hb p hinj hcond href M hM N (powerCutoff N sourceBeta)
    (powerCutoff N (sourceBeta/2)) (childLength N (M*q))
    (powerCutoff (childLength N (M*q)) sourceBeta) B s z hsize hsize' hQN hQcN
    hH hHQ hHQc hcover A hA hfree K hK hchild
  have herr := transfer_error_bound d M N (powerCutoff N (sourceBeta/2)) q C
    (((M*q:ℕ):ℝ)^2*(childLength N (M*q):ℝ)/N) hN hC.le (by positivity) hl2 he hq'
  have hfactor := child_factor_le d M N q (by omega) (Nat.mul_pos (by omega) hq) hq'
  have herr' := herr.trans (mul_le_mul_of_nonneg_right
    (show E≤E+1 from le_add_of_nonneg_right zero_le_one)
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-sourceSigma d)))
  have hb' := add_le_add (mul_le_mul_of_nonneg_right hfactor hK) herr'
  apply ht.trans
  simpa only [d,E,sourceGamma,Nat.cast_prod,q,neg_div] using hb'

end SquareDifference

end

end OAI
