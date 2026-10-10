import OAI.NumberTheory.TotientAsymptotic.HeadSquareSum
import OAI.NumberTheory.TotientAsymptotic.AllCollisionCount

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headSquareFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧
    ¬SquarefreeAbove (∏ j ∈ Finset.Icc 0 (collisionLastIndex x 0), (wholeWitnessPrime τ.head η j-1))
      (collisionSmoothCutoff x 0))

lemma headSquareFailure_card_le : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ t ≤ x, (headSquareFailureTuples x H t).card ≤ (headSquareFamily x H t).card := by
  filter_upwards [eventually_collision_indices,eventually_ge_atTop 2] with H hind hH
  filter_upwards [full_witness_prime_bound,m_tendsto.eventually (eventually_ge_atTop H)] with x hb hm
  intro t ht
  have hPH := (P_lt_self hH).le
  have hcut := (hind x hm 0 (Nat.zero_le _)).2.2
  have hsub : headSquareFailureTuples x H t ⊆
      (headSquareFamily x H t).image (fun w => witnessTuple w.2 w.1) := by
    intro τ hτ
    obtain ⟨hτ,η,hη,he,hfail⟩ := Finset.mem_filter.mp hτ
    have hτb := (mem_tupleFinset hPH).mp hτ
    have hw : witnessTuple τ.head η=τ := by
      cases τ
      simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
    have hwb : IsBasicTuple x H t (witnessTuple τ.head η) := hw.symm ▸ hτb
    let w : RemainderDatum (L x H) × ℕ := (η,τ.head)
    have hbasic : w ∈ witnessFamily t (basicRemainderFinset x H) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨mem_basicRemainderFinset.mpr hη,Finset.mem_range.mpr (basic_tuple_head_bound hPH hτb)⟩,hwb⟩
    obtain ⟨q,hq,hqz,hqd⟩ : ∃ q : ℕ, q.Prime ∧ collisionSmoothCutoff x 0 < q ∧
        q^2 ∣ ∏ j ∈ Finset.Icc 0 (collisionLastIndex x 0), (wholeWitnessPrime τ.head η j-1) := by
      simpa only [SquarefreeAbove,not_forall,not_imp,not_not,exists_prop] using hfail
    have hprime (j : ℕ) (hj : j ∈ Finset.Icc 0 (collisionLastIndex x 0)) :
        wholeWitnessPrime τ.head η j ∈ Nat.primesLE (discardPrimeBound (B x)) := by
      have hjL := (Finset.mem_Icc.mp hj).2.trans hcut.le
      rw [wholeWitnessPrime_full w hjL]
      exact hb H hPH t ht w hη hwb _
    have hqN (j : ℕ) (hj : j ∈ Finset.Icc 0 (collisionLastIndex x 0))
        (hd : q ∣ wholeWitnessPrime τ.head η j-1) : q ∈ squareLayerPrimes x 0 := by
      have hp := Nat.mem_primesLE.mp (hprime j hj)
      have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.2.one_lt) hd
      refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_,hq⟩,hqz⟩
      have hh := hle.trans ((Nat.sub_le _ _).trans hp.1)
      simpa [fordBandScale] using hh
    have hjL (j : ℕ) (hj : j ∈ Finset.Icc 0 (collisionLastIndex x 0)) :
        j ∈ Finset.Icc 0 (L x H) :=
      Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hj).2.trans hcut.le⟩
    have hmem : w ∈ headSquareFamily x H t := by
      let : DecidableEq (RemainderDatum (L x H) × ℕ) := Classical.decEq _
      rcases square_dvd_product _ _ hq hqd with ⟨j,hj,hj2⟩ | ⟨j,hj,k,hk,hjk,hqj,hqk⟩
      · have hqj : q ∣ wholeWitnessPrime τ.head η j-1 := (dvd_pow_self q (by norm_num : 2 ≠ 0)).trans hj2
        refine Finset.mem_biUnion.mpr ⟨q,hqN j hj hqj,Finset.mem_biUnion.mpr
          ⟨j,hjL j hj,Finset.mem_biUnion.mpr ⟨j,hjL j hj,?_⟩⟩⟩
        exact Finset.mem_filter.mpr ⟨hbasic,by simpa only [w,ite_true] using hj2⟩
      · refine Finset.mem_biUnion.mpr ⟨q,hqN j hj hqj,Finset.mem_biUnion.mpr
          ⟨j,hjL j hj,Finset.mem_biUnion.mpr ⟨k,hjL k hk,?_⟩⟩⟩
        exact Finset.mem_filter.mpr ⟨hbasic,by simpa only [w,ite_eq_right hjk] using And.intro hqj hqk⟩
    exact Finset.mem_image.mpr ⟨w,hmem,hw⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem head_square_tuple_discard (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((headSquareFailureTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨E,hE,hcof⟩ := tail_cofactor_sum hmertens
  let ε := fun H => E*Real.exp ((4*(lam/rho))*cofactorScale H)*polynomialGeometricTail 0 rho H
  refine ⟨ε,?_,?_⟩
  · have hh := (cofactor_polynomialGeometricTail_tendsto (4*(lam/rho)) 0 rho_pos.le rho_lt_one).const_mul E
    simpa only [ε,mul_assoc,mul_zero] using hh
  filter_upwards [headSquareFailure_card_le,head_square_family_count hmertens] with H hcard hcount
  filter_upwards [hcard,hcount,G_eventually_one_le hren,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ)] with x hc hn hG hHm hx
  intro t ht
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hw : W ≤ E*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [W,cofactorScale,mul_assoc] using hcof H
  have hr : rho^(m x) ≤ polynomialGeometricTail 0 rho H := by
    apply le_trans _ (reverse_geometric_sum hHm)
    simpa only [Nat.sub_zero] using
      (Finset.single_le_sum (f := fun i => rho^(m x-i))
        (fun _ _ => (pow_pos rho_pos _).le)
        (Finset.mem_Icc.mpr ⟨le_rfl,Nat.zero_le (m x-H)⟩))
  have hscale : 0 ≤ x/Real.log x := div_nonneg (zero_lt_one.trans hx).le (Real.log_pos hx).le
  have hsmall : W*rho^(m x) ≤ ε H := by
    apply mul_le_mul hw hr
    · exact (pow_pos rho_pos _).le
    · positivity
  have heps : 0 ≤ ε H := mul_nonneg (by positivity) (polynomialGeometricTail_nonneg 0 rho_pos.le H)
  calc
    _ ≤ ((headSquareFamily x H t).card : ℝ) := Nat.cast_le.mpr (hc t ht)
    _ ≤ (x/Real.log x)*(W*rho^(m x)) := by simpa only [W,mul_assoc] using hn t ht
    _ ≤ (x/Real.log x)*ε H := mul_le_mul_of_nonneg_left hsmall hscale
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG (mul_nonneg hscale heps)
      simpa only [mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh

end TotientAsymptotic

end

end OAI
