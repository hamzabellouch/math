import OAI.NumberTheory.TotientAsymptotic.SquareLayerSum

namespace OAI

/-! All positive-index squarefree failures, including alternate witnesses. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareInternalRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (Finset.Icc 1 (R x H)).biUnion (squareLayerRemainders x H)

lemma squareLayerRemainders_basic {x : ℝ} {H i : ℕ}
    {η : RemainderDatum (L x H)} (hη : η ∈ squareLayerRemainders x H i) :
    IsBasicRemainder x H η := by
  obtain ⟨q,_,hj⟩ := Finset.mem_biUnion.mp hη
  obtain ⟨j,_,hk⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨k,_,hη⟩ := Finset.mem_biUnion.mp hk
  exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1

lemma squareInternalRemainders_basic {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : η ∈ squareInternalRemainders x H) :
    IsBasicRemainder x H η := by
  obtain ⟨i,_,hη⟩ := Finset.mem_biUnion.mp hη
  exact squareLayerRemainders_basic hη

lemma square_failure_mem_layer : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      ¬SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (remainderPrime η j-1))
        (collisionSmoothCutoff x i) → η ∈ squareLayerRemainders x H i := by
  filter_upwards [eventually_collision_indices,ford_band_polynomial_lower 1,eventually_ge_atTop 2]
    with H hind hpoly hH
  filter_upwards [hpoly,basic_suffix_discard_bound,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hp hb hHm
  intro i hi hiR η hη hfail
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb2 : 2 ≤ fordBandScale x i := by
    have hh := hp i him hHi
    simp only [pow_one] at hh
    exact (show (2 : ℝ) ≤ (m x-i : ℕ) by exact_mod_cast hH.trans hHi).trans hh
  have hcut := (hind x hHm i hiR).2.2
  obtain ⟨q,hq,hqz,hqd⟩ : ∃ q : ℕ, q.Prime ∧ collisionSmoothCutoff x i < q ∧
      q^2 ∣ ∏ j ∈ Finset.Icc i (collisionLastIndex x i), (remainderPrime η j-1) := by
    simpa only [SquarefreeAbove,not_forall,not_imp,not_not,exists_prop] using hfail
  have hjN (j : ℕ) (hj : j ∈ Finset.Icc i (collisionLastIndex x i)) :
      remainderPrime η j ∈ Nat.primesLE (discardPrimeBound (fordBandScale x i)) :=
    hb H i j (hi.trans (Finset.mem_Icc.mp hj).1) (Finset.mem_Icc.mp hj).1
      ((Finset.mem_Icc.mp hj).2.trans hcut.le) him hb2 η hη
  have hqN (j : ℕ) (hj : j ∈ Finset.Icc i (collisionLastIndex x i))
      (hqd : q ∣ remainderPrime η j-1) : q ∈ squareLayerPrimes x i := by
    have hpj := Nat.mem_primesLE.mp (hjN j hj)
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hpj.2.one_lt) hqd
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨hle.trans ((Nat.sub_le _ _).trans hpj.1),hq⟩,hqz⟩
  rcases square_dvd_product _ _ hq hqd with ⟨j,hj,hj2⟩ | ⟨j,hj,k,hk,hjk,hqj,hqk⟩
  · have hqj : q ∣ remainderPrime η j-1 := (dvd_pow_self q (by norm_num : 2 ≠ 0)).trans hj2
    refine Finset.mem_biUnion.mpr ⟨q,hqN j hj hqj,Finset.mem_biUnion.mpr ⟨j,?_,Finset.mem_biUnion.mpr ⟨j,?_,?_⟩⟩⟩
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans hcut.le⟩
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans hcut.le⟩
    · exact Finset.mem_filter.mpr ⟨mem_basicRemainderFinset.mpr hη,by simpa only [ite_true] using hj2⟩
  · refine Finset.mem_biUnion.mpr ⟨q,hqN j hj hqj,Finset.mem_biUnion.mpr ⟨j,?_,Finset.mem_biUnion.mpr ⟨k,?_,?_⟩⟩⟩
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans hcut.le⟩
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,(Finset.mem_Icc.mp hk).2.trans hcut.le⟩
    · exact Finset.mem_filter.mpr ⟨mem_basicRemainderFinset.mpr hη,by simpa only [ite_eq_right hjk] using And.intro hqj hqk⟩

lemma square_internal_reciprocal_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        (∑ η ∈ squareInternalRemainders x H, remainderReciprocalWeight η) ≤ ε H*G x (m x) := by
  obtain ⟨E,hE,hcof⟩ := tail_cofactor_sum hmertens
  let ε := fun H => E*Real.exp ((4*(lam/rho))*cofactorScale H)*polynomialGeometricTail 0 rho H
  refine ⟨ε,?_,?_⟩
  · have hh := (cofactor_polynomialGeometricTail_tendsto (4*(lam/rho)) 0 rho_pos.le rho_lt_one).const_mul E
    simpa only [ε,mul_assoc,mul_zero] using hh
  filter_upwards [square_layer_reciprocal_discard hbox hren hmertens] with H hH
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hHm hB
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hG : 0 ≤ G x (m x) := (G_pos hB _).le
  have hw : W ≤ E*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [W,cofactorScale,mul_assoc] using hcof H
  have hsum : (∑ i ∈ Finset.Icc 1 (R x H), rho^(m x-i)) ≤ polynomialGeometricTail 0 rho H := by
    apply le_trans _ (reverse_geometric_sum hHm)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hi).2⟩)
      (fun i _ _ => (pow_pos rho_pos _).le)
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 (R x H), ∑ η ∈ squareLayerRemainders x H i, remainderReciprocalWeight η :=
      nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg
        (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
    _ ≤ ∑ i ∈ Finset.Icc 1 (R x H), W*G x (m x)*rho^(m x-i) :=
      Finset.sum_le_sum (fun i hi => hx i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
    _ = W*G x (m x)*(∑ i ∈ Finset.Icc 1 (R x H), rho^(m x-i)) := by rw [Finset.mul_sum]
    _ ≤ (E*Real.exp ((4*(lam/rho))*cofactorScale H))*G x (m x)*polynomialGeometricTail 0 rho H := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hw hG
      · exact hsum
      · exact Finset.sum_nonneg (fun _ _ => (pow_pos rho_pos _).le)
      · positivity
    _ = _ := by dsimp [ε]; ring

end TotientAsymptotic

end

end OAI
