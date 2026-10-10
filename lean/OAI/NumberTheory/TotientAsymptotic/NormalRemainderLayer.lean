import OAI.NumberTheory.TotientAsymptotic.ExceptionalPrimeLayer
import OAI.NumberTheory.TotientAsymptotic.PrimeDiscardCutoff
import OAI.NumberTheory.TotientAsymptotic.RestrictedWitnessCount

namespace OAI

/-! Ford normality applied to each actual positive-index witness layer. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalRemainders (x : ℝ) (H i j : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter (fun η =>
    ¬ IsNormalPrime (normalityScale x i) (remainderPrime η j))

lemma primeFinal_remainder {x : ℝ} {H n : ℕ} (η : RemainderDatum (L x H))
    (j : Fin (L x H-n)) :
    primeFinal η.primes n j=remainderPrime η (n+j.val+1) := by
  have hj : 1 ≤ n+j.val+1 ∧ n+j.val+1 ≤ L x H := by have := j.isLt; omega
  simp only [primeFinal,remainderPrime,dite_eq_left hj,Nat.add_sub_cancel]

lemma basic_suffix_discard_bound : ∀ᶠ x : ℝ in atTop, ∀ H i j : ℕ,
    1 ≤ j → i ≤ j → j ≤ L x H → i < m x → 2 ≤ fordBandScale x i →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      remainderPrime η j ∈ Nat.primesLE (discardPrimeBound (fordBandScale x i)) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx
  intro H i j hj1 hij hj him hb η hη
  have hp := hη.2.1 j (Finset.mem_Icc.mpr ⟨hj1,hj⟩)
  have hbi := (bandScale_pos him)
  have hf : (99/100 : ℝ)*bandScale x i ≤ fordBandScale x i := by
    have hh := (abs_lt.mp (hx i him)).1
    have hd := (lt_div_iff₀ hbi).mp (by linarith : (99/100 : ℝ)<fordBandScale x i/bandScale x i)
    exact hd.le
  have hcoord : B (remainderPrime η j) ≤ (6/5 : ℝ)*fordBandScale x i := by
    have hm := bandScale_antitone x hij
    have hu0 : B (remainderPrime η j) ≤ (11/10 : ℝ)*bandScale x j := by
      simpa only [remainderCoord,B,ite_eq_right (show j ≠ 0 by omega)] using hp.2.2
    have hu := hu0.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 11/10))
    nlinarith
  have hpR : (1 : ℝ) < remainderPrime η j := by exact_mod_cast hp.1.one_lt
  have hex : (remainderPrime η j : ℝ) ≤ Real.exp (Real.exp ((6/5 : ℝ)*fordBandScale x i)) := by
    exact (Real.log_le_iff_le_exp (zero_lt_one.trans hpR)).mp
      ((Real.log_le_iff_le_exp (Real.log_pos hpR)).mp hcoord)
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hex.trans (discardPrimeBound_bounds hb).2.2.2,hp.1⟩

theorem normal_remainder_layer_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) (hford : FordLemma26Input) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ i j : ℕ, i ≤ R x H → 1 ≤ j → i ≤ j → j ≤ L x H →
      let b := fordBandScale x i
      (∑ η ∈ nonNormalRemainders x H i j, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (C*(2*b+2)^6*Real.exp (-(b^(1/3 : ℝ))/6))*(D*(2*b+2))^(L x H-(i-1)-1) := by
  obtain ⟨C,hC,hbad⟩ := discard_normal_mass hford
  obtain ⟨D,hD,hall⟩ := prime_reciprocal_mass_bound hmertens
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [basic_prime_initial_mass hbox hren,ford_band_polynomial_lower 1,
    eventually_ge_atTop 2] with H hprefix hpoly hH
  filter_upwards [hprefix,hpoly,basic_suffix_discard_bound,theta_eventually_mem,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hpref hp hb hs hHm hBx
  intro i j hiR hj1 hij hj
  dsimp only
  let b := fordBandScale x i
  let S := nonNormalRemainders x H i j
  let Q := S.image RemainderDatum.primes
  let n := i-1
  have hPH := P_lt_self hH
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb2 : 2 ≤ b := by
    have hh := hp i him hHi
    have hh2 : (2 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
    simp only [pow_one] at hh
    exact hh2.trans hh
  have hnR : n ≤ R x H := by dsimp [n]; omega
  have hnL : n ≤ L x H := by unfold R L at *; omega
  have hS : ∀ η ∈ S, IsBasicRemainder x H η := by
    intro η hη
    exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1
  have hQ : Q ⊆ fullPrimeTuples x H := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨η,mem_basicRemainderFinset.mpr (hS η hη),rfl⟩
  let k : Fin (L x H-n) := ⟨j-(n+1),by dsimp [n]; omega⟩
  have hjk : n+k.val+1=j := by dsimp [n,k]; omega
  have hallQ : ∀ p ∈ Q, ∀ l, primeFinal p n l ∈ Nat.primesLE (discardPrimeBound b) := by
    intro p hp l
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder]
    apply hb H i (n+l.val+1) (by omega) (by dsimp [n]; omega) (by have := l.isLt; omega) him hb2 η (hS η hη)
  have hbadQ : ∀ p ∈ Q, primeFinal p n k ∈ nonNormalPrimes (normalityScale x i) (discardPrimeBound b) := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hallQ η.primes (Finset.mem_image.mpr ⟨η,hη,rfl⟩) k,?_⟩
    rw [primeFinal_remainder,hjk]
    exact (Finset.mem_filter.mp hη).2
  have hmass := prime_mass_one_exception hnL Q k _ _ hallQ hbadQ
  have hpre := hpref n hnR hnL Q hQ
  have hbadmass := hbad b hb2
  have hgoodmass : (∑ p ∈ Nat.primesLE (discardPrimeBound b), ((p-1 : ℕ) : ℝ)⁻¹) ≤ D*(2*b+2) := by
    obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb2
    exact (hall _ (by omega) hBN).trans (mul_le_mul_of_nonneg_left (by linarith) hD.le)
  have hpow : L x H-n-1=L x H-(i-1)-1 := rfl
  rw [hpow] at hmass
  have hmass' : (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      G x (m x)*(C*(2*b+2)^6*Real.exp (-(b^(1/3 : ℝ))/6))*(D*(2*b+2))^(L x H-(i-1)-1) := by
    apply hmass.trans
    apply mul_le_mul
    · exact mul_le_mul hpre hbadmass (Finset.sum_nonneg (fun p _ => by positivity)) (G_pos hBx _).le
    · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => by positivity)) hgoodmass _
    · positivity
    · exact mul_nonneg (G_pos hBx _).le (by positivity)
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ Q, reciprocalShiftWeight p := restricted_remainder_weight hPH hHm hs S hS
    _ ≤ _ := by
      have hc : 0 ≤ ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹ :=
        Finset.sum_nonneg (fun a _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      simpa only [b,mul_assoc] using mul_le_mul_of_nonneg_left hmass' hc

end TotientAsymptotic

end

end OAI
