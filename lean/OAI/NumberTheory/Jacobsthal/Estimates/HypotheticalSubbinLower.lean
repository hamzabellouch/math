import OAI.NumberTheory.Jacobsthal.Partitions.CommonSliceGeometry
import OAI.NumberTheory.Jacobsthal.Paths.TagPairBinding

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosCommonMInterval ErdosAlignedProgression
  ErdosInverseAlignment ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem subbin_primality (R V : ℝ) : ∀ p ∈ intervalPrimes R V 1 0,p.Prime := by
  intro p hp
  exact ((mem_intervalPrimes R V 1 0 p).mp hp).1

theorem hypothetical_subbin_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P R V : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      203/100 ≤ lengthExponent P Y R q → lengthExponent P Y R q ≤ 219/100 →
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (∀ p ∈ intervalPrimes R V 1 0,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet P ∧ ∀ t ∈ (p*q).primeFactors,t ≠ p →
          aligns (fun u => (a u : ℤ)) r t) →
      (39/100 : ℝ)*((intervalPrimes R V 1 0).card : ℝ)*referenceLength Y R q*primeProduct P ≤
        ∑ p : intervalPrimes R V 1 0,
          hypotheticalRowCount Y (smallPrimeSet P) (intervalPrimes R V 1 0) a r q
            (subbin_primality R V) p := by
  obtain ⟨K,hK,hPairs⟩ := moving_subbin_actual_pair_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨wA,hwA,hA⟩ := hPairs rho xi hrho hxi
  obtain ⟨wC,hC⟩ := uniform_integer_common_interval Cs K (1/1000) hCs hK (by norm_num) (by norm_num)
  refine ⟨max wA wC,hwA.trans (le_max_left _ _),?_⟩
  intro w hw P R V hPl hPu hR hVlo hVhi Y q hY hq r a hDen hNum hs hsU hqSmall hGeometry
  have hw4 : 4 ≤ w := hwA.trans ((le_max_left _ _).trans hw)
  have hw1 : 1 < w := by linarith
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hRatio : 0 < V/R := (div_pos hxi (by positivity)).trans_le hVlo
  have hV : 0 < V := (div_pos_iff.mp hRatio).resolve_right (by intro h;linarith [h.2]) |>.1
  have hWidth : R+V ≤ (1+w^(-2*Cs-10))*R := by
    have hh := (div_le_iff₀ hR0).mp hVhi
    rw [show -(2*Cs+10)= -2*Cs-10 by ring] at hh
    nlinarith
  have hP1 : 1 < P := by
    have he : 1 < Real.exp (K*(Real.log w)^3) := Real.one_lt_exp_iff.mpr
      (mul_pos hK (pow_pos (Real.log_pos hw1) _))
    exact he.trans_le hPl
  have hb := hC w ((le_max_right _ _).trans hw) P R (R+V) r.num r.den Y q hPl
    r.den_pos hDen hY hq hR0 (by linarith) hWidth hNum (by linarith)
  have hJid := reference_rpow hP1 (show (0 : ℝ) < Y by exact_mod_cast hY) hR0
    (show (0 : ℝ) < q by exact_mod_cast hq)
  have hLength : (999/1000 : ℝ)*(r.den : ℝ)*P^(lengthExponent P Y R q) ≤
      upper r.num r.den Y q R (R+V)-lower r.num q R (R+V) := by
    rw [hJid]
    convert hb.1 using 1
    norm_num
  have hHeight := common_slice_endpoint_height w Cs P R (R+V) r.num r.den Y q
    hw1.le hP1 hDen hY hq hR0 hNum hb.2.2.1
  have hPair := hA w ((le_max_left _ _).trans hw) P (lengthExponent P Y R q)
    (lower r.num q R (R+V)) (upper r.num r.den Y q R (R+V)) R V hPl hPu
    hs hsU hR hVlo hVhi r hDen q a hqSmall hLength hHeight
  rw [hJid] at hPair
  apply hPair.trans
  apply pair_count_le_hypothetical_sum Y (smallPrimeSet P) (intervalPrimes R V 1 0) a r q
    (subbin_primality R V) _ (actualTagGood P r q a) hGeometry
  · intro p hp m hm hGood
    obtain ⟨d,_hd,hm⟩ := Finset.mem_biUnion.mp hm
    have hEnds := (mem_primeMultiplesIn d P _ _ m).mp hm
    have hpBounds := (mem_intervalPrimes R V 1 0 p).mp hp
    exact common_slice_mem_parameter Y q p r R (R+V) m hq hR0 hpBounds.2.1.le
      hpBounds.2.2.1 ⟨hEnds.1.le,hEnds.2.1.le⟩
      (actual_tag_original_tests P r q p a m hGood).1
  · intro p _hp m _hm hGood
    exact actual_tag_original_tests P r q p a m hGood

end ErdosStoppedArithmetic


end Erdos970

end OAI
