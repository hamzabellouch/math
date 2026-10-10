import OAI.NumberTheory.TotientAsymptotic.HeadSquareGeometry
import OAI.NumberTheory.TotientAsymptotic.PrimeSquareMass

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headSquareCase (x : ℝ) (H : ℕ) (t : ℝ) (q j k : ℕ) :
    Finset (RemainderDatum (L x H) × ℕ) :=
  (witnessFamily t (basicRemainderFinset x H)).filter (fun w =>
    if j=k then q^2 ∣ wholeWitnessPrime w.2 w.1 j-1
    else q ∣ wholeWitnessPrime w.2 w.1 j-1 ∧ q ∣ wholeWitnessPrime w.2 w.1 k-1)

lemma headSquareCase_basic {x t : ℝ} {H q j k : ℕ}
    {w : RemainderDatum (L x H) × ℕ} (hw : w ∈ headSquareCase x H t q j k) :
    IsBasicRemainder x H w.1 ∧ IsBasicTuple x H t (witnessTuple w.2 w.1) := by
  have hh := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
  exact ⟨mem_basicRemainderFinset.mp (Finset.mem_product.mp hh.1).1,hh.2⟩

lemma head_square_case_count (hmertens : MertensProductInput) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ t ≤ x, ∀ j k q : ℕ, j ≤ L x H → k ≤ L x H → q.Prime →
      ((headSquareCase x H t q j k).card : ℝ) ≤
      x*(∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ((1+Real.log (discardPrimeBound (B x) : ℝ))^2*
          (D*(2*B x+2))^(m x))*((q : ℝ)^2)⁻¹ := by
  obtain ⟨D,hD,hall⟩ := prime_reciprocal_mass_bound hmertens
  refine ⟨D+1,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)] with H hH hP
  filter_upwards [full_witness_prime_bound,theta_eventually_mem,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with x hbound hs hHm hB hx
  intro t ht j k q hj hk hq
  let S := headSquareCase x H t q j k
  let Q := S.image fullWitnessPrimes
  let N := discardPrimeBound (B x)
  let E := (D+1)*(2*B x+2)
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hPH := P_lt_self hH
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 1 ≤ E := by dsimp [E]; nlinarith
  have hN := discardPrimeBound_bounds hB
  have hmass : (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ E := by
    have hh := (hall N (by dsimp [N]; omega) hN.2.1).trans
      (mul_le_mul_of_nonneg_left (show 1+B (N : ℝ) ≤ 2*B x+2 by linarith [hN.2.2.1]) hD.le)
    exact hh.trans (by dsimp [E]; nlinarith)
  have hS : ∀ w ∈ S, IsBasicRemainder x H w.1 ∧ IsBasicTuple x H t (witnessTuple w.2 w.1) :=
    fun _ hw => headSquareCase_basic hw
  have hU : ∀ p ∈ Q, ∀ l, p l ∈ Nat.primesLE N := by
    intro p hp l
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    exact hbound H hPH.le t ht w (hS w hw).1 (hS w hw).2 l
  let j' : Fin (L x H+1) := ⟨j,by omega⟩
  let k' : Fin (L x H+1) := ⟨k,by omega⟩
  have hdiv : ∀ p ∈ Q, if j'=k' then q^2 ∣ p j'-1 else q ∣ p j'-1 ∧ q ∣ p k'-1 := by
    intro p hp
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    have hh := (Finset.mem_filter.mp hw).2
    have hej : fullWitnessPrimes w j'=wholeWitnessPrime w.2 w.1 j := (wholeWitnessPrime_full w hj).symm
    have hek : fullWitnessPrimes w k'=wholeWitnessPrime w.2 w.1 k := (wholeWitnessPrime_full w hk).symm
    simpa only [j',k',Fin.mk.injEq,hej,hek] using hh
  have hdim : L x H+1 ≤ m x := by unfold L; omega
  have hpm := prime_square_mass (N := N) (by dsimp [N]; omega) hq hdim Q j' k' hE hU hdiv hmass
  have hc := full_witness_count_le hPH.le ht S hS
  have hw := full_witness_weight_le hPH hHm hs S (fun w hw => (hS w hw).1)
  calc
    _ ≤ x*(W*∑ p ∈ Q, reciprocalShiftWeight p) := hc.trans (mul_le_mul_of_nonneg_left hw hx.le)
    _ ≤ x*(W*((1+Real.log (N : ℝ))^2*E^(m x)*((q : ℝ)^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpm hW) hx.le
    _ = _ := by dsimp [W,N,E]; ring

end TotientAsymptotic

end

end OAI
