import OAI.NumberTheory.Jacobsthal.Analysis.CompactCorrectionLimit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Finset
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.LiteralUniformPrimeTail

theorem uniform_compact_correction_above (Kmin ell d eps : ℝ) (hell : 2 ≤ ell)
    (hd : 0 < d) (heps : 0 < eps) :
    ∃ K B₀ w₀ : ℝ,3 ≤ K ∧ Kmin ≤ K ∧ 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        B^2*|continuousBoundaryCorrection w ell start-compactCorrection K w ell start| ≤ eps := by
  obtain ⟨C,c,_wA,hC,hc,_hwA,_hD,hA⟩ := common_anomaly_exponential
  obtain ⟨M₀,BT,wT,hBT,hwT,hT⟩ := actual_uniform_original_prime_tail d c (eps/C) hd hc (div_pos heps hC)
  obtain ⟨n,hn⟩ := exists_nat_ge Kmin
  let M : ℕ := M₀+n
  let K : ℝ := 3*((M:ℝ)+1)
  have hK : 3 ≤ K := by dsimp [K]; have hn := Nat.cast_nonneg (α := ℝ) M; linarith
  have hKmin : Kmin ≤ K := by
    apply hn.trans
    dsimp [K,M]
    push_cast
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    have hm0 := Nat.cast_nonneg (α := ℝ) M₀
    linarith
  refine ⟨K,max BT (max 4 ell),wT,hK,hKmin,hBT.trans_le (le_max_left _ _),hwT,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBT' : BT ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hellB : ell ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have ht := hT M (by dsimp [M]; omega) B w hBT' hw ell (by linarith) hellB hcomp start hi h199 h23 hcons hcut
  have he := compact_correction_error (K := K) (w := w) hA hB4 hell hellB start hi h199 h23 hcons hcut
  have heB := mul_le_mul_of_nonneg_left he (sq_nonneg B)
  have htC := mul_le_mul_of_nonneg_left ht hC.le
  have hcanc : C*(eps/C)=eps := mul_div_cancel₀ eps (ne_of_gt hC)
  rw [hcanc] at htC
  nlinarith

end ErdosCorrectionLimit

end

end Erdos970

end OAI
