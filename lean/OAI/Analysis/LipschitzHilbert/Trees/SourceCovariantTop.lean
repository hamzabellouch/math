import OAI.Analysis.LipschitzHilbert.Estimates.ConstructedCovariantTop
import OAI.Analysis.LipschitzHilbert.Estimates.TopThreshold

namespace OAI

/-! A common exceptional set for all actual covariant top derivatives,
with a fixed polynomial threshold at the manuscript's scales. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PlanarPacketFamily

theorem source_covariant_top (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, PlanarPacketFamily (N i) κ (ι i)), (∀ i, (P i).constant ≤ L^p) →
      ∀ (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ), (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (data : ∀ i, TopRawPacketData (P i) lo hi (T i) (L^a) D),
      (∀ i, TopCovariantData (data i)) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z w,
          |w| ≤ L^a*(T i).width → z ∉ bad →
          (4*(L^a*(T i).width))*‖covariantSignal (data i).frequency (fun k t =>
            planarPacketInterval ((P i).mainCoefficient (cutoff i) (v i) (g i))
              (fun j u k y x => (P i).wave j u k y x) lower upper z.1 t k)
                ((z.2-(T i).slope*z.1)+w)‖ ≤
                  L^(2*p+2)*((T i).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Ab,Am,hAb,hAm,htop⟩ := constructed_covariant_top hL hlo hhi
  obtain ⟨L0,hL0,hthreshold⟩ := exists_top_threshold Ab Am J a p D hAb hAm hJ ha hp
  refine ⟨L0,hL0,?_⟩
  intro L hL τ κ _ _ N ι _ P hP cutoff v hv g hg hg1 hd T data second
  have hLpos : 0 < L := zero_lt_one.trans_le (hL0.trans hL)
  choose bad hbad harea hpoint using fun i =>
    htop (N i) κ (ι i) (P i) (cutoff i) (v i) (hv i) (g i) (hg i) (hg1 i) (hd i)
      (T i) (L^a) D (Real.rpow_pos_of_pos hLpos _) (data i) (second i) J L
  refine ⟨⋃ i, bad i, MeasurableSet.iUnion hbad,?_,?_⟩
  · calc
      _ ≤ ∑ i, (volume.prod volume) (bad i) := by
        simpa only [tsum_fintype] using measure_iUnion_le bad
      _ ≤ ∑ i, ENNReal.ofReal (Real.exp (-J*L)*(T i).area) :=
        Finset.sum_le_sum (fun i _ => harea i)
      _ = ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg
          (fun i _ => mul_nonneg (Real.exp_pos _).le (T i).area_pos.le), Finset.mul_sum]
  · intro i lower upper hlu hu z w hw hout
    exact (hpoint i lower upper hlu hu z w hw (fun hz => hout (mem_iUnion.mpr ⟨i,hz⟩))).trans
      (mul_le_mul_of_nonneg_right (hthreshold L hL (N i) κ (ι i) (P i) (hP i))
        (by positivity))

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
