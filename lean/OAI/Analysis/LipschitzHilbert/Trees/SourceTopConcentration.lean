import OAI.Analysis.LipschitzHilbert.Estimates.ConstructedTopFamily
import OAI.Analysis.LipschitzHilbert.Estimates.TopThreshold

namespace OAI

/-! The source's polynomial top bound for the actual packet sums, with
a common exponentially small exceptional set and no scale-count loss. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PlanarPacketFamily

theorem source_top_concentration (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, PlanarPacketFamily (N i) κ (ι i)), (∀ i, (P i).constant ≤ L^p) →
      ∀ (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ), (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox), (∀ i, TopRawPacketData (P i) lo hi (T i) (L^a) D) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z w,
          |w| ≤ L^a*(T i).width → z ∉ bad →
          ‖planarPacketInterval ((P i).mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k y x => (P i).wave j u k y x)
              lower upper z.1 ((z.2-(T i).slope*z.1)+w)‖ ≤
                L^(2*p+2)*((T i).weight (L^a) (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,hfamily⟩ := constructed_top_family hL hlo hhi
  obtain ⟨L0,hL0,hthreshold⟩ := exists_top_threshold Ab Am J a p D hAb hAm hJ ha hp
  refine ⟨L0,hL0,?_⟩
  intro L hL τ κ _ _ N ι _ P hP cutoff v hv g hg hg1 hd T data
  have hLpos : 0 < L := zero_lt_one.trans_le (hL0.trans hL)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hfamily τ κ N ι P cutoff v hv g hg hg1 hd T
    (L^a) D (Real.rpow_pos_of_pos hLpos _) data J L
  refine ⟨bad,hbad,harea,?_⟩
  intro i lower upper hlu hu z w hw hout
  exact (hpoint i lower upper hlu hu z w hw hout).trans
    (mul_le_mul_of_nonneg_right (hthreshold L hL (N i) κ (ι i) (P i) (hP i))
      (by positivity))

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
