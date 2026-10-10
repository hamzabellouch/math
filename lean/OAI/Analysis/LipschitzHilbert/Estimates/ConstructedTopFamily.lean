import OAI.Analysis.LipschitzHilbert.Estimates.ConstructedTopNeighborhood

namespace OAI

/-! Sum the actual top-packet exceptions. The conclusion is uniform in
the number of tops, packet scales, and Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_top_family (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
      (P : ∀ i, PlanarPacketFamily (N i) κ (ι i))
      (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ), (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      (∀ i, TopRawPacketData (P i) lo hi (T i) K D) → ∀ J L : ℝ,
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) ∧
        ∀ i a b, a ≤ b → b ≤ N i → ∀ z w, |w| ≤ K*(T i).width → z ∉ bad →
          ‖planarPacketInterval ((P i).mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k y x => (P i).wave j u k y x)
              a b z.1 ((z.2-(T i).slope*z.1)+w)‖ ≤
                ((P i).topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*((T i).weight K (D:ℝ) z)^8 := by
  classical
  obtain ⟨Ab,Am,hAb,hAm,htop⟩ := constructed_top_neighborhood hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro τ κ _ _ N ι _ P cutoff v hv g hg hg1 hd T K D hK data J L
  choose bad hbad harea hpoint using fun i =>
    htop (N i) κ (ι i) (P i) (cutoff i) (v i) (hv i) (g i) (hg i) (hg1 i) (hd i)
      (T i) K D hK (data i) J L
  refine ⟨⋃ i, bad i, MeasurableSet.iUnion hbad,?_,?_⟩
  · calc
      _ ≤ ∑ i, (volume.prod volume) (bad i) := by
        simpa only [tsum_fintype] using measure_iUnion_le bad
      _ ≤ ∑ i, ENNReal.ofReal (Real.exp (-J*L)*(T i).area) :=
        Finset.sum_le_sum (fun i _ => harea i)
      _ = ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg
          (fun i _ => mul_nonneg (Real.exp_pos _).le (T i).area_pos.le), Finset.mul_sum]
  · intro i a b hab hb z w hw hout
    exact hpoint i a b hab hb z w hw (fun hz => hout (mem_iUnion.mpr ⟨i,hz⟩))

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
