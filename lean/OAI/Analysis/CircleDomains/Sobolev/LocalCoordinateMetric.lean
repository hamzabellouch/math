import OAI.Analysis.CircleDomains.Sobolev.CoordinateEnergy
import OAI.Analysis.CircleDomains.Transfer.RankOneFilling

namespace OAI

/-!
# Metric selection for coordinates defined near a compact surface piece

Only smoothness on an open neighborhood of the retained compact piece is
required. A smooth cutoff extends the coordinates for the metric-selection
argument, and local agreement identifies the resulting metric energy with
the actual original coordinate differentials on that piece.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def coordinateGram (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) (z : ℝ × ℝ) : PlanarMetric :=
  gramTensor (fun i => (planarGradient (f i) z).1) (fun i => (planarGradient (f i) z).2) n

def coordinateWedges (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  covectorWedges (fun i => (planarGradient (f i) z).1)
    (fun i => (planarGradient (f i) z).2) n

theorem exists_metric_for_local_coordinates
    (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) {Ω Q K U : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {ε : ℝ}
    (hε : (∫ z in Q \ K, 2 * coordinateWedges f n z) < ε) :
    ∃ (τ : ℝ) (N : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → PlanarMetric),
      0 < τ ∧ IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧ (∀ᶠ z in 𝓝ˢ K, g z = 1) ∧
      (∀ z ∈ Q \ N, g z = coordinateGram f n z + τ • 1) ∧
      (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) < ε := by
  choose F hF hFeq hFoff using fun i =>
    exists_smooth_collar_extension hΩ hQ.isClosed hQΩ (hf i) 0
  have hgrad (i : ℕ) {z : ℝ × ℝ} (hz : z ∈ Q) :
      planarGradient (F i) z = planarGradient (f i) z := by
    have heq := ((hFeq i).filter_mono (nhds_le_nhdsSet hz)).fderiv_eq (𝕜 := ℝ)
    simp only [planarGradient, heq]
  let x : ℕ → (ℝ × ℝ) → ℝ := fun i z => (planarGradient (F i) z).1
  let y : ℕ → (ℝ × ℝ) → ℝ := fun i z => (planarGradient (F i) z).2
  have hx (i : ℕ) : ContDiff ℝ ∞ (x i) :=
    ((hF i).fderiv_right (by simp)).clm_apply contDiff_const
  have hy (i : ℕ) : ContDiff ℝ ∞ (y i) :=
    ((hF i).fderiv_right (by simp)).clm_apply contDiff_const
  have hG {z : ℝ × ℝ} (hz : z ∈ Q) :
      gramTensor (fun i => x i z) (fun i => y i z) n = coordinateGram f n z := by
    dsimp [x, y, coordinateGram]
    simp only [hgrad _ hz]
  have hW {z : ℝ × ℝ} (hz : z ∈ Q) :
      covectorWedges (fun i => x i z) (fun i => y i z) n = coordinateWedges f n z := by
    dsimp [x, y, coordinateWedges]
    simp only [hgrad _ hz]
  have hε' : (∫ z in Q \ K, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n) < ε := by
    have heq : (∫ z in Q \ K, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n) =
        ∫ z in Q \ K, 2 * coordinateWedges f n z :=
      setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.isClosed.measurableSet)
        (fun z hz => congrArg (fun a : ℝ => 2 * a) (hW hz.1))
    exact heq.trans_lt hε
  obtain ⟨τ, N, g, hτ, hN, hKN, hNU, hg, hgPD, hcore, hout, henergy⟩ :=
    exists_smooth_core_gramMetric x y n hx hy hK hQ.isBounded
      hQ.isClosed.measurableSet hU hKU hε'
  refine ⟨τ, N, g, hτ, hN, hKN, hNU, hg, hgPD, hcore, ?_, ?_⟩
  · intro z hz
    rw [hout z hz.2, hG hz.1]
  · have heq : (∫ z in Q \ K, matrixEnergy
        (gramTensor (fun i => x i z) (fun i => y i z) n) (g z)) =
        ∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z) :=
      setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.isClosed.measurableSet)
        (fun z hz => congrArg (fun A => matrixEnergy A (g z)) (hG hz.1))
    exact heq.symm.trans_lt henergy

end CircleDomainRigidity.FiniteTransfer

end

end OAI
