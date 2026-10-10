import OAI.NumberTheory.JointDickman.Counting.HistogramWindowBounds

namespace OAI

/-! # Histogram replacement for the actual logarithmic major-arc test -/

namespace JointDickman
open Finset MeasureTheory

theorem logOscillatoryTest_continuous {w w' : ℝ → ℝ} (B N ω : ℝ)
    (hw : ∀ t, HasDerivAt w (w' t) t) :
    Continuous (logOscillatoryTest w B N ω) := by
  exact continuous_iff_continuousAt.mpr (fun x =>
    (hasDerivAt_logOscillatoryTest (ω := ω) (hw _)).continuousAt)

/-- The bound for (38) now applies directly to the major-arc test, with
its logarithmic derivative loss and the local window length both explicit. -/
theorem majorArc_histogram_bound {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 1 ≤ B) {a b N M D ω : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (w w' : ℝ → ℝ) (hw : ∀ t, HasDerivAt w (w' t) t)
    (hwb : ∀ t, |w t| ≤ M) (hw'b : ∀ t, |w' t| ≤ D) :
    let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
    let F := logOscillatoryTest w B N ω
    let L := (D+2*Real.pi*|ω| * M)*((B : ℝ)*(b*Real.exp 1))
    (∑ h : ZMod q, ‖unitResidueFourier
      (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h -
        unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((Real.log (b/a)+2)/B)*
        (L*channelMesh (channelFineCount m B))^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ,
          (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
            manuscriptChannel m B q (fun _ => 1) (i,r)^2) := by
  classical
  dsimp only
  let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
  let L := (D+2*Real.pi*|ω| * M)*((B : ℝ)*(b*Real.exp 1))
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hb : 0 < b := ha.trans_le hab
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound := manuscript_histogram_fourier_error (q := q) hm hBpos J g hg
    (logOscillatoryTest w B N ω) hL
    (fun i _ => (logOscillatoryTest_continuous B N ω hw).intervalIntegrable _ _)
    (by
      intro i hi u hu v hv
      exact logOscillatoryTest_lipschitz hB0 hN hM hD hw
        (fun x hx => endpoint_histogram_window_scale hm hB hb hN hi hx) hwb hw'b hu hv)
  refine hbound.trans ?_
  have hφ : 0 ≤ (q : ℝ)/(q.totient : ℝ) := by positivity
  have hδ := (channelMesh_pos (channelFineCount_pos hm hBpos)).le
  have henergy : 0 ≤ ∑ i ∈ J, ∑ r : (ZMod q)ˣ,
      (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r)^2 := by
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro r _
    positivity
  apply mul_le_mul_of_nonneg_right _ henergy
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (endpoint_histogram_window_length hm hB ha hab hN) hφ

end JointDickman

end OAI
