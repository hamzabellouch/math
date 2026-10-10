import OAI.NumberTheory.JointDickman.Counting.HistogramWindows
import OAI.NumberTheory.JointDickman.Amplification.EndpointFourierBounds

namespace OAI

/-! # Exact localization of the endpoint Fourier sum to its log window -/

namespace JointDickman
open Finset

theorem endpoint_histogram_window_identity {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {N l u : ℝ} (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ) (h : ZMod q) (ν : ℝ)
    (hsupp : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3 ∩ Set.Icc l u) :
    (∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B),
      (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) k*w (k/N) : ℝ)*
        additivePhase ((k : ℝ)*(h.val/(q : ℝ)+ν))) =
      unitResidueFourier (fun r => ∑ i ∈ histogramWindowCells (channelFineCount m B) l u,
        manuscriptCellSum m B q g (logOscillatoryTest w B N (ν*N)) i r) h := by
  classical
  let n := channelFineCount m B
  let P := auxiliaryPrimes B
  let γ := signedSplitProductMass P (subsetSiteTest P g)
  have hn := channelFineCount_pos hm hB
  have hsupport (k : ℕ) (hk : k ∈ primeSplitProductSupport P)
      (hc : (γ k*w (k/N) : ℝ) ≠ (0 : ℂ)) :
      ∃ i ∈ histogramWindowCells n l u, ∃ r : (ZMod q)ˣ,
        logResidueCell B q (channelLower n) (channelUpper n) k = some (i,r) := by
    have hw : w (k/N) ≠ 0 := by intro hw; simp [hw] at hc
    obtain ⟨i,hi⟩ := channelCells_cover hn (hsupp k hk hw).1
    have hcop := primeSplitProductSupport_coprime (auxiliaryPrimes_prime B) (NeZero.ne q)
      (fun p hp => hcut.trans_lt (by exact_mod_cast (mem_filter.mp hp).2)) hk
    refine ⟨i,mem_histogramWindowCells (hsupp k hk hw).2 hi,ZMod.unitOfCoprime k hcop,?_⟩
    exact (logResidueCell_eq_some B q (channelLower n) (channelUpper n)
      (channelCells_disjoint hn) k i _).mpr ⟨hi,rfl⟩
  have he := endpoint_residue_partition (B := B) (channelLower n) (channelUpper n)
    (channelCells_disjoint hn) (primeSplitProductSupport P) (histogramWindowCells n l u)
    (fun k => ((γ k*w (k/N) : ℝ) : ℂ)) h ν hsupport
  rw [he]
  congr 1
  funext r
  apply sum_congr rfl
  intro i _
  unfold manuscriptCellSum
  apply sum_congr rfl
  intro k hk
  dsimp only [n,P,γ]
  by_cases hc : logResidueCell B q (channelLower (channelFineCount m B))
    (channelUpper (channelFineCount m B)) k = some (i,r)
  · simp only [hc,ite_true]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast primeSplitProductSupport_pos (auxiliaryPrimes_prime B) hk
    have hlog := logOscillatoryTest_majorArc w (B := (B : ℝ)) (N := N)
      (j := 1) (X := 1) (k := (k : ℝ)) (ξ := ν) (by exact_mod_cast hB.ne') hN.ne' hk0
    simp only [mul_one,div_one] at hlog
    rw [hlog,Complex.ofReal_mul]
    ring_nf
  · simp only [hc,ite_false]


end JointDickman

end OAI
