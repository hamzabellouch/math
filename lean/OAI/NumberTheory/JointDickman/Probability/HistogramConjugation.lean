import OAI.NumberTheory.JointDickman.Amplification.EndpointSupportSum
import OAI.NumberTheory.JointDickman.Amplification.EndpointFourierReflection

namespace OAI

/-! # The negative endpoint has the opposite residue and continuous frequency -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem logOscillatoryTest_conj (w : ℝ → ℝ) (B N ω x : ℝ) :
    conj (logOscillatoryTest w B N ω x) = logOscillatoryTest w B N (-ω) x := by
  unfold logOscillatoryTest oscillatoryTest
  rw [map_mul,Complex.conj_ofReal,additivePhase_conj]
  congr 2
  ring

theorem manuscriptCellSum_conj (m B q : ℕ) [NeZero q]
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) :
    conj (manuscriptCellSum m B q g F i r) =
      manuscriptCellSum m B q g (fun x => conj (F x)) i r := by
  classical
  unfold manuscriptCellSum
  rw [map_sum]
  apply sum_congr rfl
  intro k _
  split_ifs <;> simp only [map_mul,Complex.conj_ofReal,map_zero]

theorem manuscriptFourier_conj (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) :
    conj (manuscriptFourier m B q J g F h) =
      manuscriptFourier m B q J g (fun x => conj (F x)) (-h) := by
  unfold manuscriptFourier unitResidueFourier
  rw [map_sum]
  apply sum_congr rfl
  intro r _
  rw [map_mul,stdAddChar_conj,map_sum]
  simp only [neg_mul,manuscriptCellSum_conj]

theorem endpointFourierSum_histogram_neg {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ a ∨ b < x → w x = 0)
    (hlog : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (h : ZMod q) (ν : ℝ) :
    endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w (-(h.val/(q : ℝ)+ν)) =
      manuscriptFourier m B q
        (histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B))
        g (logOscillatoryTest w B N (-(ν*N))) (-h) := by
  change finiteAdditiveSum _ _ (-(h.val/(q : ℝ)+ν)) = _
  rw [finiteAdditiveSum_neg_real]
  change conj (endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w _) = _
  rw [endpointFourierSum_histogram hm hB hcut ha hab hN g w hsupp hlog h ν,
    manuscriptFourier_conj]
  simp_rw [logOscillatoryTest_conj]

end JointDickman

end OAI
