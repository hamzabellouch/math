import OAI.NumberTheory.JointDickman.Counting.EndpointWindowIdentity
import OAI.NumberTheory.JointDickman.Probability.HistogramProductError

namespace OAI

/-! # Passing between the finite integer window and the full split support -/

namespace JointDickman
open Finset

theorem signedSplitProductMass_eq_zero_of_not_mem (P : Finset ℕ) (g : Finset ℕ → ℝ)
    {n : ℕ} (hn : n ∉ primeSplitProductSupport P) : signedSplitProductMass P g n = 0 := by
  classical
  have hp : ∀ A ∈ P.powerset, (∏ p ∈ A, p) ≠ n := by
    intro A hA hprod
    exact hn (mem_image.mpr ⟨A,hA,hprod⟩)
  have hz (S : Finset ℕ) : splitProductMass P S n = 0 := by
    unfold splitProductMass
    apply sum_eq_zero
    intro A hA
    simp only [hp A hA,ite_false,mul_zero]
  simp only [signedSplitProductMass,hz,mul_zero,sum_const_zero]

theorem endpointFourierSum_eq_support {B : ℕ} {a b N : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ a ∨ b < x → w x = 0) (θ : ℝ) :
    endpointFourierSum B a b N g w θ =
      ∑ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
        (signedSplitProductMass (auxiliaryPrimes B) g n*w (n/N) : ℝ)*additivePhase ((n : ℝ)*θ) := by
  classical
  let S := Ioc ⌊a*N⌋₊ ⌊b*N⌋₊
  let P := primeSplitProductSupport (auxiliaryPrimes B)
  let f := fun n : ℕ => (signedSplitProductMass (auxiliaryPrimes B) g n*w (n/N) : ℝ)*
    additivePhase ((n : ℝ)*θ)
  have hzero (n : ℕ) (hn : n ∉ S) : w (n/N) = 0 := by
    apply hsupp
    by_contra! hc
    apply hn
    have hb := ha.trans_le hab
    exact mem_Ioc.mpr ⟨(Nat.floor_lt (mul_pos ha hN).le).mpr ((lt_div_iff₀ hN).mp hc.1),
      (Nat.le_floor_iff (mul_pos hb hN).le).mpr ((div_le_iff₀ hN).mp hc.2)⟩
  change (∑ n ∈ S, f n) = ∑ n ∈ P, f n
  calc
    _ = ∑ n ∈ S ∩ P, f n := by
      symm
      apply sum_subset inter_subset_left
      intro n hn hnot
      have hnP : n ∉ P := fun hnP => hnot (mem_inter.mpr ⟨hn,hnP⟩)
      simp [f,signedSplitProductMass_eq_zero_of_not_mem _ _ hnP]
    _ = ∑ n ∈ P, f n := by
      apply sum_subset inter_subset_right
      intro n hn hnot
      have hnS : n ∉ S := fun hnS => hnot (mem_inter.mpr ⟨hnS,hn⟩)
      simp [f,hzero n hnS]

theorem endpointFourierSum_histogram {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ a ∨ b < x → w x = 0)
    (hlog : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (h : ZMod q) (ν : ℝ) :
    endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w (h.val/(q : ℝ)+ν) =
      manuscriptFourier m B q
        (histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B))
        g (logOscillatoryTest w B N (ν*N)) h := by
  rw [endpointFourierSum_eq_support ha hab hN _ w hsupp]
  apply endpoint_histogram_window_identity hm hB hcut hN
  intro k hk hw
  refine ⟨hlog k hk hw,?_⟩
  have hb := ha.trans_le hab
  have hx : a < (k : ℝ)/N ∧ (k : ℝ)/N ≤ b := by
    constructor
    · by_contra he
      exact hw (hsupp _ (Or.inl (le_of_not_gt he)))
    · by_contra he
      exact hw (hsupp _ (Or.inr (lt_of_not_ge he)))
  have hk0 : (0 : ℝ) < k := (mul_pos ha hN).trans ((lt_div_iff₀ hN).mp hx.1)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  exact ⟨div_le_div_of_nonneg_right
    (Real.log_le_log (mul_pos ha hN) ((lt_div_iff₀ hN).mp hx.1).le) hB0.le,
    div_le_div_of_nonneg_right
      (Real.log_le_log hk0 ((div_le_iff₀ hN).mp hx.2)) hB0.le⟩

end JointDickman

end OAI
