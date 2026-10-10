import OAI.NumberTheory.JointDickman.Probability.SignedHistogramError
import OAI.NumberTheory.JointDickman.Probability.FiniteHistogramFourier

namespace OAI

/-! # Local Fourier error of the actual signed split-product histograms -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptCellSum (m B q : ℕ) [NeZero q]
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) : ℂ :=
  ∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B),
    if logResidueCell B q (channelLower (channelFineCount m B))
      (channelUpper (channelFineCount m B)) k = some (i,r) then
      (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) k : ℂ)*
        F (Real.log k/B) else 0

noncomputable def manuscriptCellApprox (m B q : ℕ) [NeZero q]
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) : ℂ :=
  ((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ)*
    complexCellAverage (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i) F

/-- A local collection of fine cells incurs exactly the square of its
oscillation scale; no number-of-boxes loss appears. -/
theorem manuscript_histogram_fourier_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B)
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ i ∈ J, IntervalIntegrable F volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hLip : ∀ i ∈ J, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F u-F v‖ ≤ L*|u-v|) :
    (∑ h : ZMod q, ‖unitResidueFourier
      (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h -
        unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*
        (L*channelMesh (channelFineCount m B))^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ,
          (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
            manuscriptChannel m B q (fun _ => 1) (i,r)^2) := by
  classical
  let δ := channelMesh (channelFineCount m B)
  let U := fun i r => manuscriptChannel m B q (fun _ => 1) (i,r)
  let e := fun r => (q.totient : ℂ)*
    (∑ i ∈ J, (manuscriptCellSum m B q g F i r-manuscriptCellApprox m B q g F i r))
  have hδ : 0 < δ := channelMesh_pos (channelFineCount_pos hm hB)
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have he (r : (ZMod q)ˣ) : ‖e r‖ ≤ δ*(L*δ)*(∑ i ∈ J, U i r) := by
    have hlocal (i : Fin (channelFineCount m B)) (hi : i ∈ J) :
        ‖manuscriptCellSum m B q g F i r-manuscriptCellApprox m B q g F i r‖ ≤
          (L*δ)*(δ/(q.totient : ℝ))*U i r :=
      manuscriptChannel_cell_average_error hm hB g hg (i,r) F hL (hF i hi) (hLip i hi)
    calc
      ‖e r‖ = (q.totient : ℝ)*‖∑ i ∈ J,
          (manuscriptCellSum m B q g F i r-manuscriptCellApprox m B q g F i r)‖ := by
        simp only [e,norm_mul,Complex.norm_natCast]
      _ ≤ (q.totient : ℝ)*∑ i ∈ J,
          ‖manuscriptCellSum m B q g F i r-manuscriptCellApprox m B q g F i r‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hφ.le
      _ ≤ (q.totient : ℝ)*∑ i ∈ J, (L*δ)*(δ/(q.totient : ℝ))*U i r :=
        mul_le_mul_of_nonneg_left (sum_le_sum hlocal) hφ.le
      _ = δ*(L*δ)*(∑ i ∈ J, U i r) := by
        rw [← mul_sum]
        field_simp
  have hb := finite_histogram_fourier_bound J hδ.le (mul_nonneg hL hδ.le) U e he
  have hid (h : ZMod q) : unitResidueFourier e h/(q.totient : ℂ) =
      unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h -
      unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h := by
    have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    unfold unitResidueFourier
    simp only [e,sum_sub_distrib,mul_sub]
    rw [← sum_sub_distrib,sum_div]
    conv_rhs => rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    field_simp
  simpa only [hid,δ,U] using hb

end JointDickman

end OAI
