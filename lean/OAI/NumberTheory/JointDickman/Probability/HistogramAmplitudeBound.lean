import OAI.NumberTheory.JointDickman.Probability.ManuscriptHistogramFourier

namespace OAI

/-! # Positive cell domination for both endpoint Fourier amplitudes -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscriptCellSum_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (F : ℝ → ℂ) (M : ℝ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ)
    (hF : ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    ‖manuscriptCellSum m B q g F i r‖ ≤
      M*(channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r) := by
  let n := channelFineCount m B
  let cell := logResidueCell B q (channelLower n) (channelUpper n)
  have hh := signedSplitProductMass_cell_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (subsetSiteTest (auxiliaryPrimes B) g) (fun _ _ => hg _) cell (i,r)
    (fun k => F (Real.log k/B)) 0 M (by
      intro k _ hk
      have hx := (logResidueCell_eq_some B q (channelLower n) (channelUpper n)
        (channelCells_disjoint (channelFineCount_pos hm hB)) k i r).mp hk
      simpa only [sub_zero] using hF _ (Set.Ioc_subset_Icc_self hx.1))
  have hone := manuscriptChannel_cell_mass hm hB (fun _ => 1) (i,r)
  change (∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B), if cell k = some (i,r) then
    signedSplitProductMass (auxiliaryPrimes B) (fun _ => 1) k else 0) = _ at hone
  simp only [signedSplitProductMass_one] at hone
  rw [hone] at hh
  simpa only [mul_zero,sub_zero,manuscriptCellSum,n,cell,mul_assoc] using hh

theorem manuscriptCellApprox_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (F : ℝ → ℂ) (M : ℝ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ)
    (hF : ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    ‖manuscriptCellApprox m B q g F i r‖ ≤
      M*(channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r) := by
  let A := complexCellAverage (channelLower (channelFineCount m B) i)
    (channelUpper (channelFineCount m B) i) F
  have hwidth := channel_width (channelFineCount m B) i
  have hi : channelLower (channelFineCount m B) i < channelUpper (channelFineCount m B) i := by
    linarith [channelMesh_pos (channelFineCount_pos hm hB)]
  have hA : ‖A‖ ≤ M := complexCellAverage_norm_le hi hF
  have he : manuscriptCellSum m B q g (fun _ => A) i r = manuscriptCellApprox m B q g F i r := by
    unfold manuscriptCellSum manuscriptCellApprox
    rw [← manuscriptChannel_cell_mass hm hB g (i,r)]
    simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,sum_mul]
    apply sum_congr rfl
    intro k _
    split_ifs <;> simp [A]
  rw [← he]
  exact manuscriptCellSum_norm_le hm hB g hg (fun _ => A) M i r (fun _ _ => hA)

theorem cellAmplitude_fourier_bound {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q]
    (J : Finset ι) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (U : ι → (ZMod q)ˣ → ℝ) (A : ι → (ZMod q)ˣ → ℂ)
    (hA : ∀ i ∈ J, ∀ r, ‖A i r‖ ≤ M*(δ/(q.totient : ℝ))*U i r) :
    (∑ h : ZMod q, ‖unitResidueFourier (fun r => ∑ i ∈ J, A i r) h‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*δ)*M^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (δ/(q.totient : ℝ))*U i r^2) := by
  let v := fun r => (q.totient : ℂ)*(∑ i ∈ J, A i r)
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hv (r : (ZMod q)ˣ) : ‖v r‖ ≤ δ*M*(∑ i ∈ J, U i r) := by
    calc
      _ = (q.totient : ℝ)*‖∑ i ∈ J, A i r‖ := by simp only [v,norm_mul,Complex.norm_natCast]
      _ ≤ (q.totient : ℝ)*(∑ i ∈ J, ‖A i r‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hφ.le
      _ ≤ (q.totient : ℝ)*(∑ i ∈ J, M*(δ/(q.totient : ℝ))*U i r) :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => hA i hi r)) hφ.le
      _ = _ := by rw [← mul_sum]; field_simp
  have hh := finite_histogram_fourier_bound J hδ hM U v hv
  have hid (h : ZMod q) : unitResidueFourier v h/(q.totient : ℂ) =
      unitResidueFourier (fun r => ∑ i ∈ J, A i r) h := by
    unfold unitResidueFourier
    rw [sum_div]
    apply sum_congr rfl
    intro r _
    dsimp [v]
    have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    field_simp
  simpa only [hid] using hh

theorem manuscript_amplitude_fourier_bounds {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    let bound := ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*M^2*
      (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r)^2)
    (∑ h : ZMod q, ‖unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h‖^2) ≤ bound ∧
    (∑ h : ZMod q, ‖unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h‖^2) ≤ bound := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  exact ⟨cellAmplitude_fourier_bound J hδ hM _ _
    (fun i hi r => manuscriptCellSum_norm_le hm hB g hg F M i r (hF i hi)),
    cellAmplitude_fourier_bound J hδ hM _ _
    (fun i hi r => manuscriptCellApprox_norm_le hm hB g hg F M i r (hF i hi))⟩

end JointDickman

end OAI
