import OAI.Analysis.LipschitzHilbert.Estimates.SeparatedWitnessCount

namespace OAI

/-! Choose a longest top and count the remaining directions against it. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LipschitzHilbert.SlopeBox

/-- The reference top contributes one; all other tops inject into popular
angular bins for the longest top. All reference counts are chosen in advance. -/
theorem admissible_list_card_le {ι : Type*} [DecidableEq ι]
    (T : ι → SlopeBox) (I : Finset ι) (u : ℝ × ℝ → ℝ)
    {L : ℝ≥0} (hu : LipschitzWith L u) (z : ℝ × ℝ)
    {M : ℕ} (hM : 0 < M) {A q P K θ c c0 B rho m lambda : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hP : 0 < P) (hK : 0 ≤ K)
    (hAK : A + K ≤ P) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (hθ : θ ≤ q / (8 * A * P)) (hlambda : 0 ≤ lambda)
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hfinite : ∀ i ∈ I, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i ∈ I, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i ∈ I, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i ∈ I, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i ∈ I, 0 ≤ d i)
    (hwidth : ∀ i ∈ I, (T i).width = m * (T i).length * d i)
    (hprecision : ∀ i ∈ I, d i ≤ rho / B ^ 2)
    (hsmall : ∀ i ∈ I, L * P * m * (T i).length ≤ 1 / 2)
    (hspan : ∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|)
    (hz : ∀ i ∈ I, (T i).radius z ≤ K)
    (N : ι → ℝ × ℝ → ℝ≥0∞)
    (hN : ∀ i ∈ I, (T i).ReferencePopularCount u c P θ M (N i))
    (hbound : ∀ i ∈ I, N i (((T i).referenceChart.symm z).2, z.1) ≤ ENNReal.ofReal lambda) :
    (I.card : ℝ) ≤ 1 + lambda := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨r, hr, hmax⟩ := I.exists_max_image (fun i => (T i).length) hI
    let J := {i // i ∈ I.erase r}
    have hmem (i : J) : i.val ∈ I := Finset.mem_of_mem_erase i.property
    have hne (i : J) : i.val ≠ r := (Finset.mem_erase.mp i.property).1
    have hcount := (T r).separated_witness_list_count (fun i : J => T i.val) u hu z hM
      hA hq hP hK hAK hc0 hc hB hrho hMB hm hθ
      (fun i : J => d i.val) (fun i : J => E i.val)
      (fun i => hE i.val (hmem i)) (fun i => hfinite i.val (hmem i))
      (fun i => hbox i.val (hmem i)) (fun i => harea i.val (hmem i))
      (fun i => hwitness i.val (hmem i)) (fun i => hd i.val (hmem i))
      (fun i => hwidth i.val (hmem i)) (fun i => hprecision i.val (hmem i))
      (fun i => hsmall i.val (hmem i))
      (fun i => hsep i.val (hmem i) r hr (hne i))
      (fun i => hspan i.val (hmem i) r hr)
      (fun i j hij => hsep i.val (hmem i) j.val (hmem j)
        (fun h => hij (Subtype.ext h)))
      (fun i => hmax i.val (hmem i)) (fun i => hz i.val (hmem i)) (N r) (hN r hr)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcount.trans (hbound r hr))
    have hcard : (Fintype.card J : ℝ) ≤ lambda := by
      simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlambda] using hreal
    have hJ : Fintype.card J = (I.erase r).card := Fintype.card_coe _
    have hcI := Finset.card_erase_add_one hr
    rw [hJ] at hcard
    have hcI' : ((I.erase r).card : ℝ) + 1 = I.card := by exact_mod_cast hcI
    linarith
  · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

end LipschitzHilbert.SlopeBox

end

end OAI
