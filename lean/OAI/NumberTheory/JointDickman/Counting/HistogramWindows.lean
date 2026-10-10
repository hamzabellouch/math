import OAI.NumberTheory.JointDickman.Probability.EndpointHistogramIdentity
import OAI.NumberTheory.JointDickman.Probability.HistogramScaleDecay

namespace OAI

/-! # Local collections of fine cells for an endpoint box -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def histogramWindowCells (n : ℕ) (l u : ℝ) : Finset (Fin n) :=
  univ.filter (fun i => channelLower n i ≤ u ∧ l ≤ channelUpper n i)

theorem mem_histogramWindowCells {n : ℕ} {l u x : ℝ} {i : Fin n}
    (hx : x ∈ Set.Icc l u) (hi : x ∈ Set.Ioc (channelLower n i) (channelUpper n i)) :
    i ∈ histogramWindowCells n l u := by
  simp only [histogramWindowCells,mem_filter,mem_univ,true_and]
  exact ⟨hi.1.le.trans hx.2,hx.1.trans hi.2⟩

theorem histogramWindowCells_length {n : ℕ} (hn : 0 < n) {l u : ℝ} (hlu : l ≤ u) :
    ((histogramWindowCells n l u).card : ℝ)*channelMesh n ≤ u-l+2*channelMesh n := by
  classical
  let J := histogramWindowCells n l u
  have hδ := channelMesh_pos hn
  by_cases hJ : J.Nonempty
  · let a := J.min' hJ
    let b := J.max' hJ
    have ha : a ∈ J := min'_mem J hJ
    have hb : b ∈ J := max'_mem J hJ
    have hab : a ≤ b := min'_le J b hb
    have hcard : J.card ≤ b.val+1-a.val := by
      have hsubset : J.image Fin.val ⊆ Icc a.val b.val := by
        intro k hk
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
        exact mem_Icc.mpr ⟨min'_le J i hi,le_max' J i hi⟩
      have hc := card_le_card hsubset
      rwa [card_image_of_injective J Fin.val_injective,Nat.card_Icc] at hc
    have hcR : (J.card : ℝ) ≤ (b.val : ℝ)+1-a.val := by
      calc
        (J.card : ℝ) ≤ ((b.val+1-a.val : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = _ := by rw [Nat.cast_sub (show a.val ≤ b.val+1 by omega),Nat.cast_add,Nat.cast_one]
    have ha' : l ≤ channelUpper n a := (mem_filter.mp ha).2.2
    have hb' : channelLower n b ≤ u := (mem_filter.mp hb).2.1
    have hlen := mul_le_mul_of_nonneg_right hcR hδ.le
    dsimp [channelLower,channelUpper] at ha' hb'
    dsimp [J] at hlen
    nlinarith
  · have he : J = ∅ := not_nonempty_iff_eq_empty.mp hJ
    change (J.card : ℝ)*channelMesh n ≤ _
    rw [he,card_empty,Nat.cast_zero,zero_mul]
    linarith

/-- Every retained integer in a fixed endpoint support lies in the interior
of the manuscript's logarithmic interval for sufficiently large B. -/
theorem endpoint_support_log_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ᶠ B : ℕ in atTop, ∀ N : ℝ, 0 < N →
      Real.log N ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ k : ℕ, a < (k : ℝ)/N → (k : ℝ)/N ≤ b →
        Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3 := by
  have hb : 0 < b := ha.trans_le hab
  have hlo : ∀ᶠ B : ℕ in atTop, -Real.log a < (3/10 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3/10)).eventually_gt_atTop _
  have hhi : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (1/2 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2)).eventually_ge_atTop _
  filter_upwards [hlo,hhi,eventually_gt_atTop 0] with B hloB hhiB hB
  intro N hN hlog k hklo hkhi
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hk0 : (0 : ℝ) < k := (mul_pos ha hN).trans ((lt_div_iff₀ hN).mp hklo)
  have hloK := Real.log_lt_log (mul_pos ha hN) ((lt_div_iff₀ hN).mp hklo)
  have hhiK := Real.log_le_log hk0 ((div_le_iff₀ hN).mp hkhi)
  rw [Real.log_mul ha.ne' hN.ne'] at hloK
  rw [Real.log_mul hb.ne' hN.ne'] at hhiK
  exact ⟨(lt_div_iff₀ hB0).mpr (by nlinarith [hlog.1]),
    (div_le_iff₀ hB0).mpr (by nlinarith [hlog.2])⟩

end JointDickman

end OAI
