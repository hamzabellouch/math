import OAI.Analysis.Daugavet.Slices

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX uY uIota

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma dual_apply_le_norm (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (z : X) : φ z ≤ ‖z‖ := by
  have hb := φ.le_opNorm z
  rw [Real.norm_eq_abs] at hb
  have hc := mul_le_mul_of_nonneg_right hφ (norm_nonneg z)
  linarith [le_abs_self (φ z)]

/-- One induction step in the diametral argument, with additive rather than multiplicative error. -/
lemma slice_add_almost (hsp : UnitSliceProperty X) {w₀ : X} (hw₀ : ‖w₀‖ = 1)
    (ell : X →L[ℝ] ℝ) (β : ℝ) (hne : ∃ y : X, ‖y‖ ≤ 1 ∧ β < ell y)
    (z : X) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∃ y : X, ‖y‖ = 1 ∧ β < ell y ∧ ‖z‖ + a - δ ≤ ‖z + a • y‖ := by
  by_cases hz : z = 0
  · obtain ⟨y, hy, hβ, _⟩ := hsp w₀ hw₀ ell β hne 1 zero_lt_one
    refine ⟨y, hy, hβ, ?_⟩
    simp only [hz, norm_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hy, mul_one]
    linarith
  · let u := ‖z‖⁻¹ • z
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hz
    let ρ := δ / (‖z‖ + a + 1)
    have hden : 0 < ‖z‖ + a + 1 := by positivity
    have hρ : 0 < ρ := div_pos hδ hden
    have hρmul : ρ * (‖z‖ + a + 1) = δ := div_mul_cancel₀ _ hden.ne'
    obtain ⟨y, hy, hβ, hfar⟩ := hsp u hu ell β hne ρ hρ
    obtain ⟨φ, hφ, hφsum⟩ := exists_dual_vector'' ℝ (u + y)
    change φ (u + y) = ‖u + y‖ at hφsum
    have hφu : φ u ≤ 1 := by simpa [hu] using dual_apply_le_norm φ hφ u
    have hφy : φ y ≤ 1 := by simpa [hy] using dual_apply_le_norm φ hφ y
    rw [map_add] at hφsum
    have hlowu : 1 - ρ ≤ φ u := by linarith
    have hlowy : 1 - ρ ≤ φ y := by linarith
    have hzid : z = ‖z‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
    have hφz : φ z = ‖z‖ * φ u := by conv_lhs => rw [hzid]; rw [map_smul, smul_eq_mul]
    have hb := dual_apply_le_norm φ hφ (z + a • y)
    rw [map_add, map_smul, smul_eq_mul, hφz] at hb
    have hb₁ := mul_le_mul_of_nonneg_left hlowu (norm_nonneg z)
    have hb₂ := mul_le_mul_of_nonneg_left hlowy ha
    exact ⟨y, hy, hβ, by nlinarith⟩

lemma slices_finite_sum (hsp : UnitSliceProperty X) {w₀ : X} (hw₀ : ‖w₀‖ = 1)
    {ι : Type uIota} (a : ι → ℝ) (ell : ι → X →L[ℝ] ℝ) (β : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hne : ∀ i, ∃ y : X, ‖y‖ ≤ 1 ∧ β i < ell i y)
    (s : Finset ι) (z : X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : ι → X, (∀ i ∈ s, ‖y i‖ = 1 ∧ β i < ell i (y i)) ∧
      ‖z‖ + ∑ i ∈ s, a i - δ ≤ ‖z + ∑ i ∈ s, a i • y i‖ := by
  classical
  induction s using Finset.induction generalizing z δ with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    simp only [Finset.sum_empty, add_zero]
    linarith
  | @insert i s hi ih =>
    obtain ⟨y, hy, hsum⟩ := ih z (half_pos hδ)
    obtain ⟨v, hv, hβv, hvfar⟩ := slice_add_almost hsp hw₀ (ell i) (β i) (hne i)
      (z + ∑ j ∈ s, a j • y j) (ha i) (half_pos hδ)
    let y' := Function.update y i v
    have hsame : ∀ j ∈ s, y' j = y j := by
      intro j hj
      have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
      simp [y', hji]
    have hins : y' i = v := by simp [y']
    have hsum' : ∑ j ∈ s, a j • y' j = ∑ j ∈ s, a j • y j :=
      Finset.sum_congr rfl (fun j hj => by rw [hsame j hj])
    refine ⟨y', ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hins ▸ ⟨hv, hβv⟩
      · rw [hsame j hj]
        exact hy j hj
    · rw [Finset.sum_insert hi, Finset.sum_insert hi, hins, hsum']
      have hid : z + (a i • v + ∑ j ∈ s, a j • y j) =
          (z + ∑ j ∈ s, a j • y j) + a i • v := by abel
      rw [hid]
      linarith

variable {Y : Type uY} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The weak-open diametral lemma in finite-dimensional coordinates. -/
theorem diametral_finite_image (hsp : UnitSliceProperty X) {x u : X} (hx : ‖x‖ = 1)
    (hu : ‖u‖ ≤ 1) (T : X →L[ℝ] Y) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ v : X, ‖v‖ ≤ 1 ∧ ‖T v - T u‖ < r ∧ 2 - δ ≤ ‖v - x‖ := by
  obtain ⟨ι, hι, a, ell, β, ha, hsum, hne, hnear⟩ := bourgain_image T hu hr
  let := hι
  obtain ⟨y, hy, hfar⟩ := slices_finite_sum hsp hx a ell β ha hne Finset.univ (-x) hδ
  let v := ∑ i, a i • y i
  have hv : ‖v‖ ≤ 1 := by
    have hm := (convex_closedBall (0 : X) 1).sum_mem (fun i _ => ha i) hsum
      (fun i _ => show y i ∈ Metric.closedBall (0 : X) 1 by simpa using (hy i (Finset.mem_univ i)).1.le)
    simpa [v] using hm
  refine ⟨v, hv, hnear y (fun i => ⟨(hy i (Finset.mem_univ i)).1.le, (hy i (Finset.mem_univ i)).2⟩), ?_⟩
  simpa only [norm_neg, hx, hsum, one_add_one_eq_two, v, sub_eq_add_neg, add_comm] using hfar

end ExactModuli

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

lemma diametral_finite_norm (hsp : UnitSliceProperty X) {x u : X} (hx : ‖x‖ = 1)
    (hu : ‖u‖ ≤ 1) (T : X →L[ℝ] Y) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ v : X, ‖v‖ ≤ 1 ∧ ‖T v - T u‖ < r ∧ 2 - δ ≤ ‖v - x‖ := by
  let e : Y ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Y)) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin])
  let C := ‖e.symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨v, hv, hnear, hfar⟩ := diametral_finite_image hsp hx hu
    (e.toContinuousLinearMap.comp T) (div_pos hr hCp) hδ
  refine ⟨v, hv, ?_, hfar⟩
  have hb := e.symm.toContinuousLinearMap.le_opNorm (e (T v) - e (T u))
  have hid : e.symm (e (T v) - e (T u)) = T v - T u := by simp only [map_sub, e.symm_apply_apply]
  change ‖e.symm (e (T v) - e (T u))‖ ≤ C * ‖e (T v) - e (T u)‖ at hb
  rw [hid] at hb
  change ‖e (T v) - e (T u)‖ < r / (C + 1) at hnear
  have hb' : ‖T v - T u‖ ≤ (C + 1) * ‖e (T v) - e (T u)‖ := by
    nlinarith [norm_nonneg (e (T v) - e (T u))]
  have hstrict := mul_lt_mul_of_pos_left hnear hCp
  rw [mul_div_cancel₀ _ hCp.ne'] at hstrict
  exact hb'.trans_lt hstrict

/-- Finite quotient correction, retaining the small error vector for equivalent-norm estimates. -/
lemma cofinite_diametral_correction (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {F : Submodule ℝ X} (hF : Cofinite F) {ε : ℝ} (hε : 0 < ε) :
    ∃ v e : X, ‖v‖ ≤ 1 ∧ ‖e‖ < ε ∧ v - x - e ∈ F ∧ 2 - ε ≤ ‖v - x‖ := by
  let : IsClosed (F : Set X) := hF.1
  let : FiniteDimensional ℝ (X ⧸ F) := hF.2
  obtain ⟨v, hv, hnear, hfar⟩ := diametral_finite_norm hsp hx hx.le F.mkQL (half_pos hε) hε
  obtain ⟨e, he, heNorm⟩ := Submodule.Quotient.norm_mk_lt (F.mkQL (v - x)) (half_pos hε)
  have hq : ‖F.mkQL (v - x)‖ < ε / 2 := by simpa only [map_sub] using hnear
  refine ⟨v, e, hv, by linarith, ?_, hfar⟩
  apply (Submodule.Quotient.mk_eq_zero F).mp
  change F.mkQL (v - x - e) = 0
  rw [map_sub]
  change F.mkQL (v - x) - Submodule.Quotient.mk e = 0
  rw [he, sub_self]

lemma cofinite_antipodal_endpoint (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {F : Submodule ℝ X} (hF : Cofinite F) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ F, 2 - 2 * ε < ‖z‖ ∧ ‖z‖ ≤ 2 + ε ∧ ‖x + z‖ ≤ 1 + ε := by
  obtain ⟨v, e, hv, he, hzF, hfar⟩ := cofinite_diametral_correction hsp hx hF hε
  refine ⟨v - x - e, hzF, ?_, ?_, ?_⟩
  · have hb := norm_sub_le (v - x - e) (-e)
    have hid : v - x - e - -e = v - x := by abel
    rw [hid, norm_neg] at hb
    linarith
  · have hb := norm_sub_le (v - x) e
    have hb' := norm_sub_le v x
    rw [hx] at hb'
    linarith
  · have hid : x + (v - x - e) = v - e := by abel
    rw [hid]
    have hb := norm_sub_le v e
    linarith

end ExactModuli

end

end OAI
