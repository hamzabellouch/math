import OAI.Analysis.LpDimension.Model

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
universe uE uI uΩ

namespace SubpolynomialLp

lemma independent_of_affine_sum {E : Type uE} {I : Type uI} [Fintype E] (z : I → E → ℝ)
    (hz : AffineIndependent ℝ z) (hs : ∀ i, ∑ e, z i e = 1) :
    LinearIndependent ℝ z := by
  classical
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hsum := congrArg (fun v : E → ℝ => ∑ e, v e) hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.sum_const_zero] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, hs, mul_one] at hsum
  exact hz.eq_zero_of_sum_eq_zero hsum hw i hi

lemma hyperplane_convex_representation {E : Type uE} [Fintype E] {K : Set (E → ℝ)}
    (hK : ∀ z ∈ K, ∑ e, z e = 1) {v : E → ℝ} (hv : v ∈ convexHull ℝ K) :
    ∃ k ≤ Fintype.card E, ∃ (z : Fin k → E → ℝ) (w : Fin k → ℝ),
      (∀ i, z i ∈ K) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = v := by
  classical
  obtain ⟨I, hI, z, w, hz, hi, hw, hws, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hv
  let e := (Fintype.equivFin I).symm
  have hlin := independent_of_affine_sum z hi (fun i => hK _ (hz ⟨i,rfl⟩))
  have hc : Fintype.card I ≤ Fintype.card E := by
    simpa using hlin.fintype_card_le_finrank
  refine ⟨Fintype.card I, hc, z ∘ e, w ∘ e, ?_, ?_, ?_, ?_⟩
  · intro i; exact hz ⟨e i, rfl⟩
  · intro i; exact (hw (e i)).le
  · exact (e.sum_comp w).trans hws
  · exact (e.sum_comp (fun i => w i • z i)).trans hsum

lemma compact_convexHull_hyperplane {E : Type uE} [Fintype E] {K : Set (E → ℝ)}
    (hKc : IsCompact K) (hK : ∀ z ∈ K, ∑ e, z e = 1) :
    IsCompact (convexHull ℝ K) := by
  classical
  let A (k : ℕ) : Set ((Fin k → E → ℝ) × (Fin k → ℝ)) :=
    (Set.pi Set.univ (fun _ => K)) ×ˢ {weights | (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1}
  let f (k : ℕ) (a : (Fin k → E → ℝ) × (Fin k → ℝ)) := ∑ i, a.2 i • a.1 i
  have hAc (k : ℕ) : IsCompact (A k) := by
    have hs : IsCompact {weights : Fin k → ℝ |
        (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1} := by
      convert isCompact_range
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin k)).continuous using 1
      ext weights
      simp [Convexity.StdSimplex.range_toFun_comp_weights]
    simpa [A, Set.pi] using (isCompact_pi_infinite (fun _ : Fin k => hKc)).prod
      hs
  have hf (k : ℕ) : Continuous (f k) := by unfold f; fun_prop
  have he : convexHull ℝ K = ⋃ k ∈ Finset.range (Fintype.card E+1), (f k) '' (A k) := by
    ext v
    constructor
    · intro hv
      obtain ⟨k,hk,z,w,hz,hw,hws,hv⟩ := hyperplane_convex_representation hK hv
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      exact ⟨(z,w), ⟨by simpa using hz, hw,hws⟩, hv⟩
    · intro hv
      obtain ⟨k,hk,a,ha,rfl⟩ := Set.mem_iUnion.mp hv |>.imp (fun k => Set.mem_iUnion.mp)
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => ha.2.1 i) ha.2.2
        (fun i _ => subset_convexHull ℝ K (ha.1 i (Set.mem_univ i)))
  rw [he]
  exact Finset.isCompact_biUnion _ (fun k _ => (hAc k).image (hf k))

lemma normalized_integral_mem {E : Type uE} {Ω : Type uΩ} [Fintype E] [MeasurableSpace Ω]
    (μ : Measure Ω) {K : Set (E → ℝ)} (hKc : IsCompact K)
    (hK : ∀ z ∈ K, ∑ e, z e = 1) (q : Ω → E → ℝ) (hqi : Integrable q μ)
    (hq : ∀ᵐ t ∂μ, q t = 0 ∨ (0 < ∑ e, q t e ∧ (∑ e, q t e)⁻¹ • q t ∈ K))
    (hS : 0 < ∫ t, ∑ e, q t e ∂μ) :
    (∫ t, ∑ e, q t e ∂μ)⁻¹ • (∫ t, q t ∂μ) ∈ convexHull ℝ K := by
  classical
  let S := ∫ t, ∑ e, q t e ∂μ
  have hsi : Integrable (fun t => ∑ e, q t e) μ :=
    integrable_finsetSum _ (fun e _ => (integrable_pi_iff.mp hqi) e)
  by_contra hn
  obtain ⟨f,a,hfa,haf⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ K)
    (compact_convexHull_hyperplane hKc hK).isClosed hn
  have hle : ∀ᵐ t ∂μ, f (q t) ≤ a * ∑ e, q t e := by
    filter_upwards [hq] with t ht
    rcases ht with ht | ⟨ht,hkt⟩
    · simp [ht]
    · have hh := (hfa _ (subset_convexHull ℝ K hkt)).le
      rw [map_smul, smul_eq_mul] at hh
      simpa only [mul_comm] using (inv_mul_le_iff₀ ht).mp hh
  have hi := integral_mono_ae (f.integrable_comp hqi) (hsi.const_mul a) hle
  rw [f.integral_comp_comm hqi, integral_const_mul] at hi
  rw [map_smul, smul_eq_mul] at haf
  have : S⁻¹ * f (∫ t, q t ∂μ) ≤ a := (inv_mul_le_iff₀ hS).mpr (by simpa only [mul_comm] using hi)
  exact (not_lt_of_ge this) haf

end SubpolynomialLp

end

end OAI
