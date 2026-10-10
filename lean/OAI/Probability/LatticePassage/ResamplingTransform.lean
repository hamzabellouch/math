import OAI.Probability.LatticePassage.FiniteResampling
import OAI.Probability.LatticePassage.ExponentialIncrement

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

theorem sum_upwardResampling_transform (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (φ : ℝ → ℝ≥0∞) (hφ : MonotoneOn φ (Set.Ici 0)) (hzero : φ 0 = 0) :
    (∑ e ∈ localEdges x R, ∫⁻ u, φ (upwardResampling ω x y R e u) ∂expMeasure 1) ≤
      (∫⁻ u, φ u ∂expMeasure 1) * R := by
  classical
  obtain ⟨p,hp,hl,hm⟩ := local_geodesic_exists ω x y R hR
  have hsub : (pathEdges p).toFinset ⊆ localEdges x R := by
    intro e he
    exact mem_biUnion.mpr ⟨⟨y,p⟩, mem_localCandidates p hp hl, he⟩
  have he : ∀ e, (∫⁻ u, φ (upwardResampling ω x y R e u) ∂expMeasure 1) ≤
      if e ∈ pathEdges p then ∫⁻ u, φ u ∂expMeasure 1 else 0 := by
    intro e
    by_cases he : e ∈ pathEdges p
    · rw [ite_eq_left he]
      apply lintegral_mono_ae
      filter_upwards [exponential_positive] with u hu
      apply hφ (by change 0 ≤ upwardResampling ω x y R e u; unfold upwardResampling; positivity) hu.le
      simpa only [ite_eq_left he] using upwardResampling_le ω hω p hp hl hm e u hu.le
    · rw [ite_eq_right he, ← lintegral_zero (μ := expMeasure 1)]
      apply lintegral_mono_ae
      filter_upwards [exponential_positive] with u hu
      have hb := upwardResampling_le ω hω p hp hl hm e u hu.le
      simp only [ite_eq_right he] at hb
      have hn : 0 ≤ upwardResampling ω x y R e u := by unfold upwardResampling; positivity
      rw [le_antisymm hb hn, hzero]
  calc
    _ ≤ ∑ e ∈ localEdges x R, if e ∈ pathEdges p then ∫⁻ u, φ u ∂expMeasure 1 else 0 :=
      sum_le_sum (fun e _ => he e)
    _ = ∑ e ∈ (pathEdges p).toFinset, ∫⁻ u, φ u ∂expMeasure 1 := by
      rw [← sum_filter]
      congr 1
      ext e
      simp only [mem_filter, List.mem_toFinset]
      exact and_iff_right_of_imp (fun he => hsub (List.mem_toFinset.mpr he))
    _ = (p.length : ℝ≥0∞) * ∫⁻ u, φ u ∂expMeasure 1 := by
      rw [sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup (pathEdges_nodup hp.isTrail),
        pathEdges_length]
    _ ≤ (∫⁻ u, φ u ∂expMeasure 1)*R := by
      rw [mul_comm]
      gcongr

lemma exponential_increment_monotone (a : ℝ) :
    MonotoneOn (fun u => ENNReal.ofReal ((exp (a*u/2)-1)^2)) (Set.Ici 0) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  apply ENNReal.ofReal_le_ofReal
  rcases le_total 0 a with ha | ha
  · have he : exp (a*u/2) ≤ exp (a*v/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : 1 ≤ exp (a*u/2) := one_le_exp_iff.mpr (by nlinarith)
    nlinarith
  · have he : exp (a*v/2) ≤ exp (a*u/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : exp (a*u/2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    nlinarith

theorem sum_upwardResampling_exponential (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e ∈ localEdges x R, ∫⁻ u, ENNReal.ofReal
      ((exp (a * upwardResampling ω x y R e u / 2)-1)^2) ∂expMeasure 1) ≤
      ENNReal.ofReal (2*a^2) * R := by
  apply (sum_upwardResampling_transform ω hω x y R hR _ (exponential_increment_monotone a)
    (by simp)).trans
  gcongr
  exact exponential_half_increment_square_le a ha

theorem finite_upward_exponential_sum (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (v : LocalCoordinates x R) (hv : ∀ e, 0 ≤ v e)
    (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e : ↥(localEdges x R), ∫⁻ u, ENNReal.ofReal
      ((exp (a * max (finitePassageTime x y R (Function.update v e u) -
        finitePassageTime x y R v) 0 / 2)-1)^2) ∂expMeasure 1) ≤
      ENNReal.ofReal (2*a^2) * R := by
  classical
  have hn : ∀ e, 0 ≤ extendLocalCoordinates x R v e := by
    intro e
    unfold extendLocalCoordinates
    split_ifs with he
    · exact hv ⟨e,he⟩
    · exact le_rfl
  have h := sum_upwardResampling_exponential (extendLocalCoordinates x R v) hn x y R hR a ha
  rw [← sum_attach (localEdges x R)] at h
  simpa only [attach_eq_univ, finitePassageTime, extendLocalCoordinates_update, upwardResampling]
    using h

end CompanionFPP

end OAI
