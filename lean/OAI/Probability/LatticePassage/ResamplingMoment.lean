import OAI.Probability.LatticePassage.NaturalMoment
import OAI.Probability.LatticePassage.EdgeInfluence

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

noncomputable def upwardResampling (ω : Environment) (x y : Vertex) (R : ℕ)
    (e : Edge) (u : ℝ) : ℝ := by
  classical
  exact max (localPassageTime (Function.update ω e u) x y R -
    localPassageTime ω x y R) 0

@[fun_prop] lemma measurable_upwardResampling (ω : Environment) (x y : Vertex)
    (R : ℕ) (e : Edge) : Measurable (upwardResampling ω x y R e) := by
  classical
  unfold upwardResampling
  fun_prop

lemma upwardResampling_le (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    {x y : Vertex} {R : ℕ} (p : lattice.Walk x y) (hp : p.IsPath)
    (hl : p.length < R) (hm : pathCost ω p = localPassageTime ω x y R)
    (e : Edge) (u : ℝ) (hu : 0 ≤ u) :
    upwardResampling ω x y R e u ≤ if e ∈ pathEdges p then u else 0 := by
  classical
  have h := localPassageTime_one_edge_upper ω (Function.update ω e u) e
    (fun f hf => Function.update_of_ne hf _ _) p hp hl hm
  simp only [Function.update_self] at h
  unfold upwardResampling
  apply max_le
  · split_ifs at h ⊢ with he
    · linarith [hω e]
    · exact h
  · split_ifs <;> positivity

theorem upwardResampling_lmoment_le (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    {x y : Vertex} {R : ℕ} (p : lattice.Walk x y) (hp : p.IsPath)
    (hl : p.length < R) (hm : pathCost ω p = localPassageTime ω x y R)
    (e : Edge) (k : ℕ) (hk : 1 ≤ k) :
    (∫⁻ u, ENNReal.ofReal ((upwardResampling ω x y R e u)^k) ∂expMeasure 1) ≤
      if e ∈ pathEdges p then (k.factorial : ℝ≥0∞) else 0 := by
  classical
  by_cases he : e ∈ pathEdges p
  · rw [ite_eq_left he, ← exponential_nat_lmoment k]
    apply lintegral_mono_ae
    filter_upwards [exponential_positive] with u hu
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by unfold upwardResampling; positivity)
    simpa [he] using upwardResampling_le ω hω p hp hl hm e u hu.le
  · rw [ite_eq_right he]
    apply le_of_eq
    rw [← lintegral_zero (μ := expMeasure 1)]
    apply lintegral_congr_ae
    filter_upwards [exponential_positive] with u hu
    have hb := upwardResampling_le ω hω p hp hl hm e u hu.le
    simp only [ite_eq_right he] at hb
    have hn : 0 ≤ upwardResampling ω x y R e u := by unfold upwardResampling; positivity
    rw [le_antisymm hb hn, zero_pow (by omega), ENNReal.ofReal_zero]

theorem sum_upwardResampling_lmoment (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ e ∈ localEdges x R,
      ∫⁻ u, ENNReal.ofReal ((upwardResampling ω x y R e u)^k) ∂expMeasure 1) ≤
      (k.factorial : ℝ≥0∞) * R := by
  classical
  obtain ⟨p,hp,hl,hm⟩ := local_geodesic_exists ω x y R hR
  have hsub : (pathEdges p).toFinset ⊆ localEdges x R := by
    intro e he
    exact mem_biUnion.mpr ⟨⟨y,p⟩,mem_localCandidates p hp hl,he⟩
  calc
    _ ≤ ∑ e ∈ localEdges x R, if e ∈ pathEdges p then (k.factorial : ℝ≥0∞) else 0 :=
      sum_le_sum (fun e _ => upwardResampling_lmoment_le ω hω p hp hl hm e k hk)
    _ = ∑ e ∈ (pathEdges p).toFinset, (k.factorial : ℝ≥0∞) := by
      rw [← sum_filter]
      congr 1
      ext e
      simp only [mem_filter, List.mem_toFinset]
      exact and_iff_right_of_imp (fun he => hsub (List.mem_toFinset.mpr he))
    _ = (p.length : ℝ≥0∞) * k.factorial := by
      rw [sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup (pathEdges_nodup hp.isTrail),
        pathEdges_length]
    _ ≤ (k.factorial : ℝ≥0∞) * R := by
      rw [mul_comm]
      gcongr

end CompanionFPP

end OAI
