import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Extending the time coordinate of a simple half-plane arc while fixing
the real boundary at time zero. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

theorem simple_arc_height_extension (p : C(unitInterval,ℂ)) (hi : Injective p)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ φ : C(ℂ,ℝ), (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, φ (p t)=(t : ℝ)) ∧ (∀ x : ℝ, φ (x : ℂ)=0) := by
  classical
  let K : Set ℂ := range p
  let A : Set ℂ := K ∪ {z : ℂ | z.im=0}
  have hK : IsClosed K := p.continuous.isClosedEmbedding hi |>.isClosed_range
  have hR : IsClosed {z : ℂ | z.im=0} := isClosed_eq Complex.continuous_im continuous_const
  have hA : IsClosed A := hK.union hR
  let t : C(unitInterval,ℝ) := ⟨fun t => t,continuous_subtype_val⟩
  obtain ⟨g,hg⟩ := t.exists_extension' (p.continuous.isClosedEmbedding hi)
  have hgp (t : unitInterval) : g (p t)=(t : ℝ) := congr_fun hg t
  let f : ℂ → ℝ := K.piecewise g 0
  have hfK : EqOn f g K := fun z hz => piecewise_eq_of_mem K g 0 hz
  have hfR (z : ℂ) (hz : z.im=0) : f z=0 := by
    by_cases hzK : z ∈ K
    · obtain ⟨s,rfl⟩ := hzK
      have hs : s=0 := by
        by_contra hs
        have hh := hH s hs
        change 0 < (p s).im at hh
        linarith
      rw [hfK (mem_range_self s),hgp,hs]
      rfl
    · exact piecewise_eq_of_notMem K g 0 hzK
  have hf : ContinuousOn f A :=
    (g.continuous.continuousOn.congr hfK).union_of_isClosed
      (continuousOn_const.congr (fun z hz => hfR z hz)) hK hR
  let fA : C(A,ℝ) := ⟨fun z => f z,hf.domRestrict⟩
  have hfA (z : A) : fA z ∈ Icc (0 : ℝ) 1 := by
    rcases z.property with hz | hz
    · obtain ⟨s,hs⟩ := hz
      change f z ∈ Icc (0 : ℝ) 1
      rw [hfK ⟨s,hs⟩,← hs,hgp]
      exact s.property
    · change f z ∈ Icc (0 : ℝ) 1
      rw [hfR z hz]
      exact ⟨le_rfl,zero_le_one⟩
  obtain ⟨φ,hφ,hφf⟩ := fA.exists_restrict_eq_forall_mem_of_closed hfA
    (nonempty_Icc.mpr zero_le_one) hA
  have he (z : ℂ) (hz : z ∈ A) : φ z=f z := congr_fun (congrArg DFunLike.coe hφf) ⟨z,hz⟩
  refine ⟨φ,hφ,?_,?_⟩
  · intro s
    rw [he _ (Or.inl (mem_range_self s)),hfK (mem_range_self s),hgp]
  · intro x
    rw [he _ (Or.inr (by simp)),hfR _ (by simp)]

end SLEExactGauge

end

end OAI
