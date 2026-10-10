import OAI.Probability.SLE.Loewner.SlitChartSmallSemicircles

namespace OAI

/-! A small image semicircle can be closed by a small path outside the
surviving domain. The closing path lies on the static slit and the real boundary. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma SimpleSlitChart.exists_small_inverse_closing_path
    {arc : C(unitInterval,ℂ)} (P : SimpleSlitChart arc) (x Q ε : ℝ) (hε : 0<ε) :
    ∃ (v : ℝ) (c : ℝ → ℂ) (p : Path (c Real.pi) (c 0)), v<Q ∧ Continuous c ∧
      (∀ θ∈Ioo 0 Real.pi, c θ=P.inverse ((x:ℂ)+Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))) ∧
      (∀ θ∈Icc 0 Real.pi, dist (c θ) (c 0)<ε) ∧
      (∀ s, dist (p s) (c 0)<ε ∧ p s∉(upperHalfPlane \ range arc)) ∧
      c 0∈frontier ((upperHalfPlane \ range arc)) ∧ c Real.pi∈frontier ((upperHalfPlane \ range arc)) ∧
      MapsTo c (Ioo 0 Real.pi) ((upperHalfPlane \ range arc)) ∧ InjOn c (Ioo 0 Real.pi) := by
  obtain ⟨M,hM⟩ := P.inverse_bounded_over_ball (‖(x:ℂ)‖+1)
  let R := max (M+1) 0
  obtain ⟨δ,hδ,hpath⟩ := slitBoundaryBarrier_uniform_paths arc R (le_max_right _ _)
    (ε/2) (half_pos hε)
  let η := min 1 (min (ε/2) (δ/2))
  have hη : 0<η := lt_min zero_lt_one (lt_min (half_pos hε) (half_pos hδ))
  obtain ⟨v,c,hv,hc,he,hdiam,hc0,hcπ,hmap,hinj⟩ :=
    P.exists_small_inverse_semicircle x (min Q 0) η hη
  have hv0 : v<0 := hv.trans_le (min_le_right _ _)
  have hη1 : η≤1 := min_le_left _ _
  have hηε : η≤ε/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η≤δ/2 := (min_le_right _ _).trans (min_le_right _ _)
  let a := Real.pi/2
  have ha : a∈Ioo 0 Real.pi := ⟨half_pos Real.pi_pos,by dsimp [a]; linarith [Real.pi_pos]⟩
  have hwa : (x:ℂ)+Complex.exp ((v:ℂ)+(a:ℂ)*Complex.I)∈upperHalfPlane := by
    have he' := exp_strip_halfplane (x := (v:ℂ)+(a:ℂ)*Complex.I) (by simpa using ha)
    change 0<((x:ℂ)+Complex.exp ((v:ℂ)+(a:ℂ)*Complex.I)).im
    simpa only [Set.mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add] using he'
  have hna : ‖(x:ℂ)+Complex.exp ((v:ℂ)+(a:ℂ)*Complex.I)‖≤‖(x:ℂ)‖+1 := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [Complex.norm_exp]
    simpa using (Real.exp_le_one_iff.mpr hv0.le)
  have hca : ‖c a‖≤M := by rw [he a ha]; exact hM _ hwa hna
  have hcb (s : ℝ) (hs : s∈Icc 0 Real.pi) : ‖c s‖≤R := by
    have hd : ‖c s-c a‖≤η := hdiam s hs a (Ioo_subset_Icc_self ha)
    calc
      ‖c s‖ ≤ ‖c s-c a‖+‖c a‖ := by
        convert norm_add_le (c s-c a) (c a) using 1; simp
      _ ≤ η+M := add_le_add hd hca
      _ ≤ 1+M := add_le_add hη1 le_rfl
      _ = M+1 := add_comm _ _
      _ ≤ R := le_max_left _ _
  have h0 : c 0∈slitBoundaryBarrier arc R :=
    frontier_mem_slitBoundaryBarrier arc hc0 (hcb 0 ⟨le_rfl,Real.pi_pos.le⟩)
  have hπ : c Real.pi∈slitBoundaryBarrier arc R :=
    frontier_mem_slitBoundaryBarrier arc hcπ (hcb Real.pi ⟨Real.pi_pos.le,le_rfl⟩)
  have hdπ : dist (c Real.pi) (c 0)≤η := by
    simpa only [dist_eq_norm] using hdiam Real.pi ⟨Real.pi_pos.le,le_rfl⟩ 0 ⟨le_rfl,Real.pi_pos.le⟩
  obtain ⟨p,hpB,hp⟩ := hpath (c Real.pi) hπ (c 0) h0 (hdπ.trans_lt (hηδ.trans_lt (half_lt_self hδ)))
  refine ⟨v,c,p,hv.trans_le (min_le_left _ _),hc,he,?_,?_,hc0,hcπ,hmap,hinj⟩
  · intro θ hθ
    have hdθ : dist (c θ) (c 0)≤η := by
      simpa only [dist_eq_norm] using hdiam θ hθ 0 ⟨le_rfl,Real.pi_pos.le⟩
    exact hdθ.trans_lt (hηε.trans_lt (half_lt_self hε))
  · intro s
    refine ⟨?_,fun hD => (disjoint_left.mp (slitBoundaryBarrier_disjoint_domain arc R)) (hpB s) hD⟩
    have htri := dist_triangle (p s) (c Real.pi) (c 0)
    have hps := hp s
    linarith

end SLEExactGauge

end

end OAI
