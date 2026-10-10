import OAI.Probability.SLE.Stochastic.WienerResidualTube

namespace OAI

/-! Uniform support of the real Wiener law on a finite time window,
proved from its Gaussian finite-dimensional laws and continuous paths. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem wienerReal_uniform_tube_pos
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (hf0 : f 0=0)
    (ε : ℝ) (hε : 0 < ε) :
    0 < W {b | ∀ t : unitInterval, |b ⟨t,t.2.1⟩-f ⟨t,t.2.1⟩| < ε} := by
  let η := ε/4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N,hN⟩ := eventually_atTop.mp (wienerGridInterp_uniform f hf.continuousOn η hη)
  obtain ⟨n,hn,hR⟩ := exists_wienerResidualTube_pos W hW η hη N
  let G : Set (Fin (n+3) → ℝ) :=
    {x | ∀ i, |x i-f (wienerGridTime n i)| < η}
  have hG : MeasurableSet G := by
    simp only [G,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_lt
      ((measurable_pi_apply i).sub measurable_const).abs measurable_const)
  have hGpos : 0 < W ((fun b (i : Fin (n+3)) => b (wienerGridTime n i)) ⁻¹' G) :=
    wienerGrid_tube_pos W hW n (fun k => f (wienerGridTime n k)) (by simpa [wienerGridTime] using hf0) η hη
  have hind := wienerGrid_residual_independent hW n
  have he := hind.measure_inter_preimage_eq_mul G (wienerResidualSet η) hG
    (measurableSet_wienerResidualSet η)
  have hpos : 0 < W (((fun b (i : Fin (n+3)) => b (wienerGridTime n i)) ⁻¹' G) ∩
      (fun b t => wienerGridResidual n (fun s b => b s) t b) ⁻¹' wienerResidualSet η) := by
    rw [he]
    exact bot_lt_iff_ne_bot.mpr (mul_ne_zero hGpos.ne' hR.ne')
  refine hpos.trans_le (measure_mono ?_)
  intro b hb t
  have hbG : ∀ k ≤ n+2, |b (wienerGridTime n k)-f (wienerGridTime n k)| ≤ η := by
    intro k hk
    exact (hb.1 (⟨k,by omega⟩ : Fin (n+3))).le
  have hbound : ∀ t : unitInterval, |b ⟨t,t.2.1⟩-f ⟨t,t.2.1⟩| ≤ 3*η := by
    intro u
    refine (show Dense (range (denseSeq unitInterval)) from denseRange_denseSeq unitInterval).induction
      (P := fun t : unitInterval => |b ⟨t,t.2.1⟩-f ⟨t,t.2.1⟩| ≤ 3*η) ?_ ?_ u
    · rintro _ ⟨k,rfl⟩
      let u := denseSeq unitInterval k
      have hr : |b ⟨u,u.2.1⟩-wienerGridInterp n b u| ≤ η := hb.2 k
      have hg := wienerGridInterp_difference n b f u hbG
      have hf' := hN n hn u
      have htri := abs_sub_le (b ⟨u,u.2.1⟩) (wienerGridInterp n b u) (f ⟨u,u.2.1⟩)
      have htri' := abs_sub_le (wienerGridInterp n b u) (wienerGridInterp n f u) (f ⟨u,u.2.1⟩)
      rw [abs_sub_comm (wienerGridInterp n f u)] at htri'
      linarith
    · apply isClosed_le _ continuous_const
      fun_prop
  exact (hbound t).trans_lt (by dsimp [η]; linarith)

end SLEExactGauge

end

end OAI
