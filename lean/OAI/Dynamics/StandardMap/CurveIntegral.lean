import OAI.Dynamics.StandardMap.CurveIterate

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma curveInterval_lintegral_speed (I : CurveInterval) (v : ℝ → CurvePlane)
    (ε : ℝ) (hε : 0≤ε) (hv : ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε) :
    (∫⁻s in Icc I.left I.right,ENNReal.ofReal ‖v s‖)≤ENNReal.ofReal ε := by
  by_cases hzero:I.length=0
  · have hab:I.left=I.right := by dsimp [CurveInterval.length] at hzero; linarith
    simp only [hab,Icc_self,Measure.restrict_singleton,measure_singleton,zero_smul,lintegral_zero_measure]
    exact bot_le
  have hpos:0<I.length := lt_of_le_of_ne I.length_nonneg (Ne.symm hzero)
  have hpoint:∀s∈Icc I.left I.right,‖v s‖≤ε/I.length := by
    intro s hs
    obtain ⟨t,ht,rfl⟩:=I.parameter_range.superset hs
    have h:=hv t ht
    rw [I.velocity_norm] at h
    exact (le_div_iff₀ hpos).mpr (by nlinarith)
  calc
    _ ≤ ∫⁻s in Icc I.left I.right,ENNReal.ofReal (ε/I.length) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      exact ENNReal.ofReal_le_ofReal (hpoint s hs)
    _ = ENNReal.ofReal ε := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      change ENNReal.ofReal (ε/I.length)*ENNReal.ofReal I.length=ENNReal.ofReal ε
      rw [← ENNReal.ofReal_mul (div_nonneg hε hpos.le),div_mul_cancel₀ _ hpos.ne']
lemma curve_cover_lintegral_speed {ι : Type*} [Fintype ι]
    (I : ι → CurveInterval) (v : ℝ → CurvePlane) (ε : ℝ) (hε : 0≤ε)
    (hv : ∀i,∀t∈Icc (0:ℝ) 1,‖(I i).velocity v t‖≤ε)
    (S : Set ℝ) (hS : ∀s∈S,∃i,s∈Icc (I i).left (I i).right) :
    (∫⁻s in S,ENNReal.ofReal ‖v s‖)≤(Fintype.card ι:ℝ≥0∞)*ENNReal.ofReal ε := by
  calc
    _ ≤ ∫⁻s in ⋃i,Icc (I i).left (I i).right,ENNReal.ofReal ‖v s‖ :=
      lintegral_mono_set (fun s hs=>mem_iUnion.mpr (hS s hs))
    _ ≤ ∑'i,∫⁻s in Icc (I i).left (I i).right,ENNReal.ofReal ‖v s‖ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑'i:ι,ENNReal.ofReal ε := ENNReal.tsum_le_tsum (fun i=>curveInterval_lintegral_speed (I i) v ε hε (hv i))
    _ = _ := by simp [tsum_fintype]
lemma controlled_curve_speed_from_map (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε : ℝ) (I : CurveInterval) (C : ControlledCurve ε) (hC : C.map=g ∘ I.parameter) :
    ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε := by
  intro t ht
  have h:=I.hasDeriv hv t
  rw [← hC] at h
  rw [h.unique (C.hasDeriv t)]
  exact C.speed t ht
lemma curve_iterate_lintegral (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g : ControlledCurve ε) (c : ℕ → CurvePlane) (n : ℕ) (S : Set ℝ)
    (hS : S⊆Icc (0:ℝ) 1)
    (hword : ∀s∈S,∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g.map s))) :
    (∫⁻s in S,ENNReal.ofReal ‖curveIterVelocity k g.map g.velocity n s‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
  obtain ⟨I,C,hcover,hmap⟩:=curve_iterate_cover k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 g c n
  have h:=curve_cover_lintegral_speed I (curveIterVelocity k g.map g.velocity n) ε hε
    (fun i=>controlled_curve_speed_from_map _ _ (curveIter_hasDeriv k g.map g.velocity g.hasDeriv n)
      ε (I i) (C i) (hmap i)) S (fun s hs=>hcover s (hS hs) (hword s hs))
  simpa only [curveTree_card,Nat.cast_pow] using h
end StandardMapEntropy

end OAI
