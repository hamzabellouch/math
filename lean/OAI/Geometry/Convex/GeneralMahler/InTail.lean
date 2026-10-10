import OAI.Geometry.Convex.GeneralMahler.InPoint

namespace OAI
/-! Uniform tail integral estimate over a spectral box. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ} [NeZero m]
namespace Param
variable {R : ℝ} (x:Param m R) (hr:0<R) (q₀:ProjField m)
lemma s0_four : (x.instanceQ hr q₀).s0 ≤ 4 := by
  unfold s0 trN
  rw [div_le_iff₀ m_pos,← mul_one (x.instanceQ hr q₀).covMat,(x.instanceQ hr q₀).trace_SPS]
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  apply le_trans (Finset.sum_le_sum (g := fun i => (4:ℝ)) ?_)
  · simp; rw [mul_comm]
  intro i hi
  rw [_root_.map_one]
  change ⟪op (x.instanceQ hr q₀).S (b i), op (x.instanceQ hr q₀).S (b i)⟫ ≤ _
  have hn : ‖b i‖ = 1 := b.orthonormal.1 i
  rw [← Z_def,real_inner_self_eq_norm_sq]
  have hh := x.Z_two hr q₀ (b i)
  rw [hn,mul_one] at hh
  nlinarith [norm_nonneg ((x.instanceQ hr q₀).Z (b i))]

lemma area_B :
    IntegrableOn (x.instanceQ hr q₀).Bt (Ici (0:ℝ)) ∧ (∫ t in Ici (0:ℝ), (x.instanceQ hr q₀).Bt t) ≤ 8 := by
  let s := Ici (0:ℝ)
  let μ := (volume : Measure ℝ).restrict s
  have he (z:ℝ) (hz:z∈s) : (x.instanceQ hr q₀).Bt z ≤ 2*(x.instanceQ hr q₀).layerW z := by
    have hp : 1/2 ≤ p z := by rw [← p_half]; apply p_mono.monotone hz
    have hq := (x.instanceQ hr q₀).Bt_nonneg z
    unfold layerW
    nlinarith [(x.instanceQ hr q₀).r1_pos z,a_pos z]
  have hi : Integrable (fun z=> (2:ℝ)*(x.instanceQ hr q₀).layerW z) μ :=
    ((x.instanceQ hr q₀).integrable_w.const_mul _).integrableOn
  have hh : Integrable (x.instanceQ hr q₀).Bt μ := hi.mono' (x.instanceQ hr q₀).Bt_cd.continuous.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg ((x.instanceQ hr q₀).Bt_nonneg z)]
    apply he z hz)
  refine ⟨hh,?_⟩
  apply le_trans (setIntegral_mono_on hh hi measurableSet_Ici he)
  rw [integral_const_mul]
  have h := setIntegral_le_integral (s := s) (x.instanceQ hr q₀).integrable_w
    (ae_of_all _ fun z => ((x.instanceQ hr q₀).w_positive z).le)
  rw [(x.instanceQ hr q₀).integral_w] at h
  have h' := x.s0_four hr q₀
  linarith

lemma B_segment (z : ℝ) (h : -1 ≤ z) :
    (x.instanceQ hr q₀).Bt z ≤ 4/a (-1) := by
  have hp : a (-1) ≤ a z := a_mono.monotone h
  have hb := ((x.instanceQ hr q₀).mul_Bt_avH z).trans (((x.instanceQ hr q₀).avH_le_s z).trans (x.s0_four hr q₀))
  apply (le_div_iff₀ (a_pos _)).mpr
  nlinarith [(x.instanceQ hr q₀).Bt_nonneg z]
end Param

lemma exponential_area {N C:ℝ} (hc:0<C) :
    let L := C*(1+N)
    let g := fun z => Real.exp (-(z/C-1-N))
    IntegrableOn g (Ioi L) ∧ (∫ z in Ioi L, g z) = C := by
  intro L g
  let f := fun z : ℝ => -C*g z
  have hd (z:ℝ) : HasDerivAt f (g z) z := by
    have hi := ((((((hasDerivAt_id' z).div_const C).sub_const 1).sub_const N).neg.exp)).const_mul (-C)
    convert hi using 1
    all_goals first | rfl | (unfold g; field_simp; rfl)
  have ht : Tendsto (fun z:ℝ=>-(z/C-1-N)) atTop atBot := by
    apply tendsto_neg_atTop_atBot.comp
    simp only [sub_eq_add_neg]
    apply tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ ?_)
    exact Tendsto.atTop_div_const hc tendsto_id
  have he : Tendsto f atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp ht).const_mul (-C)
    simpa only [mul_zero,f,g,Function.comp_def] using h
  have hi := integrableOn_Ioi_deriv_of_nonneg' (a:=L) (fun z _=>hd z) (fun z _=>Real.exp_nonneg _) he
  refine ⟨hi,?_⟩
  have hu := integral_Ioi_of_hasDerivAt_of_tendsto' (a:=L) (fun z _=>hd z) hi he
  rw [hu]
  change 0- -C*Real.exp _=C
  rw [show -(L/C-1-N)=0 from by dsimp [L]; field_simp; ring, Real.exp_zero]
  ring

lemma dir_tail_area (m:ℕ) [NeZero m] :
    ∃ A ≥ 0, ∀ K, ∀ q : ProjField m, q.Bound K → ∀ v:Rn m, ‖v‖=1 →
    ∀ N:ℝ, 4≤N →
    let C := cutoffC m K
    let L := C*(1+N)
    (∫ z in Ioi L,(1-q.dimH v z)) ≤ A*Real.exp (-(N^2)/4)*C := by
  classical
  obtain ⟨A,hA,h₁⟩ := normal_tail m 0
  refine ⟨A,hA,fun K q hk v hv N hn => ?_⟩
  let C := cutoffC m K
  let L := C*(1+N)
  let g := fun z => Real.exp (-(z/C-1-N))
  have hb := positive_exact m hk.one_le
  have hc : 0<C := lt_of_lt_of_le zero_lt_one hb.1
  have hi := exponential_area (N:=N) hc
  have HE (z) (hz:z∈Ioi L) : 1-q.dimH v z ≤ A*Real.exp (-(N^2)/4)*g z := by
    let y := z/C-1
    let S : Set (Rn m) := {x| y ≤ ‖x‖}
    have hm : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
    let f := fun x:Rn m => (1-⟪v,op (q.Pmat z x) v⟫)
    have hf (x) : f x ≤ S.indicator (fun x:Rn m=> (1+‖x‖)^0) x := by
      by_cases hx:x∈S
      · rw [indicator_of_mem hx,pow_zero]
        exact sub_le_self _ ((op_posSemidef_iff.mp (q.Pmat_psd z x).posSemidef).2 v)
      rw [indicator_of_notMem hx]
      have hh : q.Pmat z x = 1 := by
        apply projJac_id q.C (hb.2 q hk _ x ?_)
        change ¬ z/C-1≤‖x‖ at hx
        rw [mul_comm]
        apply (lt_div_iff₀ hc).mp
        linarith
      unfold f; rw [hh,_root_.map_one]; change 1-⟪v,v⟫≤0
      rw [real_inner_self_eq_norm_sq,hv]; norm_num
    let μ := normal m
    have hf' : Integrable (fun x:Rn m=>⟪v,op (q.Pmat z x) v⟫) μ :=
      integral_opPair (meanJac_integrable q.C q.root (q.shift z)) v v
    have he : 1-q.dimH v z=∫ x,f x ∂μ := by
      unfold f; rw [integral_sub (integrable_const (μ := μ) _) hf']; simp [ProjField.dimH,μ]
    have hny : N ≤ y := by
      change C*(1+N)<z at hz
      change N≤z/C-1
      have he : 1+N ≤ z/C := (le_div_iff₀ hc).mpr (by linarith)
      linarith
    rw [he]
    apply le_trans (integral_mono ((integrable_const _).sub hf')
      ((integrable_envelope (μ:=μ) 0).indicator hm) hf)
    rw [integral_indicator hm]
    apply le_trans (h₁ y (by linarith))
    rw [mul_assoc A]
    apply mul_le_mul_of_nonneg_left _ hA
    change Real.exp _ ≤ _*Real.exp (-(y-N))
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have hp := hi.1.const_mul (A*Real.exp (-(N^2)/4))
  have hl : Ioi L ⊆ Ici (0:ℝ) := fun z hz => by
    apply le_trans (show (0:ℝ) ≤ L by dsimp [L]; nlinarith) (le_of_lt (mem_Ioi.mp hz))
  apply le_trans (setIntegral_mono_on ((q.plus_int v hv).mono_set hl) hp measurableSet_Ioi HE)
  rw [integral_const_mul, hi.2]
end GeneralMahler

end

end OAI
