import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodBV

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem projection_mesh_regular_limit (B : Body E) (x₀ c : E) (r : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0<r) (hball : Metric.closedBall c r⊆B.carrier)
    (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1))
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖≤r/2) :
    ∃ u : ℝ → E,ContinuousOn u (Icc 0 1) ∧
      TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      (∀t∈Icc (0:ℝ) 1,u t∈B.carrier) ∧
      eVariationOn (fun t => u t-x₀-(w t-w 0)) (Icc (0:ℝ) 1) ≤
        ENNReal.ofReal (‖x₀-c‖^2/r) := by
  obtain ⟨u,hu,humem⟩ := projection_mesh_uniform_limit B x₀ c r hx₀ hr hball w hw hosc
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw
  have hucont : UniformContinuousOn u (Icc (0:ℝ) 1) := by
    apply Metric.uniformContinuousOn_iff.mpr
    intro ε hε
    have hg : ContinuousAt (fun a : ℝ => a+Real.sqrt (2*a*(‖x₀-c‖^2/r))) 0 := by fun_prop
    obtain ⟨d,hd,hgd⟩ := Metric.continuousAt_iff.mp hg ε hε
    let δ := d/2
    have hδ : 0<δ := half_pos hd
    have hsmall : δ+Real.sqrt (2*δ*(‖x₀-c‖^2/r))<ε := by
      have h := hgd (x:=δ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using half_lt_self hd)
      simpa only [mul_zero,zero_mul,Real.sqrt_zero,add_zero,Real.dist_eq,sub_zero,
        abs_of_nonneg (add_nonneg hδ.le (Real.sqrt_nonneg _))] using h
    obtain ⟨η,hη,hηw⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
    refine ⟨η/2,half_pos hη,fun s hs t ht hst => ?_⟩
    have hevent : ∀ᶠ n : ℕ in atTop,(1:ℝ)/(n+1:ℕ)<η/2 := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds (half_pos hη))
      simpa only [Nat.cast_add,Nat.cast_one] using hh
    have hb : ‖u s-u t‖ ≤ δ+Real.sqrt (2*δ*(‖x₀-c‖^2/r)) := by
      apply le_of_tendsto (((hu.tendsto_at hs).sub (hu.tendsto_at ht)).norm)
      filter_upwards [hevent] with n hn
      apply mesh_modulus B x₀ c r δ η hx₀ hr hball w hosc hδ.le
        (fun a ha b hb hab => by
          have hh : ‖w a-w b‖<δ := by
            simpa only [dist_eq_norm] using hηw a ha b hb (by simpa only [Real.dist_eq] using hab)
          exact hh.le)
        (n+1) (Nat.succ_pos _) s t hs ht
      rw [Real.dist_eq] at hst
      linarith
    rw [dist_eq_norm]
    exact hb.trans_lt hsmall
  refine ⟨u,hucont.continuousOn,hu,humem,?_⟩
  have hk : ∀t∈Icc (0:ℝ) 1,Tendsto
      (fun n : ℕ => regulator B x₀ (sampledDriver w (n+1)) ⌊t*((n+1:ℕ):ℝ)⌋₊)
      atTop (nhds (u t-x₀-(w t-w 0))) := by
    intro t ht
    have htend := (hw t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨sample_floor_tendsto t ht.1,Eventually.of_forall fun n => sample_floor_mem (n+1) (Nat.succ_pos _) t ht⟩)
    have hh := ((hu.tendsto_at ht).sub_const x₀).sub (htend.sub_const (w 0))
    simpa only [regulator,mesh,sampledDriver,Nat.cast_zero,zero_div,Function.comp_apply] using hh
  by_contra hn
  have hh := eVariationOn.lowerSemicontinuous_aux hk (lt_of_not_ge hn)
  obtain ⟨n,hn⟩ := hh.exists
  exact (not_lt_of_ge (mesh_regulator_variation B x₀ c r hx₀ hr hball w hosc (n+1) (Nat.succ_pos _))) hn

end ConvexSkorokhod

end OAI
