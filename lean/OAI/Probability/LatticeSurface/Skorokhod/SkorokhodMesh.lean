import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodMeshComparison

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem projection_mesh_uniform_limit (B : Body E) (x₀ c : E) (r : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0<r) (hball : Metric.closedBall c r⊆B.carrier)
    (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1))
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖≤r/2) :
    ∃ u : ℝ → E,TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      ∀t∈Icc (0:ℝ) 1,u t∈B.carrier := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw
  let R := ‖x₀-c‖
  have hCauchy : UniformCauchySeqOn (fun n => mesh B x₀ w (n+1)) atTop (Icc (0:ℝ) 1) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have hg : ContinuousAt (fun a : ℝ => a+Real.sqrt (4*a*(R^2/r))) 0 := by fun_prop
    obtain ⟨d,hd,hgd⟩ := Metric.continuousAt_iff.mp hg ε hε
    let δ := d/2
    have hδ : 0<δ := half_pos hd
    have hsmall : δ+Real.sqrt (4*δ*(R^2/r))<ε := by
      have h := hgd (x:=δ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using half_lt_self hd)
      simpa only [mul_zero,zero_mul,Real.sqrt_zero,add_zero,Real.dist_eq,sub_zero,
        abs_of_nonneg (add_nonneg hδ.le (Real.sqrt_nonneg _))] using h
    obtain ⟨η,hη,hηw⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
    obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)/η)
    refine ⟨N,fun m hm n hn t ht => ?_⟩
    have hterm (k : ℕ) (hk : N≤k) : (1:ℝ)/(k+1)<η/2 := by
      have hk' : (N:ℝ)≤k+1 := by exact_mod_cast (hk.trans (Nat.le_succ k))
      have hh := (div_lt_iff₀ hη).mp (hN.trans_le hk')
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr
      nlinarith
    have hmn : (1:ℝ)/(m+1)+1/(n+1)<η := by linarith [hterm m hm,hterm n hn]
    have hb := mesh_comparison B x₀ c r R δ η hx₀ hr le_rfl hball w hosc hδ.le
      (fun s hs t ht hst => by
        have hh : ‖w s-w t‖<δ := by simpa only [dist_eq_norm] using hηw s hs t ht (by simpa only [Real.dist_eq] using hst)
        exact hh.le)
      (m+1) (n+1) (Nat.succ_pos _) (Nat.succ_pos _) (by simpa only [Nat.cast_add,Nat.cast_one] using hmn) t ht
    rw [dist_eq_norm]
    exact hb.trans_lt hsmall
  have hex : ∀t:ℝ,∃u:E,t∈Icc (0:ℝ) 1 → Tendsto (fun n => mesh B x₀ w (n+1) t) atTop (nhds u) := by
    intro t
    by_cases ht : t∈Icc (0:ℝ) 1
    · obtain ⟨u,hu⟩ := cauchy_map_iff_exists_tendsto.mp (hCauchy.cauchy_map ht)
      exact ⟨u,fun _ => hu⟩
    · exact ⟨x₀,fun h => (ht h).elim⟩
  choose u hu using hex
  refine ⟨u,hCauchy.tendstoUniformlyOn_of_tendsto hu,fun t ht => ?_⟩
  exact B.closed.mem_of_tendsto (hu t ht) (Eventually.of_forall fun n => walk_mem B x₀ hx₀ _ _)

end ConvexSkorokhod

end OAI
