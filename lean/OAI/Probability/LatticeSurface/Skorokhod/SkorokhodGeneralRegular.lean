import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodGeneralSupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma projection_mesh_limit_of_variation (B : Body E) (x₀ : E)
    (hx₀ : x₀∈B.carrier) (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1))
    (C : ℝ) (_hC : 0 ≤ C) (M : ℕ)
    (hvar : ∀N : ℕ,M ≤ N → 0 < N → variation (regulator B x₀ (sampledDriver w N)) N ≤ C) :
    ∃u : ℝ → E,TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      ∀t∈Icc (0:ℝ) 1,u t∈B.carrier := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw
  have hCauchy : UniformCauchySeqOn (fun n => mesh B x₀ w (n+1)) atTop (Icc (0:ℝ) 1) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have hg : ContinuousAt (fun a : ℝ => a+Real.sqrt (4*a*C)) 0 := by fun_prop
    obtain ⟨d,hd,hgd⟩ := Metric.continuousAt_iff.mp hg ε hε
    let δ := d/2
    have hδ : 0<δ := half_pos hd
    have hsmall : δ+Real.sqrt (4*δ*C)<ε := by
      have h := hgd (x:=δ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using half_lt_self hd)
      simpa only [mul_zero,zero_mul,Real.sqrt_zero,add_zero,Real.dist_eq,sub_zero,
        abs_of_nonneg (add_nonneg hδ.le (Real.sqrt_nonneg _))] using h
    obtain ⟨η,hη,hηw⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
    obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)/η)
    refine ⟨max N M,fun m hm n hn t ht => ?_⟩
    have hmN : N ≤ m := (le_max_left N M).trans hm
    have hnN : N ≤ n := (le_max_left N M).trans hn
    have hmM : M ≤ m+1 := ((le_max_right N M).trans hm).trans (Nat.le_succ _)
    have hnM : M ≤ n+1 := ((le_max_right N M).trans hn).trans (Nat.le_succ _)
    have hterm (k : ℕ) (hk : N≤k) : (1:ℝ)/(k+1)<η/2 := by
      have hk' : (N:ℝ)≤k+1 := by exact_mod_cast (hk.trans (Nat.le_succ k))
      have hh := (div_lt_iff₀ hη).mp (hN.trans_le hk')
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr
      nlinarith
    have hmn : (1:ℝ)/(m+1)+1/(n+1)<η := by linarith [hterm m hmN,hterm n hnN]
    have hb := mesh_comparison_of_variation B x₀ C δ η hx₀ w hδ.le
      (fun s hs t ht hst => by
        have hh : ‖w s-w t‖<δ := by simpa only [dist_eq_norm] using hηw s hs t ht (by simpa only [Real.dist_eq] using hst)
        exact hh.le)
      (m+1) (n+1) (Nat.succ_pos _) (Nat.succ_pos _) (by simpa only [Nat.cast_add,Nat.cast_one] using hmn)
      (hvar (m+1) hmM (Nat.succ_pos _)) (hvar (n+1) hnM (Nat.succ_pos _)) t ht
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

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma projection_mesh_regular_of_variation (B : Body E) (x₀ : E)
    (hx₀ : x₀∈B.carrier) (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1))
    (C : ℝ) (hC : 0 ≤ C) (M : ℕ)
    (hvar : ∀N : ℕ,M ≤ N → 0 < N → variation (regulator B x₀ (sampledDriver w N)) N ≤ C) :
    ∃u : ℝ → E,ContinuousOn u (Icc 0 1) ∧
      TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      (∀t∈Icc (0:ℝ) 1,u t∈B.carrier) ∧
      eVariationOn (fun t => u t-x₀-(w t-w 0)) (Icc (0:ℝ) 1) ≤ ENNReal.ofReal C := by
  obtain ⟨u,hu,humem⟩ := projection_mesh_limit_of_variation B x₀ hx₀ w hw C hC M hvar
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw
  have hucont : UniformContinuousOn u (Icc (0:ℝ) 1) := by
    apply Metric.uniformContinuousOn_iff.mpr
    intro ε hε
    have hg : ContinuousAt (fun a : ℝ => a+Real.sqrt (2*a*C)) 0 := by fun_prop
    obtain ⟨d,hd,hgd⟩ := Metric.continuousAt_iff.mp hg ε hε
    let δ := d/2
    have hδ : 0<δ := half_pos hd
    have hsmall : δ+Real.sqrt (2*δ*C)<ε := by
      have h := hgd (x:=δ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using half_lt_self hd)
      simpa only [mul_zero,zero_mul,Real.sqrt_zero,add_zero,Real.dist_eq,sub_zero,
        abs_of_nonneg (add_nonneg hδ.le (Real.sqrt_nonneg _))] using h
    obtain ⟨η,hη,hηw⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
    refine ⟨η/2,half_pos hη,fun s hs t ht hst => ?_⟩
    have hevent : ∀ᶠ n : ℕ in atTop,(1:ℝ)/(n+1:ℕ)<η/2 := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds (half_pos hη))
      simpa only [Nat.cast_add,Nat.cast_one] using hh
    have hb : ‖u s-u t‖ ≤ δ+Real.sqrt (2*δ*C) := by
      apply le_of_tendsto (((hu.tendsto_at hs).sub (hu.tendsto_at ht)).norm)
      filter_upwards [hevent,eventually_ge_atTop M] with n hn hnM
      apply mesh_modulus_of_variation B x₀ C δ η hx₀ w hδ.le
        (fun a ha b hb hab => by
          have hh : ‖w a-w b‖<δ := by
            simpa only [dist_eq_norm] using hηw a ha b hb (by simpa only [Real.dist_eq] using hab)
          exact hh.le)
        (n+1) (Nat.succ_pos _) s t hs ht (hvar (n+1) (hnM.trans (Nat.le_succ _)) (Nat.succ_pos _))
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
  obtain ⟨n,hn,hnM⟩ := (hh.and (eventually_ge_atTop M)).exists
  exact (not_lt_of_ge (mesh_regulator_variation_of_bound B x₀ w (n+1) (Nat.succ_pos _) C
    (hvar (n+1) (hnM.trans (Nat.le_succ _)) (Nat.succ_pos _)))) hn

end ConvexSkorokhod

end OAI
