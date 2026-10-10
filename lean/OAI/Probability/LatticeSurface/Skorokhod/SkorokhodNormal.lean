import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodNormalSupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem projection_mesh_normal_limit (B : Body E) (x₀ c : E) (r : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1))
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2) :
    ∃u : ℝ → E,ContinuousOn u (Icc 0 1) ∧
      TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      (∀t∈Icc (0:ℝ) 1,u t∈B.carrier) ∧
      eVariationOn (fun t => u t-x₀-(w t-w 0)) (Icc (0:ℝ) 1) ≤ ENNReal.ofReal (‖x₀-c‖^2/r) ∧
      ∀ε:ℝ,0 < ε → ∃M:ℕ,∀m:ℕ,M ≤ m → 0 < m →
        ∀y:ℕ → E,(∀j< m,y j∈B.carrier) →
          normalPartition u (fun t => u t-x₀-(w t-w 0)) y m ≤ ε := by
  obtain ⟨u,hucont,hu,humem,hvar⟩ := projection_mesh_regular_limit B x₀ c r hx₀ hr hball w hw hosc
  refine ⟨u,hucont,hu,humem,hvar,?_⟩
  let C := ‖x₀-c‖^2/r
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) hr.le
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hucont
  have htime (m j : ℕ) (hm : 0 < m) (hj : j ≤ m) : (j:ℝ)/m∈Icc (0:ℝ) 1 := by
    have hm' : (0:ℝ)< m := by exact_mod_cast hm
    refine ⟨by positivity,?_⟩
    rw [div_le_one hm'];exact_mod_cast hj
  have hk : ∀t∈Icc (0:ℝ) 1,Tendsto
      (fun n : ℕ => regulator B x₀ (sampledDriver w (n+1)) ⌊t*((n+1:ℕ):ℝ)⌋₊)
      atTop (nhds (u t-x₀-(w t-w 0))) := by
    intro t ht
    have htend := (hw t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨sample_floor_tendsto t ht.1,Eventually.of_forall fun n => sample_floor_mem (n+1) (Nat.succ_pos _) t ht⟩)
    have hh := ((hu.tendsto_at ht).sub_const x₀).sub (htend.sub_const (w 0))
    simpa only [regulator,mesh,sampledDriver,Nat.cast_zero,zero_div,Function.comp_apply] using hh
  intro ε hε
  let δ := ε/(C+1)
  have hC1 : 0 < C+1 := by linarith
  have hδ : 0 < δ := div_pos hε hC1
  have hδC : δ*C < ε := by
    have he : δ*(C+1)=ε := div_mul_cancel₀ ε hC1.ne'
    nlinarith
  obtain ⟨η,hη,hηu⟩ := Metric.uniformContinuousOn_iff.mp huc (δ/2) (half_pos hδ)
  obtain ⟨M,hM⟩ := exists_nat_gt ((2:ℝ)/η)
  refine ⟨M,fun m hm hmpos y hy => ?_⟩
  have hm' : (0:ℝ)< m := by exact_mod_cast hmpos
  have hmsmall : (1:ℝ)/m < η/2 := by
    have hmlarge : (2:ℝ)/η < m := hM.trans_le (by exact_mod_cast hm)
    have hh := (div_lt_iff₀ hη).mp hmlarge
    apply (div_lt_iff₀ hm').mpr
    nlinarith
  let L : ℕ → ℝ := fun n => ∑j∈Finset.range m,
    inner ℝ (u ((j:ℝ)/m)-y j)
      (regulator B x₀ (sampledDriver w (n+1)) ⌊((j+1:ℕ)/(m:ℝ))*((n+1:ℕ):ℝ)⌋₊-
       regulator B x₀ (sampledDriver w (n+1)) ⌊((j:ℝ)/m)*((n+1:ℕ):ℝ)⌋₊)
  have hL : Tendsto L atTop
      (nhds (normalPartition u (fun t => u t-x₀-(w t-w 0)) y m)) := by
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.inner
      ((hk _ (htime m (j+1) hmpos (by simpa using Finset.mem_range.mp hj))).sub
       (hk _ (htime m j hmpos (Finset.mem_range.mp hj).le)))
  have hevent : ∀ᶠ n : ℕ in atTop,(1:ℝ)/(n+1:ℕ)<η/2 := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds (half_pos hη))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hb : normalPartition u (fun t => u t-x₀-(w t-w 0)) y m ≤ δ*C := by
    apply le_of_tendsto hL
    filter_upwards [hevent,Metric.tendstoUniformlyOn_iff.mp hu (δ/2) (half_pos hδ)] with n hn hun
    let q : ℕ → ℕ := fun j => ⌊((j:ℝ)/m)*((n+1:ℕ):ℝ)⌋₊
    have hq : Monotone q := by
      intro i j hij
      apply Nat.floor_mono
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hm'.le
    have hq₀ : q 0=0 := by simp [q]
    have hqN : q m=n+1 := by simp only [q,div_self hm'.ne',one_mul,Nat.floor_natCast]
    have hnf : 0 < n+1 := Nat.succ_pos _
    have hclose : ∀ j < m,∀i,q j ≤ i → i<q (j+1) →
        ‖u ((j:ℝ)/m)-walk B x₀ (sampledDriver w (n+1)) (i+1)‖ ≤ δ := by
      intro j hj i hi₀ hi₁
      obtain ⟨hts,hd⟩ := partition_sample_near m (n+1) hmpos hnf j i hj hi₀ hi₁
      let ts : ℝ := (i+1:ℕ)/((n+1:ℕ):ℝ)
      have hs : (j:ℝ)/m∈Icc (0:ℝ) 1 := htime m j hmpos hj.le
      have hdist : dist ((j:ℝ)/m) ts < η := by
        rw [Real.dist_eq,abs_sub_comm]
        change |((i+1:ℕ):ℝ)/((n+1:ℕ):ℝ)-(j:ℝ)/m| < η
        have hh := add_lt_add hmsmall hn
        have he : η/2+η/2=η := by ring
        rw [he] at hh
        exact hd.trans hh
      have h₁ : ‖u ((j:ℝ)/m)-u ts‖ < δ/2 := by simpa only [dist_eq_norm] using hηu _ hs _ hts hdist
      have h₂ : ‖u ts-walk B x₀ (sampledDriver w (n+1)) (i+1)‖ < δ/2 := by
        have hh := hun ts hts
        rw [dist_eq_norm,mesh_at_sample B x₀ w (n+1) hnf (i+1)] at hh
        exact hh
      exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        ((add_lt_add h₁ h₂).trans_eq (by ring)).le
    have hc := normal_coarse_bound B x₀ (sampledDriver w (n+1)) q hq hq₀ m (n+1) hqN
      (fun j => u ((j:ℝ)/m)) y hy δ hclose
    have hV := regulator_variation_bound B x₀ c r ‖x₀-c‖ hx₀ hr le_rfl hball (sampledDriver w (n+1)) (n+1)
      (by intro i hi;simpa only [sampledDriver,Nat.cast_zero,zero_div] using hosc _ (htime (n+1) i hnf hi))
    exact hc.trans (mul_le_mul_of_nonneg_left hV hδ.le)
  exact hb.trans hδC.le

end ConvexSkorokhod

end OAI
