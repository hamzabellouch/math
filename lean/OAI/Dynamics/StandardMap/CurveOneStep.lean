import OAI.Dynamics.StandardMap.CurveLift

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
abbrev CurveStepBranch (N : ℕ) := Fin N × (Fin 7 × Fin 7) × Fin 4
lemma curveStepBranch_card (N : ℕ) : Fintype.card (CurveStepBranch N)=196*N := by
  simp [CurveStepBranch,Fintype.card_prod]; omega
lemma liftCurve_total_displacement (k ε : ℝ) (hk : 0≤k) (hε : 0≤ε)
    (hsmall : growthBase k*ε≤1) (g : ControlledCurve ε)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖liftStep k (g.map s)-liftStep k (g.map t)‖≤1 := by
  have h:= (liftStep_lipschitz k hk).dist_le_mul (g.map s) (g.map t)
  simp only [dist_eq_norm] at h
  have hd:=curve_displacement _ _ g.hasDeriv ε g.speed ht hs
  have hab:|s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hM:0≤growthBase k := by have :=growthBase_ge_four k hk; linarith
  exact h.trans ((mul_le_mul_of_nonneg_left (hd.trans (mul_le_of_le_one_right hε hab)) hM).trans hsmall)

lemma curve_one_step_cover (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (_hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g : ControlledCurve ε) (c : CurvePlane) :
    ∃(I : CurveStepBranch N → CurveInterval) (C : CurveStepBranch N → ControlledCurve ε),
      (∀s∈Icc (0:ℝ) 1,wrappedBox δ c (liftStep k (g.map s))  →
        ∃i,s∈Icc (I i).left (I i).right) ∧
      ∀i,(C i).map=(liftStep k) ∘ g.map ∘ (I i).parameter := by
  let f:ℝ  →  CurvePlane:=(liftStep k) ∘ g.map
  let v:=liftCurveVelocity k g.map g.velocity
  have hv:∀t,HasDerivAt f (v t) t := liftCurve_hasDeriv k _ _ g.hasDeriv
  have hc:Continuous f := continuous_iff_continuousAt.mpr fun t=>(hv t).continuousAt
  have hcv:Continuous v := liftCurve_velocity_continuous k _ _
    (continuous_iff_continuousAt.mpr fun t=>(g.hasDeriv t).continuousAt) g.continuous_velocity
  let J:=subdivisionInterval N hN
  have hvar:∀i:Fin N,∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,
      ‖(J i).velocity v s-(J i).velocity v t‖≤ε*|s-t| := by
    intro i s hs t ht
    have h:=(J i).variation (fun s hs t ht=>liftCurve_variation k ε hk hε hε1 g hs ht) hs ht
    rw [show (J i).length=1/(N:ℝ) from subdivisionInterval_length N hN i] at h
    apply h.trans
    have hNp:0<(N:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hN)
    have hb:(1/(N:ℝ))^2*(2*growthBase k*ε)≤ε := by
      rw [one_div_pow,mul_comm,one_div,← div_eq_mul_inv,div_le_iff₀ hNp]
      nlinarith
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  let center (i : Fin N) (j : Fin 7×Fin 7) := wrappedCurveCenter c (f ((J i).parameter 0)) j
  let S (i : Fin N) (j : Fin 7×Fin 7) : Set ℝ:=
    Icc 0 1 ∩ {t | ‖f ((J i).parameter t)-center i j‖≤δ}
  have hex:∀i:Fin N,∀j:Fin 7×Fin 7,∃H:Fin 4 → CurveInterval,
      (∀s∈S i j,∃a,s∈Icc (H a).left (H a).right) ∧
      (∀a,∀t∈Icc (0:ℝ) 1,‖(H a).velocity ((J i).velocity v) t‖≤ε) := by
    intro i j
    apply curve_small_target_cover (f ∘ (J i).parameter) ((J i).velocity v)
      ((J i).hasDeriv hv) ε (2*δ) hε (by linarith) (hvar i) (S i j)
    · apply isCompact_Icc.inter_right
      apply isClosed_le _ continuous_const
      have hp:Continuous (J i).parameter := by unfold CurveInterval.parameter affineParameter; fun_prop
      exact ((hc.comp hp).sub continuous_const).norm
    · exact inter_subset_left
    · intro s hs t ht
      have h:=norm_sub_le_norm_sub_add_norm_sub (f ((J i).parameter s)) (center i j) (f ((J i).parameter t))
      rw [norm_sub_rev (center i j)] at h
      exact h.trans (add_le_add hs.2 ht.2 |>.trans_eq (by ring))
  choose H hcover hspeed using hex
  have hC:∀i:Fin N,∀j:Fin 7×Fin 7,∀a:Fin 4,∃C:ControlledCurve ε,
      C.map=(f ∘ (J i).parameter) ∘ (H i j a).parameter := by
    intro i j a
    obtain ⟨C,hC,_⟩:=restricted_controlled_curve ε hε (f ∘ (J i).parameter) ((J i).velocity v)
      ((J i).hasDeriv hv) ((J i).velocity_continuous hcv) (hvar i) (H i j a) (hspeed i j a)
    exact ⟨C,hC⟩
  choose C hC using hC
  refine ⟨fun b=>(J b.1).comp (H b.1 b.2.1 b.2.2),fun b=>C b.1 b.2.1 b.2.2,?_,?_⟩
  · intro s hs hwrap
    obtain ⟨i,hi⟩:=subdivisionInterval_cover N hN hs
    obtain ⟨t,ht,hts⟩:=(J i).parameter_range.superset hi
    have hdist:‖f ((J i).parameter 0)-f ((J i).parameter t)‖≤1 :=
      liftCurve_total_displacement k ε hk hε hε2 g ((J i).parameter_mem (by norm_num)) ((J i).parameter_mem ht)
    have hw:wrappedBox δ c (f ((J i).parameter t)) := by simpa only [hts,f,Function.comp_apply] using hwrap
    obtain ⟨j,hj⟩:=wrappedBox_finite_cover δ hδ1 c _ _ hdist hw
    obtain ⟨a,ha⟩:=hcover i j t ⟨ht,hj⟩
    refine ⟨(i,j,a),?_⟩
    rw [← hts]
    exact (J i).comp_mem (H i j a) ha
  · intro b
    rw [hC]
    funext t
    simp only [Function.comp_apply,CurveInterval.comp_parameter]
    rfl
end StandardMapEntropy

end OAI
