import OAI.Dynamics.StandardMap.CurveLineIntegral

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma product_slice_bound_reverse (E I : Set ℝ) (T:Set CurvePlane) (f:CurvePlane → ℝ≥0∞)
    (K:ℝ≥0∞) (_hE:MeasurableSet E) (hI:MeasurableSet I) (hT:MeasurableSet T) (hf:Measurable f)
    (hsub:T⊆E ×ˢ I)
    (hslice:∀y∈I,∫⁻x in E,T.indicator f (x,y)≤K) :
    (∫⁻z in T,f z)≤K*volume I := by
  have he:(∫⁻z in T,f z)=∫⁻z in E ×ˢ I,T.indicator f z := by
    rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hsub]
  rw [he]
  change (∫⁻z,T.indicator f z ∂(volume.prod volume).restrict (E ×ˢ I))≤_
  rw [← Measure.prod_restrict,lintegral_prod_symm' _ (hf.indicator hT)]
  calc
    _ ≤ ∫⁻y in I,K := setLIntegral_mono' hI hslice
    _ = _ := by simp
lemma fiber_indicator_bound (T:Set CurvePlane) (hT:MeasurableSet T) (f:CurvePlane → ℝ≥0∞)
    (g:ℝ → CurvePlane) (hg:Measurable g) (I:Set ℝ) :
    (∫⁻t in I,T.indicator f (g t))≤∫⁻t in g ⁻¹' T,f (g t) := by
  calc
    _ ≤ ∫⁻t,T.indicator f (g t) := by
      simpa only [Measure.restrict_univ] using (lintegral_mono_set (f:=fun t=>T.indicator f (g t)) (μ:=volume) (show I⊆univ from subset_univ _))
    _ = _ := by
      rw [← lintegral_indicator (hg hT)]
      congr 1

lemma grid_word_wrapped (k:ℝ) (Q:ℕ) (hQ:0<Q) (z:CurvePlane) (z0:Torus) (j:ℕ)
    (h:gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=gridLabel Q hQ ((torusStep k)^[j] z0)) :
    wrappedBox (1/(Q:ℝ)) (torusRep ((torusStep k)^[j] z0)) ((liftStep k)^[j] z) := by
  apply projection_wrappedBox
  have hp:liftProjection ((liftStep k)^[j] z)=(torusStep k)^[j] (liftProjection z) :=
    (show Function.Semiconj liftProjection (liftStep k) (torusStep k) from liftProjection_step k).iterate_right j z
  rw [hp]
  exact gridLabel_close Q hQ h
lemma grid_word_initial (Q:ℕ) (hQ:0<Q) (z:CurvePlane) (z0:Torus)
    (hz:z∈Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (h:gridLabel Q hQ (liftProjection z)=gridLabel Q hQ z0) :
    z∈Icc (gridInterval Q hQ (gridIndex Q hQ z0.1)).left (gridInterval Q hQ (gridIndex Q hQ z0.1)).right ×ˢ
      Icc (gridInterval Q hQ (gridIndex Q hQ z0.2)).left (gridInterval Q hQ (gridIndex Q hQ z0.2)).right := by
  obtain ⟨h1,h2⟩:=(gridLabel_eq_iff Q hQ _ _).mp h
  have hx:=gridInterval_mem Q hQ (liftProjection z).1
  have hy:=gridInterval_mem Q hQ (liftProjection z).2
  rw [h1] at hx
  rw [h2] at hy
  simp only [liftProjection,circleRep_coe_of_mem hz.1] at hx
  simp only [liftProjection,circleRep_coe_of_mem hz.2] at hy
  exact ⟨hx,hy⟩
lemma grid_word_columns_integral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (z0:Torus) (T:Set CurvePlane) (hT:MeasurableSet T)
    (hunit:T⊆Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1)
    (hword:∀z∈T,∀j≤n,gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=
      gridLabel Q hQ ((torusStep k)^[j] z0)) :
    (∫⁻z in T,ENNReal.ofReal ‖horizontalVelocity k n z‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ)) ∧
    (∫⁻z in T,ENNReal.ofReal ‖verticalVelocity k n z‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ)) := by
  let Jx:=gridInterval Q hQ (gridIndex Q hQ z0.1)
  let Jy:=gridInterval Q hQ (gridIndex Q hQ z0.2)
  let E:=Icc Jx.left Jx.right
  let I:=Icc Jy.left Jy.right
  have hsub:T⊆E ×ˢ I := fun z hz=>grid_word_initial Q hQ z z0 (hunit hz) (hword z hz 0 (Nat.zero_le _))
  have hq:(0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hδ:0≤1/(Q:ℝ) := by positivity
  have hδ1:1/(Q:ℝ)≤1 := (div_le_one hq).mpr (by exact_mod_cast hQ)
  have hδe:6*(1/(Q:ℝ))≤ε := by simpa only [mul_one_div] using hQε
  have hlen:1/(Q:ℝ)≤ε := by linarith
  have hvolX:volume E=ENNReal.ofReal (1/(Q:ℝ)) := by
    rw [Real.volume_Icc]; exact congrArg ENNReal.ofReal (gridInterval_length Q hQ _)
  have hvolY:volume I=ENNReal.ofReal (1/(Q:ℝ)) := by
    rw [Real.volume_Icc]; exact congrArg ENNReal.ofReal (gridInterval_length Q hQ _)
  constructor
  · have hs:∀y∈I,∫⁻x in E,T.indicator (fun z=>ENNReal.ofReal ‖horizontalVelocity k n z‖) (x,y)≤
        ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
      intro y hy
      let g:ℝ → CurvePlane:=fun x=>(x,y)
      have hg:∀t,HasDerivAt g (1,0) t := fun t=>(hasDerivAt_id t).prodMk (hasDerivAt_const t y)
      have hc:=cell_line_lintegral k ε (1/(Q:ℝ)) hk hε hδ hδ1 hδe hε1 hε2 N hN hN2 g (1,0)
        (by simp) hg Jx (by rw [gridInterval_length]; exact hlen)
        (fun j=>torusRep ((torusStep k)^[j+1] z0)) n (g ⁻¹' T)
        (fun t ht=>(hsub ht).1) (fun t ht j hj=>grid_word_wrapped k Q hQ (g t) z0 (j+1) (hword (g t) ht _ (by omega)))
      exact (fiber_indicator_bound T hT _ g (measurable_id.prodMk measurable_const) E).trans hc
    have hh:=product_slice_bound_reverse E I T _ _ measurableSet_Icc measurableSet_Icc hT
      (ENNReal.measurable_ofReal.comp (continuous_horizontalVelocity k n).norm.measurable) hsub hs
    simpa only [hvolY,Function.comp_apply] using hh
  · have hs:∀x∈E,∫⁻y in I,T.indicator (fun z=>ENNReal.ofReal ‖verticalVelocity k n z‖) (x,y)≤
        ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
      intro x hx
      let g:ℝ → CurvePlane:=fun y=>(x,y)
      have hg:∀t,HasDerivAt g (0,1) t := fun t=>(hasDerivAt_const t x).prodMk (hasDerivAt_id t)
      have hc:=cell_line_lintegral k ε (1/(Q:ℝ)) hk hε hδ hδ1 hδe hε1 hε2 N hN hN2 g (0,1)
        (by simp) hg Jy (by rw [gridInterval_length]; exact hlen)
        (fun j=>torusRep ((torusStep k)^[j+1] z0)) n (g ⁻¹' T)
        (fun t ht=>(hsub ht).2) (fun t ht j hj=>grid_word_wrapped k Q hQ (g t) z0 (j+1) (hword (g t) ht _ (by omega)))
      exact (fiber_indicator_bound T hT _ g (measurable_const.prodMk measurable_id) I).trans hc
    have hh:=product_slice_bound E I T _ _ measurableSet_Icc measurableSet_Icc hT hsub hs
    simpa only [hvolX] using hh
lemma grid_word_transfer_integral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (z0:Torus) (T:Set CurvePlane) (hT:MeasurableSet T)
    (hunit:T⊆Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1)
    (hword:∀z∈T,∀j≤n,gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=
      gridLabel Q hQ ((torusStep k)^[j] z0)) :
    (∫⁻z in T,ENNReal.ofReal ‖liftSegmentTransfer k z 0 n‖)≤
      ENNReal.ofReal (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ≥0∞)^n := by
  have hmX:Measurable (fun z=>ENNReal.ofReal ‖horizontalVelocity k n z‖) := ENNReal.measurable_ofReal.comp (continuous_horizontalVelocity k n).norm.measurable
  have hmY:Measurable (fun z=>ENNReal.ofReal ‖verticalVelocity k n z‖) := ENNReal.measurable_ofReal.comp (continuous_verticalVelocity k n).norm.measurable
  obtain ⟨hx,hy⟩:=grid_word_columns_integral k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n z0 T hT hunit hword
  calc
    _ ≤ ∫⁻z in T,(2:ℝ≥0∞)*(ENNReal.ofReal ‖horizontalVelocity k n z‖+ENNReal.ofReal ‖verticalVelocity k n z‖) := by
      apply lintegral_mono
      intro z
      have h:=ENNReal.ofReal_le_ofReal (liftTransfer_columns_bound k n z)
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] using h
    _ = 2*((∫⁻z in T,ENNReal.ofReal ‖horizontalVelocity k n z‖)+
        (∫⁻z in T,ENNReal.ofReal ‖verticalVelocity k n z‖)) := by
      change (∫⁻z in T,(2:ℝ≥0∞)*((fun z=>ENNReal.ofReal ‖horizontalVelocity k n z‖)+(fun z=>ENNReal.ofReal ‖verticalVelocity k n z‖)) z)=_
      rw [lintegral_const_mul _ (hmX.add hmY)]
      simp only [Pi.add_apply]
      rw [lintegral_add_left hmX]
    _ ≤ 2*(((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ))+
        ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity)
    _ = _ := by
      rw [show 4*ε/(Q:ℝ)=4*(ε*(1/(Q:ℝ))) by ring,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4), ENNReal.ofReal_mul hε,ENNReal.ofReal_ofNat]
      ring
end StandardMapEntropy

end OAI
