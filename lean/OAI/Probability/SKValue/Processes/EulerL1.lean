import Mathlib
import OAI.Probability.SKValue.Equations.LipschitzCompMemLpFinite
import OAI.Probability.SKValue.Evolution.BoundedSmooth
import OAI.Probability.SKValue.Equations.TestGenerator
import OAI.Probability.SKValue.Processes.TestExpectation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma euler_same_noise_sum_bound {T G L e : ℝ} {d : ℕ → ℝ} {N : ℕ} {γ β : ℝ → ℝ}
    {u v : ℝ → ℝ → ℝ} (hT : 0≤T) (hN : 0<N)
    (hG : 0≤G) (hL : 0≤L) (hd : ∀ k<N,0≤d k) (he : 0≤e)
    (hg : ∀ j<N,|γ (meshTime T N j)|≤G)
    (hc : ∀ j<N,|β (meshTime T N j)-γ (meshTime T N j)|≤d j)
    (hv : ∀ j<N,∀ x,|v (meshTime T N j) x|≤1)
    (hs : ∀ j<N,∀ x,|v (meshTime T N j) x-u (meshTime T N j) x|≤e)
    (hu : ∀ j<N,∀ x y,|u (meshTime T N j) x-u (meshTime T N j) y|≤L*|x-y|)
    (z : Fin (N+1) → ℝ) {j : ℕ} (hj : j≤N) :
    |euler T N β v z j-euler T N γ u z j|≤(∑ k∈Finset.range j,stepSize T N*(d k+G*e))*Real.exp (T*G*L) := by
  let δ := stepSize T N
  have hδ : 0≤δ := div_nonneg hT (Nat.cast_nonneg _)
  have hNd : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have hrec (k : ℕ) (hk : k<N) :
      |euler T N β v z (k+1)-euler T N γ u z (k+1)|≤
        (1+δ*G*L)*|euler T N β v z k-euler T N γ u z k|+δ*(d k+G*e) := by
    let y := euler T N β v z k
    let x := euler T N γ u z k
    let t := meshTime T N k
    have hb : |β t*v t y-γ t*u t x|≤d k+G*e+G*L*|y-x| := by
      calc
        |β t*v t y-γ t*u t x| = |(β t-γ t)*v t y+γ t*(v t y-u t y)+γ t*(u t y-u t x)| := by congr 1; ring
        _ ≤ |(β t-γ t)*v t y|+|γ t*(v t y-u t y)|+|γ t*(u t y-u t x)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ d k*1+G*e+G*(L*|y-x|) := by
          simp only [abs_mul]
          gcongr
          · exact hd k hk
          · exact hc k hk
          · exact hv k hk y
          · exact hg k hk
          · exact hs k hk y
          · exact hg k hk
          · exact hu k hk y x
        _ = _ := by ring
    change |y+Real.sqrt δ*coordinate N k z+δ*β t*v t y-
      (x+Real.sqrt δ*coordinate N k z+δ*γ t*u t x)|≤_
    calc
      _ = |(y-x)+δ*(β t*v t y-γ t*u t x)| := by congr 1; ring
      _ ≤ |y-x|+δ*|β t*v t y-γ t*u t x| := by simpa only [abs_mul,abs_of_nonneg hδ] using abs_add_le (y-x) (δ*(β t*v t y-γ t*u t x))
      _ ≤ |y-x|+δ*(d k+G*e+G*L*|y-x|) := add_le_add_right (mul_le_mul_of_nonneg_left hb hδ) _
      _ = _ := by ring
  have h := finite_discrete_gronwall (e := fun k ↦ |euler T N β v z k-euler T N γ u z k|) (mul_nonneg (mul_nonneg hδ hG) hL)
    (show |euler T N β v z 0-euler T N γ u z 0|=0 by simp [euler])
    (fun k hk ↦ mul_nonneg hδ (add_nonneg (hd k hk) (mul_nonneg hG he))) hrec j hj
  apply h.trans
  apply mul_le_mul le_rfl
  · apply Real.exp_le_exp.mpr
    calc
      (j : ℝ)*(δ*G*L)≤(N : ℝ)*(δ*G*L) := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (mul_nonneg (mul_nonneg hδ hG) hL)
      _=T*G*L := by rw [←hNd]; ring
  · positivity
  · exact Finset.sum_nonneg (fun k hk ↦ mul_nonneg hδ (add_nonneg (hd k ((Finset.mem_range.mp hk).trans_le hj)) (mul_nonneg hG he)))

end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma monotone_grid_sum_tendsto {γ:ℝ → ℝ} {T:ℝ} (hT:0<T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) (h0:0≤γ 0) :
    Tendsto (fun N:ℕ ↦ stepSize T N*∑ j∈Finset.range N,γ (meshTime T N j)) atTop
      (𝓝 (∫ t in (0:ℝ)..T,γ t)) := by
  simpa only [mul_one,stepSize,meshTime] using
    monotone_weighted_grid_tendsto (γ:=γ) (f:=fun _ ↦ (1:ℝ)) (K:=1) hT (by norm_num) hm h0
      continuousOn_const (fun _ _ ↦ by norm_num)
lemma euler_ordered_coeff_bound {T G L a b:ℝ} {β γ:ℝ → ℝ} {u v:ℝ → ℝ → ℝ}
    {N:ℕ} (hT:0≤T) (hN:0<N) (hG:0≤G) (hL:0≤L) (ha:0≤a) (hb:0≤b)
    (hg:∀ j<N,|γ (meshTime T N j)|≤G)
    (hc:∀ j<N,β (meshTime T N j)≤γ (meshTime T N j)+a)
    (hv:∀ j<N,∀ x,|v (meshTime T N j) x|≤1)
    (hs:∀ j<N,∀ x,|v (meshTime T N j) x-u (meshTime T N j) x|≤b)
    (hu:∀ j<N,∀ x y,|u (meshTime T N j) x-u (meshTime T N j) y|≤L*|x-y|)
    (z:Fin (N+1) → ℝ) :
    |euler T N β v z N-euler T N γ u z N|≤
      (stepSize T N*(∑ j∈Finset.range N,γ (meshTime T N j))-
        stepSize T N*(∑ j∈Finset.range N,β (meshTime T N j))+T*(2*a+G*b))*Real.exp (T*G*L) := by
  have hd (j:ℕ) (hj:j<N) : 0≤γ (meshTime T N j)-β (meshTime T N j)+2*a := by linarith [hc j hj]
  have h:=euler_same_noise_sum_bound (β:=β) (γ:=γ) (u:=u) (v:=v) hT hN hG hL hd hb hg
    (fun j hj ↦ by apply abs_le.mpr;constructor <;> linarith [hc j hj]) hv hs hu z le_rfl
  have he:(∑ j∈Finset.range N,stepSize T N*(γ (meshTime T N j)-β (meshTime T N j)+2*a+G*b))=
      stepSize T N*(∑ j∈Finset.range N,γ (meshTime T N j))-
        stepSize T N*(∑ j∈Finset.range N,β (meshTime T N j))+T*(2*a+G*b) := by
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hNd:(N:ℝ)*stepSize T N=T := by dsimp [stepSize];field_simp
    nlinarith only [congrArg (fun x:ℝ ↦ x*(2*a+G*b)) hNd]
  rwa [he] at h
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma BackwardTest.diffusion_comparison {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L' Lu a b H:ℝ} {γ β:ℝ → ℝ} {u v V:ℝ → ℝ → ℝ}
    (hT:0<T) (hT1:T≤1) (hu:GradientStrip T γ u K L) (h:BackwardTest T β v V K' L')
    (hLu:0≤Lu) (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (ha:0≤a) (hb:0≤b) (hH:0≤H)
    (hc:∀ t∈Icc (0:ℝ) T,β t≤γ t+a)
    (hs:∀ t∈Icc (0:ℝ) T,∀ x,|v t x-u t x|≤b)
    (hf:∀ x y,|V T x-V T y|≤H*|x-y|)
    (hXM:∀ t∈Icc (0:ℝ) T,MemLp (X t) 2 μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
    |(∫ ω,V T (X T ω) ∂μ)-V 0 0|≤
      H*((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,β t)+T*(2*a+γ T*b))*Real.exp (T*γ T*Lu) := by
  let D:=fun N:ℕ ↦ stepSize T N*(∑ j∈Finset.range N,γ (meshTime T N j))-
      stepSize T N*(∑ j∈Finset.range N,β (meshTime T N j))+T*(2*a+γ T*b)
  let E:=fun N:ℕ ↦ T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (β T) K' ((1/2+β T)*L')+
    stepSize T N*K'*(β T-β 0)
  let F:=fun N:ℕ ↦ H*Real.sqrt (∫ ω,(meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)
  have hG:0≤γ T := hu.gamma_nonneg T ⟨hT.le,le_rfl⟩
  have hD:Tendsto D atTop (𝓝 ((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,β t)+T*(2*a+γ T*b))) :=
    ((monotone_grid_sum_tendsto hT hu.gamma_mono (hu.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)).sub
      (monotone_grid_sum_tendsto hT h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩))).add_const _
  have hδ:Tendsto (fun N:ℕ ↦ stepSize T N) atTop (𝓝 (0:ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hδ
  have hE:Tendsto E atTop (𝓝 0) := by
    simpa only [E,Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,add_zero] using
      (((hsqrt.const_mul T).mul_const (cubicEnvelopeMean (β T) K' ((1/2+β T)*L'))).add
        ((hδ.mul_const K').mul_const (β T-β 0)))
  have hF:Tendsto F atTop (𝓝 0) := by
    simpa only [F,Function.comp_def,Real.sqrt_zero,mul_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp
        (coupled_euler_L2_convergence hB hT hu hLu hLip (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths)).const_mul H)
  have hlip:LipschitzWith ⟨H,hH⟩ (V T) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hf x y
  have hbound:∀ᶠ N in atTop,|(∫ ω,V T (X T ω) ∂μ)-V 0 0|≤E N+H*D N*Real.exp (T*γ T*Lu)+F N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    let P:=fun z:Fin (N+1) → ℝ ↦ V T (euler T N β v z N)
    let Q:=fun z:Fin (N+1) → ℝ ↦ V T (euler T N γ u z N)
    have htime (j:ℕ) (hj:j≤N):meshTime T N j∈Icc (0:ℝ) T := mesh_time_mem hT.le hN hj
    have hp:Integrable P (gaussianProduct (Fin (N+1))) := by
      apply Integrable.of_bound ((hlip.continuous.measurable.comp
        (measurable_euler T N β v (fun j hj ↦ h.drift_measurable _ (htime j hj.le)) N le_rfl)).aestronglyMeasurable) K'
      exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_apply] using h.bound T ⟨hT.le,le_rfl⟩ _)
    have hq:Integrable Q (gaussianProduct (Fin (N+1))) := by
      apply Integrable.of_bound ((hlip.continuous.measurable.comp
        (measurable_euler T N γ u (fun j hj ↦ (hu.smooth _ (htime j hj.le)).continuous.measurable) N le_rfl)).aestronglyMeasurable) K'
      exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_apply] using h.bound T ⟨hT.le,le_rfl⟩ _)
    have hpq:|(∫ z,P z ∂gaussianProduct (Fin (N+1)))-(∫ z,Q z ∂gaussianProduct (Fin (N+1)))|≤H*D N*Real.exp (T*γ T*Lu) := by
      rw [←integral_sub hp hq]
      apply (show |∫ z,P z-Q z ∂gaussianProduct (Fin (N+1))|≤H*D N*Real.exp (T*γ T*Lu) from ?_)
      have hnorm:=norm_integral_le_of_norm_le_const (μ:=gaussianProduct (Fin (N+1)))
        (C:=H*D N*Real.exp (T*γ T*Lu)) (f:=fun z ↦ P z-Q z) (Eventually.of_forall (fun z ↦ by
          rw [Real.norm_eq_abs]
          apply (hf _ _).trans
          have he:=euler_ordered_coeff_bound (β:=β) (γ:=γ) (u:=u) (v:=v) hT.le hN hG hLu ha hb
            (fun j hj ↦ by rw [abs_of_nonneg (hu.gamma_nonneg _ (htime j hj.le))]; exact hu.gamma_mono (htime j hj.le) ⟨hT.le,le_rfl⟩ (htime j hj.le).2)
            (fun j hj ↦ hc _ (htime j hj.le)) (fun j hj ↦ h.drift_bound _ (htime j hj.le))
            (fun j hj ↦ hs _ (htime j hj.le))
            (fun j hj x y ↦ by simpa only [sub_self,abs_zero,zero_add] using hLip _ (htime j hj.le) _ (htime j hj.le) x y) z
          simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_left he hH))
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hnorm
    have he:=h.mesh_expectation hT hT1 hN
    have hqX:=coupled_lipschitz_expectation_bound hB hT hu hXM
      (hpaths.mono (fun _ hω ↦ hω.2.2)) hN le_rfl hlip
    have hend:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
    rw [hend] at hqX
    change |(∫ z,Q z ∂gaussianProduct (Fin (N+1)))-(∫ ω,V T (X T ω) ∂μ)|≤F N at hqX
    change |(∫ z,P z ∂gaussianProduct (Fin (N+1)))-V 0 0|≤E N at he
    calc
      |(∫ ω,V T (X T ω) ∂μ)-V 0 0| ≤
          |(∫ ω,V T (X T ω) ∂μ)-(∫ z,Q z ∂gaussianProduct (Fin (N+1)))|+
          |(∫ z,Q z ∂gaussianProduct (Fin (N+1)))-V 0 0| := abs_sub_le _ _ _
      _ ≤ F N+(H*D N*Real.exp (T*γ T*Lu)+E N) := by
        apply add_le_add
        · rw [abs_sub_comm]; exact hqX
        · exact (abs_sub_le _ (∫ z,P z ∂gaussianProduct (Fin (N+1))) _).trans
            (add_le_add (by rw [abs_sub_comm]; exact hpq) he)
      _ = E N+H*D N*Real.exp (T*γ T*Lu)+F N := by ring
  have he:=le_of_tendsto_of_tendsto tendsto_const_nhds
    ((hE.add ((hD.const_mul H).mul_const (Real.exp (T*γ T*Lu)))).add hF) hbound
  simpa only [zero_add,add_zero] using he
end SKValue

end

end OAI
