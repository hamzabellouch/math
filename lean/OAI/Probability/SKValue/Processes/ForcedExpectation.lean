import Mathlib
import OAI.Probability.SKValue.Processes.CrossMesh
import OAI.Probability.SKValue.Control.Forced

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace SKValue
lemma ForcedTest.expectation_step {T K L t δ:ℝ} {γ:ℝ → ℝ} {u V b₀ p₀:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b₀ p₀ K L) (ht:0≤t) (hδ:0≤δ) (hδ1:δ≤1) (htδ:t+δ≤T)
    {N j:ℕ} (hj:j<N+1) {Y:(Fin (N+1) → ℝ) → ℝ}
    (hYm:Measurable Y) (hYp:DependsBefore j Y) :
    let μ := gaussianProduct (Fin (N+1))
    let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*γ t*u t (Y z)
    |(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)-δ*(∫ z,forcedSource γ u V b₀ p₀ t (Y z) ∂μ)|≤
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+δ*K*(γ (t+δ)-γ t) := by
  let μ := gaussianProduct (Fin (N+1))
  let p := fun z ↦ deriv (V t) (Y z)
  let a := fun z ↦ deriv (deriv (V t)) (Y z)
  let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*γ t*u t (Y z)
  let P := fun z ↦ Real.sqrt δ*rawIncrement p j z
  let Q := fun z ↦ (δ/2)*(a z*((coordinate N j z)^2-1))
  let S := fun z ↦ forcedSource γ u V b₀ p₀ t (Y z)
  let D := fun z ↦ V (t+δ) (Y' z)-V t (Y z)-δ*S z
  let R := fun z ↦ D z-P z-Q z
  let E := fun z ↦ δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N j z)+δ*K*(γ (t+δ)-γ t)
  have htT:t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hpm:Measurable p := ((h.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have ham:Measurable a := by
    have hh := (h.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ] at hh
    exact hh.measurable.comp hYm
  have hpM:MemLp p 2 μ := MemLp.of_bound hpm.aestronglyMeasurable K
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.first_bound t htm (Y z)))
  have haM:MemLp a 2 μ := MemLp.of_bound ham.aestronglyMeasurable K
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.second_bound t htm (Y z)))
  have hpp:DependsBefore j p := fun z z' hz ↦ by dsimp only [p];rw [hYp z z' hz]
  have hap:DependsBefore j a := fun z z' hz ↦ by dsimp only [a];rw [hYp z z' hz]
  have hPi:Integrable P μ := (((rawIncrement_memLp hj hpm hpp hpM).const_mul _).integrable (by norm_num))
  have hQi:Integrable Q μ := (((predictableCenteredSquare_memLp ham (fun z ↦ h.second_bound t htm (Y z))).const_mul _).integrable (by norm_num))
  have hP0:(∫ z,P z ∂μ)=0 := by
    dsimp only [P]
    rw [integral_const_mul,rawIncrement_mean hj hpm hpp,mul_zero]
  have hQ0:(∫ z,Q z ∂μ)=0 := by
    dsimp only [Q]
    rw [integral_const_mul,predictableCenteredSquare_mean hj ham hap,mul_zero]
  have hY'm:Measurable Y' := (hYm.add ((measurable_coordinate N j).const_mul _)).add
    (((h.drift_measurable t htm).comp hYm).const_mul _)
  have hcur:Integrable (fun z ↦ V t (Y z)) μ :=
    (MemLp.of_bound ((h.smooth t htm).continuous.measurable.comp hYm).aestronglyMeasurable K
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.bound t htm (Y z))) :
        MemLp (fun z ↦ V t (Y z)) 2 μ).integrable (by norm_num)
  have hnext:Integrable (fun z ↦ V (t+δ) (Y' z)) μ :=
    (MemLp.of_bound ((h.smooth (t+δ) hem).continuous.measurable.comp hY'm).aestronglyMeasurable K
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.bound (t+δ) hem (Y' z))) :
        MemLp (fun z ↦ V (t+δ) (Y' z)) 2 μ).integrable (by norm_num)
  have hSi:Integrable S μ :=
    (MemLp.of_bound ((h.source_measurable htm).comp hYm).aestronglyMeasurable ((1+2*γ T)*K)
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.source_bound htm (Y z))) :
        MemLp S 2 μ).integrable (by norm_num)
  have hDi:Integrable D μ := (hnext.sub hcur).sub (hSi.const_mul δ)
  have hRi:Integrable R μ := (hDi.sub hPi).sub hQi
  have hEi0 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j)
    (h.gamma_nonneg T ⟨ht.trans htT,le_rfl⟩) K ((1/2+γ T)*L)).integrable (by norm_num)
  have hEi:Integrable E μ := (hEi0.const_mul _).add (integrable_const _)
  have hRE (z) : |R z|≤E z := by
    have hh := h.euler_one_step ht hδ hδ1 htδ (x:=Y z) (z:=coordinate N j z)
    convert! hh using 1
    dsimp only [R,D,P,Q,p,a,Y',S,E,rawIncrement]
    congr 1
    ring_nf
  have hRmean:(∫ z,R z ∂μ)=(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)-δ*(∫ z,S z ∂μ) := by
    have hs := integral_sub (hDi.sub hPi) hQi
    change (∫ z,D z-P z-Q z ∂μ)=(∫ z,D z-P z ∂μ)-(∫ z,Q z ∂μ) at hs
    have hs1 := integral_sub hDi hPi
    change (∫ z,D z-P z ∂μ)=(∫ z,D z ∂μ)-(∫ z,P z ∂μ) at hs1
    change (∫ z,D z-P z-Q z ∂μ)=_
    rw [hs,hs1,hP0,hQ0,sub_zero,sub_zero]
    have hs2 := integral_sub (hnext.sub hcur) (hSi.const_mul δ)
    change (∫ z,V (t+δ) (Y' z)-V t (Y z)-δ*S z ∂μ)=
      (∫ z,V (t+δ) (Y' z)-V t (Y z) ∂μ)-(∫ z,δ*S z ∂μ) at hs2
    dsimp only [D]
    rw [hs2,integral_sub hnext hcur,integral_const_mul]
  have hEmean:(∫ z,E z ∂μ)=
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+δ*K*(γ (t+δ)-γ t) := by
    dsimp only [E]
    rw [integral_add (hEi0.const_mul _) (integrable_const _),integral_const_mul]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have he:(∫ z,cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N j z) ∂μ)=
        cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) := by
      simpa only [Function.comp_def,cubicEnvelopeMean,standardGaussian] using
        (coordinate_hasLaw N j).integral_comp (measurable_cubicEnvelope (γ T) K ((1/2+γ T)*L)).aestronglyMeasurable
    rw [he]
  change |(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)-δ*(∫ z,forcedSource γ u V b₀ p₀ t (Y z) ∂μ)|≤_
  rw [←hRmean,←hEmean]
  exact abs_integral_le_integral_abs.trans (integral_mono hRi.norm hEi hRE)
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace SKValue
lemma ForcedTest.mesh_expectation {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) (hT:0<T) (hT1:T≤1) {N:ℕ} (hN:0<N) :
    |(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))-V 0 0-stepSize T N*∑ j∈Finset.range N,
      (∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))|≤
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
        stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  let A := fun j ↦ ∫ z,V (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))
  let S := fun j ↦ ∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  have hδ:0≤δ := div_nonneg hT.le hNr.le
  have hδ1:δ≤1 := by
    apply (div_le_iff₀ hNr).mpr
    have hn:(1:ℝ)≤N := by exact_mod_cast hN
    simpa only [one_mul] using hT1.trans hn
  have htime (j:ℕ) (hj:j≤N) := mesh_time_mem hT.le hN hj
  have hs (j:ℕ) : meshTime T N j+δ=meshTime T N (j+1) := by dsimp [meshTime];push_cast;ring
  have hlast:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
  have hzero:meshTime T N 0=0 := by simp [meshTime]
  have hum (j:ℕ) (hj:j<N) : Measurable (u (meshTime T N j)) := h.drift_measurable _ (htime j hj.le)
  have hstep (j:ℕ) (hj:j<N) : |A (j+1)-A j+(-δ*S j)|≤
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
        δ*K*(γ (meshTime T N (j+1))-γ (meshTime T N j))+0*((0:ℝ)-0) := by
    have hYp:DependsBefore j (fun z ↦ euler T N γ u z j) :=
      eulerCoefficient_dependsBefore T hj.le γ u (fun _ y ↦ y)
    have he := h.expectation_step (htime j hj.le).1 hδ hδ1
      (by rw [hs];exact (htime (j+1) (by omega)).2) (by omega:j<N+1)
      (measurable_euler T N γ u hum j hj.le) hYp
    dsimp only at he
    rw [hs] at he
    simpa only [A,S,euler,δ,mul_assoc,add_zero,sub_self,mul_zero,sub_eq_add_neg,neg_mul] using he
  have hh := abs_telescope_source (A:=A) (b:=fun j ↦ -δ*S j) (Γ:=fun j ↦ γ (meshTime T N j))
    (Δ:=fun _ ↦ 0) (e:=0) hstep
  have hA0:A 0=V 0 0 := by simp [A,meshTime,euler]
  rw [hA0,show A N=(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1))) by
    dsimp only [A];rw [hlast],hlast,hzero] at hh
  have hNd:(N:ℝ)*δ=T := by dsimp [δ,stepSize];field_simp
  simpa only [neg_mul,Finset.sum_neg_distrib,←Finset.mul_sum,sub_self,mul_zero,add_zero,←mul_assoc,hNd,←sub_eq_add_neg,S] using hh

lemma ForcedTest.terminal_lipschitz {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) (hT:0≤T) (x y:ℝ) : |V T x-V T y|≤K*|x-y| := by
  have hd := (h.smooth T ⟨hT,le_rfl⟩).differentiable (by norm_num)
  have hb:∀ z,‖deriv (V T) z‖≤K := fun z ↦ by simpa only [Real.norm_eq_abs] using h.first_bound T ⟨hT,le_rfl⟩ z
  have hl : LipschitzWith ⟨K,h.K_nonneg⟩ (V T) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro z
    exact_mod_cast hb z
  have hh := hl.dist_le_mul x y
  change |V T x-V T y|≤K*|x-y| at hh
  exact hh

lemma ForcedTest.coupled_terminal_error {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L':ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (hT:0<T) (hu:GradientStrip T γ u K L) (h:ForcedTest T γ u V b p K' L')
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,(∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+
      ∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) {N:ℕ} (hN:0<N) :
    |(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))-
      (∫ ω,V T (X T ω) ∂μ)|≤K'*Real.sqrt (∫ ω,(meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let F := fun ω ↦ V T (coupledEuler T γ u B N N ω)
  let G := fun ω ↦ V T (X T ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht:T∈Icc (0:ℝ) T := ⟨hT.le,le_rfl⟩
  have hm:Continuous (V T) := (h.smooth T ht).continuous
  have hFM:MemLp F 2 μ := MemLp.of_bound
    (hm.measurable.comp_aemeasurable (coupled_euler_measurable hB hT hu N N le_rfl).aemeasurable).aestronglyMeasurable K'
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs,F] using h.bound T ht _))
  have hGM:MemLp G 2 μ := MemLp.of_bound
    (hm.measurable.comp_aemeasurable (hXM T ht).aemeasurable).aestronglyMeasurable K'
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs,G] using h.bound T ht _))
  have hEM:MemLp E 2 μ := coupled_mesh_error_memLp hB hT hu hXM hpaths hN
  have hlast:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
  have hFG (ω:Ω) : |F ω-G ω|≤K'*|E ω| := by
    have he:|coupledEuler T γ u B N N ω-X T ω|≤E ω := by
      have hh := le_initialMax (f:=fun k ↦
        |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) (le_refl N)
      change |coupledEuler T γ u B N N ω-X (meshTime T N N) ω|≤E ω at hh
      rwa [hlast] at hh
    exact (h.terminal_lipschitz hT.le _ _).trans
      (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) h.K_nonneg)
  have heq:(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))=(∫ ω,F ω ∂μ) := by
    have heum := measurable_euler T N γ u (fun j hj ↦ (hu.smooth _ (mesh_time_mem hT.le hN hj.le)).continuous.measurable) N le_rfl
    have hh := (coupledCoordinates_hasLaw hB hT hN).integral_comp (hm.measurable.comp heum).aestronglyMeasurable
    simpa only [Function.comp_apply,F,coupledEuler,ite_eq_right (Nat.ne_of_gt hN)] using hh.symm
  rw [heq]
  exact first_moment_perturbation hFM hGM hEM h.K_nonneg (Eventually.of_forall hFG)
end SKValue

end

end OAI
