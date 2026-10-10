import OAI.InformationTheory.PhotonNumber.ThermalLimit

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace HilbertBasis
open scoped _root_.HilbertBasis
variable {I E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tendsto_isometries (b : HilbertBasis I ℂ E) {l : Filter A}
    (U : A → E ≃ₗᵢ[ℂ] E) (V : E ≃ₗᵢ[ℂ] E)
    (hb : ∀ i, Tendsto (fun a => U a (b i)) l (𝓝 (V (b i)))) (x : E) :
    Tendsto (fun a => U a x) l (𝓝 (V x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,hs⟩ := ((b.hasSum_repr x).eventually
    (Metric.ball_mem_nhds x (by positivity : 0<ε/3))).exists
  let v := ∑ i ∈ s, (b.repr x i) • b i
  have hdist : dist v x<ε/3 := hs
  have hv : Tendsto (fun a => U a v) l (𝓝 (V v)) := by
    simp only [v,map_sum,map_smul]
    exact tendsto_finsetSum s (fun i _ => (hb i).const_smul _)
  filter_upwards [hv.eventually (Metric.ball_mem_nhds (V v) (by positivity : 0<ε/3))] with a ha
  have h1 := dist_triangle (U a x) (U a v) (V x)
  have h2 := dist_triangle (U a v) (V v) (V x)
  have h3 : dist (U a v) (V v)<ε/3 := ha
  rw [(U a).dist_map] at h1
  rw [V.dist_map] at h2
  rw [dist_comm v x] at hdist
  linarith
end HilbertBasis

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

theorem continuous_oneModeBeamCoefficient (k e a b : ℕ) :
    Continuous (fun η => oneModeBeamCoefficient η k e a b) := by
  unfold oneModeBeamCoefficient
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro p _hp
    apply continuous_finsetSum
    intro q _hq
    split_ifs <;> fun_prop
  · exact continuous_const

theorem continuous_beamCoefficient {n : ℕ} (k e a b : NumberIndex n) :
    Continuous (fun η => beamCoefficient η k e a b) := by
  exact continuous_finsetProd _ (fun j _ => continuous_oneModeBeamCoefficient _ _ _ _)

theorem tendsto_beamUnitary {n : ℕ} {A : Type*} {l : Filter A} {η : A → ℝ}
    (hη : ∀ a, η a∈Set.Icc 0 1) {θ : ℝ} (hθ : θ∈Set.Icc 0 1)
    (hlim : Tendsto η l (𝓝 θ)) (x : JointFock n) :
    Tendsto (fun a => beamUnitary (η a) (hη a) x) l (𝓝 (beamUnitary θ hθ x)) := by
  apply _root_.OAI.HilbertBasis.tendsto_isometries (jointSectorBasis n)
    (fun a => beamUnitary (η a) (hη a)) (beamUnitary θ hθ)
  rintro ⟨T,i⟩
  simp only [beamUnitary_apply_sector,BlockUnitary.rotated,← beam_sectorCoefficient]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((continuous_beamCoefficient _ _ _ _).continuousAt.tendsto.comp hlim)).smul_const _

theorem tendsto_beamOutput_parameter {n : ℕ} {A : Type*} {l : Filter A} {η : A → ℝ}
    (hη : ∀ a, η a∈Set.Icc 0 1) {θ : ℝ} (hθ : θ∈Set.Icc 0 1)
    (hlim : Tendsto η l (𝓝 θ)) (ρ σ : State n) :
    Tendsto (fun a => (beamOutput (η a) (hη a) ρ σ).op) l (𝓝 (beamOutput θ hθ ρ σ).op) := by
  apply TraceEnsemble.tendsto_operator
    (fun a => hasSum_slice_family (mixedVector_norm (η a) (hη a) ρ σ))
    (hasSum_slice_family (mixedVector_norm θ hθ ρ σ))
  intro bi
  exact (sliceCLM bi.1).continuous.tendsto _ |>.comp
    (tendsto_beamUnitary hη hθ hlim (tensor (rootColumn ρ bi.2.1) (rootColumn σ bi.2.2)))

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators Topology

open Set Filter ThermalMetric

@[simp] theorem g_zero : g 0 = 0 := by simp [g]

theorem continuous_g : Continuous g := by
  have h : g = fun t : ℝ => Real.negMulLog t - Real.negMulLog (t + 1) := by
    funext t
    simp only [g, Real.negMulLog_def]
    ring
  rw [h]
  exact Real.continuous_negMulLog.sub
    (Real.continuous_negMulLog.comp (continuous_id.add continuous_const))

theorem hasDerivAt_g {t : ℝ} (ht : 0 < t) :
    HasDerivAt g (Real.log (t + 1) - Real.log t) t := by
  have h₁ := Real.hasDerivAt_negMulLog (ne_of_gt ht)
  have h₂ := (Real.hasDerivAt_negMulLog (ne_of_gt (by linarith : 0 < t + 1))).comp t
    ((hasDerivAt_id t).add_const 1)
  convert! h₁.sub h₂ using 1
  · funext x
    simp only [g, Real.negMulLog_def, Pi.sub_apply, Function.comp_apply, id_eq]
    ring
  · ring

theorem strictMonoOn_g : StrictMonoOn g (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_g.continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_g hx).deriv]
  exact sub_pos.mpr (Real.strictMonoOn_log hx
    (show 0 < x + 1 by linarith) (show x < x + 1 by linarith))

theorem g_nonneg {t : ℝ} (ht : 0  ≤  t) : 0  ≤  g t := by
  simpa using strictMonoOn_g.monotoneOn (show 0 ∈ Ici (0 : ℝ) by simp) ht ht

theorem g_pos {t : ℝ} (ht : 0 < t) : 0 < g t := by
  simpa using strictMonoOn_g (show 0 ∈ Ici (0 : ℝ) by simp) (le_of_lt ht) ht

theorem gInv_g {t : ℝ} (ht : 0  ≤  t) : gInv (g t) = t := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (s := {u : ℝ | 0  ≤  u ∧ g t  ≤  g u})
  · exact ⟨t, ht, le_rfl⟩
  · intro u hu
    by_contra h
    have hlt := strictMonoOn_g hu.1 ht (lt_of_not_ge h)
    exact (not_lt_of_ge hu.2) hlt
  · intro w hw
    exact ⟨t, ⟨ht, le_rfl⟩, hw⟩

@[simp] theorem gInv_zero : gInv 0 = 0 := by simpa using gInv_g (t := 0) le_rfl

theorem h_antitone {a b : ℝ} (ha : 0<a) (hab : a ≤ b) : h b ≤ h a := by
  have hb := lt_of_lt_of_le ha hab
  unfold h
  rw [← Real.log_div (by linarith : b+1≠0) hb.ne',← Real.log_div (by linarith : a+1≠0) ha.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hb ha).mpr
  nlinarith

theorem g_ge_log {t : ℝ} (ht : 0<t) : Real.log (t+1) ≤ g t := by
  have hp := mul_nonneg ht.le (h_pos ht).le
  dsimp [g,h] at *
  nlinarith

theorem g_surjective_nonneg {s : ℝ} (hs : 0  ≤  s) : ∃ t : ℝ, 0 ≤ t ∧ g t=s := by
  have hb : s ≤ g (Real.exp s) := by
    calc
      s = Real.log (Real.exp s) := (Real.log_exp s).symm
      _  ≤  Real.log (Real.exp s+1) := Real.log_le_log (Real.exp_pos s) (by linarith)
      _  ≤  g (Real.exp s) := g_ge_log (Real.exp_pos s)
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (Real.exp_pos s).le continuous_g.continuousOn
    (show s∈Set.Icc (g 0) (g (Real.exp s)) from ⟨by simpa using hs,hb⟩)
  exact ⟨t,ht.1,he⟩

theorem gInv_nonneg {s : ℝ} (hs : 0  ≤  s) : 0 ≤ gInv s := by
  obtain ⟨t,ht,rfl⟩ := g_surjective_nonneg hs
  simpa only [gInv_g ht] using ht

theorem g_gInv {s : ℝ} (hs : 0  ≤  s) : g (gInv s)=s := by
  obtain ⟨t,ht,rfl⟩ := g_surjective_nonneg hs
  rw [gInv_g ht]

theorem le_gInv_iff {t s : ℝ} (ht : 0 ≤ t) (hs : 0  ≤  s) : t ≤ gInv s ↔ g t ≤ s := by
  have hh := strictMonoOn_g.le_iff_le ht (gInv_nonneg hs)
  rw [g_gInv hs] at hh
  exact hh.symm

end EntropyPhotonNumber

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric Filter

structure ThermalInterior where
  η : ℝ
  θ : ℝ
  d : ℝ
  r1 : ℝ
  r2 : ℝ
  hη : η ∈ Set.Ioo 0 1
  hθ : θ ∈ Set.Ioo 0 1
  hd : 0<d
  hr1 : 0<r1
  hr2 : 0<r2

namespace ThermalInterior
variable (T : ThermalInterior)
def a : ℝ := T.θ*(T.η*T.r1+(1-T.η)*T.r2)
def b : ℝ := T.a+T.θ
def r0 : ℝ := T.a+(1-T.θ)*T.d
theorem a_pos : 0<T.a := mul_pos T.hθ.1
  (add_pos (mul_pos T.hη.1 T.hr1) (mul_pos (sub_pos.mpr T.hη.2) T.hr2))
theorem b_pos : 0<T.b := add_pos T.a_pos T.hθ.1
theorem r0_pos : 0<T.r0 := add_pos T.a_pos (mul_pos (sub_pos.mpr T.hθ.2) T.hd)
def cap : ℝ := min ((1-T.θ)*T.d/T.a) ((1-T.θ)*(T.d+1)/T.b)
theorem cap_pos : 0<T.cap := lt_min
  (div_pos (mul_pos (sub_pos.mpr T.hθ.2) T.hd) T.a_pos)
  (div_pos (mul_pos (sub_pos.mpr T.hθ.2) (by linarith [T.hd])) T.b_pos)
def eps (m : ℕ) : ℝ := min T.cap (1/((m:ℝ)+1))
theorem eps_pos (m : ℕ) : 0<T.eps m := lt_min T.cap_pos (by positivity)
theorem eps_limit : Tendsto T.eps atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => min T.cap (1/((m:ℝ)+1))) atTop (𝓝 (0:ℝ))
  simpa only [min_eq_right T.cap_pos.le,eps] using
    (tendsto_const_nhds.min tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun m : ℕ => min T.cap (1/((m:ℝ)+1))) atTop (𝓝 (min T.cap 0)))
def kap (m : ℕ) : ℝ := min (1/((m:ℝ)+2))
  (T.eps m^2/(4*(T.eps m+2)*mixtureConstant T.r0^2))
theorem kap_pos (m : ℕ) : 0<T.kap m := by
  apply lt_min
  · positivity
  · exact div_pos (sq_pos_of_pos (T.eps_pos m)) (mul_pos
      (mul_pos (by norm_num) (by linarith [T.eps_pos m])) (sq_pos_of_pos (mixtureConstant_pos T.r0_pos)))
theorem kap_lt_one (m : ℕ) : T.kap m<1 := by
  apply (min_le_left _ _).trans_lt
  exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
theorem kap_limit : Tendsto T.kap atTop (𝓝 0) := by
  apply squeeze_zero (fun m => (T.kap_pos m).le) (fun _ => min_le_left _ _)
  have hh : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp := hh.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun m : ℕ => 1/(((m+1:ℕ):ℝ)+1)) atTop (𝓝 (0:ℝ)) at hcomp
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hcomp

def setup (m : ℕ) : ThermalSetup where
  η := T.η
  θ := T.θ
  κ := T.kap m
  ε := T.eps m
  d := T.d
  r1 := T.r1
  r2 := T.r2
  hη := T.hη
  hθ := T.hθ
  hκ := ⟨T.kap_pos m,T.kap_lt_one m⟩
  hε := T.eps_pos m
  hd := T.hd
  hr1 := T.hr1
  hr2 := T.hr2
  slack_r := by
    have hh := (min_le_left T.cap (1/((m:ℝ)+1))).trans
      (min_le_left ((1-T.θ)*T.d/T.a) ((1-T.θ)*(T.d+1)/T.b))
    have hm := (le_div_iff₀ T.a_pos).mp hh
    change T.eps m*T.a≤(1-T.θ)*T.d at hm
    dsimp [a] at hm
    nlinarith
  slack_s := by
    have hh := (min_le_left T.cap (1/((m:ℝ)+1))).trans
      (min_le_right ((1-T.θ)*T.d/T.a) ((1-T.θ)*(T.d+1)/T.b))
    have hm := (le_div_iff₀ T.b_pos).mp hh
    change T.eps m*T.b≤(1-T.θ)*(T.d+1) at hm
    dsimp [b,a] at hm
    nlinarith
  small_κ := min_le_right _ _

def raw {n : ℕ} (ρ σ : State n) : State n :=
  beamOutput T.θ ⟨T.hθ.1.le,T.hθ.2.le⟩
    (beamOutput T.η ⟨T.hη.1.le,T.hη.2.le⟩ ρ σ) (thermalState n T.d T.hd)

theorem out_limit {n : ℕ} (ρ σ : State n) :
    Tendsto (fun m => ((T.setup m).out ρ σ).op) atTop (𝓝 (T.raw ρ σ).op) := by
  have hc : Tendsto (fun m => (T.kap m : ℂ)) atTop (𝓝 0) := by
    simpa using T.kap_limit.ofReal
  have h1 := (hc.const_sub 1).smul_const (T.raw ρ σ).op
  have h2 := hc.zero_smul_const (thermalState n T.r0 T.r0_pos).op
  have hh := h1.add h2
  simpa only [sub_zero,one_smul,add_zero,
    ThermalSetup.out,ThermalSetup.output_op,setup,ThermalSetup.raw,ThermalSetup.middle,
    ThermalSetup.r0,raw,r0,a,Complex.ofReal_sub,Complex.ofReal_one,Function.comp_apply] using hh

theorem out_entropy_limit {n : ℕ} {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    Tendsto (fun m => entropy ((T.setup m).out ρ σ)) atTop (𝓝 (entropy (T.raw ρ σ))) := by
  let E := energy ρ+energy σ+energy (thermalState n T.d T.hd)+energy (thermalState n T.r0 T.r0_pos)
  apply tendsto_entropy (E:=E)
  · intro m
    exact regularizedOutput_finiteEnergy T.η (1-T.θ) (T.kap m)
      (T.setup m).η_mem (T.setup m).δ_mem (T.setup m).κ_mem
      (thermalState_finiteEnergy n T.d T.hd) (thermalState_finiteEnergy n T.r0 T.r0_pos) hρ hσ
  · exact beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ)
      (thermalState_finiteEnergy n T.d T.hd)
  · intro m
    exact regularizedOutput_energy_bound T.η (1-T.θ) (T.kap m)
      (T.setup m).η_mem (T.setup m).δ_mem (T.setup m).κ_mem
      (thermalState_finiteEnergy n T.d T.hd) (thermalState_finiteEnergy n T.r0 T.r0_pos) hρ hσ
  · have hh := beamOutput_energy_bound T.θ ⟨T.hθ.1.le,T.hθ.2.le⟩
      (beamOutput_finiteEnergy T.η ⟨T.hη.1.le,T.hη.2.le⟩ hρ hσ) (thermalState_finiteEnergy n T.d T.hd)
    have hi := beamOutput_energy_bound T.η ⟨T.hη.1.le,T.hη.2.le⟩ hρ hσ
    have hp := energy_nonneg (thermalState n T.r0 T.r0_pos)
    dsimp [E,raw]
    linarith
  · exact T.out_limit ρ σ

theorem entropy_tangent {n : ℕ} {ρ σ : State n} (hρ : FiniteMoment 4 ρ) (hσ : FiniteMoment 4 σ) :
    0≤(entropy (T.raw ρ σ)-n*g T.r0)/h T.r0-
      (T.θ*T.η)*(entropy ρ-n*g T.r1)/h T.r1-
      (T.θ*(1-T.η))*(entropy σ-n*g T.r2)/h T.r2 := by
  have ho := T.out_entropy_limit (finiteMoment_finiteEnergy (by decide : 1≤4) hρ)
    (finiteMoment_finiteEnergy (by decide : 1≤4) hσ)
  have hw1 := ((T.kap_limit.const_sub 1).mul_const T.θ).mul_const T.η
  have hw2 := ((T.kap_limit.const_sub 1).mul_const T.θ).mul_const (1-T.η)
  have he := (((ho.sub_const (n*g T.r0)).div_const (h T.r0)).sub
    ((hw1.mul_const (entropy ρ-n*g T.r1)).div_const (h T.r1))).sub
    ((hw2.mul_const (entropy σ-n*g T.r2)).div_const (h T.r2))
  have hp := T.eps_limit.mul
    (((hw1.div_const (h T.r1)).mul_const (thermalRelative T.r1 ρ)).add
      ((hw2.div_const (h T.r2)).mul_const (thermalRelative T.r2 σ)))
  have hh := he.add hp
  simp only [sub_zero,one_mul,zero_mul,add_zero] at hh
  apply ge_of_tendsto hh
  filter_upwards [] with m
  exact (T.setup m).base_nonnegative hρ hσ
end ThermalInterior
end

section
open QuantumTrace FischerBeam TensorLp MvPolynomial

theorem oneModeBeamCoefficient_one (k e a b : ℕ) :
    oneModeBeamCoefficient 1 k e a b=if k=a ∧ e=b then 1 else 0 := by
  classical
  rw [oneModeBeamCoefficient_eq]
  have hp : rotated 1 0 a b=monomial (degree a b) 1 := by
    simp only [rotated,creatorA,creatorB,one_smul,zero_smul,sub_zero,zero_add,
      X_pow_eq_monomial,monomial_mul_monomial,one_mul,degree]
  simp only [Real.sqrt_one,sub_self,Real.sqrt_zero,hp,coeff_monomial,degree_eq_iff,eq_comm (a := a) (b := k),eq_comm (a := b) (b := e)]
  split_ifs with hh
  · rcases hh with ⟨rfl,rfl⟩
    rw [div_self (Real.sqrt_ne_zero'.mpr (by simp [weight_degree]; positivity)),mul_one]
  · simp

theorem beamCoefficient_one {n : ℕ} (k e a b : NumberIndex n) :
    beamCoefficient 1 k e a b=if k=a ∧ e=b then 1 else 0 := by
  classical
  simp only [beamCoefficient,oneModeBeamCoefficient_one]
  by_cases hh : k=a ∧ e=b
  · rcases hh with ⟨rfl,rfl⟩; simp
  · rw [ite_eq_right hh]
    have hj : ∃ j, ¬ (k j=a j ∧ e j=b j) := by
      by_contra hn
      push Not at hn
      exact hh ⟨funext (fun j => (hn j).1),funext (fun j => (hn j).2)⟩
    obtain ⟨j,hj⟩ := hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem beamUnitary_one {n : ℕ} (h1 : (1:ℝ)∈Set.Icc 0 1) (x : JointFock n) :
    beamUnitary 1 h1 x=x := by
  have he : (beamUnitary (n:=n) 1 h1).toContinuousLinearEquiv.toContinuousLinearMap=ContinuousLinearMap.id ℂ (JointFock n) := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr (jointNumberBasis n).dense_span)
    rintro _ ⟨⟨a,b⟩,rfl⟩
    apply lp.ext
    funext ⟨k,e⟩
    simp only [jointNumberBasis_apply]
    change beamUnitary 1 h1 (lp.single 2 (a,b) 1 : JointFock n) (k,e)=
      (lp.single 2 (a,b) 1 : JointFock n) (k,e)
    simp only [beam_coordinate,beamCoefficient_one,lp.single_apply]
    split_ifs <;> simp_all [eq_comm]
  exact congrArg (fun A : JointFock n →L[ℂ] JointFock n => A x) he

theorem beamOutput_one {n : ℕ} (h1 : (1:ℝ)∈Set.Icc 0 1) (ρ σ : State n) :
    beamOutput 1 h1 ρ σ=ρ := by
  apply State.ext_op
  apply entry_ext
  intro k l
  have hv := (TraceEnsemble.hasSum_tensor_norm (rootColumn_norm ρ) (rootColumn_norm σ)).summable
  have hh := partialTrace_entry hv k l
  simp only [TraceEnsemble.tensor_entry (rootColumn_norm ρ).summable (rootColumn_norm σ).summable,
    rootColumn_operator] at hh
  have hs : HasSum (fun e => entry σ.op e e) (1:ℂ) := by
    convert! σ.trace_one.mapL Complex.ofRealCLM using 1
    funext e
    apply Complex.ext
    · rfl
    · exact (RCLike.nonneg_iff.mp (σ.positive.inner_nonneg_right (numberKet e))).2
  have ht := hs.mul_left (entry ρ.op k l)
  rw [mul_one] at ht
  have he := hh.unique ht
  change entry (partialTrace (mixedVector 1 h1 ρ σ)) k l=entry ρ.op k l
  have hm : mixedVector 1 h1 ρ σ=(fun ij => tensor (rootColumn ρ ij.1) (rootColumn σ ij.2)) := by
    funext ij
    exact beamUnitary_one h1 _
  rw [hm]
  exact he
end

section
open QuantumTrace ThermalMetric Filter

theorem continuousAt_h_pos {r : ℝ} (hr : 0<r) : ContinuousAt h r := by
  change ContinuousAt (fun x : ℝ => Real.log (x+1)-Real.log x) r
  have hs : ContinuousAt (fun x : ℝ => x+1) r := continuousAt_id.add continuousAt_const
  apply ContinuousAt.sub
  · exact hs.log (by linarith : r+1≠0)
  · exact Real.continuousAt_log hr.ne'

theorem tendsto_entropy_beamOutput_parameter {n : ℕ} {A : Type*} {l : Filter A} {η : A → ℝ}
    (hη : ∀ a, η a∈Set.Icc 0 1) {θ : ℝ} (hθ : θ∈Set.Icc 0 1)
    (hlim : Tendsto η l (𝓝 θ)) {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    Tendsto (fun a => entropy (beamOutput (η a) (hη a) ρ σ)) l
      (𝓝 (entropy (beamOutput θ hθ ρ σ))) := by
  exact tendsto_entropy (E:=energy ρ+energy σ)
    (fun a => beamOutput_finiteEnergy (η a) (hη a) hρ hσ)
    (beamOutput_finiteEnergy θ hθ hρ hσ)
    (fun a => beamOutput_energy_bound (η a) (hη a) hρ hσ)
    (beamOutput_energy_bound θ hθ hρ hσ)
    (tendsto_beamOutput_parameter hη hθ hlim ρ σ)

def interiorTransmission (m : ℕ) : ℝ := 1-1/((m:ℝ)+2)
theorem interiorTransmission_mem (m : ℕ) : interiorTransmission m∈Set.Ioo 0 1 := by
  have h1 : 0<1/((m:ℝ)+2) := by positivity
  have h2 : 1/((m:ℝ)+2)<1 := (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  exact ⟨sub_pos.mpr h2,sub_lt_self _ h1⟩
theorem interiorTransmission_limit : Tendsto interiorTransmission atTop (𝓝 1) := by
  have hh : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 (0:ℝ)) := by
    have hf : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := hf.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun m : ℕ => 1/(((m+1:ℕ):ℝ)+1)) atTop (𝓝 (0:ℝ)) at hc
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hc
  change Tendsto (fun m : ℕ => 1-1/((m:ℝ)+2)) atTop (𝓝 (1:ℝ))
  simpa only [sub_zero] using hh.const_sub 1

theorem entropy_tangent_beam {n : ℕ} {η r1 r2 : ℝ} (hη : η∈Set.Ioo 0 1)
    (hr1 : 0<r1) (hr2 : 0<r2) {ρ σ : State n} (hρ : FiniteMoment 4 ρ) (hσ : FiniteMoment 4 σ) :
    0≤(entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)-n*g (η*r1+(1-η)*r2))/h (η*r1+(1-η)*r2)-
      η*(entropy ρ-n*g r1)/h r1-(1-η)*(entropy σ-n*g r2)/h r2 := by
  let T : ℕ → ThermalInterior := fun m => {
    η := η, θ := interiorTransmission m, d := 1, r1 := r1, r2 := r2,
    hη := hη, hθ := interiorTransmission_mem m, hd := zero_lt_one, hr1 := hr1, hr2 := hr2 }
  have hEρ := finiteMoment_finiteEnergy (by decide : 1≤4) hρ
  have hEσ := finiteMoment_finiteEnergy (by decide : 1≤4) hσ
  have hl := tendsto_entropy_beamOutput_parameter
    (fun m => ⟨(interiorTransmission_mem m).1.le,(interiorTransmission_mem m).2.le⟩)
    (show (1:ℝ)∈Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩) interiorTransmission_limit
    (beamOutput_finiteEnergy η ⟨hη.1.le,hη.2.le⟩ hEρ hEσ) (thermalState_finiteEnergy n 1 zero_lt_one)
  rw [beamOutput_one] at hl
  have hr0 : 0<η*r1+(1-η)*r2 := add_pos (mul_pos hη.1 hr1) (mul_pos (sub_pos.mpr hη.2) hr2)
  have hrlim : Tendsto (fun m => (T m).r0) atTop (𝓝 (η*r1+(1-η)*r2)) := by
    have hh := (interiorTransmission_limit.mul_const (η*r1+(1-η)*r2)).add
      ((interiorTransmission_limit.const_sub 1).mul_const 1)
    simpa only [one_mul,sub_self,zero_mul,add_zero,T,ThermalInterior.r0,ThermalInterior.a] using hh
  have hg := continuous_g.continuousAt.tendsto.comp hrlim
  have hh := (continuousAt_h_pos hr0).tendsto.comp hrlim
  have hmain := ((hl.sub (hg.const_mul (n:ℝ))).div hh (h_pos hr0).ne').sub
    ((interiorTransmission_limit.mul_const η).mul_const (entropy ρ-n*g r1) |>.div_const (h r1))
  have hmain' := hmain.sub
    ((interiorTransmission_limit.mul_const (1-η)).mul_const (entropy σ-n*g r2) |>.div_const (h r2))
  simp only [one_mul] at hmain'
  apply ge_of_tendsto hmain'
  filter_upwards [] with m
  exact (T m).entropy_tangent hρ hσ
end

namespace NumberCutoff
open QuantumTrace Filter InnerProductSpace

variable {n : ℕ} (ρ : State n) (F : Finset (NumberIndex n))
def mass : ℝ := ∑ k ∈ F, (entry ρ.op k k).re
def projection : Fock n →L[ℂ] Fock n := basisProjection (numberBasis n) F
def compressed : Fock n →L[ℂ] Fock n := projection F ∘L ρ.op ∘L projection F
def vacuum : Fock n →L[ℂ] Fock n := rankOne ℂ (numberKet (0:NumberIndex n)) (numberKet 0)

theorem mass_le_one : mass ρ F≤1 := by
  apply (ρ.trace_one.summable.sum_le_tsum F (fun k _ => ρ.positive.re_inner_nonneg_right (numberKet k))).trans_eq
  exact ρ.trace_one.tsum_eq

theorem compressed_positive : (compressed ρ F).IsPositive := by
  have hh := ρ.positive.adjoint_conj (projection F)
  simpa only [compressed, projection,basisProjection_adjoint] using hh

theorem compressed_diagonal (k : NumberIndex n) :
    entry (compressed ρ F) k k=if k∈F then entry ρ.op k k else 0 := by
  classical
  unfold entry compressed
  rw [← numberBasis_apply n k]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left,projection,basisProjection_adjoint,
    basisProjection_apply_basis]
  split_ifs <;> simp

theorem vacuum_diagonal (k : NumberIndex n) : entry (vacuum (n:=n)) k k=if k=0 then 1 else 0 := by
  classical
  simp only [vacuum,entry,rankOne_apply,inner_smul_right,← numberBasis_apply,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal]
  split_ifs <;> simp_all

def state : State n where
  op := compressed ρ F+((1-mass ρ F:ℝ):ℂ) • vacuum
  positive := (compressed_positive ρ F).add
    ((isPositive_rankOne_self (numberKet (0:NumberIndex n))).smul_of_nonneg
      (by exact_mod_cast sub_nonneg.mpr (mass_le_one ρ F)))
  trace_one := by
    classical
    have h1 : HasSum (fun k => if k∈F then (entry ρ.op k k).re else 0) (mass ρ F) := by
      simpa only [mass, Finset.sum_ite_mem, Finset.inter_self] using
        (hasSum_sum_of_ne_finset_zero (s:=F) (f:=fun k => if k∈F then (entry ρ.op k k).re else 0)
          (by intro k hk; simp only [ite_eq_right hk]))
    have h2 : HasSum (fun k : NumberIndex n => if k=0 then 1-mass ρ F else 0) (1-mass ρ F) :=
      hasSum_ite_eq 0 _
    convert! h1.add h2 using 1
    · funext k
      simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
      change (entry (compressed ρ F) k k+((1-mass ρ F:ℝ):ℂ)*entry vacuum k k).re=_
      rw [compressed_diagonal,vacuum_diagonal]
      split_ifs <;> simp [entry]
    · ring

theorem diagonal (k : NumberIndex n) :
    (entry (state ρ F).op k k).re=
      (if k∈F then (entry ρ.op k k).re else 0)+(if k=0 then 1-mass ρ F else 0) := by
  classical
  change (entry (compressed ρ F+((1-mass ρ F:ℝ):ℂ) • vacuum) k k).re=_
  simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  change (entry (compressed ρ F) k k+((1-mass ρ F:ℝ):ℂ)*entry vacuum k k).re=_
  rw [compressed_diagonal,vacuum_diagonal]
  split_ifs <;> simp [entry]

theorem finiteMoment (m : ℕ) : FiniteMoment m (state ρ F) := by
  classical
  apply summable_of_ne_finset_zero (s:=insert 0 F)
  intro k hk
  have hF : k∉F := fun h => hk (Finset.mem_insert_of_mem h)
  have h0 : k≠0 := by intro h; subst k; exact hk (Finset.mem_insert_self 0 F)
  rw [diagonal,ite_eq_right hF,ite_eq_right h0]
  simp

theorem energy_le (hρ : FiniteEnergy ρ) : energy (state ρ F)≤energy ρ := by
  classical
  have he (k : NumberIndex n) : (totalNumber k:ℝ)*(entry (state ρ F).op k k).re=
      if k∈F then (totalNumber k:ℝ)*(entry ρ.op k k).re else 0 := by
    rw [diagonal]
    by_cases h0 : k=0
    · subst k; simp [totalNumber]
    · rw [ite_eq_right h0,add_zero]; split_ifs <;> simp [entry]
  unfold energy
  simp only [he]
  have hs : HasSum (fun k => if k∈F then (totalNumber k:ℝ)*(entry ρ.op k k).re else 0)
      (∑ k∈F, (totalNumber k:ℝ)*(entry ρ.op k k).re) := by
    simpa only [Finset.sum_ite_mem, Finset.inter_self] using
      (hasSum_sum_of_ne_finset_zero (s:=F)
        (f:=fun k => if k∈F then (totalNumber k:ℝ)*(entry ρ.op k k).re else 0)
        (by intro k hk; simp only [ite_eq_right hk]))
  rw [hs.tsum_eq]
  exact hρ.sum_le_tsum F (fun k _ => mul_nonneg (Nat.cast_nonneg _)
    (ρ.positive.re_inner_nonneg_right (numberKet k)))

theorem limit : Tendsto (fun F : Finset (NumberIndex n) => (state ρ F).op) atTop (𝓝 ρ.op) := by
  have hm : Tendsto (mass ρ) atTop (𝓝 1) := ρ.trace_one
  have hc : Tendsto (compressed ρ) atTop (𝓝 ρ.op) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun F => (norm_sub_rev _ _).le.trans (double_compression_norm_le (numberBasis n) ρ.positive
        (trace_one_numberBasis ρ) F))
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp (hm.const_sub 1)).const_mul 2
    simpa only [sub_self,Real.sqrt_zero,mul_zero,numberBasis_apply,entry,projection,compressed,mass,Function.comp_apply] using hh
  have hr : Tendsto (fun F => ((1 - mass ρ F : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using (hm.const_sub 1).ofReal
  have hh := hc.add (hr.zero_smul_const (vacuum (n:=n)))
  simpa only [add_zero,state] using hh
end NumberCutoff

open QuantumTrace ThermalMetric Filter

theorem entropy_tangent_finiteEnergy {n : ℕ} {η r1 r2 : ℝ} (hη : η∈Set.Ioo 0 1)
    (hr1 : 0<r1) (hr2 : 0<r2) {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    0≤(entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)-n*g (η*r1+(1-η)*r2))/h (η*r1+(1-η)*r2)-
      η*(entropy ρ-n*g r1)/h r1-(1-η)*(entropy σ-n*g r2)/h r2 := by
  let ρm := NumberCutoff.state ρ
  let σm := NumberCutoff.state σ
  have hρm (F : Finset (NumberIndex n)) : FiniteEnergy (ρm F) :=
    finiteMoment_finiteEnergy (by decide : 1≤4) (NumberCutoff.finiteMoment ρ F 4)
  have hσm (F : Finset (NumberIndex n)) : FiniteEnergy (σm F) :=
    finiteMoment_finiteEnergy (by decide : 1≤4) (NumberCutoff.finiteMoment σ F 4)
  have hρlim := tendsto_entropy hρm hρ (fun F => NumberCutoff.energy_le ρ F hρ) le_rfl (NumberCutoff.limit ρ)
  have hσlim := tendsto_entropy hσm hσ (fun F => NumberCutoff.energy_le σ F hσ) le_rfl (NumberCutoff.limit σ)
  have hclim := tendsto_entropy (E:=energy ρ+energy σ)
    (fun F => beamOutput_finiteEnergy η ⟨hη.1.le,hη.2.le⟩ (hρm F) (hσm F))
    (beamOutput_finiteEnergy η ⟨hη.1.le,hη.2.le⟩ hρ hσ)
    (fun F => (beamOutput_energy_bound η ⟨hη.1.le,hη.2.le⟩ (hρm F) (hσm F)).trans
      (add_le_add (NumberCutoff.energy_le ρ F hρ) (NumberCutoff.energy_le σ F hσ)))
    (beamOutput_energy_bound η ⟨hη.1.le,hη.2.le⟩ hρ hσ)
    (tendsto_beamOutput η ⟨hη.1.le,hη.2.le⟩ (NumberCutoff.limit ρ) (NumberCutoff.limit σ))
  have hl := (((hclim.sub_const ((n:ℝ)*g (η*r1+(1-η)*r2))).div_const (h (η*r1+(1-η)*r2))).sub
    (((hρlim.sub_const ((n:ℝ)*g r1)).const_mul η).div_const (h r1)))
  have hl' := hl.sub (((hσlim.sub_const ((n:ℝ)*g r2)).const_mul (1-η)).div_const (h r2))
  apply ge_of_tendsto hl'
  filter_upwards [] with F
  exact entropy_tangent_beam hη hr1 hr2 (NumberCutoff.finiteMoment ρ F 4) (NumberCutoff.finiteMoment σ F 4)

def positiveReference (a : ℝ) (m : ℕ) : ℝ := a+1/((m:ℝ)+1)
theorem positiveReference_pos {a : ℝ} (ha : 0≤a) (m : ℕ) : 0<positiveReference a m := by
  unfold positiveReference
  positivity
theorem positiveReference_le {a : ℝ} (_ha : 0≤a) (m : ℕ) : positiveReference a m≤a+1 := by
  unfold positiveReference
  have hm : 0<(m:ℝ)+1 := by positivity
  have hdiv : 1/((m:ℝ)+1)≤1 := (div_le_one hm).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  linarith [hdiv]
theorem positiveReference_limit (a : ℝ) : Tendsto (positiveReference a) atTop (𝓝 a) := by
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ))).const_add a
  change Tendsto (fun m : ℕ => a+1/((m:ℝ)+1)) atTop (𝓝 a)
  simpa only [add_zero] using hh

theorem reference_error_limit {a : ℝ} (ha : 0≤a) :
    Tendsto (fun m => (g a-g (positiveReference a m))/h (positiveReference a m)) atTop (𝓝 0) := by
  have hc : 0<h (a+1) := h_pos (by linarith)
  have hnum := (continuous_g.continuousAt.tendsto.comp (positiveReference_limit a)).const_sub (g a)
  have hbound := (hnum.norm.div_const (h (a+1)))
  have hnorm : Tendsto (fun m => ‖(g a-g (positiveReference a m))/h (positiveReference a m)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun m => ?_) (by simpa only [sub_self,norm_zero,zero_div] using hbound)
    rw [norm_div,Real.norm_eq_abs (h (positiveReference a m)),abs_of_pos (h_pos (positiveReference_pos ha m))]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hc
      (h_antitone (positiveReference_pos ha m) (positiveReference_le ha m))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hnorm

theorem epni_entropy_interior {n : ℕ} (hn : 1≤n) {η : ℝ} (hη : η∈Set.Ioo 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    g (η*gInv (entropy ρ/n)+(1-η)*gInv (entropy σ/n)) ≤
      entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)/n := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let a := gInv (entropy ρ/n)
  let b := gInv (entropy σ/n)
  have ha : 0≤a := gInv_nonneg (div_nonneg (entropy_nonneg ρ) hnR.le)
  have hb : 0≤b := gInv_nonneg (div_nonneg (entropy_nonneg σ) hnR.le)
  have hga : g a=entropy ρ/n := g_gInv (div_nonneg (entropy_nonneg ρ) hnR.le)
  have hgb : g b=entropy σ/n := g_gInv (div_nonneg (entropy_nonneg σ) hnR.le)
  have hρeq : entropy ρ=(n:ℝ)*g a := by rw [hga]; field_simp
  have hσeq : entropy σ=(n:ℝ)*g b := by rw [hgb]; field_simp
  have hc0 : 0≤η*a+(1-η)*b := add_nonneg (mul_nonneg hη.1.le ha) (mul_nonneg (sub_nonneg.mpr hη.2.le) hb)
  rcases eq_or_lt_of_le hc0 with hzero | hpos
  · rw [← hzero,g_zero]
    exact div_nonneg (entropy_nonneg _) hnR.le
  have hrlim := ((positiveReference_limit a).const_mul η).add
    ((positiveReference_limit b).const_mul (1-η))
  have hg := continuous_g.continuousAt.tendsto.comp hrlim
  have hh := (continuousAt_h_pos hpos).tendsto.comp hrlim
  have heρ := (reference_error_limit ha).const_mul ((n:ℝ)*η)
  have heσ := (reference_error_limit hb).const_mul ((n:ℝ)*(1-η))
  have hout := ((hg.const_mul (n:ℝ)).const_sub
    (entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ))).div hh (h_pos hpos).ne'
  have hmain := (hout.sub heρ).sub heσ
  simp only [mul_zero,sub_zero] at hmain
  have hnonneg : 0≤(entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)-(n:ℝ)*g (η*a+(1-η)*b))/h (η*a+(1-η)*b) := by
    apply ge_of_tendsto hmain
    filter_upwards [] with m
    have ht := entropy_tangent_finiteEnergy hη (positiveReference_pos ha m) (positiveReference_pos hb m) hρ hσ
    rw [hρeq,hσeq] at ht
    convert! ht using 1
    dsimp only [Pi.div_apply,Function.comp_apply]
    ring
  have ht := (le_div_iff₀ (h_pos hpos)).mp hnonneg
  change g (η*a+(1-η)*b)≤_
  exact (le_div_iff₀ hnR).mpr (by nlinarith)

theorem epni_entropy_closed {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : η∈Set.Icc 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    g (η*gInv (entropy ρ/n)+(1-η)*gInv (entropy σ/n))  ≤ 
      entropy (beamOutput η hη ρ σ)/n := by
  let ηm : ℕ → ℝ := fun m => interiorTransmission m*η+(1-interiorTransmission m)/2
  have hηm (m : ℕ) : ηm m∈Set.Ioo 0 1 := by
    have ht := interiorTransmission_mem m
    have hp := mul_nonneg ht.1.le hη.1
    have hu : interiorTransmission m*η ≤ interiorTransmission m :=
      mul_le_of_le_one_right ht.1.le hη.2
    dsimp [ηm]
    constructor <;> linarith [ht.1,ht.2]
  have hlim : Tendsto ηm atTop (𝓝 η) := by
    have hh := (interiorTransmission_limit.mul_const η).add
      ((interiorTransmission_limit.const_sub 1).div_const 2)
    simpa only [one_mul,sub_self,zero_div,add_zero,ηm] using hh
  have hout := (tendsto_entropy_beamOutput_parameter
    (fun m => ⟨(hηm m).1.le,(hηm m).2.le⟩) hη hlim hρ hσ).div_const (n:ℝ)
  have harg := (hlim.mul_const (gInv (entropy ρ/n))).add
    ((hlim.const_sub 1).mul_const (gInv (entropy σ/n)))
  have hg := continuous_g.continuousAt.tendsto.comp harg
  exact le_of_tendsto_of_tendsto hg hout (Eventually.of_forall (fun m => epni_entropy_interior hn (hηm m) hρ hσ))

theorem entropy_photon_number_inequality
    (n : ℕ) (hn : 1 ≤ n) (ρA ρB ρC : State n)
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hC : IsBeamSplitterOutput η ρA ρB ρC) :
    η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n) ≤
      gInv (entropy ρC / n) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha := gInv_nonneg (div_nonneg (entropy_nonneg ρA) hnR.le)
  have hb := gInv_nonneg (div_nonneg (entropy_nonneg ρB) hnR.le)
  have hw := add_nonneg (mul_nonneg hη.1 ha) (mul_nonneg (sub_nonneg.mpr hη.2) hb)
  apply (le_gInv_iff hw (div_nonneg (entropy_nonneg ρC) hnR.le)).mpr
  rw [output_eq hη hC]
  exact epni_entropy_closed hn hη hA hB
end EntropyPhotonNumber

end

end OAI
