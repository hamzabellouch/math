import Mathlib
import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EnergyLp, Markov, VariationalLaplacian. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
section EnergyLp
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

 
noncomputable def energyLp (f : Lp ℝ 2 μ) : ℝ≥0∞ := cheegerEnergy μ f

@[simp] theorem energyLp_zero : energyLp μ 0 = 0 := by
  change cheegerEnergy μ (⇑(0 : Lp ℝ 2 μ)) = 0
  rw [cheegerEnergy_congr_ae μ (Lp.coeFn_zero ℝ 2 μ)]
  exact cheegerEnergy_zero μ

theorem energyLp_smul (c : ℝ) (f : Lp ℝ 2 μ) :
    energyLp μ (c • f) = (ENNReal.ofReal |c|) ^ 2 * energyLp μ f := by
  change cheegerEnergy μ (⇑(c • f)) = _
  rw [cheegerEnergy_congr_ae μ (Lp.coeFn_smul c f)]
  exact cheegerEnergy_const_mul μ c f

theorem energyLp_parallelogram (hQ : QuadraticCheegerEnergy μ) (f g : Lp ℝ 2 μ) :
    energyLp μ (f + g) + energyLp μ (f - g) = 2 * (energyLp μ f + energyLp μ g) := by
  unfold energyLp
  rw [cheegerEnergy_congr_ae μ (Lp.coeFn_add f g),
    cheegerEnergy_congr_ae μ (Lp.coeFn_sub f g)]
  exact hQ f g (Lp.memLp f) (Lp.memLp g)

 

noncomputable def finiteEnergy (hQ : QuadraticCheegerEnergy μ) : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | energyLp μ f ≠ ∞}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    have h := energyLp_parallelogram μ hQ f g
    have ht : 2 * (energyLp μ f + energyLp μ g) ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
    rw [← h] at ht
    exact (ENNReal.add_ne_top.mp ht).1
  smul_mem' := by
    intro c f hf
    change energyLp μ (c • f) ≠ ∞
    rw [energyLp_smul]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hf

 
def SobolevSpace (hQ : QuadraticCheegerEnergy μ) : Type u := ↥(finiteEnergy μ hQ)

noncomputable instance (hQ : QuadraticCheegerEnergy μ) : AddCommGroup (SobolevSpace μ hQ) :=
  inferInstanceAs (AddCommGroup ↥(finiteEnergy μ hQ))
noncomputable instance (hQ : QuadraticCheegerEnergy μ) : Module ℝ (SobolevSpace μ hQ) :=
  inferInstanceAs (Module ℝ ↥(finiteEnergy μ hQ))

variable (hQ : QuadraticCheegerEnergy μ)

 
noncomputable def SobolevSpace.toLp : SobolevSpace μ hQ →ₗ[ℝ] Lp ℝ 2 μ := (finiteEnergy μ hQ).subtype

noncomputable def SobolevSpace.energy (f : SobolevSpace μ hQ) : ℝ :=
  (energyLp μ (SobolevSpace.toLp μ hQ f)).toReal

theorem SobolevSpace.energy_nonneg (f : SobolevSpace μ hQ) :
    0 ≤ SobolevSpace.energy μ hQ f := ENNReal.toReal_nonneg

@[simp] theorem SobolevSpace.energy_zero : SobolevSpace.energy μ hQ 0 = 0 := by
  simp [SobolevSpace.energy]

theorem SobolevSpace.energy_smul (c : ℝ) (f : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (c • f) = c ^ 2 * SobolevSpace.energy μ hQ f := by
  simp only [SobolevSpace.energy, map_smul, energyLp_smul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg c), sq_abs]

theorem SobolevSpace.energy_parallelogram (f g : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (f + g) + SobolevSpace.energy μ hQ (f - g) =
      2 * (SobolevSpace.energy μ hQ f + SobolevSpace.energy μ hQ g) := by
  have he := congrArg ENNReal.toReal (energyLp_parallelogram μ hQ
    (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g))
  have hf : energyLp μ (SobolevSpace.toLp μ hQ f) ≠ ∞ := f.property
  have hg : energyLp μ (SobolevSpace.toLp μ hQ g) ≠ ∞ := g.property
  have hfg : energyLp μ (SobolevSpace.toLp μ hQ (f + g)) ≠ ∞ := (f + g).property
  have hfm : energyLp μ (SobolevSpace.toLp μ hQ (f - g)) ≠ ∞ := (f - g).property
  rw [← map_add, ← map_sub] at he
  simpa only [ENNReal.toReal_add hfg hfm, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hf hg, SobolevSpace.energy] using he

 
noncomputable def SobolevSpace.normSq (f : SobolevSpace μ hQ) : ℝ :=
  ‖SobolevSpace.toLp μ hQ f‖ ^ 2 + 2 * SobolevSpace.energy μ hQ f

theorem SobolevSpace.normSq_nonneg (f : SobolevSpace μ hQ) :
    0 ≤ SobolevSpace.normSq μ hQ f :=
  add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ f))

@[simp] theorem SobolevSpace.normSq_zero : SobolevSpace.normSq μ hQ 0 = 0 := by
  simp [SobolevSpace.normSq]

theorem SobolevSpace.normSq_smul (c : ℝ) (f : SobolevSpace μ hQ) :
    SobolevSpace.normSq μ hQ (c • f) = c ^ 2 * SobolevSpace.normSq μ hQ f := by
  simp only [SobolevSpace.normSq, map_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, SobolevSpace.energy_smul]
  ring

theorem SobolevSpace.normSq_parallelogram (f g : SobolevSpace μ hQ) :
    SobolevSpace.normSq μ hQ (f + g) + SobolevSpace.normSq μ hQ (f - g) =
      2 * (SobolevSpace.normSq μ hQ f + SobolevSpace.normSq μ hQ g) := by
  have h1 := parallelogram_law_with_norm ℝ
    (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)
  have h2 := SobolevSpace.energy_parallelogram μ hQ f g
  simp only [SobolevSpace.normSq, map_add, map_sub]
  linarith

theorem SobolevSpace.normSq_eq_zero {f : SobolevSpace μ hQ}
    (hf : SobolevSpace.normSq μ hQ f = 0) : f = 0 := by
  have hn := SobolevSpace.energy_nonneg μ hQ f
  have hl : ‖SobolevSpace.toLp μ hQ f‖ = 0 := by
    unfold SobolevSpace.normSq at hf
    nlinarith [sq_nonneg ‖SobolevSpace.toLp μ hQ f‖]
  apply Subtype.ext
  exact norm_eq_zero.mp hl

@[instance_reducible]
noncomputable def SobolevSpace.innerCore : InnerProductSpace.Core ℝ (SobolevSpace μ hQ) where
  __ := EnergyPolarization.preInner (SobolevSpace.normSq μ hQ)
    (SobolevSpace.normSq_zero μ hQ) (SobolevSpace.normSq_nonneg μ hQ)
    (SobolevSpace.normSq_smul μ hQ) (SobolevSpace.normSq_parallelogram μ hQ)
  definite := by
    intro f hf
    apply SobolevSpace.normSq_eq_zero μ hQ
    exact (EnergyPolarization.bracket_self (SobolevSpace.normSq μ hQ)
      (SobolevSpace.normSq_zero μ hQ) (SobolevSpace.normSq_smul μ hQ) f).symm.trans hf

noncomputable instance : NormedAddCommGroup (SobolevSpace μ hQ) :=
  (SobolevSpace.innerCore μ hQ).toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℝ (SobolevSpace μ hQ) :=
  letI : InnerProductSpace.Core ℝ (SobolevSpace μ hQ) := SobolevSpace.innerCore μ hQ
  InnerProductSpace.ofCore inferInstance

 theorem energyLp_le_liminf {f : Lp ℝ 2 μ} {fs : ℕ → Lp ℝ 2 μ}
    (hconv : Tendsto fs atTop (𝓝 f)) :
    energyLp μ f ≤ liminf (fun i => energyLp μ (fs i)) atTop := by
  apply cheegerEnergy_le_liminf_of_L2 μ (Lp.memLp f) (fun i => Lp.memLp (fs i))
  have h := hconv.edist (tendsto_const_nhds (x := f))
  simp only [edist_self, Lp.edist_def] at h
  exact h

 theorem SobolevSpace.norm_sq (f : SobolevSpace μ hQ) :
    ‖f‖ ^ 2 = SobolevSpace.normSq μ hQ f := by
  rw [@norm_sq_eq_re_inner ℝ]
  exact EnergyPolarization.bracket_self (SobolevSpace.normSq μ hQ)
    (SobolevSpace.normSq_zero μ hQ) (SobolevSpace.normSq_smul μ hQ) f

 theorem SobolevSpace.norm_toLp_le (f : SobolevSpace μ hQ) :
    ‖SobolevSpace.toLp μ hQ f‖ ≤ ‖f‖ := by
  have h := SobolevSpace.norm_sq μ hQ f
  have hn := SobolevSpace.energy_nonneg μ hQ f
  unfold SobolevSpace.normSq at h
  nlinarith [norm_nonneg f, norm_nonneg (SobolevSpace.toLp μ hQ f)]

 noncomputable def SobolevSpace.toLpCLM : SobolevSpace μ hQ →L[ℝ] Lp ℝ 2 μ :=
    (SobolevSpace.toLp μ hQ).mkContinuous 1 (by
      intro f
      simpa using SobolevSpace.norm_toLp_le μ hQ f)

 theorem SobolevSpace.two_energy_le_norm_sq (f : SobolevSpace μ hQ) :
    2 * SobolevSpace.energy μ hQ f ≤ ‖f‖ ^ 2 := by
  rw [SobolevSpace.norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

 theorem SobolevSpace.energyLp_le_of_norm_le {f : SobolevSpace μ hQ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ‖f‖ ≤ C) :
    energyLp μ (SobolevSpace.toLp μ hQ f) ≤ ENNReal.ofReal (C ^ 2 / 2) := by
  have he := SobolevSpace.two_energy_le_norm_sq μ hQ f
  have he' : SobolevSpace.energy μ hQ f ≤ C ^ 2 / 2 := by
    nlinarith [norm_nonneg f]
  rw [← ENNReal.ofReal_toReal (show energyLp μ (SobolevSpace.toLp μ hQ f) ≠ ∞ from f.property)]
  exact ENNReal.ofReal_le_ofReal he'

 theorem SobolevSpace.energyLp_le_of_tendsto_of_norm_bdd
    {us : ℕ → SobolevSpace μ hQ} {f : Lp ℝ 2 μ} {C : ℝ} (hC : 0 ≤ C)
    (hf : Tendsto (fun i => SobolevSpace.toLp μ hQ (us i)) atTop (𝓝 f))
    (hu : ∀ᶠ i in atTop, ‖us i‖ ≤ C) :
    energyLp μ f ≤ ENNReal.ofReal (C ^ 2 / 2) := by
  apply (energyLp_le_liminf μ hf).trans
  apply liminf_le_of_frequently_le'
  exact (hu.mono fun i hi => SobolevSpace.energyLp_le_of_norm_le μ hQ hC hi).frequently

 

noncomputable instance : CompleteSpace (SobolevSpace μ hQ) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro us hu
  have hLpC : CauchySeq (fun i => SobolevSpace.toLp μ hQ (us i)) :=
    (SobolevSpace.toLpCLM μ hQ).uniformContinuous.comp_cauchySeq hu
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hLpC
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hu 1 zero_lt_one
  have hbound : ∀ᶠ i in atTop, ‖us i‖ ≤ ‖us N‖ + 1 := by
    filter_upwards [eventually_ge_atTop N] with i hi
    have hd := hN i hi
    have hn := norm_sub_norm_le (us i) (us N)
    rw [dist_eq_norm] at hd
    linarith
  have he := SobolevSpace.energyLp_le_of_tendsto_of_norm_bdd μ hQ
    (by positivity : 0 ≤ ‖us N‖ + 1) hf hbound
  have hfin : energyLp μ f ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top he
  let g : SobolevSpace μ hQ := ⟨f, hfin⟩
  refine ⟨g, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨M, fun i hi => ?_⟩
  have hdiff : Tendsto (fun j => SobolevSpace.toLp μ hQ (us i - us j)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ (us i - g))) := by
    have ht := (tendsto_const_nhds (x := SobolevSpace.toLp μ hQ (us i))).sub hf
    convert ht using 1 <;> rfl
  have hdbound : ∀ᶠ j in atTop, ‖us i - us j‖ ≤ ε / 2 := by
    filter_upwards [eventually_ge_atTop M] with j hj
    exact (show ‖us i - us j‖ < ε / 2 by simpa only [dist_eq_norm] using hM i hi j hj).le
  have hediff := SobolevSpace.energyLp_le_of_tendsto_of_norm_bdd μ hQ
    (half_pos hε).le hdiff hdbound
  have hE : SobolevSpace.energy μ hQ (us i - g) ≤ (ε / 2) ^ 2 / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hediff
  have hL : ‖SobolevSpace.toLp μ hQ (us i - g)‖ ≤ ε / 2 := by
    apply le_of_tendsto hdiff.norm
    filter_upwards [hdbound] with j hj
    exact (SobolevSpace.norm_toLp_le μ hQ (us i - us j)).trans hj
  have hs := SobolevSpace.norm_sq μ hQ (us i - g)
  unfold SobolevSpace.normSq at hs
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (SobolevSpace.toLp μ hQ (us i - g)), norm_nonneg (us i - g)]

end EnergyLp

section Markov
variable {X : Type u} [MetricSpace X]

 theorem localSlope_comp_le {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (f : X → ℝ) (x : X) :
    localSlope (φ ∘ f) x ≤ localSlope f x := by
  unfold localSlope
  apply iInf_mono fun r => iInf_mono fun _ => ?_
  apply iSup_mono fun y => iSup_mono fun _ => iSup_mono fun _ => ?_
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ dist_nonneg
  simpa only [Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul] using
    hφ.dist_le_mul (f y) (f x)

variable [MeasurableSpace X] (μ : Measure X)

 theorem slopeEnergy_comp_le {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (f : X → ℝ) :
    slopeEnergy μ (φ ∘ f) ≤ slopeEnergy μ f := by
  exact mul_le_mul' le_rfl (lintegral_mono fun x =>
    pow_le_pow_left' (localSlope_comp_le hφ f x) 2)

 theorem IsLipschitzApproximation.memLp
    {f : X → ℝ} {fs : ℕ → X → ℝ} (hfs : IsLipschitzApproximation μ f fs) :
    MemLp f 2 μ := by
  obtain ⟨index, hindex⟩ := (hfs.2.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  have hdiff : MemLp (fun x => fs index x - f x) 2 μ := hindex
  simpa only [Pi.sub_def, sub_sub_cancel] using (hfs.1 index).1.sub hdiff

 theorem IsLipschitzApproximation.comp_contraction {φ : ℝ → ℝ}
    (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0)
    {f : X → ℝ} {fs : ℕ → X → ℝ} (hfs : IsLipschitzApproximation μ f fs) :
    IsLipschitzApproximation μ (φ ∘ f) (fun i => φ ∘ fs i) := by
  constructor
  · intro i
    obtain ⟨hm, C, hC⟩ := hfs.1 i
    exact ⟨hφ.comp_memLp hφ0 hm, C, by simpa using hφ.comp hC⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfs.2 (fun _ => bot_le)
    intro i
    apply eLpNorm_mono ((hφ.comp_memLp hφ0 (hfs.1 i).1).aestronglyMeasurable.sub
      (hφ.comp_memLp hφ0 (hfs.memLp μ)).aestronglyMeasurable)
    intro x
    simpa only [Pi.sub_apply, Function.comp_apply, ← dist_eq_norm, NNReal.coe_one, one_mul] using
      hφ.dist_le_mul (fs i x) (f x)

 
 theorem cheegerEnergy_comp_contraction {φ : ℝ → ℝ}
    (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0) (f : X → ℝ) :
    cheegerEnergy μ (φ ∘ f) ≤ cheegerEnergy μ f := by
  unfold cheegerEnergy
  apply le_iInf fun fs => le_iInf fun hfs => ?_
  apply iInf_le_of_le (fun i => φ ∘ fs i)
  apply iInf_le_of_le (hfs.comp_contraction μ hφ hφ0)
  exact liminf_le_liminf (Eventually.of_forall fun i => slopeEnergy_comp_le μ hφ (fs i))

end Markov

section VariationalLaplacian
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)
variable (hQ : QuadraticCheegerEnergy μ)

 
noncomputable def energyForm (f g : SobolevSpace μ hQ) : ℝ :=
  inner ℝ f g - inner ℝ (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)

 theorem energyForm_self (f : SobolevSpace μ hQ) :
    energyForm μ hQ f f = 2 * SobolevSpace.energy μ hQ f := by
  simp only [energyForm, real_inner_self_eq_norm_sq, SobolevSpace.norm_sq,
    SobolevSpace.normSq]
  ring

 theorem energyForm_add_left (f g h : SobolevSpace μ hQ) :
    energyForm μ hQ (f + g) h = energyForm μ hQ f h + energyForm μ hQ g h := by
  simp only [energyForm, map_add, inner_add_left]
  ring

 theorem energyForm_smul_left (c : ℝ) (f g : SobolevSpace μ hQ) :
    energyForm μ hQ (c • f) g = c * energyForm μ hQ f g := by
  simp only [energyForm, map_smul, real_inner_smul_left]
  ring

 theorem energyForm_comm (f g : SobolevSpace μ hQ) :
    energyForm μ hQ f g = energyForm μ hQ g f := by
  simp only [energyForm, real_inner_comm f g,
    real_inner_comm (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]

 
def IsWeakLaplacian (f : SobolevSpace μ hQ) (g : Lp ℝ 2 μ) : Prop :=
  ∀ φ : SobolevSpace μ hQ, energyForm μ hQ f φ = -inner ℝ g (SobolevSpace.toLp μ hQ φ)

 

noncomputable def SobolevSpace.resolvent : Lp ℝ 2 μ →L[ℝ] SobolevSpace μ hQ :=
  (SobolevSpace.toLpCLM μ hQ).adjoint

 theorem SobolevSpace.resolvent_inner (f : Lp ℝ 2 μ) (φ : SobolevSpace μ hQ) :
    inner ℝ (SobolevSpace.resolvent μ hQ f) φ = inner ℝ f (SobolevSpace.toLp μ hQ φ) :=
  ContinuousLinearMap.adjoint_inner_left (SobolevSpace.toLpCLM μ hQ) φ f

 theorem SobolevSpace.resolvent_weak_laplacian (f : Lp ℝ 2 μ) :
    IsWeakLaplacian μ hQ (SobolevSpace.resolvent μ hQ f)
      (SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f) - f) := by
  intro φ
  rw [energyForm, SobolevSpace.resolvent_inner, inner_sub_left]
  ring

 theorem SobolevSpace.resolvent_unique {f : Lp ℝ 2 μ} {u : SobolevSpace μ hQ}
    (hu : IsWeakLaplacian μ hQ u (SobolevSpace.toLp μ hQ u - f)) :
    u = SobolevSpace.resolvent μ hQ f := by
  apply ext_inner_right ℝ
  intro φ
  have h := hu φ
  rw [energyForm, inner_sub_left] at h
  rw [SobolevSpace.resolvent_inner]
  linarith

 theorem SobolevSpace.resolvent_norm_le (f : Lp ℝ 2 μ) :
    ‖SobolevSpace.resolvent μ hQ f‖ ≤ ‖f‖ := by
  have hnorm : ‖SobolevSpace.toLpCLM μ hQ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    simpa only [one_mul, SobolevSpace.toLpCLM, LinearMap.mkContinuous_apply] using
      SobolevSpace.norm_toLp_le μ hQ g
  calc
    _ ≤ ‖SobolevSpace.resolvent μ hQ‖ * ‖f‖ := (SobolevSpace.resolvent μ hQ).le_opNorm f
    _ = ‖SobolevSpace.toLpCLM μ hQ‖ * ‖f‖ := by
      simp only [SobolevSpace.resolvent, LinearIsometryEquiv.norm_map]
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)
    _ = ‖f‖ := one_mul _

 
 theorem SobolevSpace.resolvent_variational_identity (f : Lp ℝ 2 μ) (u : SobolevSpace μ hQ) :
    ‖SobolevSpace.toLp μ hQ u - f‖ ^ 2 + 2 * SobolevSpace.energy μ hQ u =
      ‖SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f) - f‖ ^ 2 +
        2 * SobolevSpace.energy μ hQ (SobolevSpace.resolvent μ hQ f) +
          ‖u - SobolevSpace.resolvent μ hQ f‖ ^ 2 := by
  have hu := SobolevSpace.norm_sq μ hQ u
  have hr := SobolevSpace.norm_sq μ hQ (SobolevSpace.resolvent μ hQ f)
  have hi := SobolevSpace.resolvent_inner μ hQ f u
  have hi_self := SobolevSpace.resolvent_inner μ hQ f (SobolevSpace.resolvent μ hQ f)
  rw [real_inner_self_eq_norm_sq] at hi_self
  unfold SobolevSpace.normSq at hu hr
  simp only [norm_sub_sq_real]
  rw [real_inner_comm (SobolevSpace.resolvent μ hQ f) u,
    real_inner_comm f (SobolevSpace.toLp μ hQ u),
    real_inner_comm f (SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f))]
  linarith

 theorem SobolevSpace.resolvent_minimizes (f : Lp ℝ 2 μ) (u : SobolevSpace μ hQ) :
    ‖SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f) - f‖ ^ 2 +
        2 * SobolevSpace.energy μ hQ (SobolevSpace.resolvent μ hQ f) ≤
      ‖SobolevSpace.toLp μ hQ u - f‖ ^ 2 + 2 * SobolevSpace.energy μ hQ u := by
  rw [SobolevSpace.resolvent_variational_identity μ hQ f u]
  linarith [sq_nonneg ‖u - SobolevSpace.resolvent μ hQ f‖]

end VariationalLaplacian

open Metric
end RegularPointCoordinates

end OAI
