import Mathlib
import OAI.Analysis.RCDHeat.PoissonExp

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatEnergy, HeatSmoothing, HeatContraction, HeatFullGenerator. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section HeatEnergy
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.energy_eq_norms (f : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ f =
      (‖f‖^2 - ‖SobolevSpace.toLp μ hQ f‖^2)/2 := by
  rw [SobolevSpace.norm_sq, SobolevSpace.normSq]
  ring

 theorem SobolevSpace.energy_continuous : Continuous (SobolevSpace.energy μ hQ) := by
  have hL : Continuous (SobolevSpace.toLp μ hQ) := (SobolevSpace.toLpCLM μ hQ).continuous
  change Continuous (fun f : SobolevSpace μ hQ => SobolevSpace.energy μ hQ f)
  simp_rw [SobolevSpace.energy_eq_norms]
  fun_prop

 theorem SobolevSpace.energy_hasDerivAt {f : ℝ → SobolevSpace μ hQ}
    {f' : SobolevSpace μ hQ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => SobolevSpace.energy μ hQ (f s)) (energyForm μ hQ (f t) f') t := by
  have hL := (SobolevSpace.toLpCLM μ hQ).hasFDerivAt.comp_hasDerivAt t hf
  have h := (hf.norm_sq.sub hL.norm_sq).div_const 2
  convert! h using 1
  · funext s
    exact SobolevSpace.energy_eq_norms μ hQ (f s)
  · change energyForm μ hQ (f t) f' =
      (2 * inner ℝ (f t) f' - 2 * inner ℝ (SobolevSpace.toLp μ hQ (f t))
        (SobolevSpace.toLp μ hQ f'))/2
    unfold energyForm
    ring

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatCore_continuous (f : Lp ℝ 2 μ) : Continuous (fun t => heatCore μ hQ t f) :=
  (SobolevSpace.resolventAt μ hQ 1 zero_lt_one).continuous.comp (heatAt_continuous μ hQ f)

 theorem heatCore_double_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => heatCore μ hQ s (resolventLp μ hQ 1 zero_lt_one f))
      (heatCore μ hQ t (resolventLp μ hQ 1 zero_lt_one f - f)) t := by
  have h := (SobolevSpace.resolventAt μ hQ 1 zero_lt_one).hasFDerivAt.comp_hasDerivAt t
    (heatAt_core_hasDerivAt μ hQ t ht f)
  simpa only [heatCore, Function.comp_def, neg_sub, ← map_neg] using h

 theorem heatCore_double_energy_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => SobolevSpace.energy μ hQ
      (heatCore μ hQ s (resolventLp μ hQ 1 zero_lt_one f)))
      (-‖heatAt μ hQ t (resolventLp μ hQ 1 zero_lt_one
        (resolventLp μ hQ 1 zero_lt_one f) - resolventLp μ hQ 1 zero_lt_one f)‖^2) t := by
  have h := SobolevSpace.energy_hasDerivAt μ hQ (heatCore_double_hasDerivAt μ hQ t ht f)
  have he := heatCore_laplacian μ hQ t (resolventLp μ hQ 1 zero_lt_one f)
    (heatCore μ hQ t (resolventLp μ hQ 1 zero_lt_one f-f))
  rw [heatCore_toLp, map_sub (resolventLp μ hQ 1 zero_lt_one), real_inner_self_eq_norm_sq] at he
  simpa only [he] using h

 theorem heatCore_norm_sq_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => ‖SobolevSpace.toLp μ hQ (heatCore μ hQ s f)‖^2)
      (-4 * SobolevSpace.energy μ hQ (heatCore μ hQ t f)) t := by
  have h := (heatCore_hasDerivAt μ hQ t ht f).norm_sq
  have he := heatCore_laplacian μ hQ t f (heatCore μ hQ t f)
  rw [energyForm_self, real_inner_comm] at he
  convert h using 1
  linarith

 theorem heatCore_double_energy_antitone (f : Lp ℝ 2 μ) :
    AntitoneOn (fun t => SobolevSpace.energy μ hQ
      (heatCore μ hQ t (resolventLp μ hQ 1 zero_lt_one f))) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    ((SobolevSpace.energy_continuous μ hQ).comp (heatCore_continuous μ hQ _)).continuousOn
    (fun t ht => (heatCore_double_energy_hasDerivAt μ hQ t (by simpa using ht) f).hasDerivWithinAt)
  intro t _
  exact neg_nonpos.mpr (sq_nonneg _)

 theorem heatCore_double_energy_bound (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    SobolevSpace.energy μ hQ (heatCore μ hQ t (resolventLp μ hQ 1 zero_lt_one f)) ≤
      ‖resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one f)‖^2 / (4*t) := by
  let g := resolventLp μ hQ 1 zero_lt_one f
  let e := SobolevSpace.energy μ hQ (heatCore μ hQ t g)
  have he : ∀ s ∈ Icc (0 : ℝ) t, e ≤ SobolevSpace.energy μ hQ (heatCore μ hQ s g) := by
    intro s hs
    exact heatCore_double_energy_antitone μ hQ f hs.1 ht.le hs.2
  have ha : AntitoneOn (fun s => ‖SobolevSpace.toLp μ hQ (heatCore μ hQ s g)‖^2 + 4*s*e)
      (Icc 0 t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      ((((SobolevSpace.toLpCLM μ hQ).continuous.comp (heatCore_continuous μ hQ g)).norm.pow 2).add
        ((continuous_const.mul continuous_id).mul continuous_const)).continuousOn
      (fun s hs => by
        have hs' : s ∈ Ioo (0 : ℝ) t := by simpa only [interior_Icc] using hs
        exact ((heatCore_norm_sq_hasDerivAt μ hQ s hs'.1 g).add
          (((hasDerivAt_id s).const_mul 4).mul_const e)).hasDerivWithinAt)
    intro s hs
    have hi : s ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs)
    have hh := he s hi
    linarith
  have ha' := ha (left_mem_Icc.mpr ht.le) (right_mem_Icc.mpr ht.le) ht.le
  simp only [heatCore_toLp, heatAt_zero, one_apply_eq_self, mul_zero, zero_mul, add_zero] at ha'
  apply (le_div_iff₀ (by linarith : 0 < 4*t)).mpr
  dsimp [e] at ha' ⊢
  nlinarith [sq_nonneg ‖SobolevSpace.toLp μ hQ (heatCore μ hQ t g)‖]

end HeatEnergy

section HeatSmoothing
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.energyLp_eq (f : SobolevSpace μ hQ) :
    energyLp μ (SobolevSpace.toLp μ hQ f) = ENNReal.ofReal (SobolevSpace.energy μ hQ f) :=
  (ENNReal.ofReal_toReal f.property).symm

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatAt_energy_bound (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    energyLp μ (heatAt μ hQ t f) ≤ ENNReal.ofReal (‖f‖^2/(4*t)) := by
  obtain ⟨fs, hfs, hconv⟩ := mem_closure_iff_seq_limit.mp
    (resolventLp_sq_denseRange μ hQ 1 zero_lt_one f)
  apply (energyLp_le_liminf μ ((heatAt μ hQ t).continuous.continuousAt.tendsto.comp hconv)).trans
  have hbound : ∀ i, energyLp μ (heatAt μ hQ t (fs i)) ≤ ENNReal.ofReal (‖fs i‖^2/(4*t)) := by
    intro i
    obtain ⟨g, hg⟩ := hfs i
    rw [← hg, ← heatCore_toLp, SobolevSpace.energyLp_eq]
    exact ENNReal.ofReal_le_ofReal (heatCore_double_energy_bound μ hQ t ht g)
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp ((hconv.norm.pow 2).div_const (4*t))
  exact (liminf_le_liminf (Eventually.of_forall hbound)).trans_eq hlim.liminf_eq

 
noncomputable def heatSobolev (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) : SobolevSpace μ hQ :=
  ⟨heatAt μ hQ t f, ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heatAt_energy_bound μ hQ t ht f)⟩

 theorem heatSobolev_toLp (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f) = heatAt μ hQ t f := rfl

 theorem heatSobolev_energy_bound (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    SobolevSpace.energy μ hQ (heatSobolev μ hQ t ht f) ≤ ‖f‖^2/(4*t) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (heatAt_energy_bound μ hQ t ht f)
  simpa only [SobolevSpace.energy, heatSobolev_toLp,
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (by positivity : 0 ≤ 4*t))] using h

 theorem heatSobolev_norm_bound (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    ‖heatSobolev μ hQ t ht f‖ ≤ Real.sqrt (1+1/(2*t)) * ‖f‖ := by
  have hE := heatSobolev_energy_bound μ hQ t ht f
  have hN := (heatAt μ hQ t).le_of_opNorm_le (heatAt_norm_le μ hQ t) f
  simp only [one_mul] at hN
  have hS := SobolevSpace.norm_sq μ hQ (heatSobolev μ hQ t ht f)
  simp only [SobolevSpace.normSq, heatSobolev_toLp] at hS
  have hpos : 0 ≤ 1+1/(2*t) := by positivity
  have hroot := Real.sq_sqrt hpos
  have hT : ‖heatSobolev μ hQ t ht f‖^2 ≤ (1+1/(2*t))*‖f‖^2 := by
    have halg : (1+1/(2*t))*‖f‖^2 = ‖f‖^2 + 2*(‖f‖^2/(4*t)) := by ring
    rw [halg]
    nlinarith [sq_nonneg (‖f‖-‖heatAt μ hQ t f‖), norm_nonneg (heatAt μ hQ t f)]
  have hprod : 0 ≤ Real.sqrt (1+1/(2*t)) * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (‖heatSobolev μ hQ t ht f‖ - Real.sqrt (1+1/(2*t))*‖f‖)]

 
noncomputable def heatSobolevMap (t : ℝ) (ht : 0 < t) : Lp ℝ 2 μ →L[ℝ] SobolevSpace μ hQ :=
  LinearMap.mkContinuous
    { toFun := heatSobolev μ hQ t ht
      map_add' := fun f g => Subtype.ext (map_add (heatAt μ hQ t) f g)
      map_smul' := fun c f => Subtype.ext (map_smul (heatAt μ hQ t) c f) }
    (Real.sqrt (1+1/(2*t))) (heatSobolev_norm_bound μ hQ t ht)

 theorem heatSobolevMap_apply (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    heatSobolevMap μ hQ t ht f = heatSobolev μ hQ t ht f := rfl

end HeatSmoothing

section HeatContraction
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.resolventAt_one :
    SobolevSpace.resolventAt μ hQ 1 zero_lt_one = SobolevSpace.resolvent μ hQ := by
  apply ContinuousLinearMap.ext
  intro f
  apply SobolevSpace.resolvent_unique
  simpa only [inv_one, one_smul] using
    SobolevSpace.resolventAt_weak_laplacian μ hQ 1 zero_lt_one f

 theorem SobolevSpace.resolvent_denseRange : DenseRange (SobolevSpace.resolvent μ hQ) := by
  have h : (SobolevSpace.resolvent μ hQ).range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro f hf
    apply Subtype.ext
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hh := hf _ ⟨SobolevSpace.toLp μ hQ f, rfl⟩
    change inner ℝ (SobolevSpace.resolvent μ hQ (SobolevSpace.toLp μ hQ f)) f = 0 at hh
    rw [SobolevSpace.resolvent_inner] at hh
    exact hh
  rw [DenseRange, dense_iff_closure_eq]
  simpa only [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe,
    Submodule.top_coe] using congrArg (fun s : Submodule ℝ (SobolevSpace μ hQ) =>
      (s : Set (SobolevSpace μ hQ))) h

 theorem SobolevSpace.resolventAt_one_denseRange :
    DenseRange (SobolevSpace.resolventAt μ hQ 1 zero_lt_one) := by
  rw [SobolevSpace.resolventAt_one]
  exact SobolevSpace.resolvent_denseRange μ hQ

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem SobolevSpace.double_core_denseRange :
    DenseRange (fun f => SobolevSpace.resolventAt μ hQ 1 zero_lt_one
      (resolventLp μ hQ 1 zero_lt_one f)) :=
  (SobolevSpace.resolventAt_one_denseRange μ hQ).comp
    (resolventLp_denseRange μ hQ 1 zero_lt_one)
    (SobolevSpace.resolventAt μ hQ 1 zero_lt_one).continuous

 theorem heatSobolev_core (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    heatSobolev μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f) = heatCore μ hQ t f := by
  apply Subtype.ext
  exact (heatCore_toLp μ hQ t f).symm

 theorem heatSobolev_energy_le (t : ℝ) (ht : 0 < t) (f : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (heatSobolev μ hQ t ht (SobolevSpace.toLp μ hQ f)) ≤
      SobolevSpace.energy μ hQ f := by
  refine (SobolevSpace.double_core_denseRange μ hQ).induction_on f ?_ ?_
  · exact isClosed_le
      ((SobolevSpace.energy_continuous μ hQ).comp
        ((heatSobolevMap μ hQ t ht).continuous.comp (SobolevSpace.toLpCLM μ hQ).continuous))
      (SobolevSpace.energy_continuous μ hQ)
  · intro g
    change SobolevSpace.energy μ hQ (heatSobolev μ hQ t ht
      (resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one g))) ≤ _
    rw [heatSobolev_core]
    have h := heatCore_double_energy_antitone μ hQ g (by simp : (0:ℝ) ∈ Ici 0) ht.le ht.le
    simpa only [heatCore, heatAt_zero, one_apply_eq_self] using h

end HeatContraction

variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def energyOperator : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ :=
  1 - (SobolevSpace.toLpCLM μ hQ).adjoint.comp (SobolevSpace.toLpCLM μ hQ)

 theorem energyOperator_inner (f g : SobolevSpace μ hQ) :
    inner ℝ (energyOperator μ hQ f) g = energyForm μ hQ f g := by
  simp only [energyOperator, sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

 theorem energyOperator_norm_le : ‖energyOperator μ hQ‖ ≤ 2 := by
  have hJ : ‖SobolevSpace.toLpCLM μ hQ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    exact (SobolevSpace.norm_toLp_le μ hQ f).trans_eq (one_mul _).symm
  have hI : ‖(1 : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  calc
    _ ≤ ‖(1 : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ)‖ +
        ‖(SobolevSpace.toLpCLM μ hQ).adjoint.comp (SobolevSpace.toLpCLM μ hQ)‖ := by
      simpa only [energyOperator] using norm_sub_le
        (1 : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ)
        ((SobolevSpace.toLpCLM μ hQ).adjoint.comp (SobolevSpace.toLpCLM μ hQ))
    _ ≤ 1 + ‖(SobolevSpace.toLpCLM μ hQ).adjoint‖ * ‖SobolevSpace.toLpCLM μ hQ‖ :=
      add_le_add hI (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 + 1*1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact add_le_add_right (mul_le_mul hJ hJ (norm_nonneg (SobolevSpace.toLpCLM μ hQ)) zero_le_one) 1
    _ = 2 := by norm_num

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatAt_inner (t : ℝ) (f g : Lp ℝ 2 μ) :
    inner ℝ (heatAt μ hQ t f) g = inner ℝ f (heatAt μ hQ t g) :=
  heatFlow_inner μ hQ (max t 0) (le_max_right _ _) f g

 theorem heatAt_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatAt μ hQ (s+t) = heatAt μ hQ s * heatAt μ hQ t := by
  rw [heatAt_of_nonneg μ hQ (s+t) (add_nonneg hs ht), heatAt_of_nonneg μ hQ s hs,
    heatAt_of_nonneg μ hQ t ht]
  exact heatFlow_add μ hQ s t hs ht

 

noncomputable def heatGenerator (t : ℝ) (ht : 0 < t) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (heatSobolevMap μ hQ (t/2) (half_pos ht)).adjoint.comp
    ((energyOperator μ hQ).comp (heatSobolevMap μ hQ (t/2) (half_pos ht)))

 theorem heatGenerator_inner (t : ℝ) (ht : 0 < t) (f g : Lp ℝ 2 μ) :
    inner ℝ (heatGenerator μ hQ t ht f) g = energyForm μ hQ
      (heatSobolev μ hQ (t/2) (half_pos ht) f)
      (heatSobolev μ hQ (t/2) (half_pos ht) g) := by
  simp only [heatGenerator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, heatSobolevMap_apply, energyOperator_inner]

 theorem heatGenerator_core (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    heatGenerator μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f) =
      heatAt μ hQ t (f - resolventLp μ hQ 1 zero_lt_one f) := by
  apply ext_inner_right ℝ
  intro g
  rw [heatGenerator_inner, heatSobolev_core]
  rw [heatCore_laplacian μ hQ (t/2) f, heatSobolev_toLp]
  rw [← heatAt_inner μ hQ (t/2)]
  have he : heatAt μ hQ (t/2) (heatAt μ hQ (t/2)
      (resolventLp μ hQ 1 zero_lt_one f-f)) =
      heatAt μ hQ t (resolventLp μ hQ 1 zero_lt_one f-f) := by
    rw [← mul_apply_eq_comp, ← heatAt_add μ hQ _ _ (half_pos ht).le (half_pos ht).le]
    congr 2
    ring
  rw [he, ← inner_neg_left, ← map_neg, neg_sub]

 theorem heatGenerator_form (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) (φ : SobolevSpace μ hQ) :
    energyForm μ hQ (heatSobolev μ hQ t ht f) φ =
      inner ℝ (heatGenerator μ hQ t ht f) (SobolevSpace.toLp μ hQ φ) := by
  refine (resolventLp_denseRange μ hQ 1 zero_lt_one).induction_on f ?_ ?_
  · have h1 : Continuous (fun f : Lp ℝ 2 μ =>
        energyForm μ hQ (heatSobolev μ hQ t ht f) φ) := by
      simp_rw [← energyOperator_inner]
      exact (((energyOperator μ hQ).continuous.comp (heatSobolevMap μ hQ t ht).continuous).inner
        continuous_const)
    exact isClosed_eq h1 ((heatGenerator μ hQ t ht).continuous.inner continuous_const)
  · intro g
    rw [heatSobolev_core, heatGenerator_core, heatCore_laplacian μ hQ t g,
      ← inner_neg_left, ← map_neg, neg_sub]

 theorem heatSobolev_weak_laplacian (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    IsWeakLaplacian μ hQ (heatSobolev μ hQ t ht f) (-heatGenerator μ hQ t ht f) := by
  intro φ
  simpa only [inner_neg_left, neg_neg] using heatGenerator_form μ hQ t ht f φ

 theorem heatSobolevMap_norm_le (t : ℝ) (ht : 0 < t) :
    ‖heatSobolevMap μ hQ t ht‖ ≤ Real.sqrt (1+1/(2*t)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact heatSobolev_norm_bound μ hQ t ht

 theorem heatGenerator_norm_le (t : ℝ) (ht : 0 < t) :
    ‖heatGenerator μ hQ t ht‖ ≤ 2*(1+1/t) := by
  have hS := heatSobolevMap_norm_le μ hQ (t/2) (half_pos ht)
  have hP : 0 ≤ 1+1/t := by positivity
  have hS' : ‖heatSobolevMap μ hQ (t/2) (half_pos ht)‖ ≤ Real.sqrt (1+1/t) := by
    convert hS using 2
    congr 2
    ring
  have hA := energyOperator_norm_le μ hQ
  calc
    _ ≤ ‖(heatSobolevMap μ hQ (t/2) (half_pos ht)).adjoint‖ *
        ‖(energyOperator μ hQ).comp (heatSobolevMap μ hQ (t/2) (half_pos ht))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖heatSobolevMap μ hQ (t/2) (half_pos ht)‖ *
        (‖energyOperator μ hQ‖ * ‖heatSobolevMap μ hQ (t/2) (half_pos ht)‖) := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ Real.sqrt (1+1/t) * (2*Real.sqrt (1+1/t)) :=
      mul_le_mul hS' (mul_le_mul hA hS' (norm_nonneg (heatSobolevMap μ hQ (t/2) (half_pos ht))) (by norm_num))
        (mul_nonneg (norm_nonneg (energyOperator μ hQ))
          (norm_nonneg (heatSobolevMap μ hQ (t/2) (half_pos ht)))) (Real.sqrt_nonneg _)
    _ = 2*(1+1/t) := by nlinarith [Real.sq_sqrt hP]

end RegularPointCoordinates

end OAI
