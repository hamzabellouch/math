import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ArrivalConeKernelPolarNorm
import OAI.Analysis.VlasovMaxwell.Retarded.CutoffSourceTangent

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def representativeClosedBin (T w : ℝ) (k : Fin 4→ℕ) : ClosedConeBin where
  rmin := max 1 T*cappedRepresentative (k 3)/2
  rmax := 2*max 1 T*cappedRepresentative (k 3)
  qmin := sourceRepresentative (k 0)/128
  qmax := sourceRepresentative (k 0)/32
  wmin := w/8
  wmax := 8*w
  dmin := cappedRepresentative (k 1)^2/2
  dmax := 8*cappedRepresentative (k 1)^2
  Dmin := cappedRepresentative (k 2)^2/2
  Dmax := 8*cappedRepresentative (k 2)^2
  emin := 0
  emax := 2

lemma representativeClosedBin_radius_pos (T w : ℝ) (k : Fin 4→ℕ) :
    0<(representativeClosedBin T w k).rmin := by
  have h : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  dsimp [representativeClosedBin,cappedRepresentative]
  positivity

lemma velocity_deficit_mem_unit2 (v w : Vec) :
    1-dot (velocity w) (velocity v)∈Icc (0:ℝ) 2 := by
  have hd := abs_real_inner_le_norm (velocity w) (velocity v)
  rw [←dot_eq_inner] at hd
  have hn : ‖velocity w‖*‖velocity v‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one w).le).trans
      (norm_velocity_lt_one v).le
  have ha := (abs_le.mp (hd.trans hn))
  constructor <;> linarith

lemma physicalCutoff_positive_closedBin {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hband : q (V t)∈Icc (w/8) (8*w))
    {k : Fin 4→ℕ} {n : Sphere} {v : Vec}
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))) :
    (t,σ,n)∈physicalBinBase V (representativeClosedBin T w k) J ∧
      v∈coneBinMomentumSet (representativeClosedBin T w k) n.1 (velocity (V t)) := by
  have hh := dyadicMultiFactor_positive_bands hk
  have hq := dyadicBand_source_range (show DyadicBand (k 0) (1/q v) from hh 0)
  have hd := dyadicBand_angular_range (cone_denom_pos v n.1 (sphere_norm n)).le
    (show DyadicBand (k 1) (Real.sqrt ((1-dot n.1 (velocity v))/2)) from hh 1)
  have hD := dyadicBand_angular_range (cone_denom_pos (V t) n.1 (sphere_norm n)).le
    (show DyadicBand (k 2) (Real.sqrt ((1-dot n.1 (velocity (V t)))/2)) from hh 2)
  have hr := dyadicBand_radius_range
    (show DyadicBand (k 3) ((t-σ)/max 1 T) from hh 3)
  exact ⟨⟨ht,hσ,hr,hband,hD⟩,⟨hq,hd,velocity_deficit_mem_unit2 v (V t)⟩⟩

lemma dyadicMultiFactor_le_one {ι : Type*} [Fintype ι] (k : ι→ℕ) (x : ι→ℝ) :
    dyadicMultiFactor k x≤1 :=
  Finset.prod_le_one₀ (fun i _=>dyadicFactor_nonneg (k i) (x i))
    (fun i _=>dyadicFactor_le_one (k i) (x i))

def coneDyadicFactor (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (k : Fin 4→ℕ)
    (p : ConeKernelState) : ℝ :=
  dyadicMultiFactor k (physicalCutoffCoordinates T (p.1.1-p.1.2) p.2.1 p.2.2.2 (α zX p.1.1).2)

lemma PhaseFlowOn.coneDyadicFactor_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : Fin 4→ℕ) :
    ContinuousOn (coneDyadicFactor F.flow zX T k) (coneKernelDomain T) := by
  have hV : ContinuousOn (fun p : ConeKernelState=>(F.flow zX p.1.1).2) (coneKernelDomain T) :=
    ((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd
  have hv : Continuous (fun p : ConeKernelState=>p.2.2.2) := continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hV
  have hq := (contDiff_q (k:=1)).continuous.comp hv
  have hc : ∀i,ContinuousOn (fun p : ConeKernelState=>physicalCutoffCoordinates T (p.1.1-p.1.2)
      p.2.1 p.2.2.2 (F.flow zX p.1.1).2 i) (coneKernelDomain T) := by
    intro i
    fin_cases i
    · exact continuousOn_const.div hq.continuousOn (fun p _=>(q_pos p.2.2.2).ne')
    · exact ((continuousOn_const.sub (continuous_dot.comp_continuousOn
        (hn.continuousOn.prodMk hu.continuousOn))).div_const 2).sqrt
    · exact ((continuousOn_const.sub (continuous_dot.comp_continuousOn
        (hn.continuousOn.prodMk ha))).div_const 2).sqrt
    · exact (continuous_fst.fst.sub continuous_fst.snd).continuousOn.div_const _
  exact continuousOn_finsetProd Finset.univ (fun i _=>
    (contDiff_dyadicFactor (k i)).continuous.comp_continuousOn (hc i))

def projectedDyadicRateKernel (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (k : Fin 4→ℕ) (G : ℝ→Vec→L[ℝ]Vec) (p : ConeKernelState) : Vec :=
  coneDyadicFactor α zX T k p • G p.1.1 (normalisedRatePrimitive α zX p)

lemma PhaseFlowOn.projectedDyadicRateKernel_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : Fin 4→ℕ)
    {G : ℝ→Vec→L[ℝ]Vec} (hG : Continuous G) :
    ContinuousOn (projectedDyadicRateKernel F.flow zX T k G) (coneKernelDomain T) :=
  (F.coneDyadicFactor_continuousOn zX k).smul
    ((hG.comp continuous_fst.fst).continuousOn.clm_apply (F.normalisedRatePrimitive_continuousOn zX))

lemma normalisedRatePrimitive_flux_norm (α : Phase→ℝ→Phase) (zX : Phase)
    {t σ c : ℝ} {n : Sphere} {v : Vec} (hσ : σ<t) (G : Vec→L[ℝ]Vec) :
    (1-dot n.1 (velocity (α zX t).2))*
      ‖c • G (normalisedRatePrimitive α zX ((t,σ),(n.1,((0 : Vec),v))))‖ =
      (t-σ)*‖c • G (signedPrimitive (velocity (α zX t).2) (velocity v) n.1)‖ := by
  have hd := cone_denom_pos v n.1 (sphere_norm n)
  have hD := cone_denom_pos (α zX t).2 n.1 (sphere_norm n)
  have he : (1-dot n.1 (velocity v))/(1-dot n.1 (velocity (α zX t).2))*
      ((t-σ)/(1-dot n.1 (velocity v)))=(t-σ)/(1-dot n.1 (velocity (α zX t).2)) := by
    field_simp
  dsimp only [normalisedRatePrimitive,normalisedPrimitive]
  rw [smul_smul,he,map_smul,smul_comm c,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hσ.le) hD.le)]
  field_simp

lemma projectedDyadicRateKernel_flux_norm (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (k : Fin 4→ℕ) (G : ℝ→Vec→L[ℝ]Vec) {t σ c : ℝ} {n : Sphere} {y v : Vec} (hσ : σ<t) :
    (1-dot n.1 (velocity (α zX t).2))*
      ‖c • projectedDyadicRateKernel α zX T k G ((t,σ),(n.1,(y,v)))‖ =
      coneDyadicFactor α zX T k ((t,σ),(n.1,(y,v)))*(t-σ)*
        ‖c • G t (signedPrimitive (velocity (α zX t).2) (velocity v) n.1)‖ := by
  have hχ : 0≤coneDyadicFactor α zX T k ((t,σ),(n.1,(y,v))) := dyadicMultiFactor_nonneg _ _
  dsimp only [projectedDyadicRateKernel]
  rw [smul_comm c,norm_smul,Real.norm_eq_abs,abs_of_nonneg hχ]
  have he := normalisedRatePrimitive_flux_norm α zX (c:=c) (n:=n) (v:=v) hσ (G t)
  change _ * (_ * ‖c • G t (normalisedRatePrimitive α zX ((t,σ),(n.1,((0 : Vec),v))))‖) = _
  calc
    _ = coneDyadicFactor α zX T k ((t,σ),(n.1,(y,v))) *
        ((1-dot n.1 (velocity (α zX t).2))*
          ‖c • G t (normalisedRatePrimitive α zX ((t,σ),(n.1,((0 : Vec),v))))‖) := by ring
    _ = _ := by rw [he]; ring

def physicalDyadicPrimitiveDensity (s : Solution) (X V : ℝ→Vec) (T w : ℝ)
    (k : Fin 4→ℕ) (z : ConeCoordinate) : ℝ≥0∞ :=
  ∫⁻v : Vec, ENNReal.ofReal (dyadicMultiFactor k
    (physicalCutoffCoordinates T (z.1-z.2.1) z.2.2.1 v (V z.1))*(z.1-z.2.1)*
      ‖s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖)

lemma physicalPrimitive_radius_norm {c r : ℝ} (hr : 0<r) (v : Vec) :
    r*‖c • v‖=r^2*‖(c/r) • v‖ := by
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_div,abs_of_pos hr]
  field_simp

lemma physicalDyadicPrimitiveDensity_le {s : Solution} {X V : ℝ→Vec} {T w t σ : ℝ}
    {k : Fin 4→ℕ} {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hσt : σ<t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (n : Sphere) :
    physicalDyadicPrimitiveDensity s X V T w k (t,σ,n) ≤
      (physicalBinBase V (representativeClosedBin T w k) J).indicator
        (physicalProjectedPrimitiveDensity s X V (representativeClosedBin T w k) w) (t,σ,n) := by
  classical
  let B := representativeClosedBin T w k
  let χ : Vec→ℝ := fun v=>dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))
  let H : Vec→ℝ := fun v=>‖s.f (σ,(X t-(t-σ) • n.1,v)) •
    angularMultiplierCLM w (V t) (signedPrimitive (velocity (V t)) (velocity v) n.1)‖
  have hp : ∀v, ENNReal.ofReal (χ v*(t-σ)*H v) ≤
      (coneBinMomentumSet B n.1 (velocity (V t))).indicator
        (fun v=>ENNReal.ofReal ((t-σ)*H v)) v := by
    intro v
    by_cases hχ : 0<χ v
    · have hv := (physicalCutoff_positive_closedBin ht hσ hband hχ).2
      rw [indicator_of_mem hv]
      apply ENNReal.ofReal_le_ofReal
      have hm := dyadicMultiFactor_le_one k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))
      have hrH : 0≤(t-σ)*H v := mul_nonneg (sub_nonneg.mpr hσt.le) (norm_nonneg _)
      have hm' := mul_le_mul_of_nonneg_right hm hrH
      dsimp [χ] at *
      nlinarith
    · have hz : χ v=0 := le_antisymm (le_of_not_gt hχ) (dyadicMultiFactor_nonneg _ _)
      simp only [hz,zero_mul,ENNReal.ofReal_zero]
      exact bot_le
  by_cases hbase : (t,σ,n)∈physicalBinBase V B J
  · rw [indicator_of_mem hbase]
    calc
      _ ≤ ∫⁻v, (coneBinMomentumSet B n.1 (velocity (V t))).indicator
          (fun v=>ENNReal.ofReal ((t-σ)*H v)) v := lintegral_mono hp
      _ = ∫⁻v in coneBinMomentumSet B n.1 (velocity (V t)), ENNReal.ofReal ((t-σ)*H v) :=
        lintegral_indicator (measurableSet_coneBinMomentumSet _ _ _) _
      _ = _ := by
        simp only [H,physicalPrimitive_radius_norm (sub_pos.mpr hσt)]
        simp_rw [ENNReal.ofReal_mul (sq_nonneg (t-σ))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [indicator_of_notMem hbase]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro v
    have hχ : χ v=0 := by
      apply le_antisymm _ (dyadicMultiFactor_nonneg _ _)
      exact le_of_not_gt (fun h=>hbase (physicalCutoff_positive_closedBin ht hσ hband h).1)
    change ENNReal.ofReal (χ v*(t-σ)*H v)=0
    simp only [hχ,zero_mul,ENNReal.ofReal_zero]

lemma projectedDyadicRateKernel_polar_density (α : Phase→ℝ→Phase) (zX : Phase)
    (s : Solution) (T w : ℝ) (k : Fin 4→ℕ) {G : ℝ→Vec→L[ℝ]Vec} {t σ : ℝ}
    (hσt : σ<t) (hG : G t=angularMultiplierCLM w (α zX t).2) (n : Sphere) :
    ENNReal.ofReal (1-dot n.1 (velocity (α zX t).2))*
      (∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((α zX t).1-(t-σ) • n.1,v)) •
        projectedDyadicRateKernel α zX T k G ((t,σ),(n.1,((α zX t).1-(t-σ) • n.1,v)))‖)=
      physicalDyadicPrimitiveDensity s (fun t=>(α zX t).1) (fun t=>(α zX t).2) T w k (t,σ,n) := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro v
  rw [←ENNReal.ofReal_mul (cone_denom_pos _ _ (sphere_norm n)).le,
    projectedDyadicRateKernel_flux_norm α zX T k G hσt,hG]
  rfl

def positiveCoordinate (i : Fin 3) (v : Vec) : Vec := max (v i) 0 • basis 0

lemma positiveCoordinate_continuous (i : Fin 3) : Continuous (positiveCoordinate i) := by
  exact (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3=>ℝ) i).continuous).max continuous_const).smul continuous_const

lemma positiveCoordinate_norm (i : Fin 3) (v : Vec) :
    ‖positiveCoordinate i v‖=max (v i) 0 := by
  simp only [positiveCoordinate,norm_smul,Real.norm_eq_abs,abs_of_nonneg (le_max_right (v i) (0:ℝ))]
  simp [basis,PiLp.norm_single]

lemma positiveCoordinate_zero (i : Fin 3) : positiveCoordinate i 0=0 := by
  simp [positiveCoordinate]

lemma positiveCoordinate_smul (i : Fin 3) {c : ℝ} (hc : 0≤c) (v : Vec) :
    positiveCoordinate i (c • v)=c • positiveCoordinate i v := by
  simp only [positiveCoordinate,PiLp.smul_apply,smul_eq_mul,smul_smul]
  rw [mul_max_of_nonneg (v i) 0 hc, mul_zero]

lemma integral_eq_of_positiveCoordinate {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α→Vec} {g : β→Vec}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hp : ∀i, (∫⁻x,ENNReal.ofReal ‖positiveCoordinate i (f x)‖ ∂μ)=
      ∫⁻y,ENNReal.ofReal ‖positiveCoordinate i (g y)‖ ∂ν)
    (hn : ∀i, (∫⁻x,ENNReal.ofReal ‖positiveCoordinate i (-f x)‖ ∂μ)=
      ∫⁻y,ENNReal.ofReal ‖positiveCoordinate i (-g y)‖ ∂ν) :
    ∫x,f x ∂μ=∫y,g y ∂ν := by
  ext i
  let C := PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3=>ℝ) i
  change C (∫x,f x ∂μ)=C (∫y,g y ∂ν)
  rw [←C.integral_comp_comm hf,←C.integral_comp_comm hg]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (C.integrable_comp hf),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (C.integrable_comp hg)]
  have hp' := hp i
  have hn' := hn i
  have hmax (x : ℝ) : max (ENNReal.ofReal x) 0=ENNReal.ofReal x := max_eq_left (by positivity)
  simp only [positiveCoordinate_norm,ENNReal.ofReal_max,ENNReal.ofReal_zero,hmax,PiLp.neg_apply] at hp' hn'
  simp only [C,PiLp.proj_apply,hp',hn']

abbrev TrianglePhase := ConeCoordinate×Vec

def trianglePhaseDomain (T : ℝ) : Set TrianglePhase :=
  {p | p.1.1∈Ioo 0 T ∧ p.1.2.1∈Ioo 0 p.1.1}

def trianglePhaseMeasure : Measure TrianglePhase :=
  ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod sphereMeasure)).prod volume

def triangleKernelState (α : Phase→ℝ→Phase) (zX : Phase) (p : TrianglePhase) : ConeKernelState :=
  ((p.1.1,p.1.2.1),(p.1.2.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))

def triangleConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) : TrianglePhase→Vec :=
  (trianglePhaseDomain T).indicator (fun p=>
    (1-dot p.1.2.2.1 (velocity (α zX p.1.1).2)) •
      (s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2) •
        A (triangleKernelState α zX p)))

lemma measurableSet_trianglePhaseDomain (T : ℝ) : MeasurableSet (trianglePhaseDomain T) :=
  ((measurable_fst.fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_fst.snd.fst).inter
      (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst)))

lemma PhaseFlowOn.triangleKernelState_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (triangleKernelState F.flow zX) (trianglePhaseDomain T) := by
  have hX : ContinuousOn (fun p : TrianglePhase=>F.flow zX p.1.1) (trianglePhaseDomain T) :=
    (F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>Ioo_subset_Icc_self hp.1)
  exact (continuous_fst.fst.prodMk continuous_fst.snd.fst).continuousOn.prodMk
    (continuous_fst.snd.snd.subtype_val.continuousOn.prodMk
      ((hX.fst.sub ((continuous_fst.fst.sub continuous_fst.snd.fst).continuousOn.smul
        continuous_fst.snd.snd.subtype_val.continuousOn)).prodMk continuous_snd.continuousOn))

lemma triangleKernelState_mem (α : Phase→ℝ→Phase) (zX : Phase) {T : ℝ} {p : TrianglePhase}
    (hp : p∈trianglePhaseDomain T) : triangleKernelState α zX p∈coneKernelDomain T := by
  exact ⟨⟨Ioo_subset_Icc_self hp.1,⟨hp.2.1.le,hp.2.2.le.trans hp.1.2.le⟩⟩,
    ⟨p.1.2.2.2,mem_univ _⟩⟩

lemma PhaseFlowOn.triangleConeKernel_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Measurable (triangleConeKernel s F.flow zX T A) := by
  classical
  have hS := F.triangleKernelState_continuousOn zX
  have hSA := hA.comp hS (fun _ hp=>triangleKernelState_mem _ _ hp)
  have hSf := hs.f_smooth.continuousOn.comp (hS.fst.snd.prodMk hS.snd.snd)
    (fun _ hp=>⟨(triangleKernelState_mem F.flow zX hp).1.2,mem_univ _⟩)
  have hV : ContinuousOn (fun p : TrianglePhase=>(F.flow zX p.1.1).2) (trianglePhaseDomain T) :=
    ((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn
      (fun _ hp=>Ioo_subset_Icc_self hp.1)).snd
  have hD : ContinuousOn (fun p : TrianglePhase=>1-dot p.1.2.2.1 (velocity (F.flow zX p.1.1).2))
      (trianglePhaseDomain T) := by
    simp only [dot_eq_inner]
    exact continuousOn_const.sub (continuous_fst.snd.snd.subtype_val.continuousOn.inner
      ((contDiff_velocity (k:=1)).continuous.comp_continuousOn hV))
  exact (hD.smul (hSf.smul hSA)).measurable_piecewise continuousOn_const
    (measurableSet_trianglePhaseDomain T)

lemma PhaseFlowOn.triangleConeKernel_lintegral_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫⁻p,ENNReal.ofReal ‖triangleConeKernel s F.flow zX T A p‖ ∂trianglePhaseMeasure)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  classical
  let g : TrianglePhase→ℝ≥0∞ := fun p=>ENNReal.ofReal ‖triangleConeKernel s F.flow zX T A p‖
  have hg : Measurable g := (F.triangleConeKernel_measurable hs zX hA).norm.ennreal_ofReal
  have hm : Measurable (fun z : ConeCoordinate=>∫⁻v : Vec,g (z,v)) := hg.lintegral_prod_right'
  have he : (∫⁻p,g p ∂trianglePhaseMeasure)=
      ∫⁻t : ℝ,∫⁻σ : ℝ,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
    rw [trianglePhaseMeasure,lintegral_prod _ hg.aemeasurable,lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro t
    exact lintegral_prod _ ((hm.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  rw [he]
  rw [←lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  by_cases ht : t∈Ioo 0 T
  · rw [indicator_of_mem ht,←lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro σ
    by_cases hσ : σ∈Ioo 0 t
    · rw [indicator_of_mem hσ]
      apply lintegral_congr
      intro n
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro v
      have hp : ((t,σ,n),v)∈trianglePhaseDomain T := ⟨ht,hσ⟩
      simp only [g,triangleConeKernel,indicator_of_mem hp,triangleKernelState,
        norm_smul,Real.norm_eq_abs,abs_of_pos (cone_denom_pos _ _ (sphere_norm n)),
        ENNReal.ofReal_mul (cone_denom_pos _ _ (sphere_norm n)).le]
    · rw [indicator_of_notMem hσ]
      have hz : ∀n : Sphere,∀v : Vec,g ((t,σ,n),v)=0 := by
        intro n v
        have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>hσ hp.2
        simp only [g,triangleConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero]
      simp only [hz,lintegral_zero]
  · rw [indicator_of_notMem ht]
    have hz : ∀σ : ℝ,∀n : Sphere,∀v : Vec,g ((t,σ,n),v)=0 := by
      intro σ n v
      have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>ht hp.1
      simp only [g,triangleConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero]
    simp only [hz,lintegral_zero]

lemma PhaseFlowOn.triangleConeKernel_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Integrable (triangleConeKernel s F.flow zX T A) trianglePhaseMeasure := by
  refine ⟨(F.triangleConeKernel_measurable hs zX hA).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [F.triangleConeKernel_lintegral_norm hs zX hA,←F.labelConeKernel_triangle_norm hs hT zX hA]
  exact ((hasFiniteIntegral_iff_norm _).mp (F.labelConeKernel_integrable hs zX hA).2)

lemma labelConeKernel_positiveCoordinate {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) (α : Phase→ℝ→Phase) (zX : Phase)
    (A : ConeKernelState→Vec) (i : Fin 3) (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun q=>positiveCoordinate i (A q)) p=
      positiveCoordinate i (labelConeKernel s α zX T A p) := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,indicator_of_mem hp,
      positiveCoordinate_smul i (sq_nonneg _),positiveCoordinate_smul i (hs.nonnegative 0 ⟨le_rfl,hT⟩ p.2)]
  · simp only [labelConeKernel,indicator_of_notMem hp,positiveCoordinate_zero]

lemma triangleConeKernel_positiveCoordinate {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (α : Phase→ℝ→Phase) (zX : Phase)
    (A : ConeKernelState→Vec) (i : Fin 3) (p : TrianglePhase) :
    triangleConeKernel s α zX T (fun q=>positiveCoordinate i (A q)) p=
      positiveCoordinate i (triangleConeKernel s α zX T A p) := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · have hσ := (triangleKernelState_mem α zX hp).1.2
    simp only [triangleConeKernel,indicator_of_mem hp,
      positiveCoordinate_smul i (cone_denom_pos _ _ (sphere_norm p.1.2.2)).le,
      positiveCoordinate_smul i (hs.nonnegative _ hσ _)]
  · simp only [triangleConeKernel,indicator_of_notMem hp,positiveCoordinate_zero]

lemma labelConeKernel_neg (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun q=>-A q) p=-labelConeKernel s α zX T A p := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,indicator_of_mem hp,smul_neg]
  · simp only [labelConeKernel,indicator_of_notMem hp,neg_zero]

lemma triangleConeKernel_neg (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) (p : TrianglePhase) :
    triangleConeKernel s α zX T (fun q=>-A q) p=-triangleConeKernel s α zX T A p := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · simp only [triangleConeKernel,indicator_of_mem hp,smul_neg]
  · simp only [triangleConeKernel,indicator_of_notMem hp,neg_zero]

lemma PhaseFlowOn.labelConeKernel_triangle_positiveCoordinate {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) (i : Fin 3) :
    (∫⁻p,ENNReal.ofReal ‖positiveCoordinate i (labelConeKernel s F.flow zX T A p)‖)=
      ∫⁻p,ENNReal.ofReal ‖positiveCoordinate i (triangleConeKernel s F.flow zX T A p)‖ ∂trianglePhaseMeasure := by
  have hAP := (positiveCoordinate_continuous i).comp_continuousOn hA
  calc
    _ = ∫⁻p,ENNReal.ofReal ‖labelConeKernel s F.flow zX T (fun q=>positiveCoordinate i (A q)) p‖ := by
      simp only [labelConeKernel_positiveCoordinate hs hT]
    _ = ∫⁻p,ENNReal.ofReal ‖triangleConeKernel s F.flow zX T (fun q=>positiveCoordinate i (A q)) p‖ ∂trianglePhaseMeasure :=
      (F.labelConeKernel_triangle_norm hs hT zX hAP).trans (F.triangleConeKernel_lintegral_norm hs zX hAP).symm
    _ = _ := by simp only [triangleConeKernel_positiveCoordinate hs]

lemma PhaseFlowOn.labelConeKernel_triangle_integral {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫p,labelConeKernel s F.flow zX T A p)=
      ∫p,triangleConeKernel s F.flow zX T A p ∂trianglePhaseMeasure := by
  apply integral_eq_of_positiveCoordinate (F.labelConeKernel_integrable hs zX hA)
    (F.triangleConeKernel_integrable hs hT zX hA)
  · exact F.labelConeKernel_triangle_positiveCoordinate hs hT zX hA
  · intro i
    simpa only [labelConeKernel_neg,triangleConeKernel_neg] using
      F.labelConeKernel_triangle_positiveCoordinate hs hT zX (A:=fun p=>-A p) hA.neg i

lemma PhaseFlowOn.triangleConeKernel_integral {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫p,triangleConeKernel s F.flow zX T A p ∂trianglePhaseMeasure)=
      ∫t in Ioo (0:ℝ) T,∫σ in Ioo (0:ℝ) t,∫n : Sphere,
        (1-dot n.1 (velocity (F.flow zX t).2)) •
        ∫v : Vec,s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v))) ∂volume ∂sphereMeasure := by
  classical
  let g := triangleConeKernel s F.flow zX T A
  have hg := F.triangleConeKernel_integrable hs hT zX hA
  have hi : Integrable (fun z : ConeCoordinate=>∫v : Vec,g (z,v))
      (volume.prod (volume.prod sphereMeasure)) := hg.integral_prod_left
  have he : (∫p,g p ∂trianglePhaseMeasure)=
      ∫t : ℝ,∫σ : ℝ,∫n : Sphere,∫v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
    rw [trianglePhaseMeasure,integral_prod _ hg,integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_right_ae] with t ht
    exact integral_prod _ ht
  rw [he,←integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact ae_of_all _ (fun t=>by
    by_cases ht : t∈Ioo 0 T
    · rw [indicator_of_mem ht,←integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      exact ae_of_all _ (fun σ=>by
        by_cases hσ : σ∈Ioo 0 t
        · rw [indicator_of_mem hσ]
          apply integral_congr_ae
          exact ae_of_all _ (fun n=>by
            dsimp only
            rw [←integral_smul]
            apply integral_congr_ae
            exact ae_of_all _ (fun v=>by
              have hp : ((t,σ,n),v)∈trianglePhaseDomain T := ⟨ht,hσ⟩
              simp only [g,triangleConeKernel,indicator_of_mem hp,triangleKernelState]))
        · rw [indicator_of_notMem hσ]
          have hz : ∀n : Sphere,∀v : Vec,g ((t,σ,n),v)=0 := by
            intro n v
            have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>hσ hp.2
            simp only [g,triangleConeKernel,indicator_of_notMem hp]
          simp only [hz,integral_zero])
    · rw [indicator_of_notMem ht]
      have hz : ∀σ : ℝ,∀n : Sphere,∀v : Vec,g ((t,σ,n),v)=0 := by
        intro σ n v
        have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>ht hp.1
        simp only [g,triangleConeKernel,indicator_of_notMem hp]
      simp only [hz,integral_zero])

lemma PhaseFlowOn.triangleConeKernel_integral_sphere {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫p,triangleConeKernel s F.flow zX T A p ∂trianglePhaseMeasure)=
      ∫t in Ioo (0:ℝ) T,∫n : Sphere,∫σ in Ioo (0:ℝ) t,
        (1-dot n.1 (velocity (F.flow zX t).2)) •
        ∫v : Vec,s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  classical
  let g := triangleConeKernel s F.flow zX T A
  have hg := F.triangleConeKernel_integrable hs hT zX hA
  have hi : Integrable (fun z : ConeCoordinate=>∫v : Vec,g (z,v))
      (volume.prod (volume.prod sphereMeasure)) := hg.integral_prod_left
  have he : (∫p,g p ∂trianglePhaseMeasure)=
      ∫t : ℝ,∫n : Sphere,∫σ : ℝ,∫v : Vec,g ((t,σ,n),v) ∂volume ∂volume ∂sphereMeasure := by
    rw [trianglePhaseMeasure,integral_prod _ hg,integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_right_ae] with t ht
    exact integral_prod_symm _ ht
  rw [he,←integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact ae_of_all _ (fun t=>by
    by_cases ht : t∈Ioo 0 T
    · rw [indicator_of_mem ht]
      apply integral_congr_ae
      exact ae_of_all _ (fun n=>by
        dsimp only
        rw [←integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        exact ae_of_all _ (fun σ=>by
          by_cases hσ : σ∈Ioo 0 t
          · rw [indicator_of_mem hσ]
            dsimp only
            rw [←integral_smul]
            apply integral_congr_ae
            exact ae_of_all _ (fun v=>by
              have hp : ((t,σ,n),v)∈trianglePhaseDomain T := ⟨ht,hσ⟩
              simp only [g,triangleConeKernel,indicator_of_mem hp,triangleKernelState])
          · rw [indicator_of_notMem hσ]
            have hz : ∀v : Vec,g ((t,σ,n),v)=0 := by
              intro v
              have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>hσ hp.2
              simp only [g,triangleConeKernel,indicator_of_notMem hp]
            simp only [hz,integral_zero]))
    · rw [indicator_of_notMem ht]
      have hz : ∀n : Sphere,∀σ : ℝ,∀v : Vec,g ((t,σ,n),v)=0 := by
        intro n σ v
        have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>ht hp.1
        simp only [g,triangleConeKernel,indicator_of_notMem hp]
      simp only [hz,integral_zero])

lemma physicalDyadicPrimitiveDensity_near_pointwise {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {X V : ℝ→Vec} {J : Set ℝ} (hJT : J⊆Icc 0 T)
    {w C p θ φ t σ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (_hC : 0≤C) (_hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (ht : t∈J) (hσ : σ∈Icc 0 t) (hσt : σ<t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (hv : w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V (representativeClosedBin T w k) J,
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
        ENNReal.ofReal (128*C*p^3*θ^2)) (n : Sphere) :
    physicalDyadicPrimitiveDensity s X V T w k (t,σ,n)≤
      (physicalBinBase V (representativeClosedBin T w k) J).indicator
        (fun _=>ENNReal.ofReal (401408*C*(p*θ)^3*(representativeClosedBin T w k).rmax)) (t,σ,n) := by
  classical
  let B := representativeClosedBin T w k
  have h := physicalDyadicPrimitiveDensity_le ht hσ hσt hband n (s:=s) (X:=X) (k:=k) (T:=T)
  by_cases hz : (t,σ,n)∈physicalBinBase V B J
  · rw [indicator_of_mem hz] at h ⊢
    have hk := physicalProjectedPrimitiveDensity_bound (s:=s) (X:=X) (z:=(t,σ,n))
      hw hv (sub_pos.mpr hσt) hθ hφ hsmall hd (hDlo.trans hz.2.2.2.2.1)
      (hz.2.2.2.2.2.trans hDhi)
      (fun v=>hs.nonnegative σ ⟨hσ.1,hσ.2.trans (hJT ht).2⟩ _)
    have hn : 0≤B.rmax := (representativeClosedBin_radius_pos T w k).le.trans
      (hz.2.2.1.1.trans hz.2.2.1.2)
    have hden := hdensity (t,σ,n) hz
    have hrad : ENNReal.ofReal (t-σ)≤ENNReal.ofReal B.rmax :=
      ENNReal.ofReal_le_ofReal hz.2.2.1.2
    have hmul : ENNReal.ofReal (3136*θ)*ENNReal.ofReal (t-σ)≤
        ENNReal.ofReal (3136*θ)*ENNReal.ofReal B.rmax := mul_le_mul' (a:=ENNReal.ofReal (3136*θ)) (b:=ENNReal.ofReal (3136*θ)) le_rfl hrad
    calc
      _ ≤ ENNReal.ofReal (3136*θ)*ENNReal.ofReal (t-σ)*
          physicalBinDensity s X V B t σ n := h.trans hk
      _ ≤ ENNReal.ofReal (3136*θ)*ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2) :=
        mul_le_mul' hmul hden
      _ = _ := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤3136*θ),
          ←ENNReal.ofReal_mul (mul_nonneg (by positivity) hn)]
        congr 1
        dsimp [B]
        ring
  · exact (h.trans (by rw [indicator_of_notMem hz,indicator_of_notMem hz]))

lemma physicalBin_triangle_weight_le {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (T : ℝ)
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
      (physicalBinBase V B J).indicator (fun z : ConeCoordinate=>g z.1) (t,σ,n)
        ∂sphereMeasure)≤∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J := by
  let H : ConeCoordinate→ℝ≥0∞ := (physicalBinBase V B J).indicator (fun z=>g z.1)
  have hm : Measurable H := (hg.comp measurable_fst).indicator (measurableSet_physicalBinBase hV B hJ)
  calc
    _ ≤ ∫⁻t : ℝ,∫⁻σ : ℝ,∫⁻n : Sphere,H (t,σ,n) ∂sphereMeasure := by
      calc
        _ ≤ ∫⁻t in Ioo (0:ℝ) T,∫⁻σ : ℝ,∫⁻n : Sphere,H (t,σ,n) ∂sphereMeasure := by
          apply lintegral_mono
          intro t
          exact lintegral_mono' (Measure.restrict_le_self (μ:=volume) (s:=Ioo (0:ℝ) t)) (fun _=>le_rfl)
        _ ≤ _ := lintegral_mono' (Measure.restrict_le_self (μ:=volume) (s:=Ioo (0:ℝ) T)) (fun _=>le_rfl)
    _ = ∫⁻z : ConeCoordinate,H z ∂volume.prod (volume.prod sphereMeasure) := by
      rw [lintegral_prod _ hm.aemeasurable]
      apply lintegral_congr
      intro t
      exact (lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    _ = _ := lintegral_indicator (measurableSet_physicalBinBase hV B hJ) _

lemma physicalDyadicPrimitive_triangle_near {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {X V : ℝ→Vec} (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w)) (hv : ∀t∈J,w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V (representativeClosedBin T w k) J,
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
        ENNReal.ofReal (128*C*p^3*θ^2))
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) (hgJ : ∀t∉J,g t=0) :
    (∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
      g t*physicalDyadicPrimitiveDensity s X V T w k (t,σ,n) ∂sphereMeasure)≤
    (∫⁻t in J,g t)*ENNReal.ofReal (154140672*C*(p*θ)^3*φ^2*
      (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
        (representativeClosedBin T w k).rmin)) := by
  classical
  let B := representativeClosedBin T w k
  let c := 401408*C*(p*θ)^3*B.rmax
  have hc : 0≤c := by
    have hr : 0≤B.rmax := by
      dsimp [B,representativeClosedBin]
      have hh : 0<cappedRepresentative (k 3) := by dsimp [cappedRepresentative]; positivity
      positivity
    dsimp [c]
    positivity
  have hm : Measurable (fun t=>g t*ENNReal.ofReal c) := hg.mul measurable_const
  calc
    _ ≤ ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        (physicalBinBase V B J).indicator (fun z : ConeCoordinate=>g z.1*ENNReal.ofReal c) (t,σ,n)
          ∂sphereMeasure := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t _
      apply setLIntegral_mono' measurableSet_Ioo
      intro σ hσ
      apply lintegral_mono
      intro n
      by_cases ht : t∈J
      · have hpw := mul_le_mul' (a:=g t) (b:=g t) le_rfl
          (physicalDyadicPrimitiveDensity_near_pointwise hs hJT hw hC hp hθ hφ hsmall
            hDlo hDhi hd ht (Ioo_subset_Icc_self hσ) hσ.2 (hband t ht) (hv t ht) hdensity n)
        by_cases hz : (t,σ,n)∈physicalBinBase V B J
        · dsimp [B] at hz
          simpa only [B,c,indicator_of_mem hz] using hpw
        · dsimp [B] at hz
          simpa only [B,c,indicator_of_notMem hz,mul_zero] using hpw
      · simp only [hgJ t ht,zero_mul]
        exact bot_le
    _ ≤ ∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal c ∂physicalBinMeasure V B J :=
      physicalBin_triangle_weight_le hV B hJ T hm
    _ = (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)*ENNReal.ofReal c :=
      lintegral_mul_const _ (hg.comp measurable_fst)
    _ ≤ ((∫⁻t in J,g t)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2))*ENNReal.ofReal c :=
      mul_le_mul' (physicalBinMeasure_receiver_weight hV B hJ hφ.le hDhi hg) le_rfl
    _ = _ := by
      have hr : B.rmin≤B.rmax := by
        dsimp [B,representativeClosedBin]
        have hh : 0<cappedRepresentative (k 3) := by dsimp [cappedRepresentative]; positivity
        have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
        nlinarith [mul_pos hT hh]
      rw [mul_assoc, mul_assoc, ←ENNReal.ofReal_mul (by positivity : 0≤384*φ^2),
        ←ENNReal.ofReal_mul (sub_nonneg.mpr hr)]
      congr 2
      dsimp [c,B]
      ring

lemma weighted_labelProjected_congr (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (k : Fin 4→ℕ) {J : Set ℝ}
    {G H : ℝ→Vec→L[ℝ]Vec} (hGH : EqOn G H J)
    {b : ℝ→ℝ} (hbJ : ∀t∉J,b t=0) (p : ℝ×Phase) :
    ENNReal.ofReal (b (labelReceiverTime α zX T p))*
      ENNReal.ofReal ‖labelConeKernel s α zX T (projectedDyadicRateKernel α zX T k G) p‖=
    ENNReal.ofReal (b (labelReceiverTime α zX T p))*
      ENNReal.ofReal ‖labelConeKernel s α zX T (projectedDyadicRateKernel α zX T k H) p‖ := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelReceiverTime,labelConeKernel,indicator_of_mem hp]
    by_cases ht : branchTime α zX p.2 T p.1∈J
    · simp only [projectedDyadicRateKernel,labelKernelState,hGH ht]
    · simp only [hbJ _ ht,ENNReal.ofReal_zero,zero_mul]
  · simp only [labelConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero,mul_zero]

lemma PhaseFlowOn.label_projected_primitive_near {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hv : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
        (representativeClosedBin T w k) J,
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
          ENNReal.ofReal (128*C*p^3*θ^2))
    {b : ℝ→ℝ} (hb : Measurable b) (hbJ : ∀t∉J,b t=0) :
    (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
      ENNReal.ofReal ‖labelConeKernel s F.flow zX T
        (projectedDyadicRateKernel F.flow zX T k (fun t=>angularMultiplierCLM w (F.flow zX t).2)) z‖)≤
    (∫⁻t in J,ENNReal.ofReal (b t))*ENNReal.ofReal (154140672*C*(p*θ)^3*φ^2*
      (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
        (representativeClosedBin T w k).rmin)) := by
  let X : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).1
  let V : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).2
  let G := prefixAngularMultiplier s F.flow T w hw zX
  have hV : Measurable V :=
    (((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd).measurable
  have hG : ∀t∈J,G t=angularMultiplierCLM w (F.flow zX t).2 :=
    fun t ht=>(prefixAngular_highband (s:=s) hw zX (hJT ht) (hv t ht)).1
  have he : ∀t∈Icc 0 T,X t=(F.flow zX t).1 ∧ V t=(F.flow zX t).2 := by
    intro t ht
    simp only [X,V,prefixFlow,prefixClamp_eq ht,and_self]
  calc
    _ = ∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) z‖ := by
      apply lintegral_congr
      intro z
      exact weighted_labelProjected_congr s F.flow zX T k (fun t ht=>(hG t ht).symm) hbJ z
    _ = ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (b t)*physicalDyadicPrimitiveDensity s X V T w k (t,σ,n) ∂sphereMeasure := by
      rw [F.labelConeKernel_triangle_weighted_norm hs hT zX
        (F.projectedDyadicRateKernel_continuousOn zX k (F.prefixAngular_regular hs hT hw zX).1) hb]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      apply lintegral_congr
      intro n
      by_cases htJ : t∈J
      · rw [mul_assoc,projectedDyadicRateKernel_polar_density F.flow zX s T w k hσ.2 (hG t htJ) n]
        unfold physicalDyadicPrimitiveDensity
        rw [(he t (Ioo_subset_Icc_self ht)).1,(he t (Ioo_subset_Icc_self ht)).2]
      · simp only [hbJ t htJ,ENNReal.ofReal_zero,zero_mul]
    _ ≤ _ := physicalDyadicPrimitive_triangle_near hs hV hJ hJT hw hC hp hθ hφ hsmall
      hDlo hDhi hd (fun t ht=>by rw [(he t (hJT ht)).2]; exact hband t ht)
      (fun t ht=>by rw [(he t (hJT ht)).2]; exact hv t ht) hdensity hb.ennreal_ofReal
      (fun t ht=>by rw [hbJ t ht,ENNReal.ofReal_zero])

lemma Admissible.label_projected_primitive_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w p θ φ : ℝ) (k : Fin 4→ℕ),
      MeasurableSet J → J⊆Icc 0 T → 0<w → 0≤p → 0≤θ → 0<φ → θ≤φ →
      φ^2/2≤(representativeClosedBin T w k).Dmin →
      (representativeClosedBin T w k).Dmax≤8*φ^2 →
      (representativeClosedBin T w k).dmax≤8*θ^2 →
      (representativeClosedBin T w k).qmax≤p →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k (fun t=>angularMultiplierCLM w (F.flow zX t).2)) z‖)≤
      (∫⁻t in J,ENNReal.ofReal (b t))*ENNReal.ofReal (C*(p*θ)^3*φ^2*
        (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
          (representativeClosedBin T w k).rmin)) := by
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨154140672*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w p θ φ k hJ hJT hw hp hθ hφ hsmall hDlo hDhi hd hq hband hv b hbm hbJ
  apply F.label_projected_primitive_near hs hT zX hJ hJT hw hC hp hθ hφ hsmall hDlo hDhi hd hband hv _ hbm hbJ
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)

lemma finset_subset_dyadicBox {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) :
    ∃M : ℕ,S⊆dyadicBox ι M := by
  classical
  obtain ⟨M,hM⟩ := (S.biUnion (fun k=>Finset.univ.image k)).exists_nat_subset_range
  refine ⟨M,?_⟩
  intro k hk
  simp only [dyadicBox,Fintype.mem_piFinset]
  intro i
  apply hM
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

def directionWeightMajorant (N : ℕ) (k : Fin 4→ℕ) : ℝ :=
  (if k 0<N then 1 else 0)*(if k 1<N then 1 else 0)*
    (1/2:ℝ)^(k 2)*Real.sqrt ((1/2:ℝ)^(k 3))

lemma directionWeightMajorant_nonneg (N : ℕ) (k : Fin 4→ℕ) :
    0≤directionWeightMajorant N k := by
  unfold directionWeightMajorant
  positivity

lemma sum_range_indicator_lt (M N : ℕ) :
    (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)≤N := by
  classical
  rw [Finset.sum_boole,Nat.cast_le]
  have h : (Finset.range M).filter (fun i=>i<N)⊆Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  simpa only [Finset.card_range] using Finset.card_le_card h

lemma sum_directionWeightMajorant_box (M N : ℕ) :
    ∑k∈dyadicBox (Fin 4) M,directionWeightMajorant N k≤8*(N:ℝ)^2 := by
  classical
  let g : Fin 4→ℕ→ℝ := ![fun i=>if i<N then 1 else 0,
    fun i=>if i<N then 1 else 0,fun i=>(1/2:ℝ)^i,fun i=>Real.sqrt ((1/2:ℝ)^i)]
  have he : ∑k∈dyadicBox (Fin 4) M,directionWeightMajorant N k=
      ∏j,∑i∈Finset.range M,g j i := by
    have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
        (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
    have hh := Finset.sum_prod_piFinset (Finset.range M) g
    rw [heq] at hh
    simpa [dyadicBox,Fin.prod_univ_four,directionWeightMajorant,g] using hh
  rw [he,Fin.prod_univ_four]
  change (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)*
    (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)*
    (∑i∈Finset.range M,(1/2:ℝ)^i)*(∑i∈Finset.range M,Real.sqrt ((1/2:ℝ)^i))≤_
  have hN : 0≤(∑i∈Finset.range M,if i<N then (1:ℝ) else 0) :=
    Finset.sum_nonneg (fun i _=>by positivity)
  have ha : 0≤∑i∈Finset.range M,(1/2:ℝ)^i := Finset.sum_nonneg (fun i _=>by positivity)
  have hs : 0≤∑i∈Finset.range M,Real.sqrt ((1/2:ℝ)^i) := Finset.sum_nonneg (fun i _=>by positivity)
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul (sum_range_indicator_lt M N) (sum_range_indicator_lt M N) hN (by positivity))
      (sum_angular_half_decay M) ha (by positivity))
    (sum_radial_half_decay M) hs (by positivity)
  exact h.trans_eq (by ring)

lemma sum_directionWeightMajorant (S : Finset (Fin 4→ℕ)) (N : ℕ) :
    ∑k∈S,directionWeightMajorant N k≤8*(N:ℝ)^2 := by
  obtain ⟨M,hM⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hM
    (fun k _ _=>directionWeightMajorant_nonneg N k)).trans (sum_directionWeightMajorant_box M N)

lemma tsum_directionWeightMajorant (N : ℕ) :
    (∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k))≤ENNReal.ofReal (8*(N:ℝ)^2) := by
  have hs : Summable (directionWeightMajorant N) :=
    summable_of_sum_le (directionWeightMajorant_nonneg N) (fun S=>sum_directionWeightMajorant S N)
  rw [←ENNReal.ofReal_tsum_of_nonneg (directionWeightMajorant_nonneg N) hs]
  exact ENNReal.ofReal_le_ofReal (hs.tsum_le_of_sum_le (fun S=>sum_directionWeightMajorant S N))

lemma selected_representative_weight_bound {T C : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    (hC : 0≤C) (h0 : k 0<N) (h1 : k 1<N)
    (hsel : sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) (w : ℝ) :
    C*(sourceRepresentative (k 0)*cappedRepresentative (k 1))^3*
      cappedRepresentative (k 2)^2*(representativeClosedBin T w k).rmax*
      ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin)≤
      (4*C*Real.sqrt (max 1 T))*directionWeightMajorant N k := by
  have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  have hb := selected_projected_coefficient hC hp.le (hc 1).le
    (mul_nonneg hT.le (hc 3).le) hsel
    (R:=(representativeClosedBin T w k).rmax) (r:=(representativeClosedBin T w k).rmin)
    (φ:=cappedRepresentative (k 2)) (by
      exact mul_nonneg (mul_nonneg (by norm_num) hT.le) (hc 3).le)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
    (by dsimp [representativeClosedBin]; ring_nf; exact le_rfl)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
  have ha : cappedRepresentative (k 2)≤1 := by
    dsimp [cappedRepresentative]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsq : cappedRepresentative (k 2)^2≤cappedRepresentative (k 2) := by nlinarith [hc 2]
  calc
    _ ≤ 4*C*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2)^2 := hb
    _ ≤ 4*C*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul hT.le]
      simp only [directionWeightMajorant,ite_eq_left h0,ite_eq_left h1,one_mul,cappedRepresentative]
      norm_num
      ring

lemma selectedDyadicCutoff_ofReal {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hx : ∀i,0<x i) (Q : Set (ι→ℕ)) :
    ENNReal.ofReal (selectedDyadicCutoff Q x)=
      ∑'k : ι→ℕ,Q.indicator (fun k=>ENNReal.ofReal (dyadicMultiFactor k x)) k := by
  classical
  obtain ⟨N,_hN,he⟩ := dyadicMultiFactor_curve_locally_finite
    (t:=(0:ℝ)) (g:=fun i (_ : ℝ)=>x i) (fun _=>continuousAt_const) hx
  have hz : ∀k,k∉dyadicBox ι N→dyadicMultiFactor k x=0 := he.self_of_nhds
  have hs : Summable (Q.indicator (fun k=>dyadicMultiFactor k x)) := by
    apply summable_of_hasFiniteSupport
    apply (Finset.finite_toSet (dyadicBox ι N)).subset
    intro k hk
    by_contra hkn
    apply hk
    by_cases hQ : k∈Q
    · rw [indicator_of_mem hQ,hz k hkn]
    · exact indicator_of_notMem hQ _
  rw [selectedDyadicCutoff,ENNReal.ofReal_tsum_of_nonneg (fun k=>by
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk]; exact dyadicMultiFactor_nonneg k x
    · rw [indicator_of_notMem hk]) hs]
  apply tsum_congr
  intro k
  by_cases hk : k∈Q
  · simp only [indicator_of_mem hk]
  · simp only [indicator_of_notMem hk,ENNReal.ofReal_zero]

lemma PhaseFlowOn.label_projected_dyadic_eq {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase)
    (k : Fin 4→ℕ) (G : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) :
    labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p=
      dyadicMultiFactor k (actualCutoffCoordinates F.flow T zX p.2 p.1) •
        G (labelReceiverTime F.flow zX T p) (actualLabelRatePrimitive s F.flow zX T p) := by
  classical
  rw [F.actualLabelRatePrimitive_eq s zX]
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · simp only [labelConeKernel,indicator_of_mem hp,projectedDyadicRateKernel,
      coneDyadicFactor,labelKernelState,actualCutoffCoordinates,labelReceiverTime,
      map_smul,smul_smul]
    congr 1
    ring
  · simp only [labelConeKernel,indicator_of_notMem hp,map_zero,smul_zero]

lemma PhaseFlowOn.selected_receiver_rate_norm_sum {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (b : ℝ→ℝ) (G : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) :
    ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
      (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖=
    ∑'k : Fin 4→ℕ,Q.indicator (fun k=>
      ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
  classical
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hj : p∈jointBranchDomain F.flow zX T := hp
    have hx : ∀i,0<actualCutoffCoordinates F.flow T zX p.2 p.1 i :=
      physicalCutoffCoordinates_pos (F.branchDirection_norm zX p.2 hp.1 hp.2)
        (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1)
    have hle : ∀i,actualCutoffCoordinates F.flow T zX p.2 p.1 i≤1 := by
      apply physicalCutoffCoordinates_le_one (F.branchDirection_norm zX p.2 hp.1 hp.2)
      linarith [(F.branch_time_mem zX p.2 hp.1 hp.2).2,hp.1.1.1,le_max_right (1:ℝ) T]
    have hχ := (selectedDyadicCutoff_mem_unit hx hle Q).1
    rw [map_smul,norm_smul,Real.norm_eq_abs,labelWeight,abs_mul,labelSelectedCutoff,
      indicator_of_mem hj,abs_of_nonneg hχ,ENNReal.ofReal_mul (by positivity :
        0≤|b (labelReceiverTime F.flow zX T p)| *selectedDyadicCutoff Q
          (actualCutoffCoordinates F.flow T zX p.2 p.1)),
      ENNReal.ofReal_mul (abs_nonneg _),selectedDyadicCutoff_ofReal hx Q]
    rw [mul_assoc,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    by_cases hk : k∈Q
    · simp only [indicator_of_mem hk]
      rw [F.label_projected_dyadic_eq s zX k G p]
      simp only [norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (dyadicMultiFactor_nonneg _ _),
        ENNReal.ofReal_mul (dyadicMultiFactor_nonneg _ _)]
    · simp only [indicator_of_notMem hk,zero_mul,mul_zero]
  · rw [F.actualLabelRatePrimitive_eq s zX]
    simp only [labelConeKernel,indicator_of_notMem hp,smul_zero,map_zero,norm_zero,ENNReal.ofReal_zero,mul_zero,
      indicator_zero,tsum_zero]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma sourceRepresentative_le_four {a b : ℕ} (h : a ≤ b+2) :
    sourceRepresentative a ≤ 4*sourceRepresentative b := by
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
  dsimp only [sourceRepresentative]
  calc
    64*(2:ℝ)^a ≤ 64*(2:ℝ)^(b+2) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by rw [pow_add]; ring

lemma cappedRepresentative_le_four {a b : ℕ} (h : b ≤ a+2) :
    cappedRepresentative a ≤ 4*cappedRepresentative b := by
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹ ≤ 1) h
  dsimp only [cappedRepresentative]
  rw [pow_add] at hp
  norm_num at hp
  nlinarith

lemma dyadicSelectionBoundary_direction {T κ : ℝ} (hκ : 0 ≤ κ)
    {Q : Set (Fin 4→ℕ)}
    (hQ : ∀j∈Q,cappedRepresentative (j 1) ≤ κ*cappedRepresentative (j 2) ∧
      sourceRepresentative (j 0)*cappedRepresentative (j 1)*
        Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤ 1)
    {k : Fin 4→ℕ} (hk : k∈dyadicSelectionBoundary Q) :
    cappedRepresentative (k 1) ≤ 16*κ*cappedRepresentative (k 2) ∧
      sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 32 := by
  obtain ⟨⟨j,hj,hnear⟩,_⟩ := hk
  have hT : 0 ≤ max (1:ℝ) T := le_trans (by norm_num) (le_max_left _ _)
  have hc (i : Fin 4) : 0<cappedRepresentative (j i) := by dsimp [cappedRepresentative]; positivity
  have hp : 0<sourceRepresentative (j 0) := by dsimp [sourceRepresentative]; positivity
  have hφ := cappedRepresentative_le_four (hnear 2).2
  have hθ := cappedRepresentative_le_four (hnear 1).1
  have hr := cappedRepresentative_le_four (hnear 3).1
  have hq := sourceRepresentative_le_four (hnear 0).2
  have hsqrt : Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤
      2*Real.sqrt (max 1 T*cappedRepresentative (j 3)) := by
    calc
      _ ≤ Real.sqrt (max 1 T*(4*cappedRepresentative (j 3))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr hT)
      _ = _ := by
        rw [show max 1 T*(4*cappedRepresentative (j 3))=4*(max 1 T*cappedRepresentative (j 3)) by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
  constructor
  · calc
      _ ≤ 4*cappedRepresentative (j 1) := hθ
      _ ≤ 4*(κ*cappedRepresentative (j 2)) := mul_le_mul_of_nonneg_left (hQ j hj).1 (by norm_num)
      _ ≤ 4*(κ*(4*cappedRepresentative (k 2))) := by gcongr
      _ = _ := by ring
  · have hkc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hkp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    calc
      _ ≤ (4*sourceRepresentative (j 0))*(4*cappedRepresentative (j 1))*
          (2*Real.sqrt (max 1 T*cappedRepresentative (j 3))) :=
          mul_le_mul (mul_le_mul hq hθ (hkc 1).le (by positivity)) hsqrt
            (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (hc 1).le))
      _ = 32*(sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3))) := by ring
      _ ≤ 32*1 := mul_le_mul_of_nonneg_left (hQ j hj).2 (by norm_num)
      _ = _ := by norm_num

lemma representativeClosedBin_small_of_angle {T w : ℝ} {k : Fin 4→ℕ}
    (h : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/4) :
    (representativeClosedBin T w k).dmax ≤ (representativeClosedBin T w k).Dmin := by
  have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  dsimp only [representativeClosedBin]
  nlinarith [mul_self_le_mul_self (hc 1).le h]

lemma dyadicSelectionBoundary_small {T w κ : ℝ} (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1/64)
    {Q : Set (Fin 4→ℕ)}
    (hQ : ∀j∈Q,cappedRepresentative (j 1) ≤ κ*cappedRepresentative (j 2) ∧
      sourceRepresentative (j 0)*cappedRepresentative (j 1)*
        Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤ 1)
    {k : Fin 4→ℕ} (hk : k∈dyadicSelectionBoundary Q) :
    (representativeClosedBin T w k).dmax ≤ (representativeClosedBin T w k).Dmin := by
  have h := (dyadicSelectionBoundary_direction hκ hQ hk).1
  apply representativeClosedBin_small_of_angle
  have hc : 0<cappedRepresentative (k 2) := by dsimp [cappedRepresentative]; positivity
  nlinarith [mul_le_mul_of_nonneg_right hκsmall hc.le]

lemma relaxed_representative_moving_bound {T C w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    (hC : 0 ≤ C) (hw : 0 ≤ w) (h0 : k 0<N) (h1 : k 1<N)
    (hsel : sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 32) :
    C*(sourceRepresentative (k 0)*cappedRepresentative (k 1))^3*
      cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
      ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin) ≤
      (131072*C*Real.sqrt (max 1 T)/w)*directionWeightMajorant N k := by
  have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  have hsel' : (sourceRepresentative (k 0)/32)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 1 := by nlinarith
  have hb := selected_moving_coefficient (C:=32768*C) (by positivity)
    (p:=sourceRepresentative (k 0)/32) (by positivity) (hc 1).le (hc 2).le hw
    (mul_nonneg hT.le (hc 3).le) hsel'
    (R:=(representativeClosedBin T w k).rmax) (r:=(representativeClosedBin T w k).rmin)
    (by exact mul_nonneg (mul_nonneg (by norm_num) hT.le) (hc 3).le)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
    (by dsimp [representativeClosedBin]; ring_nf; exact le_rfl)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
  calc
    _ = (32768*C)*((sourceRepresentative (k 0)/32)*cappedRepresentative (k 1))^3*
        cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
        ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin) := by ring
    _ ≤ 4*(32768*C)*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2)/w := hb
    _ = _ := by
      rw [Real.sqrt_mul hT.le]
      simp only [directionWeightMajorant,ite_eq_left h0,ite_eq_left h1,one_mul,cappedRepresentative]
      norm_num
      ring

def receiverBoundaryBinCost (s : Solution) (X V K : ℝ→Vec) (T w : ℝ)
    (J : Set ℝ) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ) : ℝ≥0∞ :=
  ∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V
    (representativeClosedBin T w k) T w Q K z
    ∂physicalBinMeasure V (representativeClosedBin T w k) J

lemma Admissible.receiver_cutoff_boundary_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(X V K : ℝ→Vec) (J : Set ℝ) (w κ : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      Measurable V → Measurable K → MeasurableSet J → J⊆Icc 0 T →
      0<w → 0 ≤ κ → κ ≤ 1/64 →
      (∀j∈Q,cappedRepresentative (j 1) ≤ κ*cappedRepresentative (j 2) ∧
        sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤ 1) →
      (∀t∈J,w/16 ≤ ‖V t‖) →
      (∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator
        (receiverBoundaryBinCost s X V K T w J Q) k) ≤
      (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨C,hC,hnear⟩ := hd₀.receiver_cutoff_near_constant
  refine ⟨1048576*C,by positivity,?_⟩
  intro s T F hs h0 X V K J w κ N Q hV hK hJ hJT hw hκ hκsm hQ hband
  let W := ∫⁻t in J,ENNReal.ofReal ‖K t‖
  have hb (k : Fin 4→ℕ) (hk : k∈dyadicSelectionBoundary Q) (hk0 : k 0<N) (hk1 : k 1<N) :
      receiverBoundaryBinCost s X V K T w J Q k ≤
        W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (directionWeightMajorant N k)) := by
    have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    have hn := hnear s T F hs h0 X V K (representativeClosedBin T w k) J w
      (sourceRepresentative (k 0)) (cappedRepresentative (k 1)) (cappedRepresentative (k 2)) Q
      hV hK hJ hJT hw hp.le (hc 1).le (hc 2)
      (dyadicSelectionBoundary_small hκ hκsm hQ hk) (representativeClosedBin_radius_pos T w k)
      le_rfl le_rfl le_rfl (by change sourceRepresentative (k 0)/32 ≤ sourceRepresentative (k 0); linarith) hband
    refine hn.trans (mul_le_mul' (a:=W) (b:=W) le_rfl ?_)
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 131072*C*Real.sqrt (max 1 T)/w)]
    exact ENNReal.ofReal_le_ofReal (relaxed_representative_moving_bound hC hw.le hk0 hk1
      (dyadicSelectionBoundary_direction hκ hQ hk).2)
  calc
    _ ≤ ∑'k : Fin 4→ℕ,W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*
        ENNReal.ofReal (directionWeightMajorant N k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
      · simpa only [indicator_of_mem hk] using hb k hk.1 hk.2.1 hk.2.2
      · rw [indicator_of_notMem hk]
        exact bot_le
    _ = W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*
        ∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k)) := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      mul_le_mul' (a:=W) (b:=W) le_rfl (mul_le_mul' (a:=ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w))
        (b:=ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)) le_rfl (tsum_directionWeightMajorant N))
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 131072*C*Real.sqrt (max 1 T)/w)]
      congr 2
      ring

end RVM

end

end OAI
