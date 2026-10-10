import Mathlib

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates. -/




 

 

 

 

 

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace RegularPointCoordinates

universe u v

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Time := unitInterval

 
def IsGeodesic {X : Type u} [MetricSpace X] (γ : C(Time, X)) : Prop :=
  ∀ s t : Time, dist (γ s) (γ t) = |(s : ℝ) - (t : ℝ)| * dist (γ 0) (γ 1)

 
def IsGeodesicSpace (X : Type u) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : C(Time, X), γ 0 = x ∧ γ 1 = y ∧ IsGeodesic γ

 
noncomputable def hausdorff (n : ℕ) (X : Type u) [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] : Measure X :=
  ((volume (Metric.ball (0 : Euclidean n) 1)) / (2 : ℝ≥0∞) ^ n) •
    Measure.hausdorffMeasure (n : ℝ)

 
noncomputable def localSlope {X : Type u} [MetricSpace X] (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 < r),
    ⨆ (y : X) (_ : dist x y < r) (_ : y ≠ x),
      ENNReal.ofReal (|f y - f x| / dist x y)

 
def IsLipschitzApproximation {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (fs : ℕ → X → ℝ) : Prop :=
  (∀ i, MemLp (fs i) 2 μ ∧ ∃ C : ℝ≥0, LipschitzWith C (fs i)) ∧
    Tendsto (fun i => eLpNorm (fun x => fs i x - f x) 2 μ) atTop (𝓝 0)

 

noncomputable def cheegerEnergy {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  ⨅ (fs : ℕ → X → ℝ) (_ : IsLipschitzApproximation μ f fs),
    Filter.liminf (fun i => (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, (localSlope (fs i) x) ^ 2 ∂μ) atTop

 
def QuadraticCheegerEnergy {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∀ f g : X → ℝ, MemLp f 2 μ → MemLp g 2 μ →
    cheegerEnergy μ (fun x => f x + g x) + cheegerEnergy μ (fun x => f x - g x) =
      2 * (cheegerEnergy μ f + cheegerEnergy μ g)

 
def FiniteSecondMoment {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (ν : Measure X) : Prop :=
  ∃ o : X, (∫⁻ x, ENNReal.ofReal (dist x o) ^ 2 ∂ν) < ∞

 
noncomputable def transportCost {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (π : Measure (X × X)) : ℝ≥0∞ :=
  ∫⁻ xy, ENNReal.ofReal (dist xy.1 xy.2) ^ 2 ∂π

 
def IsOptimalCoupling {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (ν₀ ν₁ : Measure X) (π : Measure (X × X)) : Prop :=
  Measure.map Prod.fst π = ν₀ ∧ Measure.map Prod.snd π = ν₁ ∧
  ∀ π' : Measure (X × X),
    Measure.map Prod.fst π' = ν₀ → Measure.map Prod.snd π' = ν₁ →
      transportCost π ≤ transportCost π'

 

noncomputable def sigma (K N t θ : ℝ) : ℝ≥0∞ :=
  if θ = 0 ∨ K = 0 then ENNReal.ofReal t
  else if (N - 1) * Real.pi ^ 2 ≤ K * θ ^ 2 then ∞
  else if 0 < K then
    ENNReal.ofReal (Real.sin (t * θ * Real.sqrt (K / (N - 1))) /
      Real.sin (θ * Real.sqrt (K / (N - 1))))
  else
    ENNReal.ofReal (Real.sinh (t * θ * Real.sqrt (-K / (N - 1))) /
      Real.sinh (θ * Real.sqrt (-K / (N - 1))))

 
noncomputable def tau (K N t θ : ℝ) : ℝ≥0∞ :=
  if t = 0 then 0 else if t = 1 then 1 else
    (ENNReal.ofReal t) ^ (1 / N) * (sigma K N t θ) ^ (1 - 1 / N)

 

noncomputable def renyiIntegral {X : Type u} [MeasurableSpace X]
    (μ ν : Measure X) (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (ν.rnDeriv μ x) ^ (1 - 1 / N) ∂μ

 

def FullCD {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (K : ℝ) (n : ℕ) : Prop :=
  letI : MeasurableSpace C(Time, X) := borel _
  ∀ ν₀ ν₁ : Measure X,
    IsProbabilityMeasure ν₀ → IsProbabilityMeasure ν₁ →
    ν₀.AbsolutelyContinuous μ → ν₁.AbsolutelyContinuous μ →
    FiniteSecondMoment ν₀ → FiniteSecondMoment ν₁ →
    ∃ plan : Measure C(Time, X),
      IsProbabilityMeasure plan ∧ (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (Measure.map (fun γ => (γ 0, γ 1)) plan) ∧
      ∀ (N : ℝ), (n : ℝ) ≤ N → ∀ t : Time,
        (∫⁻ γ,
          tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)) *
            (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) +
          tau K N (t : ℝ) (dist (γ 0) (γ 1)) *
            (ν₁.rnDeriv μ (γ 1)) ^ (-(1 / N)) ∂plan) ≤
          renyiIntegral μ (Measure.map (fun γ => γ t) plan) N

 
structure NoncollapsedRCD (K : ℝ) (n : ℕ) (X : Type u) [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] : Prop where
  complete : CompleteSpace X
  separable : SeparableSpace X
  geodesic : IsGeodesicSpace X
  fullSupport : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < hausdorff n X (Metric.ball x r)
  finiteOnBounded : ∀ s : Set X, Bornology.IsBounded s → hausdorff n X s < ∞
  cd : FullCD (hausdorff n X) K n
  quadratic : QuadraticCheegerEnergy (hausdorff n X)

 

def IsPointedApproximation {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (p : X) (q : Y) (r R ε : ℝ) (f : X → Y) : Prop :=
  dist (f p) q ≤ ε ∧
  (∀ x z : X, dist x p ≤ R * r → dist z p ≤ R * r →
    |dist (f x) (f z) - dist x z / r| ≤ ε) ∧
  ∀ y : Y, dist y q ≤ R - ε →
    ∃ x : X, dist x p ≤ R * r ∧ dist (f x) y ≤ ε

 

def RescalingsConverge {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (p : X) (q : Y) (r : ℕ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ i in atTop, ∃ f : X → Y, IsPointedApproximation p q (r i) R ε f

 
def IsTangent {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (p : X) (q : Y) : Prop :=
  ∃ r : ℕ → ℝ, (∀ i, 0 < r i) ∧ Tendsto r atTop (𝓝 0) ∧
    RescalingsConverge p q r

 

def IsRegular {X : Type u} [MetricSpace X] (n : ℕ) (p : X) : Prop :=
  ∀ (Y : Type u) (dY : MetricSpace Y),
    letI := dY
    ProperSpace Y → ∀ q : Y, IsTangent p q →
      ∃ e : Y ≃ᵢ Euclidean n, e q = 0

 
def HasOpenBilipschitzChart {X : Type u} [MetricSpace X] (n : ℕ) (p : X) : Prop :=
  ∃ (U : Set X) (V : Set (Euclidean n)),
    IsOpen U ∧ p ∈ U ∧ IsOpen V ∧
    ∃ (F : U ≃ₜ V) (L : ℝ), 1 ≤ L ∧
      ∀ x z : U,
        L⁻¹ * dist (x : X) (z : X) ≤ dist (F x : Euclidean n) (F z : Euclidean n) ∧
        dist (F x : Euclidean n) (F z : Euclidean n) ≤ L * dist (x : X) (z : X)

section EnergyFoundations

variable {X : Type u} [MetricSpace X]

@[simp] theorem localSlope_const (c : ℝ) (x : X) :
    localSlope (fun _ : X => c) x = 0 := by
  apply le_antisymm _ bot_le
  unfold localSlope
  refine (iInf_le_of_le 1 (iInf_le_of_le zero_lt_one ?_))
  simp

theorem localSlope_const_mul (c : ℝ) (f : X → ℝ) (x : X) :
    localSlope (fun y => c * f y) x = ENNReal.ofReal |c| * localSlope f x := by
  by_cases hc : c = 0
  · subst c
    simp
  have hc0 : ENNReal.ofReal |c| ≠ 0 := by
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using abs_pos.mpr hc
  unfold localSlope
  simp_rw [← mul_sub, abs_mul, mul_div_assoc, ENNReal.ofReal_mul (abs_nonneg c),
    ← ENNReal.mul_iSup, ← ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]

theorem localSlope_le_of_lipschitz {C : ℝ≥0} {f : X → ℝ}
    (hf : LipschitzWith C f) (x : X) : localSlope f x ≤ C := by
  unfold localSlope
  refine iInf_le_of_le 1 (iInf_le_of_le zero_lt_one ?_)
  refine iSup_le fun y => iSup_le fun _ => iSup_le fun hy => ?_
  apply ENNReal.ofReal_le_coe.mpr
  apply (div_le_iff₀ (dist_pos.mpr (Ne.symm hy))).mpr
  rw [abs_sub_comm]
  simpa only [Real.dist_eq] using hf.dist_le_mul x y

variable [MeasurableSpace X] (μ : Measure X)

theorem cheegerEnergy_zero : cheegerEnergy μ (fun _ : X => 0) = 0 := by
  apply le_antisymm _ bot_le
  unfold cheegerEnergy
  let fs : ℕ → X → ℝ := fun _ _ => 0
  have hfs : IsLipschitzApproximation μ (fun _ => 0) fs := by
    constructor
    · intro i
      exact ⟨MemLp.zero, 0, LipschitzWith.const 0⟩
    · simp [fs]
  refine iInf_le_of_le fs (iInf_le_of_le hfs ?_)
  simp [fs, localSlope_const]

theorem IsLipschitzApproximation.const_mul {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hfs : IsLipschitzApproximation μ f fs) (c : ℝ) :
    IsLipschitzApproximation μ (fun x => c * f x) (fun i x => c * fs i x) := by
  constructor
  · intro i
    obtain ⟨hm, C, hC⟩ := hfs.1 i
    refine ⟨hm.const_mul c, ‖c‖₊ * C, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs]
    calc
      |c| * |fs i x - fs i y| ≤ |c| * ((C : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hC.dist_le_mul x y)
          (abs_nonneg c)
      _ = |c| * (C : ℝ) * dist x y := (mul_assoc _ _ _).symm
  · have heq : (fun i => eLpNorm (fun x => c * fs i x - c * f x) 2 μ) =
        fun i => ‖c‖ₑ * eLpNorm (fun x => fs i x - f x) 2 μ := by
      funext i
      simpa only [Pi.smul_def, smul_eq_mul, mul_sub] using
        eLpNorm_const_smul c (fun x => fs i x - f x) 2 μ
    rw [heq]
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) hfs.2 (Or.inr enorm_ne_top)

 
noncomputable def slopeEnergy (f : X → ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, (localSlope f x) ^ 2 ∂μ

theorem slopeEnergy_const_mul (c : ℝ) (f : X → ℝ) :
    slopeEnergy μ (fun x => c * f x) = (ENNReal.ofReal |c|) ^ 2 * slopeEnergy μ f := by
  simp_rw [slopeEnergy, localSlope_const_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  ac_rfl

theorem cheegerEnergy_le_liminf {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hfs : IsLipschitzApproximation μ f fs) :
    cheegerEnergy μ f ≤ liminf (fun i => slopeEnergy μ (fs i)) atTop :=
  iInf_le_of_le fs (iInf_le_of_le hfs le_rfl)

theorem cheegerEnergy_const_mul_le (c : ℝ) (f : X → ℝ) :
    cheegerEnergy μ (fun x => c * f x) ≤
      (ENNReal.ofReal |c|) ^ 2 * cheegerEnergy μ f := by
  by_cases hc : c = 0
  · subst c
    simp [cheegerEnergy_zero]
  have hc0 : (ENNReal.ofReal |c|) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using abs_pos.mpr hc
  have hct : (ENNReal.ofReal |c|) ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  unfold cheegerEnergy
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun fs => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun hfs => ?_
  calc
    _ ≤ liminf (fun i => slopeEnergy μ (fun x => c * fs i x)) atTop :=
      cheegerEnergy_le_liminf μ (hfs.const_mul μ c)
    _ = _ := by
      simp_rw [slopeEnergy_const_mul]
      rw [ENNReal.liminf_const_mul_of_ne_top hct]
      rfl

theorem cheegerEnergy_const_mul (c : ℝ) (f : X → ℝ) :
    cheegerEnergy μ (fun x => c * f x) =
      (ENNReal.ofReal |c|) ^ 2 * cheegerEnergy μ f := by
  apply le_antisymm (cheegerEnergy_const_mul_le μ c f)
  by_cases hc : c = 0
  · subst c
    simp
  have hcn : ENNReal.ofReal |c| ≠ 0 := by
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using abs_pos.mpr hc
  have hinv : (ENNReal.ofReal |c|) ^ 2 * (ENNReal.ofReal |c⁻¹|) ^ 2 = 1 := by
    rw [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hc), ← mul_pow,
      ENNReal.mul_inv_cancel hcn ENNReal.ofReal_ne_top, one_pow]
  have h := mul_le_mul_right (cheegerEnergy_const_mul_le μ c⁻¹ (fun x => c * f x))
      ((ENNReal.ofReal |c|) ^ 2)
  have heq : (fun x => c⁻¹ * (c * f x)) = f := by
    funext x
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [heq, ← mul_assoc, hinv, one_mul] at h
  exact h

theorem IsLipschitzApproximation.congr_ae {f g : X → ℝ} {fs : ℕ → X → ℝ}
    (hfs : IsLipschitzApproximation μ f fs) (hfg : f =ᵐ[μ] g) :
    IsLipschitzApproximation μ g fs := by
  refine ⟨hfs.1, ?_⟩
  have heq : (fun i => eLpNorm (fun x => fs i x - g x) 2 μ) =
      fun i => eLpNorm (fun x => fs i x - f x) 2 μ := by
    funext i
    apply eLpNorm_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [heq]
  exact hfs.2

theorem cheegerEnergy_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[μ] g) :
    cheegerEnergy μ f = cheegerEnergy μ g := by
  apply le_antisymm
  · unfold cheegerEnergy
    refine le_iInf fun fs => le_iInf fun hfs => ?_
    exact cheegerEnergy_le_liminf μ (hfs.congr_ae μ hfg.symm)
  · unfold cheegerEnergy
    refine le_iInf fun fs => le_iInf fun hfs => ?_
    exact cheegerEnergy_le_liminf μ (hfs.congr_ae μ hfg)

theorem QuadraticCheegerEnergy.finite_add {f g : X → ℝ}
    (hQ : QuadraticCheegerEnergy μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hEf : cheegerEnergy μ f ≠ ∞) (hEg : cheegerEnergy μ g ≠ ∞) :
    cheegerEnergy μ (fun x => f x + g x) ≠ ∞ := by
  have hsum := hQ f g hf hg
  have ht : 2 * (cheegerEnergy μ f + cheegerEnergy μ g) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hEf, hEg⟩)
  rw [← hsum] at ht
  exact (ENNReal.add_ne_top.mp ht).1

theorem QuadraticCheegerEnergy.finite_sub {f g : X → ℝ}
    (hQ : QuadraticCheegerEnergy μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hEf : cheegerEnergy μ f ≠ ∞) (hEg : cheegerEnergy μ g ≠ ∞) :
    cheegerEnergy μ (fun x => f x - g x) ≠ ∞ := by
  have hsum := hQ f g hf hg
  have ht : 2 * (cheegerEnergy μ f + cheegerEnergy μ g) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hEf, hEg⟩)
  rw [← hsum] at ht
  exact (ENNReal.add_ne_top.mp ht).2

 

theorem exists_lipschitzApproximation_of_energy_lt {f : X → ℝ} {a ε : ℝ≥0∞}
    (ha : cheegerEnergy μ f < a) (hε : 0 < ε) :
    ∃ g : X → ℝ, MemLp g 2 μ ∧ (∃ C : ℝ≥0, LipschitzWith C g) ∧
      eLpNorm (fun x => g x - f x) 2 μ < ε ∧ slopeEnergy μ g < a := by
  obtain ⟨fs, hfs⟩ := iInf_lt_iff.mp ha
  obtain ⟨hfs, he⟩ := iInf_lt_iff.mp hfs
  have hf : ∃ᶠ i in atTop, slopeEnergy μ (fs i) < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) he
  have hn : ∀ᶠ i in atTop, eLpNorm (fun x => fs i x - f x) 2 μ < ε :=
    hfs.2.eventually (gt_mem_nhds hε)
  obtain ⟨i, hi, hn⟩ := (hf.and_eventually hn).exists
  exact ⟨fs i, (hfs.1 i).1, (hfs.1 i).2, hn, hi⟩

theorem cheegerEnergy_le_of_lipschitz_approximants {f : X → ℝ} {a : ℝ≥0∞}
    (h : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ g : X → ℝ, MemLp g 2 μ ∧ (∃ C : ℝ≥0, LipschitzWith C g) ∧
        eLpNorm (fun x => g x - f x) 2 μ < ε ∧ slopeEnergy μ g ≤ a) :
    cheegerEnergy μ f ≤ a := by
  let δ : ℕ → ℝ≥0∞ := fun i => (1 / 2 : ℝ≥0∞) ^ i
  have hδ : ∀ i, 0 < δ i := fun i => ENNReal.pow_pos (by norm_num) i
  choose fs hmem hlip hnorm henergy using fun i => h (δ i) (hδ i)
  apply (cheegerEnergy_le_liminf μ (fs := fs) ⟨fun i => ⟨hmem i, hlip i⟩, ?_⟩).trans
  · exact liminf_le_of_frequently_le' (Eventually.of_forall henergy).frequently
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num))
      (fun _ => bot_le) (fun i => (hnorm i).le)

 

theorem cheegerEnergy_le_liminf_of_L2 {f : X → ℝ} {fs : ℕ → X → ℝ}
    (_hf : MemLp f 2 μ) (_hfs : ∀ i, MemLp (fs i) 2 μ)
    (hconv : Tendsto (fun i => eLpNorm (fun x => fs i x - f x) 2 μ) atTop (𝓝 0)) :
    cheegerEnergy μ f ≤ liminf (fun i => cheegerEnergy μ (fs i)) atTop := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  apply cheegerEnergy_le_of_lipschitz_approximants μ
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hn : ∀ᶠ i in atTop, eLpNorm (fun x => fs i x - f x) 2 μ < ε / 2 :=
    hconv.eventually (gt_mem_nhds hhalf)
  have he : ∃ᶠ i in atTop, cheegerEnergy μ (fs i) < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) ha
  obtain ⟨i, hi, hni⟩ := (he.and_eventually hn).exists
  obtain ⟨g, hgm, hgl, hdist, hEg⟩ :=
    exists_lipschitzApproximation_of_energy_lt μ hi hhalf
  refine ⟨g, hgm, hgl, ?_, hEg.le⟩
  have ht : eLpNorm (fun x => g x - f x) 2 μ ≤
      eLpNorm (fun x => g x - fs i x) 2 μ +
        eLpNorm (fun x => fs i x - f x) 2 μ := by
    have heq : (fun x => g x - f x) =
        (fun x => g x - fs i x) + (fun x => fs i x - f x) := by
      funext x
      simp
    rw [heq]
    exact eLpNorm_add_le (by norm_num)
  exact ht.trans_lt ((ENNReal.add_lt_add hdist hni).trans_eq (ENNReal.add_halves ε))

end EnergyFoundations

namespace EnergyPolarization

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (q : E → ℝ) (hq0 : q 0 = 0)
  (hqnonneg : ∀ x, 0 ≤ q x)
  (hqsmul : ∀ (c : ℝ) x, q (c • x) = c ^ 2 * q x)
  (hqpar : ∀ x y, q (x + y) + q (x - y) = 2 * (q x + q y))

noncomputable def bracket (x y : E) : ℝ := (q (x + y) - q (x - y)) / 4

include hqsmul in
theorem neg (x : E) : q (-x) = q x := by
  have h := hqsmul (-1) x
  simpa using h

include hq0 hqsmul in
theorem bracket_self (x : E) : bracket q x x = q x := by
  have h := hqsmul 2 x
  have heq : (2 : ℝ) • x = x + x := by module
  rw [heq] at h
  simp only [bracket, sub_self, hq0, sub_zero, h]
  ring

include hqsmul in
theorem bracket_symm (x y : E) : bracket q y x = bracket q x y := by
  have h : q (y - x) = q (x - y) := by
    rw [← neg_sub x y, neg q hqsmul]
  simp only [bracket, add_comm y x, h]

omit [Module ℝ E] in
include hqpar in
theorem bracket_add_left (x y z : E) :
    bracket q (x + y) z = bracket q x z + bracket q y z := by
  unfold bracket
  have h1 := hqpar (x + y + z) (x - z)
  have h2 := hqpar (x + y - z) (x + z)
  have h3 := hqpar (y + z) z
  have h4 := hqpar (y - z) z
  abel_nf at *
  linear_combination (-h1 + h2 + h3 - h4) / 8

omit [Module ℝ E] in
include hqnonneg hqpar in
theorem bracket_abs_le (x y : E) : |bracket q x y| ≤ (q x + q y) / 2 := by
  have hp := hqpar x y
  have hsum := hqnonneg (x + y)
  have hdiff := hqnonneg (x - y)
  rw [abs_le]
  unfold bracket
  constructor <;> linarith

include hqnonneg hqsmul hqpar in
theorem bracket_smul_left (c : ℝ) (x y : E) :
    bracket q (c • x) y = c * bracket q x y := by
  let b : ℝ →+ ℝ := AddMonoidHom.mk' (fun t => bracket q (t • x) y)
    (fun a b => by simpa only [add_smul] using bracket_add_left q hqpar (a • x) (b • x) y)
  have hb : Continuous b := by
    apply b.continuous_of_isBounded_nhds_zero (s := Set.Ioo (-1) 1)
      (Ioo_mem_nhds (by norm_num) (by norm_num))
    refine (isCompact_Icc (a := -(q x + q y) / 2) (b := (q x + q y) / 2)).isBounded.subset ?_
    rintro _ ⟨t, ht, rfl⟩
    have h := bracket_abs_le q hqnonneg hqpar (t • x) y
    rw [hqsmul] at h
    have ht2 : t ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr ht.1.le)]
    have hh : |b t| ≤ (q x + q y) / 2 := h.trans (by nlinarith [hqnonneg x])
    simpa only [mem_Icc, neg_div] using abs_le.mp hh
  have h := map_real_smul b hb c 1
  simpa only [smul_eq_mul, mul_one, b, AddMonoidHom.mk'_apply, one_smul] using h

@[instance_reducible]
noncomputable def preInner : PreInnerProductSpace.Core ℝ E where
  inner := bracket q
  conj_inner_symm := by
    intro x y
    simpa using bracket_symm q hqsmul x y
  re_inner_nonneg := by
    intro x
    simpa only [RCLike.re_to_real, bracket_self q hq0 hqsmul] using hqnonneg x
  add_left := bracket_add_left q hqpar
  smul_left := by
    intro x y c
    simpa using bracket_smul_left q hqnonneg hqsmul hqpar c x y

end EnergyPolarization
end RegularPointCoordinates

end OAI
