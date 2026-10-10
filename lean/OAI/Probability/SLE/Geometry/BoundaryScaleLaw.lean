import OAI.Probability.SLE.Geometry.PublishedFiniteBoundaryExtension
import OAI.Probability.SLE.Geometry.FrontClockChange
import OAI.Probability.SLE.Loewner.ScaleTraceLaw

namespace OAI

/-! Finite boundary charts commute with normalization. Capacity scaling
changes only the clock of the physical image path, and therefore preserves
the first-front success-and-sausage event. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.BoundaryScaleLaw

local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace
local instance boundaryScalePathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance boundaryScalePathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem finite_boundary_ext (f g : C(closedHalfPlane, ℂ))
    (heq : ∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane → f z = g z) : f = g := by
  ext z
  let zₙ (n : ℕ) : closedHalfPlane :=
    ⟨z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I, by
      change 0 ≤ (z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      exact add_nonneg z.2 (by positivity)⟩
  have hH (n : ℕ) : (zₙ n).1 ∈ upperHalfPlane := by
    change 0 < (z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact add_pos_of_nonneg_of_pos z.2 (by positivity)
  have hz : Tendsto zₙ atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] using
      tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const Complex.I)
  exact tendsto_nhds_unique ((f.continuous.tendsto z).comp hz)
    (((g.continuous.tendsto z).comp hz).congr (fun n => (heq (zₙ n) (hH n)).symm))

def scaleClosed (c : ℝ≥0) : C(closedHalfPlane, closedHalfPlane) :=
  ⟨fun z => ⟨(c : ℂ) * z, by
    change 0 ≤ ((c : ℂ) * (z : ℂ)).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] using mul_nonneg c.coe_nonneg z.2⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk _⟩

theorem normalized_boundary_eq
    (F : ℂ → ℂ) (u : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (f₁ fc : C(closedHalfPlane, ℂ))
    (h₁ : ∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane → f₁ z = F ((u : ℂ) + z))
    (hscaled : ∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane →
      fc z = F ((u : ℂ) + (c : ℂ) * z)) :
    fc = f₁.comp (scaleClosed c) := by
  apply finite_boundary_ext
  intro z hz
  change fc z = f₁ (scaleClosed c z)
  rw [hscaled z hz, h₁]
  · rfl
  · change 0 < ((c : ℂ) * (z : ℂ)).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] using mul_pos (show 0 < (c : ℝ) by exact_mod_cast hc) hz

def clockPath (e : ℝ≥0 ≃o ℝ≥0) (p : C(ℝ≥0, ℂ)) : C(ℝ≥0, ℂ) :=
  ⟨fun t => p (e t), p.continuous.comp e.toHomeomorph.continuous⟩

theorem measurable_clockPath (e : ℝ≥0 ≃o ℝ≥0) : Measurable (clockPath e) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun p : C(ℝ≥0, ℂ) => p (e t))
  exact (continuous_eval_const (e t)).measurable

theorem boundary_scale_clock_identity
    (c : ℝ≥0) (hc : 0 < c) (f : C(closedHalfPlane, ℂ))
    (p : C(ℝ≥0, ℂ)) (hp : ClosedPathProperty p) :
    finiteBoundaryPath (f.comp (scaleClosed c)) p =
      clockPath (OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2))
        (finiteBoundaryPath f (ScaleTraceLaw.scalePath c p)) := by
  have hpc : ClosedPathProperty (ScaleTraceLaw.scalePath c p) := by
    intro t
    change 0 ≤ ((c : ℂ) * p (sourceScaleTime c t)).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] using mul_nonneg c.coe_nonneg (hp _)
  ext t
  rw [finiteBoundaryPath_apply _ _ hp]
  change f (scaleClosed c ⟨p t, hp t⟩) =
    finiteBoundaryPath f (ScaleTraceLaw.scalePath c p) ((c ^ 2) * t)
  rw [finiteBoundaryPath_apply _ _ hpc]
  congr 1
  apply Subtype.ext
  change (c : ℂ) * p t = (c : ℂ) * p (sourceScaleTime c (c ^ 2 * t))
  congr 2
  unfold sourceScaleTime
  field_simp

/-- The normalized physical path has the same law as a deterministic
capacity-clock change of the unnormalized physical path. -/
theorem boundary_scale_path_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : Ω → C(ℝ≥0, ℂ)) (hp : Measurable p)
    (hclosed : ∀ᵐ ω ∂P, ClosedPathProperty (p ω))
    (c : ℝ≥0) (hc : 0 < c) (f : C(closedHalfPlane, ℂ))
    (hlaw : P.map (fun ω => ScaleTraceLaw.scalePath c (p ω)) = P.map p) :
    P.map (fun ω => finiteBoundaryPath (f.comp (scaleClosed c)) (p ω)) =
      P.map (fun ω => clockPath (OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2))
        (finiteBoundaryPath f (p ω))) := by
  let e := OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2)
  calc
    _ = P.map (fun ω => clockPath e (finiteBoundaryPath f (ScaleTraceLaw.scalePath c (p ω)))) := by
      apply Measure.map_congr
      filter_upwards [hclosed] with ω hω
      exact boundary_scale_clock_identity c hc f (p ω) hω
    _ = (P.map (fun ω => ScaleTraceLaw.scalePath c (p ω))).map
        (fun q => clockPath e (finiteBoundaryPath f q)) := by
      exact (Measure.map_map ((measurable_clockPath e).comp (measurable_finiteBoundaryPath f))
        ((ScaleTraceLaw.measurable_scalePath c).comp hp)).symm
    _ = (P.map p).map (fun q => clockPath e (finiteBoundaryPath f q)) := by rw [hlaw]
    _ = _ := by
      exact Measure.map_map ((measurable_clockPath e).comp (measurable_finiteBoundaryPath f)) hp

open FirstFrontPassage PassageSuccess

def frontMassEvent (p : ℂ → ℝ) (V : Set ℂ) (a : ℂ) (ε κ v c : ℝ) (R : Set ℂ) :
    Set C(ℝ≥0, ℂ) :=
  {γ | γ ∈ FrontSuccess (fun _ (γ : C(ℝ≥0, ℂ)) => (γ : ℝ≥0 → ℂ)) (fun _ => p) (fun _ => 0)
      (fun _ => V) (fun _ => a) ε 0 ∧
    ENNReal.ofReal c ≤ segmentSausageCharge κ γ 0
      (frontTime (fun t => p (γ t)) 1) v R}

theorem measurableSet_frontMassEvent
    (p : ℂ → ℝ) (V : Set ℂ) (a : ℂ) (ε κ v c : ℝ) (R K : Set ℂ)
    (hK : IsClosed K) (hp : ContinuousOn p K) (hV : IsOpen V) (hVK : V ⊆ K) :
    MeasurableSet (frontMassEvent p V a ε κ v c R) := by
  let ℱ : Filtration ℝ≥0 (borel C(ℝ≥0, ℂ)) :=
    Filtration.const ℝ≥0 (borel C(ℝ≥0, ℂ)) le_rfl
  have ha : Adapted ℱ (fun t (γ : C(ℝ≥0, ℂ)) => γ t) := by
    intro t
    change @Measurable C(ℝ≥0, ℂ) ℂ (borel C(ℝ≥0, ℂ)) _ (fun γ => γ t)
    exact (continuous_eval_const t).measurable
  exact FrontSuccessMeasurability.measurableSet_frontSuccess_mass
    ℱ
    (fun _ (γ : C(ℝ≥0, ℂ)) => (γ : ℝ≥0 → ℂ)) (fun _ => p) (fun _ => 0)
    (fun _ => V) (fun _ => a) ε 0
    ha (fun γ => γ.continuous)
    K hK hp measurable_const hV hVK κ v c R

theorem mem_frontMassEvent_clock
    (e : ℝ≥0 ≃o ℝ≥0) (p : ℂ → ℝ) (V : Set ℂ) (a : ℂ)
    (ε κ v c : ℝ) (R : Set ℂ) (γ : C(ℝ≥0, ℂ)) :
    clockPath e γ ∈ frontMassEvent p V a ε κ v c R ↔
      γ ∈ frontMassEvent p V a ε κ v c R := by
  have he := congrArg (fun S : Set C(ℝ≥0, ℂ) => γ ∈ S)
    (FrontClockChange.frontSuccess_mass_clock e (fun γ : C(ℝ≥0, ℂ) => (γ : ℝ≥0 → ℂ)) p (fun _ => 0)
      V a ε κ v c R)
  have he0 : e.symm 0 = 0 := e.symm.map_bot
  simpa only [he0, frontMassEvent, FrontSuccess, clockPath, ContinuousMap.coe_mk,
    mem_ofPred_eq] using eq_iff_iff.mp he

/-- Normalize the inverse chart without changing the physical first-front
event probability. The scale law is the actual SLE path law. -/
theorem frontMassEvent_boundary_scale_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : Ω → C(ℝ≥0, ℂ)) (hγ : Measurable γ)
    (hclosed : ∀ᵐ ω ∂P, ClosedPathProperty (γ ω))
    (ell : ℝ≥0) (hell : 0 < ell) (f : C(closedHalfPlane, ℂ))
    (hlaw : P.map (fun ω => ScaleTraceLaw.scalePath ell (γ ω)) = P.map γ)
    (p : ℂ → ℝ) (V : Set ℂ) (a : ℂ) (ε κ v c : ℝ) (R K : Set ℂ)
    (hK : IsClosed K) (hp : ContinuousOn p K) (hV : IsOpen V) (hVK : V ⊆ K) :
    P {ω | finiteBoundaryPath (f.comp (scaleClosed ell)) (γ ω) ∈ frontMassEvent p V a ε κ v c R} =
      P {ω | finiteBoundaryPath f (γ ω) ∈ frontMassEvent p V a ε κ v c R} := by
  let e := OrderIso.mulLeft₀ (ell ^ 2) (pow_pos hell 2)
  let E := frontMassEvent p V a ε κ v c R
  have hE : MeasurableSet E := measurableSet_frontMassEvent p V a ε κ v c R K hK hp hV hVK
  have hn := (measurable_finiteBoundaryPath (f.comp (scaleClosed ell))).comp hγ
  have hm := (measurable_clockPath e).comp ((measurable_finiteBoundaryPath f).comp hγ)
  calc
    _ = (P.map (fun ω => finiteBoundaryPath (f.comp (scaleClosed ell)) (γ ω))) E :=
      (Measure.map_apply hn hE).symm
    _ = (P.map (fun ω => clockPath e (finiteBoundaryPath f (γ ω)))) E := by
      rw [boundary_scale_path_law P γ hγ hclosed ell hell f hlaw]
    _ = P {ω | clockPath e (finiteBoundaryPath f (γ ω)) ∈ E} := Measure.map_apply hm hE
    _ = _ := by
      congr 1
      ext ω
      exact mem_frontMassEvent_clock e p V a ε κ v c R _

end SLEExactGauge.BoundaryScaleLaw

end

end OAI
