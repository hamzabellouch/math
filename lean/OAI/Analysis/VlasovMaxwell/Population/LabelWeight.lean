import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ActualLabelCutoffCost

namespace OAI

noncomputable section

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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def labelWeight (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : ℝ :=
  ψ (labelReceiverTime α zX T p)*labelSelectedCutoff α zX T Q p

def selectedLabelSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : Vec :=
  labelWeight α zX T Q ψ p • actualLabelSignedForce s α zX T p

def selectedLabelCosts (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : Vec :=
  labelWeight α zX T Q (deriv ψ) p • actualLabelRatePrimitive s α zX T p +
    ψ (labelReceiverTime α zX T p) • actualLabelCutoffCost s α zX T Q p +
      labelWeight α zX T Q ψ p • actualLabelRemainder s α zX T p

lemma PhaseFlowOn.labelWeight_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} (hψ : Measurable ψ) :
    Measurable (labelWeight F.flow zX T Q ψ) :=
  (hψ.comp (F.labelReceiverTime_measurable zX)).mul (F.selectedCutoff_measurable zX Q)

lemma PhaseFlowOn.labelWeight_bound {E B : Field} {T C : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} (hψ : ∀t∈Icc 0 T,|ψ t|≤C) (p : ℝ×Phase) :
    |labelWeight F.flow zX T Q ψ p|≤C := by
  rw [labelWeight,abs_mul]
  exact (mul_le_mul_of_nonneg_left (F.labelSelectedCutoff_bound zX Q p) (abs_nonneg _)).trans
    (by simpa only [mul_one] using hψ _ (F.labelReceiverTime_mem hT zX p))

lemma PhaseFlowOn.selectedLabelSignedForce_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} (hψ : Measurable ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) :
    Integrable (selectedLabelSignedForce s F.flow zX T Q ψ) := by
  apply (F.actualLabelSignedForce_integrable hs zX).bdd_smul 1
    (F.labelWeight_measurable zX Q hψ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p=>by
    simpa only [Real.norm_eq_abs] using F.labelWeight_bound hT zX Q hψb p)

lemma PhaseFlowOn.selectedLabelCosts_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) :
    Integrable (selectedLabelCosts s F.flow zX T Q ψ) := by
  have hd : ∀t∈Icc 0 T,|deriv ψ t|≤(L:ℝ) := fun t _=>by
    simpa only [Real.norm_eq_abs] using
      norm_deriv_le_of_lipschitzOn (x₀:=t) (s:=univ) Filter.univ_mem hψ.lipschitzOnWith
  have hi₁ := (F.actualLabelRatePrimitive_integrable hs zX).bdd_smul (L:ℝ)
    (F.labelWeight_measurable zX Q (measurable_deriv ψ)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p=>by
      simpa only [Real.norm_eq_abs] using F.labelWeight_bound hT zX Q hd p))
  have hi₂ := (F.actualLabelCutoffCost_integrable hs zX Q).bdd_smul 1
    (hψ.continuous.measurable.comp (F.labelReceiverTime_measurable zX)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p=>by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using hψb _ (F.labelReceiverTime_mem hT zX p)))
  have hi₃ := (F.actualLabelRemainder_integrable hs zX).bdd_smul 1
    (F.labelWeight_measurable zX Q hψ.continuous.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p=>by
      simpa only [Real.norm_eq_abs] using F.labelWeight_bound hT zX Q hψb p))
  exact (hi₁.add hi₂).add hi₃

lemma initialSignedBoundary_velocity_lintegral_bound {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (x w : Vec) (t ψ M : ℝ) (χ : Vec→ℝ)
      (P : Vec→L[ℝ]Vec) (n : Vec), 0≤t → (∀ v,χ v∈Icc (0:ℝ) 1) →
      ‖P‖≤M → ‖n‖=1 →
      (∫⁻ v : Vec, ENNReal.ofReal ‖initialSignedBoundaryDensity f x w t ψ (χ v) P n v‖)
        ≤ ENNReal.ofReal (C*t*|ψ| *M) := by
  obtain ⟨C,hC,hbound⟩ := datum_reciprocal_cone_bound hf hc
  refine ⟨4*C,by positivity,?_⟩
  intro x w t ψ M χ P n ht hχ hP hn
  have hM : 0≤M := (norm_nonneg P).trans hP
  obtain ⟨hgi,hgb⟩ := hbound (x-t • n) n hn
  have hgn (v : Vec) : 0≤f (x-t • n,v)/(1-dot n (velocity v)) :=
    div_nonneg (hpos _) (cone_denom_pos v n hn).le
  calc
    _ ≤ ∫⁻ v : Vec, ENNReal.ofReal
        ((4*t*|ψ| *M)*(f (x-t • n,v)/(1-dot n (velocity v)))) := by
      apply lintegral_mono
      intro v
      exact ENNReal.ofReal_le_ofReal (initialSignedBoundaryDensity_norm f hpos x w ht (hχ v) ψ P hP n v hn)
    _ = ENNReal.ofReal (∫ v : Vec,
        (4*t*|ψ| *M)*(f (x-t • n,v)/(1-dot n (velocity v)))) :=
      (ofReal_integral_eq_lintegral_ofReal (hgi.const_mul _)
        (ae_of_all _ (fun v=>mul_nonneg (by positivity) (hgn v)))).symm
    _ ≤ ENNReal.ofReal ((4*C)*t*|ψ| *M) := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul]
      nlinarith [mul_le_mul_of_nonneg_left hgb (show 0≤4*t*|ψ| *M by positivity)]

lemma initialSignedBoundary_lintegral_bound {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (T M : ℝ) (J : Set ℝ) (X V : ℝ→Vec)
      (ψ : ℝ→ℝ) (χ : ℝ→Sphere→Vec→ℝ) (P : ℝ→Vec→L[ℝ]Vec),
      0≤T → 0≤M → MeasurableSet J → J⊆Icc 0 T → IntegrableOn ψ J →
      (∀ t∈J,∀ n v,χ t n v∈Icc (0:ℝ) 1) → (∀ t∈J,‖P t‖≤M) →
      (∫⁻ t in J,∫⁻ n : Sphere,∫⁻ v : Vec,
        ENNReal.ofReal ‖initialSignedBoundaryDensity f (X t) (V t) t (ψ t)
          (χ t n v) (P t) n.1 v‖ ∂volume ∂sphereMeasure)
        ≤ ENNReal.ofReal (C*T*M*(∫ t in J,|ψ t|)) := by
  obtain ⟨C,hC,hb⟩ := initialSignedBoundary_velocity_lintegral_bound hf hc hpos
  refine ⟨C*(4*Real.pi),by positivity,?_⟩
  intro T M J X V ψ χ P hT hM hJ hJT hψ hχ hP
  calc
    _ ≤ ∫⁻ t in J, ∫⁻ _n : Sphere, ENNReal.ofReal (C*t*|ψ t| *M) ∂sphereMeasure := by
      apply setLIntegral_mono' hJ
      intro t ht
      apply lintegral_mono
      intro n
      exact hb (X t) (V t) t (ψ t) M (χ t n) (P t) n.1 (hJT ht).1 (hχ t ht n) (hP t ht) (sphere_norm n)
    _ = ∫⁻ t in J, ENNReal.ofReal (C*t*|ψ t| *M*(4*Real.pi)) := by
      apply setLIntegral_congr_fun hJ
      intro t ht
      have ht0 := (hJT ht).1
      dsimp only
      rw [lintegral_const, ← ofReal_measureReal, sphere_area, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ∫⁻ t in J, ENNReal.ofReal ((C*(4*Real.pi)*T*M)*|ψ t|) := by
      apply setLIntegral_mono' hJ
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_right (hJT ht).2
        (show 0≤C*|ψ t| *M*(4*Real.pi) by positivity)]
    _ = ENNReal.ofReal ((C*(4*Real.pi))*T*M*(∫ t in J,|ψ t|)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hψ.abs.const_mul _)
        (ae_of_all _ (fun t=>by positivity)), integral_const_mul]

end RVM

end

end OAI
