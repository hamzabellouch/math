import OAI.Probability.ClassicalON.WeightedTilt

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory
namespace ClassicalON

def LogSupermodular {X : Type uX} [Lattice X] (w : X → ℝ) : Prop :=
  ∀ x y,w x*w y≤w (x⊓y)*w (x⊔y)

def ContinuousFKG {X : Type uX} [Lattice X] [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∀ w : X → ℝ,Continuous w → (∀ x,0<w x) → LogSupermodular w → ContinuousAssociated μ w

section Lattice
variable {X : Type uX} {Y : Type uY} [Lattice X] [LinearOrder Y]

theorem logSupermodular_slice {w : Y×X → ℝ} (h : LogSupermodular w) (y : Y) :
    LogSupermodular (fun x => w (y,x)) := by
  intro u v
  simpa only [Prod.inf_def,Prod.sup_def,inf_idem,sup_idem] using h (y,u) (y,v)

theorem logSupermodular_ratio_monotone {w : Y×X → ℝ} (h : LogSupermodular w)
    (hp : ∀ p,0<w p) {s t : Y} (hst : s≤t) :
    Monotone (fun x => w (t,x)/w (s,x)) := by
  intro u v huv
  have hh := h (t,u) (s,v)
  simp only [Prod.inf_def,Prod.sup_def,inf_eq_right.mpr hst,inf_eq_left.mpr huv,
    sup_eq_left.mpr hst,sup_eq_right.mpr huv] at hh
  exact (div_le_div_iff₀ (hp (s,u)) (hp (s,v))).2 (by nlinarith)

end Lattice

section Product
variable {X : Type uX} {Y : Type uY} [Lattice X] [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [LinearOrder Y] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [FirstCountableTopology Y] [LocallyCompactSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [SecondCountableTopology X] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [FirstCountableTopology Y]
  [LocallyCompactSpace Y] in
theorem conditionalMean_monotone (hX : ContinuousFKG μ) {w f : Y×X → ℝ}
    (hw : Continuous w) (hp : ∀ p,0<w p) (hLS : LogSupermodular w)
    (hf : Continuous f) (hfn : ∀ p,0≤f p) (hfm : Monotone f) :
    Monotone (conditionalMean μ w f) := by
  intro s t hst
  have hs : ContinuousAssociated μ (fun x => w (s,x)) :=
    hX _ (by fun_prop) (fun x => hp (s,x)) (logSupermodular_slice hLS s)
  calc
    conditionalMean μ w f s ≤ weightedMean μ (fun x => w (t,x)) (fun x => f (s,x)) := by
      apply weightedMean_tilt_mono (by fun_prop) (by fun_prop)
        (fun x => hp (s,x)) (fun x => hp (t,x)) hs (by fun_prop) (fun x => hfn (s,x))
      · exact fun u v huv => hfm ⟨le_rfl,huv⟩
      · exact logSupermodular_ratio_monotone hLS hp hst
    _ ≤ conditionalMean μ w f t := by
      apply weightedMean_mono (by fun_prop) (fun x => hp (t,x)) (by fun_prop) (by fun_prop)
      exact fun x => hfm ⟨hst,le_rfl⟩

theorem continuousFKG_prod (hX : ContinuousFKG μ) : ContinuousFKG (ν.prod μ) := by
  intro w hw hp hLS f g hf hg hfn hgn hfm hgm
  let m := marginalWeight μ w
  let F := conditionalMean μ w f
  let H := conditionalMean μ w g
  let J := conditionalMean μ w (fun p => f p*g p)
  have hmc : Continuous m := marginalWeight_continuous μ hw
  have hmp : ∀ y,0 < m y := marginalWeight_pos μ hw hp
  have hFc : Continuous F := conditionalMean_continuous μ hw hf hp
  have hHc : Continuous H := conditionalMean_continuous μ hw hg hp
  have hJc : Continuous J := conditionalMean_continuous μ hw (hf.mul hg) hp
  have hFn : ∀ y,0≤F y := fun y => weightedMean_nonneg (by fun_prop)
    (fun x => hp (y,x)) (fun x => hfn (y,x))
  have hHn : ∀ y,0≤H y := fun y => weightedMean_nonneg (by fun_prop)
    (fun x => hp (y,x)) (fun x => hgn (y,x))
  have hFm : Monotone F := conditionalMean_monotone hX hw hp hLS hf hfn hfm
  have hHm : Monotone H := conditionalMean_monotone hX hw hp hLS hg hgn hgm
  have hpoint : ∀ y,F y*H y≤J y := by
    intro y
    exact hX _ (show Continuous (fun x => w (y,x)) from by fun_prop) (fun x => hp (y,x))
      (logSupermodular_slice hLS y) _ _ (by fun_prop) (by fun_prop)
      (fun x => hfn (y,x)) (fun x => hgn (y,x))
      (fun u v huv => hfm ⟨le_rfl,huv⟩) (fun u v huv => hgm ⟨le_rfl,huv⟩)
  rw [weightedMean_prod μ ν hw hf hp,weightedMean_prod μ ν hw hg hp,
    weightedMean_prod μ ν hw (show Continuous (fun p => f p*g p) from hf.mul hg) hp]
  exact ((continuousAssociated_chain ν m hmc hmp) F H hFc hHc hFn hHn hFm hHm).trans
    (weightedMean_mono hmc hmp (hFc.mul hHc) hJc hpoint)

end Product
end ClassicalON

end

end OAI
