import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MildScalarMild

namespace OAI

noncomputable section
namespace VelocityDetection.MildScalar
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open TailSpace.Jets WeakVolterra

structure SupportedData where
  scalar : ScalarField 2
  smooth : ContDiff ℝ ∞ (uncurry scalar)
  support : TailSpace.LocalHorizontalSupport scalar

end VelocityDetection.MildScalar
end

noncomputable section
namespace VelocityDetection.MildScalar.SupportedData
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open TailSpace.Jets WeakVolterra

def jets (d : SupportedData) (a : ℕ) (t : ℝ) : E a :=
  ofSupportedCurve a d.smooth d.support t

@[simp] theorem jets_value (d : SupportedData) (a : ℕ) (t : ℝ) :
    value (d.jets a t) = d.scalar t := rfl

theorem continuous_jets (d : SupportedData) (a : ℕ) : Continuous (d.jets a) :=
  continuous_ofSupportedCurve a d.smooth d.support

@[simp] theorem restrict_jets (d : SupportedData) {a b : ℕ} (hab : a ≤ b) (t : ℝ) :
    restrict hab (d.jets b t) = d.jets a t :=
  restrict_ofSupportedCurve hab d.smooth d.support t

def curve (d : SupportedData) (T : ℝ) (a : ℕ) : TimeCurve T a :=
  ⟨fun t => d.jets a t.val, (d.continuous_jets a).comp continuous_subtype_val⟩

@[simp] theorem curve_apply (d : SupportedData) (T : ℝ) (a : ℕ) (t : Icc (0 : ℝ) T) :
    d.curve T a t = d.jets a t.val := rfl

@[simp] theorem lower_curve (d : SupportedData) (T : ℝ) {a b : ℕ} (hab : a ≤ b) :
    lowerCurve hab (d.curve T b) = d.curve T a := by
  apply ContinuousMap.ext
  intro t
  exact d.restrict_jets hab t.val

@[simp] theorem short_curve (d : SupportedData) {S T : ℝ} (hST : S ≤ T) (a : ℕ) :
    shortCurve hST (d.curve T a) = d.curve S a := rfl

end VelocityDetection.MildScalar.SupportedData
end

noncomputable section
namespace VelocityDetection.MildScalar
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open TailSpace.Jets WeakVolterra
variable {ν : ℝ} (hν : 0 < ν) (W : Fin 2 → SupportedData) (g : SupportedData)

def finiteSolution {T : ℝ} (hT : 0 ≤ T) (a : ℕ) : TimeCurve T a :=
  evolution hT hν (fun i => (W i).curve T a) (g.curve T a)

@[simp] theorem lower_finiteSolution {T : ℝ} (hT : 0 ≤ T) {a b : ℕ} (hab : a ≤ b) :
    lowerCurve hab (finiteSolution hν W g hT b) = finiteSolution hν W g hT a := by
  simp only [finiteSolution, lower_evolution, SupportedData.lower_curve]

@[simp] theorem short_finiteSolution {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S ≤ T) (a : ℕ) :
    shortCurve hST (finiteSolution hν W g hT a) = finiteSolution hν W g hS a := by
  have hh := short_evolution hS hT hST hν (fun i => (W i).curve T a) (g.curve T a)
  simpa only [finiteSolution, SupportedData.short_curve] using hh

theorem finiteSolution_agree {S T t : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (htS : t ∈ Icc 0 S) (htT : t ∈ Icc 0 T) (a : ℕ) :
    finiteSolution hν W g hS a ⟨t,htS⟩ = finiteSolution hν W g hT a ⟨t,htT⟩ := by
  rcases le_total S T with hST | hTS
  · have hh := congrArg (fun q : TimeCurve S a => q ⟨t,htS⟩)
      (short_finiteSolution hν W g hS hT hST a)
    exact hh.symm
  · have hh := congrArg (fun q : TimeCurve T a => q ⟨t,htT⟩)
      (short_finiteSolution hν W g hT hS hTS a)
    exact hh

def globalJets (a : ℕ) (t : ℝ) : E a :=
  finiteSolution hν W g (show 0 ≤ max t 0 + 1 by positivity) a
    ⟨max t 0, le_max_right _ _, by linarith⟩

theorem globalJets_eq_finite {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (a : ℕ) :
    globalJets hν W g a t = finiteSolution hν W g hT a ⟨t,ht⟩ := by
  have hh := finiteSolution_agree hν W g
    (show 0 ≤ max t 0 + 1 by positivity) hT
    (show max t 0 ∈ Icc 0 (max t 0 + 1) from ⟨le_max_right _ _, by linarith⟩)
    (show max t 0 ∈ Icc 0 T by simpa only [max_eq_left ht.1] using ht) a
  simpa only [globalJets, max_eq_left ht.1] using hh

@[simp] theorem restrict_globalJets {a b : ℕ} (hab : a ≤ b) (t : ℝ) :
    restrict hab (globalJets hν W g b t) = globalJets hν W g a t := by
  exact congrArg (fun q => q ⟨max t 0, le_max_right _ _, by linarith⟩)
    (lower_finiteSolution hν W g (show 0 ≤ max t 0 + 1 by positivity) hab)

theorem continuousOn_globalJets (a : ℕ) : ContinuousOn (globalJets hν W g a) (Ici (0 : ℝ)) := by
  intro t ht
  change 0 ≤ t at ht
  let T := t + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [ht]
  have hn : Iio T ∈ 𝓝 t := Iio_mem_nhds (by dsimp [T]; linarith)
  have he : globalJets hν W g a =ᶠ[𝓝[Ici (0 : ℝ)] t]
      extend hT (finiteSolution hν W g hT a) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with r hr hTr
    rw [globalJets_eq_finite hν W g hT ⟨hr, le_of_lt hTr⟩,
      extend_of_mem hT _ ⟨hr, le_of_lt hTr⟩]
  apply (continuous_extend hT (finiteSolution hν W g hT a)).continuousWithinAt.congr_of_eventuallyEq
    he ?_
  rw [globalJets_eq_finite hν W g hT ⟨ht, by dsimp [T]; linarith⟩,
    extend_of_mem hT _ ⟨ht, by dsimp [T]; linarith⟩]

def scalar : ScalarField 2 := fun t => value (globalJets hν W g 0 t)

theorem value_globalJets (a : ℕ) (t : ℝ) :
    value (globalJets hν W g a t) = scalar hν W g t := by
  have hh := congrArg value (restrict_globalJets hν W g (Nat.zero_le a) t)
  exact hh

theorem contDiff_scalar_space (t : ℝ) : ContDiff ℝ ∞ (scalar hν W g t) := by
  rw [contDiff_infty]
  intro a
  rw [← value_globalJets hν W g a t]
  exact contDiff_value _

end VelocityDetection.MildScalar
end

end OAI
