import Mathlib
import OAI.Probability.LogConcave.Dynamics.NormSubSqThree
import OAI.Probability.LogConcave.Dynamics.SameLaw
import OAI.Probability.LogConcave.Dynamics.SharedLipschitz

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function TopologicalSpace
open scoped Classical

variable {X Ω : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] [MeasurableSpace Ω]
  {d : ℕ}

theorem SquaredAt.noisy_circuit (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : X → Ω → Point d) (g u : X → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable g) (hu : Measurable u)
    (ρ : X → ℝ) (hρ : ∀x,1≤ρ x) (hρlip : ∀x y,ρ y≤ρ x+dist x y)
    (hρi : Integrable (fun x => (ρ x)^2) μ)
    {Lf Lg E R n : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (hE : 0<E)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y,‖g x-g y‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt ν (stdGaussian (Point d)) (f x)
      (fun w => g x+n • w) (E^2*(ρ x)^2))
    (hi : Integrable (fun x => ‖g x-u x‖^2) μ)
    (he : (∫x,‖g x-u x‖^2 ∂μ)≤R) :
    SquaredAt (μ.prod ν) (μ.prod (stdGaussian (Point d))) (uncurry f)
      (fun z => u z.1+n • z.2) (20*E^2*(∫x,(ρ x)^2 ∂μ)+2*R) := by
  have hnmeas : Measurable (fun z : X × Point d => g z.1+n • z.2) := by fun_prop
  have hc' := SquaredAt.random_anchor μ ν (stdGaussian (Point d)) f
    (fun x w => g x+n • w) hf hnmeas ρ hρ hρlip hρi hLf hLg hE hfl
    (fun x y w => by simpa only [add_sub_add_right_eq_sub] using hgl x y) hc
  have hbase := SquaredAt.same_tape μ g u hg hu hi he
  have hnoise := hbase.add_shared (stdGaussian (Point d)) hg hu (fun w => n • w) (by fun_prop)
  have ht := hc'.trans hf hnmeas (by fun_prop) hnoise
  convert ht using 1
  ring

theorem SquaredAt.noisy_circuit_target {Γ : Type*} [MeasurableSpace Γ]
    [StandardBorelSpace Γ] [Nonempty Γ]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (θ : Measure Γ) [IsProbabilityMeasure θ]
    (f : X → Ω → Point d) (g u : X → Point d) (v : Γ → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable g) (hu : Measurable u) (hv : Measurable v)
    (ρ : X → ℝ) (hρ : ∀x,1≤ρ x) (hρlip : ∀x y,ρ y≤ρ x+dist x y)
    (hρi : Integrable (fun x => (ρ x)^2) μ)
    {Lf Lg E R n : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (hE : 0<E)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y,‖g x-g y‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt ν (stdGaussian (Point d)) (f x)
      (fun w => g x+n • w) (E^2*(ρ x)^2))
    (hi : Integrable (fun x => ‖g x-u x‖^2) μ) (he : (∫x,‖g x-u x‖^2 ∂μ)≤R)
    (hlaw : (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+n • z.2)=θ.map v) :
    SquaredAt (μ.prod ν) θ (uncurry f) v (40*E^2*(∫x,(ρ x)^2 ∂μ)+4*R) := by
  have hh := (SquaredAt.noisy_circuit μ ν f g u hf hg hu ρ hρ hρlip hρi
    hLf hLg hE hfl hgl hc hi he).change_ideal θ v hf (by fun_prop) hv hlaw
  convert hh using 1
  ring
end LogConcaveSampling.Coupling

end

end

end OAI
