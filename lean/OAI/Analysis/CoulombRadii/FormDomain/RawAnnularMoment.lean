import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalLikelihoodBridge

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma raw_second_moment_asH1 {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {S : Set Position} (hS : MeasurableSet S) :
    (∫ x,(rawCount S x)^2 ∂rawLaw ψ)=
      Coulomb.localCountSecondMoment (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) S := by
  rw [integral_rawLaw hd.2.2.1,rawExpectation_eq_stateWeightedIntegral hd.2.2.1
    ((measurable_rawCount hS).pow_const 2) (C:=(n:ℝ)^2) (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (rawCount_nonneg S x) (rawCount_le_number S x) 2)]
  have H := asH1_potentialForm ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    (fun x => (Coulomb.localCount S x)^2)
  exact H.symm

lemma atomic_raw_annular_second_moment {α β : ℝ} (hα : 0<α) (hαβ : α<β) :
    ∃ C : ℝ,0≤C ∧ ∀ {n : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    ∀ {E D : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → 0≤D → ∀ {r : ℝ},0<r →
    (∫ x,(rawCount {y : Position | α*r<‖y‖ ∧ ‖y‖<β*r} x)^2 ∂rawLaw ψ)≤
      C*(Coulomb.screenMass D r)^2 := by
  obtain ⟨C,hC,HC⟩ := Coulomb.atomic_annular_second_moment hα hαβ
  refine ⟨C,hC,?_⟩
  intro n Z hZ ψ g hd hn E D hE he hD r hr
  have hS : MeasurableSet {y : Position | α*r<‖y‖ ∧ ‖y‖<β*r} :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  rw [raw_second_moment_asH1 hd hS]
  apply HC (Coulomb.atom Z hZ) (fun _ => rfl) _ (asH1_antisymmetric hd)
    ((asH1_mass ..).trans hn) hE _ hD hr
  rwa [asH1_energy Z hZ]

lemma packet_shell_center {g : Position → ℝ} (hg : ∀ x,1<‖x‖ → g x=0)
    {c r₀ s r : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (hrr : r₀≤r)
    (hq : c*s^packetExponent≤1/4) {z y : Position}
    (hy : r≤‖y‖ ∧ ‖y‖<2*r) (hK : packetKernel g c r₀ s z y≠0) :
    r/2<‖z‖ ∧ ‖z‖<4*r := by
  have hr : 0<r := hr₀.trans_le hrr
  by_cases hz : r₀≤‖z‖
  · have H := packetKernel_relative_support g hg hc hr₀ hs z y hz hK
    have hn := norm_nonneg z
    constructor <;> nlinarith
  · have hd := (packetKernel_support g hg hc hr₀ hs z y hK).trans
      (packetWidth_le c r₀ s hc.le hr₀ hs z)
    rw [max_eq_right (le_of_not_ge hz)] at hd
    have hdiff := norm_sub_norm_le y z
    have hq' := mul_le_mul_of_nonneg_right hq hr₀.le
    constructor <;> nlinarith [norm_nonneg z]
end NeutralAtom
end

end

end OAI
