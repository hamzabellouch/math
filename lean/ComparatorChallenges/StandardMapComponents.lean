import Mathlib

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace StandardMapEntropy

abbrev Circle := AddCircle (1 : ℝ)
abbrev Torus := Circle × Circle

lemma sine_periodic : Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 := by
  intro x
  dsimp only
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  exact Real.sin_add_two_pi _

noncomputable def sine (x : Circle) : ℝ := sine_periodic.lift x

noncomputable def standardMap (k : ℝ) (z : Torus) : Torus :=
  (z.1 + z.2 + (k * sine z.1 : ℝ), z.2 + (k * sine z.1 : ℝ))

noncomputable def area : Measure Torus :=
  (volume : Measure Circle).prod (volume : Measure Circle)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

lemma cosine_periodic : Function.Periodic (fun x : ℝ => Real.cos (2*Real.pi*x)) 1 := by
  intro x
  dsimp only
  rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring]
  exact Real.cos_add_two_pi _
noncomputable def cosine (x : Circle) : ℝ := cosine_periodic.lift x

noncomputable def torusPotential (k : ℝ) (x : Circle) : ℝ := 2+(2*Real.pi*k)*cosine x

noncomputable def transferStep (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨v*z.re-z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (((continuous_const.mul Complex.continuous_re).sub Complex.continuous_im).prodMk Complex.continuous_re) }

noncomputable def wedge (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

noncomputable def tangentCoordinates : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.re, z.re-z.im⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_re.prodMk (Complex.continuous_re.sub Complex.continuous_im)) }

local instance realTangentCompTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

noncomputable def standardDerivative (k : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp ((transferStep (torusPotential k z.1)).comp tangentCoordinates)

noncomputable def standardDerivativeProduct (k : ℝ) (z : Torus) (steps : ℕ) : ℂ →L[ℝ] ℂ :=
  Nat.rec (ContinuousLinearMap.id ℝ ℂ)
    (fun iteration product => (standardDerivative k ((standardMap k)^[iteration] z)).comp product) steps

def VectorGrowth (k : ℝ) (z : Torus) (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n v‖ / (n : ℝ))
    atTop (𝓝 l)

def LyapunovSpectrumAt (k : ℝ) (z : Torus) (l : ℝ) : Prop :=
  0 ≤ l ∧ ((l = 0 ∧ ∀ v : ℂ, v ≠ 0 → VectorGrowth k z v 0) ∨
    (0 < l ∧ ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 →
      VectorGrowth k z v (if wedge s v = 0 then -l else l)))

noncomputable def normalizedArea (E : Set Torus) : Measure Torus :=
  (area E)⁻¹ • area.restrict E

def IsBernoulli (f : Torus → Torus) (μ : Measure Torus) : Prop :=
  ∃ (β : Measure ℝ), IsProbabilityMeasure β ∧
    ∃ (encode : Torus → (ℤ → ℝ)) (decode : (ℤ → ℝ) → Torus),
      MeasurePreserving encode μ (MeasureTheory.Measure.infinitePi (fun _ : ℤ => β)) ∧
      MeasurePreserving decode (MeasureTheory.Measure.infinitePi (fun _ : ℤ => β)) μ ∧
      (∀ᵐ z ∂μ, decode (encode z) = z) ∧
      (∀ᵐ w ∂MeasureTheory.Measure.infinitePi (fun _ : ℤ => β), encode (decode w) = w) ∧
      (∀ᵐ z ∂μ, encode (f z) = fun i : ℤ => encode z (i+1))

def HyperbolicBernoulliComponent (k : ℝ) : Prop :=
  ∃ E : Set Torus, MeasurableSet E ∧ 0 < area E ∧
    ((standardMap k) ⁻¹' E =ᵐ[area] E) ∧
    Ergodic (standardMap k) (normalizedArea E) ∧
    (∀ᵐ z ∂normalizedArea E, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l) ∧
    ∃ (N : ℕ) (hN : 0 < N) (P : Fin N → Set Torus),
      (∀ j, MeasurableSet (P j)) ∧
      ((⋃ j, P j) =ᵐ[area] E) ∧
      (∀ i j, i ≠ j → area (P i ∩ P j) = 0) ∧
      (∀ j : Fin N, (standardMap k '' P j) =ᵐ[area]
        P ⟨(j.val+1)%N, Nat.mod_lt _ hN⟩) ∧
      (∀ j, area (P j) = area E / (N : ℝ≥0∞) ∧ 0 < area (P j)) ∧
      (∀ j, IsBernoulli ((standardMap k)^[N]) (normalizedArea (P j)))

def MainComponentsObligation : Prop :=
  ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k → HyperbolicBernoulliComponent k

theorem main_components : MainComponentsObligation := by
  sorry

end StandardMapEntropy

end OAI
