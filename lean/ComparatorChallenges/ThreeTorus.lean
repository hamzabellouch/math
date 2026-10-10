import Mathlib

namespace OAI

/-!
The torus is (ℝ/ℤ)³ with normalized product Haar measure. Smoothness means
local smooth lifts on the universal cover, for both the map and its inverse.

The almost-everywhere graph conditions are independent of representatives of
L² classes. The real generator's bilateral Koopman orbit spans the entire
complex mean-zero L² space. The spectral model is the full circle L² space
with multiplication by the first Fourier character.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

abbrev Torus := Fin 3 → UnitAddCircle
abbrev Cover := Fin 3 → ℝ

def project (x : Cover) : Torus := fun i => (x i : UnitAddCircle)

def Smooth (T : Torus → Torus) : Prop :=
  ∀ x : Cover, ∃ U : Set Cover, IsOpen U ∧ x ∈ U ∧
    ∃ F : Cover → Cover, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
      ∀ y ∈ U, T (project y) = project (F y)

def μ : Measure Torus := Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

abbrev H : Type := Lp ℂ 2 μ

/-- The full complex subspace defined by zero Lebesgue integral. -/
def meanZero : Submodule ℂ H where
  carrier := {f | ∫ x, f x ∂μ = 0}
  zero_mem' := by
    change ∫ x, (0 : H) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_zero ℂ 2 μ)]
    simp
  add_mem' := by
    intro f g hf hg
    change ∫ x, (f + g) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_add f g)]
    change ∫ x, f x + g x ∂μ = 0
    rw [integral_add (MemLp.integrable (by norm_num) (Lp.memLp f))
      (MemLp.integrable (by norm_num) (Lp.memLp g))]
    change (∫ x, f x ∂μ) + (∫ x, g x ∂μ) = 0
    rw [show ∫ x, f x ∂μ = 0 from hf, show ∫ x, g x ∂μ = 0 from hg, add_zero]
  smul_mem' := by
    intro c f hf
    change ∫ x, (c • f) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_smul c f)]
    change ∫ x, c • f x ∂μ = 0
    rw [integral_smul]
    rw [show ∫ x, f x ∂μ = 0 from hf, smul_zero]

abbrev H₀ := ↥meanZero
abbrev CircleH : Type := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

def IsReal (f : H₀) : Prop := ∀ᵐ x ∂μ, (f.1 x).im = 0

/-- Complete simple Lebesgue spectrum, including the stated consequences. -/
def MainConclusion : Prop :=
  ∃ T : Equiv.Perm Torus,
    Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ ∧
    ∃ f : H₀, IsReal f ∧
    ∃ v : ℤ → H₀,
      (∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T ^ n) x)) ∧
      Orthonormal ℂ v ∧
      Dense (Submodule.span ℂ (Set.range v) : Set H₀) ∧
      Ergodic T μ ∧
      ∃ W : H₀ ≃ₗᵢ[ℂ] CircleH,
        ∀ g : H₀, ∃ h : H₀,
          (∀ᵐ x ∂μ, h.1 x = g.1 (T x)) ∧
          (∀ᵐ z ∂(AddCircle.haarAddCircle (T := (1 : ℝ))),
            W h z = fourier 1 z * W g z)

theorem simple_lebesgue_spectrum : MainConclusion := by
  sorry

end ThreeTorus

end

end OAI
