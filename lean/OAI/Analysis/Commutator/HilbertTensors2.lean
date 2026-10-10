import Mathlib
import OAI.Analysis.Commutator.HilbertTensors

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.PreHilbert

theorem pure_orthonormal (E : PreHilbert) {ι : Type*} (v : ι → E)
    (hv : Orthonormal ℂ v) (n : ℕ) :
    Orthonormal ℂ (fun b : Fin n → ι => pure E n (fun i => v (b i))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro b c
  rw [inner_pure]
  simp_rw [orthonormal_iff_ite.mp hv]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_const, Finset.prod_const_one]
  congr 1
  exact propext funext_iff.symm

abbrev hilbertPower (E : PreHilbert) (n : ℕ) := UniformSpace.Completion (power E n)

def hilbertPure (E : PreHilbert) (n : ℕ) (v : Fin n → E) : hilbertPower E n :=
  (pure E n v : UniformSpace.Completion (power E n))

@[simp] theorem norm_hilbertPure (E : PreHilbert) (n : ℕ) (v : Fin n → E) :
    ‖hilbertPure E n v‖ = ∏ i, ‖v i‖ := by
  rw [hilbertPure, UniformSpace.Completion.norm_coe, norm_pure]

@[simp] theorem inner_hilbertPure (E : PreHilbert) (n : ℕ) (v w : Fin n → E) :
    inner ℂ (hilbertPure E n v) (hilbertPure E n w) = ∏ i, inner ℂ (v i) (w i) := by
  rw [hilbertPure, hilbertPure, UniformSpace.Completion.inner_coe, inner_pure]

theorem hilbertPure_orthonormal (E : PreHilbert) {ι : Type*} (v : ι → E)
    (hv : Orthonormal ℂ v) (n : ℕ) :
    Orthonormal ℂ (fun b : Fin n → ι => hilbertPure E n (fun i => v (b i))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro b c
  rw [hilbertPure, hilbertPure, UniformSpace.Completion.inner_coe]
  exact orthonormal_iff_ite.mp (pure_orthonormal E v hv n) b c

end Kadison.PreHilbert
end

end OAI
