import OAI.Geometry.SingularHomology.HomologyTransfer

namespace OAI

noncomputable section

open scoped ContinuousMap

namespace Problem340

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def realHomologyHomotopyEquiv (n : ℕ) (e : X ≃ₕ Y) :
    RealSingularHomology n X ≃ₗ[ℝ] RealSingularHomology n Y where
  toLinearMap := realHomologyMap n e e.continuous
  invFun := realHomologyMap n e.symm e.symm.continuous
  left_inv x := by
    have h : realHomologyMap n (e.symm ∘ e) (e.symm.continuous.comp e.continuous) =
        LinearMap.id := by
      calc
        _ = realHomologyMap n id continuous_id :=
          realHomologyMap_eq_of_homotopic n _ _ e.left_inv
        _ = LinearMap.id := realHomologyMap_id n
    rw [realHomologyMap_comp] at h
    exact congrArg (fun A => A x) h
  right_inv y := by
    have h : realHomologyMap n (e ∘ e.symm) (e.continuous.comp e.symm.continuous) =
        LinearMap.id := by
      calc
        _ = realHomologyMap n id continuous_id :=
          realHomologyMap_eq_of_homotopic n _ _ e.right_inv
        _ = LinearMap.id := realHomologyMap_id n
    rw [realHomologyMap_comp] at h
    exact congrArg (fun A => A y) h

@[simp] theorem realHomologyHomotopyEquiv_apply (n : ℕ) (e : X ≃ₕ Y)
    (x : RealSingularHomology n X) :
    realHomologyHomotopyEquiv n e x = realHomologyMap n e e.continuous x := rfl

@[simp] theorem realHomologyHomotopyEquiv_symm_apply (n : ℕ) (e : X ≃ₕ Y)
    (y : RealSingularHomology n Y) :
    (realHomologyHomotopyEquiv n e).symm y =
      realHomologyMap n e.symm e.symm.continuous y := rfl

theorem realHomologyHomotopyEquiv_naturality (n : ℕ) (e : X ≃ₕ Y)
    (f : X → X) (g : Y → Y) (hf : Continuous f) (hg : Continuous g)
    (H : (continuousMapOf (e ∘ f) (e.continuous.comp hf)).Homotopic
      (continuousMapOf (g ∘ e) (hg.comp e.continuous)))
    (x : RealSingularHomology n X) :
    realHomologyHomotopyEquiv n e (realHomologyMap n f hf x) =
      realHomologyMap n g hg (realHomologyHomotopyEquiv n e x) := by
  have h := realHomologyMap_eq_of_homotopic n _ _ H
  rw [realHomologyMap_comp, realHomologyMap_comp] at h
  exact congrArg (fun A => A x) h

abbrev realHomologyEquivOfHomotopyEquiv (n : ℕ) (e : X ≃ₕ Y) :=
  realHomologyHomotopyEquiv n e

@[simp] theorem realHomologyEquivOfHomotopyEquiv_apply (n : ℕ) (e : X ≃ₕ Y)
    (v : RealSingularHomology n X) :
    realHomologyEquivOfHomotopyEquiv n e v = realHomologyMap n e e.continuous v := rfl

@[simp] theorem realHomologyEquivOfHomotopyEquiv_symm_apply (n : ℕ) (e : X ≃ₕ Y)
    (v : RealSingularHomology n Y) :
    (realHomologyEquivOfHomotopyEquiv n e).symm v =
      realHomologyMap n e.symm e.symm.continuous v := rfl

end Problem340

end

end OAI
