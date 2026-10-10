import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteOrbitalComplement

namespace OAI

/-! Moving the contracted electron from the first to the last coordinate
preserves occupation for an antisymmetric full-product wave function. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def lastTensorFiber {A : Type*} {n : ℕ} (f : (Fin (n+1) → A) → ℂ)
    (z : (Fin n → A) × A) : ℂ := f (Fin.snoc z.1 z.2)

theorem last_first_fiber_norm_integral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (ha : Coulomb.ProductAntisymmetric (μ := μ) f)
    (v : A → ℂ) :
    (∫ y, ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) =
    ∫ y, ‖Coulomb.fiberContract (μ := μ) v (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons (z : (Fin n → A) × A) : e.symm z = Fin.cons z.2 z.1 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm]
  have hp := (he.symm e).quasiMeasurePreserving.ae (ha Fin.revPerm)
  have hc : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ),
      ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) (y ∘ Fin.rev)‖^2 =
        ‖Coulomb.fiberContract (μ := μ) v (Coulomb.firstFiber f) y‖^2 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hp] with y hy
    have hcontract : Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) (y ∘ Fin.rev) =
        (((Fin.revPerm : Equiv.Perm (Fin (n+1))).sign : ℤ):ℂ)*
          Coulomb.fiberContract (μ := μ) v (Coulomb.firstFiber f) y := by
      unfold Coulomb.fiberContract
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hy] with z hz
      simp only [hcons] at hz
      change f (Fin.cons z y ∘ Fin.rev) = _ at hz
      rw [Fin.cons_comp_rev] at hz
      change star (v z)*f (Fin.snoc (y ∘ Fin.rev) z) =
        _*(star (v z)*f (Fin.cons z y))
      rw [hz]
      ring
    rw [hcontract,norm_mul,Coulomb.sign_complex_norm,one_mul]
  have hr := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) Fin.revPerm).integral_comp'
    (fun y => ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) y‖^2)
  have hrev (y : Fin n → A) :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => A) Fin.revPerm) y = y ∘ Fin.rev := by
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => A) Fin.revPerm y i.rev
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n => A) Fin.revPerm) y i.rev.rev = y i.rev at h
    simpa only [Fin.rev_rev,Function.comp_apply] using h
  simp only [hrev] at hr
  calc
    _ = ∫ y, ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) (y ∘ Fin.rev)‖^2
        ∂(Measure.pi fun _ : Fin n => μ) := hr.symm
    _ = _ := integral_congr_ae hc

end ContinuumCoulomb

end

end OAI
