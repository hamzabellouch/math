import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorState

namespace OAI

/-! The all-orbital tensor projection and its genuine H1 remainder have
orthogonal L2 values. In particular their masses add exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem h1_toHilbert_add {n : ℕ} (u w : Coulomb.H1Vector n) :
    (u.add w).toHilbert = u.toHilbert+w.toHilbert := by
  apply PiLp.ext
  intro s
  rfl

theorem h1_toHilbert_scale {n : ℕ} (u : Coulomb.H1Vector n) (c : ℂ) :
    (Coulomb.H1Vector.scale c u).toHilbert = c • u.toHilbert := by
  apply PiLp.ext
  intro s
  rfl

def finiteTensorRemainder {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) : Coulomb.H1Vector n :=
  u.add (Coulomb.H1Vector.scale (-1) (finiteTensorProjection v hv hL2 hpartial u))

theorem finiteTensorRemainder_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) :
    (finiteTensorRemainder v hv hL2 hpartial u).toHilbert =
      u.toHilbert-(finiteTensorProjection v hv hL2 hpartial u).toHilbert := by
  simp only [finiteTensorRemainder,h1_toHilbert_add,h1_toHilbert_scale,neg_smul,one_smul,sub_eq_add_neg]

theorem finiteTensorRemainder_orthogonal {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t)*v c y t) =
      if a = c then (1:ℂ) else 0) (u : Coulomb.H1Vector n) (p : Fin n → α) :
    inner ℂ (Coulomb.tensorHilbert v hL2 p)
      (finiteTensorRemainder v hv hL2 hpartial u).toHilbert = 0 := by
  rw [finiteTensorRemainder_toHilbert,inner_sub_right,
    ← Coulomb.orbitalCoefficient_eq_inner u v hL2,
    ← Coulomb.orbitalCoefficient_eq_inner (finiteTensorProjection v hv hL2 hpartial u) v hL2,
    finiteTensorProjection_coefficients v hv hL2 hpartial ho u p,sub_self]

theorem finiteTensorProjection_mass_decomposition {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t)*v c y t) =
      if a = c then (1:ℂ) else 0) (u : Coulomb.H1Vector n) :
    Coulomb.mass u = Coulomb.mass (finiteTensorProjection v hv hL2 hpartial u)+
      Coulomb.mass (finiteTensorRemainder v hv hL2 hpartial u) := by
  have hi : inner ℂ (finiteTensorProjection v hv hL2 hpartial u).toHilbert
      (finiteTensorRemainder v hv hL2 hpartial u).toHilbert = 0 := by
    rw [finiteTensorProjection_toHilbert,sum_inner]
    simp only [inner_smul_left,finiteTensorRemainder_orthogonal v hv hL2 hpartial ho u,
      mul_zero,Finset.sum_const_zero]
  have hs : u.toHilbert = (finiteTensorProjection v hv hL2 hpartial u).toHilbert+
      (finiteTensorRemainder v hv hL2 hpartial u).toHilbert := by
    rw [finiteTensorRemainder_toHilbert]
    abel
  rw [← Coulomb.H1Vector.toHilbert_norm_sq u,
    ← Coulomb.H1Vector.toHilbert_norm_sq (finiteTensorProjection v hv hL2 hpartial u),
    ← Coulomb.H1Vector.toHilbert_norm_sq (finiteTensorRemainder v hv hL2 hpartial u),hs]
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi

theorem finiteTensorProjection_antisymmetric {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) (hu : Coulomb.Antisymmetric u) :
    Coulomb.Antisymmetric (finiteTensorProjection v hv hL2 hpartial u) := by
  intro p s
  filter_upwards [] with x
  change (∑ b, Coulomb.orbitalCoefficient u v b*Coulomb.tensorOrbital v b (s ∘ p)
      (Coulomb.permute p x)) =
    (((p.sign : ℤ):ℂ))*(∑ b, Coulomb.orbitalCoefficient u v b*Coulomb.tensorOrbital v b s x)
  let e : (Fin n → α) ≃ (Fin n → α) := Equiv.arrowCongr p (Equiv.refl α)
  have he (b : Fin n → α) : e.symm b = b ∘ p := rfl
  rw [← e.symm.sum_comp]
  simp only [he,Coulomb.orbitalCoefficient_antisymmetric hu v,
    Coulomb.tensorOrbital_permute,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end ContinuumCoulomb

end

end OAI
