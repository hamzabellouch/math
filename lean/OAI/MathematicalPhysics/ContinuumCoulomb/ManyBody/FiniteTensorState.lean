import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalTensor
import OAI.Analysis.CoulombRadii.FieldAnalysis.TsumFixed
import OAI.Analysis.CoulombRadii.FormDomain.Pullback

namespace OAI

/-! Finite products of the actual smooth orbitals lie in the full H1 domain.
Their synthesis agrees with the orthogonal L2 tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def classicalTensorState {n : ℕ} {α : Type*}
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (p : Fin n → α) : Coulomb.H1Vector n :=
  classicalH1State (Coulomb.tensorOrbital v p) (tensorOrbital_C1 v hv p)
    (Coulomb.tensorOrbital_memLp v hL2 p)
    (fun s a => tensorOrbital_partial_memLp v hv hL2 hpartial p s a.1 a.2)

def finiteTensorState {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) : Coulomb.H1Vector n :=
  Coulomb.H1Vector.finiteSum (fun p =>
    Coulomb.H1Vector.scale (c p) (classicalTensorState v hv hL2 hpartial p))

theorem finiteTensorState_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) :
    (finiteTensorState v hv hL2 hpartial c).toHilbert =
      ∑ p, c p • Coulomb.tensorHilbert v hL2 p := by
  apply PiLp.ext
  intro s
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    Coulomb.tensorHilbert,Coulomb.H1Vector.toHilbert,WithLp.ofLp_toLp]
  exact Coulomb.orbital_sum_toLp (fun p => Coulomb.tensorOrbital v p s)
    (fun p => Coulomb.tensorOrbital_memLp v hL2 p s) Finset.univ c

def finiteTensorProjection {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) : Coulomb.H1Vector n :=
  finiteTensorState v hv hL2 hpartial (Coulomb.orbitalCoefficient u v)

theorem finiteTensorProjection_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) :
    (finiteTensorProjection v hv hL2 hpartial u).toHilbert =
      ∑ p, inner ℂ (Coulomb.tensorHilbert v hL2 p) u.toHilbert •
        Coulomb.tensorHilbert v hL2 p := by
  simp only [finiteTensorProjection,finiteTensorState_toHilbert,
    Coulomb.orbitalCoefficient_eq_inner u v hL2]

theorem finiteTensorProjection_coefficients {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t)*v c y t) =
      if a = c then (1:ℂ) else 0) (u : Coulomb.H1Vector n) (p : Fin n → α) :
    Coulomb.orbitalCoefficient (finiteTensorProjection v hv hL2 hpartial u) v p =
      Coulomb.orbitalCoefficient u v p := by
  simp only [Coulomb.orbitalCoefficient_eq_inner _ v hL2,finiteTensorProjection_toHilbert]
  exact (Coulomb.tensorHilbert_orthonormal v hL2 ho).inner_right_sum _ (Finset.mem_univ p)

end ContinuumCoulomb

end

end OAI
