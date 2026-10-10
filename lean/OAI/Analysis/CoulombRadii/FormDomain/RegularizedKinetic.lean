import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.H1Pairing
import OAI.Analysis.CoulombRadii.FieldAnalysis.BodyCoefficient

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma regularizedU_second {l:ℝ} (hl:l≠0) (e:ℝ) (a b:Fin 3) (x:Space):
    fderiv ℝ (fun y => fderiv ℝ (regularizedU l e) y (EuclideanSpace.single a 1)) x
      (EuclideanSpace.single b 1)=NeutralAtom.dirPartial
        (NeutralAtom.dirPartial (NeutralAtom.regularizedKernel l) (NeutralAtom.axis a))
        (NeutralAtom.axis b) x := by
  simp_rw [regularizedU_partial hl]
  rfl
lemma regularizedU_second_le {l:ℝ} (hl:l≠0) (e:ℝ) (a b:Fin 3) (x:Space):
    |fderiv ℝ (fun y => fderiv ℝ (regularizedU l e) y (EuclideanSpace.single a 1)) x
      (EuclideanSpace.single b 1)|≤4*(l^2)^(-3/2:ℝ) := by
  rw [regularizedU_second hl]
  exact NeutralAtom.regularizedSecond_uniform_bound hl x a b
lemma regularizedU_lap {l:ℝ} (hl:l≠0) (e:ℝ) (x:Space):
    (∑ a:Fin 3,fderiv ℝ (fun y => fderiv ℝ (regularizedU l e) y (EuclideanSpace.single a 1)) x
      (EuclideanSpace.single a 1))≤0 := by
  simp_rw [regularizedU_second hl]
  rw [←NeutralAtom.coordinateLaplacian_eq_partials
    ((NeutralAtom.contDiff_regularizedKernel hl).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    NeutralAtom.laplacian_regularizedKernel hl]
  unfold NeutralAtom.regularizedCharge
  apply neg_nonpos.mpr
  positivity

def regularizedUCoefficient (l e:ℝ) (hl:l≠0):SmoothBoundedCoefficient where
  value:=regularizedU l e
  smooth:=regularizedU_smooth hl e
  bound:=(l^2)^(-1/2:ℝ)+|e|
  derivBound:=(l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ)
  bound_nonneg:=by positivity
  derivBound_nonneg:=by positivity
  value_le x:= (abs_add_le _ _).trans (add_le_add (NeutralAtom.regularizedKernel_uniform_bound hl x) le_rfl)
  deriv_le a x:=by rw [regularizedU_partial hl]; exact NeutralAtom.regularizedPartial_uniform_bound hl x a

def firstCoordinateBlock (k:ℕ):Finset (Fin (1+k) × Fin 3):=
  Finset.univ.map ⟨fun a => (0,a),fun _ _ h => Prod.mk.inj h |>.2⟩
lemma regularized_weight_kinetic {k:ℕ} (u:H1Vector (1+k)) (s:Spins (1+k))
    (l e:ℝ) (hl:l≠0) (he:0<e):
    let w:=reciprocalCoefficient l e hl he
    let v:=u.smoothMul (fun x => w.value (position x 0)) (w.lift_smooth 0) w.bound w.derivBound
      (fun x => w.value_le (position x 0)) (w.lift_deriv_le 0)
    0≤∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x) := by
  let U:=regularizedUCoefficient l e hl
  let w:=reciprocalCoefficient l e hl he
  have hDD:∀ a b (x:Configuration (1+k)),
      |fderiv ℝ (fun y => fderiv ℝ (fun z => U.value (position z 0)) y (EuclideanSpace.single a 1))
        x (EuclideanSpace.single b 1)|≤4*(l^2)^(-3/2:ℝ) := by
    rintro ⟨j,a⟩ ⟨i,b⟩ x
    rw [oneBody_second_derivative U.value U.smooth]
    split_ifs
    · simpa only [U,regularizedUCoefficient] using regularizedU_second_le hl e a b (position x 0)
    · simp only [abs_zero]
      positivity
  have hLap:∀ x:Configuration (1+k),
      (∑ a∈firstCoordinateBlock k,fderiv ℝ (fun y => fderiv ℝ (fun z => U.value (position z 0)) y
        (EuclideanSpace.single a 1)) x (EuclideanSpace.single a 1))≤0 := by
    intro x
    simp only [firstCoordinateBlock,Finset.sum_map]
    change (∑ a:Fin 3,fderiv ℝ (fun y => fderiv ℝ (fun z => U.value (position z 0)) y
      (EuclideanSpace.single (0,a) 1)) x (EuclideanSpace.single (0,a) 1))≤0
    simp_rw [oneBody_second_derivative U.value U.smooth]
    simp only [and_self,ite_true]
    simpa only [U,regularizedUCoefficient] using regularizedU_lap hl e (position x 0)
  have H:=reciprocal_kinetic_nonneg u s (firstCoordinateBlock k)
    (fun x => U.value (position x 0)) (fun x => w.value (position x 0))
    (U.lift_smooth 0) (w.lift_smooth 0) U.bound U.derivBound w.derivBound w.bound (4*(l^2)^(-3/2:ℝ))
    (fun x => U.value_le (position x 0)) (U.lift_deriv_le 0)
    (fun x => w.value_le (position x 0)) (w.lift_deriv_le 0) hDD
    (fun x => by exact (regularizedU_pos (l:=l) he (position x 0)).le)
    (fun x => by exact mul_inv_cancel₀ (regularizedU_pos (l:=l) he (position x 0)).ne') hLap
  simp only [firstCoordinateBlock,Finset.sum_map] at H
  exact H
end Coulomb
end

end

end OAI
