import OAI.NumberTheory.Ostmann.Tree.CoupledHaar
import OAI.NumberTheory.Ostmann.Tree.CycleProducts

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators ComplexConjugate
open Ostmann.Arithmetic.ResidueHaar

lemma average_fintype_congr {I : Type*} (i j : Fintype I) (f : I → ℂ) :
    @average I i f = @average I j f := by
  cases Subsingleton.elim i j
  rfl
lemma real_average_fintype_congr {I : Type*} (i j : Fintype I) (f : I → ℝ) :
    @Density.average I i f = @Density.average I j f := by
  cases Subsingleton.elim i j
  rfl

lemma average_mul_const {I : Type*} [Fintype I] (f : I → ℂ) (c : ℂ) :
    average (fun i => f i*c)=average f*c := by
  simp only [average,← Finset.sum_mul]
  ring
lemma average_const {I : Type*} [Fintype I] [Nonempty I] (c : ℂ) :
    average (fun _ : I => c)=c := by
  have hn : (Fintype.card I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [average,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hn c
lemma average_comm {I J : Type*} [Fintype I] [Fintype J] (f : I → J → ℂ) :
    average (fun i => average (f i)) = average (fun j => average (fun i => f i j)) := by
  simp only [average,← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

def BalancedSelection.projection {E V W U : Type*}
    [DecidableEq E] [DecidableEq V] [DecidableEq W] [CommGroup U] [Fintype U]
    {left : E → V} {right : E → W} (c : BalancedSelection left right)
    (F : (E → U) → ℂ) (M : E → U) : ℂ := average (fun z : U => F (c.act z M))

theorem cycle_projection_correlation {E E' V W U : Type*}
    [Fintype E] [Fintype E'] [Fintype U] [CommGroup U]
    [DecidableEq E] [DecidableEq E'] [DecidableEq V] [DecidableEq W]
    {left : E → V} {right : E → W} (other : E' → V)
    (c : BalancedSelection left right) (F : (E → U) → ℂ) (G : (E' → U) → ℂ) :
    average (fun x : coupledGroup (labelProducts left) (labelProducts other) =>
      c.projection F x.val.1*conj (G x.val.2)) =
    average (fun x : coupledGroup (labelProducts left) (labelProducts other) =>
      F x.val.1*conj (G x.val.2)) := by
  classical
  let S := coupledGroup (labelProducts (U:=U) left) (labelProducts other)
  calc
    _ = average (fun x : S => average (fun z : U => F (c.act z x.val.1)*conj (G x.val.2))) := by
      congr 1
      funext x
      exact (average_mul_const _ _).symm
    _ = average (fun z : U => average (fun x : S => F (c.act z x.val.1)*conj (G x.val.2))) :=
      average_comm _
    _ = average (fun _z : U => average (fun x : S => F x.val.1*conj (G x.val.2))) := by
      congr 1
      funext z
      have h := coupledGroup.average_change_first (labelProducts left) (labelProducts other)
        (c.actEquiv z) (c.labelProducts_act z) F G
      simp only [average_fintype_congr _ (inferInstance : Fintype S)] at h
      change average (fun x : S => F (c.act z x.val.1)*conj (G x.val.2)) = _ at h
      exact h
    _ = _ := average_const _

theorem cycle_projection_reduction {E E' V W U : Type*}
    [Fintype E] [Fintype E'] [Fintype U] [CommGroup U]
    [DecidableEq E] [DecidableEq E'] [DecidableEq V] [DecidableEq W]
    {left : E → V} {right : E → W} (other : E' → V)
    (hl : Function.Surjective left) (ho : Function.Surjective other)
    (c : BalancedSelection left right) (F : (E → U) → ℂ) (G : (E' → U) → ℂ) :
    ‖average (fun x : coupledGroup (labelProducts left) (labelProducts other) =>
      F x.val.1*conj (G x.val.2))‖^2 ≤
      Density.average (fun M => ‖c.projection F M‖^2)*Density.average (fun N => ‖G N‖^2) := by
  classical
  let S := coupledGroup (labelProducts (U:=U) left) (labelProducts other)
  have hi := cycle_projection_correlation other c F G
  have h := coupled_cauchy_sq (labelProducts left) (labelProducts other)
    (labelProducts_surjective left hl) (labelProducts_surjective other ho) (c.projection F) G
  simp only [average_fintype_congr _ (inferInstance : Fintype S)] at hi h
  simp only [real_average_fintype_congr _ (inferInstance : Fintype (E → U)),
    real_average_fintype_congr _ (inferInstance : Fintype (E' → U))] at h
  rw [hi] at h
  exact h

end
end Ostmann.Tree

end OAI
