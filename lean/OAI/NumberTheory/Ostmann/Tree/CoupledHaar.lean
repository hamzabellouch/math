import OAI.NumberTheory.Ostmann.Tree.DensityHorizontal

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators ComplexConjugate
open Ostmann.Arithmetic.ResidueHaar

def coupledGroup {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    (f : A →* C) (g : B →* C) : Subgroup (A × B) where
  carrier := {x | f x.1=g x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change f x.1=g x.2 at hx
    change f y.1=g y.2 at hy
    change f (x.1*y.1)=g (x.2*y.2)
    rw [map_mul,map_mul,hx,hy]
  inv_mem' := by
    intro x hx
    change f x.1=g x.2 at hx
    change f x.1⁻¹=g x.2⁻¹
    rw [map_inv,map_inv,hx]

namespace coupledGroup
variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
  (f : A →* C) (g : B →* C)

instance coupledFintype [Fintype A] [Fintype B] : Fintype (coupledGroup f g) := Fintype.ofFinite _

def fstHom : coupledGroup f g →* A := (MonoidHom.fst A B).comp (coupledGroup f g).subtype
def sndHom : coupledGroup f g →* B := (MonoidHom.snd A B).comp (coupledGroup f g).subtype

theorem fst_surjective (hg : Function.Surjective g) : Function.Surjective (fstHom f g) := by
  intro a
  obtain ⟨b,hb⟩ := hg (f a)
  exact ⟨⟨(a,b),hb.symm⟩,rfl⟩
theorem snd_surjective (hf : Function.Surjective f) : Function.Surjective (sndHom f g) := by
  intro b
  obtain ⟨a,ha⟩ := hf (g b)
  exact ⟨⟨(a,b),ha⟩,rfl⟩

def liftEquiv (e : A ≃ A) (he : ∀a,f (e a)=f a) : coupledGroup f g ≃ coupledGroup f g where
  toFun x := ⟨(e x.val.1,x.val.2),(he _).trans x.property⟩
  invFun x := ⟨(e.symm x.val.1,x.val.2),by
    have h := he (e.symm x.val.1)
    rw [e.apply_symm_apply] at h
    exact h.symm.trans x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem average_change_first [Fintype A] [Fintype B]
    (e : A ≃ A) (he : ∀a,f (e a)=f a) (F : A → ℂ) (G : B → ℂ) :
    average (fun x : coupledGroup f g => F (e x.val.1)*conj (G x.val.2)) =
      average (fun x : coupledGroup f g => F x.val.1*conj (G x.val.2)) :=
  average_equiv (liftEquiv f g e he) (fun x => F x.val.1*conj (G x.val.2))

end coupledGroup

theorem average_cauchy_sq {I : Type*} [Fintype I] (f g : I → ℂ) :
    ‖average (fun i => f i*conj (g i))‖^2 ≤
      Density.average (fun i => ‖f i‖^2)*Density.average (fun i => ‖g i‖^2) := by
  classical
  let c : ℝ := (Fintype.card I:ℝ)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hn : ‖average (fun i => f i*conj (g i))‖ ≤ c*∑ i,‖f i‖*‖g i‖ := by
    unfold average
    rw [norm_mul]
    simp only [norm_inv,Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ hc
    simpa only [norm_mul,Complex.norm_conj] using
      norm_sum_le (Finset.univ) (fun i => f i*conj (g i))
  calc
    _ ≤ (c*∑ i,‖f i‖*‖g i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = c^2*(∑ i,‖f i‖*‖g i‖)^2 := mul_pow _ _ _
    _ ≤ c^2*((∑ i,‖f i‖^2)*(∑ i,‖g i‖^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => ‖f i‖) (fun i => ‖g i‖)) (sq_nonneg c)
    _ = _ := by simp only [Density.average]; dsimp [c]; ring

theorem coupled_cauchy_sq {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    [Fintype A] [Fintype B] (f : A →* C) (g : B →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (F : A → ℂ) (G : B → ℂ) :
    ‖average (fun x : coupledGroup f g => F x.val.1*conj (G x.val.2))‖^2 ≤
      Density.average (fun a => ‖F a‖^2)*Density.average (fun b => ‖G b‖^2) := by
  classical
  have h := average_cauchy_sq (fun x : coupledGroup f g => F x.val.1)
    (fun x : coupledGroup f g => G x.val.2)
  have hfst := Density.average_surjective (coupledGroup.fstHom f g)
    (coupledGroup.fst_surjective f g hg) (fun a => ‖F a‖^2)
  have hsnd := Density.average_surjective (coupledGroup.sndHom f g)
    (coupledGroup.snd_surjective f g hf) (fun b => ‖G b‖^2)
  change Density.average (fun x : coupledGroup f g => ‖F x.val.1‖^2) = _ at hfst
  change Density.average (fun x : coupledGroup f g => ‖G x.val.2‖^2) = _ at hsnd
  rwa [hfst,hsnd] at h

end
end Ostmann.Tree

end OAI
