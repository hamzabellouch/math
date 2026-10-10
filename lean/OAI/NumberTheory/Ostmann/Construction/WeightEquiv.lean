import Mathlib

namespace OAI

namespace Ostmann.Construction

structure WeightEquiv {α β : Type*} (w : α → ℝ) (v : β → ℝ) where
  equiv : α ≃ β
  mass : ∀x,w x=v (equiv x)

namespace WeightEquiv
variable {α β γ δ : Type*}

def refl (w : α → ℝ) : WeightEquiv w w := ⟨Equiv.refl _,fun _ => rfl⟩

def symm {w : α → ℝ} {v : β → ℝ} (e : WeightEquiv w v) : WeightEquiv v w :=
  ⟨e.equiv.symm,fun y => by simpa only [e.equiv.apply_symm_apply] using (e.mass (e.equiv.symm y)).symm⟩

def trans {w : α → ℝ} {v : β → ℝ} {u : γ → ℝ}
    (e : WeightEquiv w v) (f : WeightEquiv v u) : WeightEquiv w u :=
  ⟨e.equiv.trans f.equiv,fun x => (e.mass x).trans (f.mass (e.equiv x))⟩

def prod {w : α → ℝ} {v : β → ℝ} {u : γ → ℝ} {t : δ → ℝ}
    (e : WeightEquiv w v) (f : WeightEquiv u t) :
    WeightEquiv (fun x : α×γ => w x.1*u x.2) (fun x : β×δ => v x.1*t x.2) :=
  ⟨Equiv.prodCongr e.equiv f.equiv,fun x => by rw [e.mass,f.mass]; rfl⟩

def assoc (w : α → ℝ) (v : β → ℝ) (u : γ → ℝ) :
    WeightEquiv (fun x : (α×β)×γ => (w x.1.1*v x.1.2)*u x.2)
      (fun x : α×β×γ => w x.1*(v x.2.1*u x.2.2)) :=
  ⟨Equiv.prodAssoc _ _ _,fun _ => mul_assoc _ _ _⟩

def swap (w : α → ℝ) (v : β → ℝ) (u : γ → ℝ) :
    WeightEquiv (fun x : α×β×γ => w x.1*(v x.2.1*u x.2.2))
      (fun x : β×α×γ => v x.1*(w x.2.1*u x.2.2)) :=
  ⟨{ toFun := fun x => (x.2.1,x.1,x.2.2)
     invFun := fun x => (x.2.1,x.1,x.2.2)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl },fun x => by
       change w x.1*(v x.2.1*u x.2.2)=v x.2.1*(w x.1*u x.2.2)
       ring⟩

end WeightEquiv
end Ostmann.Construction

end OAI
