import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteTotal

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (δ : Differential K) (ε : Differential L)
variable (f : ∀ i, K i ⟶ L i)

/-- The degreewise map between the actual finite sums of columns. -/
def componentMap (n : ℤ) : term K n →ₗ[R] term L n :=
  LinearMap.pi (fun i => ((f i).f n).hom.comp (LinearMap.proj i))

@[simp] theorem componentMap_apply (n : ℤ) (z : term K n) (i : Fin l) :
    componentMap K L f n z i = ((f i).f n).hom (z i) := rfl

/-- A compatible family of column maps gives an actual map of total complexes. -/
def complexMap (hc : ∀ n,
    (ε.d n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (δ.d n)) :
    complex K δ ⟶ complex L ε where
  f n := ModuleCat.ofHom (componentMap K L f n)
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    exact hc n
end LittleFinitistic.FiniteColumnComplex

end

end OAI
