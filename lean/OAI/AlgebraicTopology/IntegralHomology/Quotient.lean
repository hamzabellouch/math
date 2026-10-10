import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

namespace OAI

noncomputable section

namespace Kaplansky

/-! Short exact quotient complexes and biproduct cokernels. -/

section
open CategoryTheory Limits
variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex C} (f : S ⟶ T)

/-- Componentwise cokernels, with the actual induced maps. -/
def quotientShortComplex : ShortComplex C where
  f := cokernel.map f.τ₁ f.τ₂ S.f T.f f.comm₁₂
  g := cokernel.map f.τ₂ f.τ₃ S.g T.g f.comm₂₃
  zero := by
    apply (cancel_epi (cokernel.π f.τ₁)).mp
    simp [Category.assoc]

def quotientShortComplexProjection : T ⟶ quotientShortComplex f where
  τ₁ := cokernel.π f.τ₁
  τ₂ := cokernel.π f.τ₂
  τ₃ := cokernel.π f.τ₃
  comm₁₂ := by simp [quotientShortComplex]
  comm₂₃ := by simp [quotientShortComplex]

def kernelShortComplex : ShortComplex C where
  f := kernel.map f.τ₁ f.τ₂ S.f T.f f.comm₁₂
  g := kernel.map f.τ₂ f.τ₃ S.g T.g f.comm₂₃
  zero := by
    apply (cancel_mono (kernel.ι f.τ₃)).mp
    simp [Category.assoc]

def kernelShortComplexInclusion : kernelShortComplex f ⟶ S where
  τ₁ := kernel.ι f.τ₁
  τ₂ := kernel.ι f.τ₂
  τ₃ := kernel.ι f.τ₃
  comm₁₂ := by simp [kernelShortComplex]
  comm₂₃ := by simp [kernelShortComplex]

def quotientSnakeInput (hS : S.ShortExact) (hT : T.ShortExact) :
    ShortComplex.SnakeInput C where
  L₀ := kernelShortComplex f
  L₁ := S
  L₂ := T
  L₃ := quotientShortComplex f
  v₀₁ := kernelShortComplexInclusion f
  v₁₂ := f
  v₂₃ := quotientShortComplexProjection f
  w₀₂ := by ext <;> exact kernel.condition _
  w₁₃ := by ext <;> exact cokernel.condition _
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2 <;>
      exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;>
      exact cokernelIsCokernel _
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

/-- Quotienting two short exact rows by an injective map on their right
terms gives a short exact row. This is the algebraic relative gluing step. -/
theorem quotientShortComplex_shortExact (hS : S.ShortExact) (hT : T.ShortExact)
    [Mono f.τ₃] : (quotientShortComplex f).ShortExact := by
  let D := quotientSnakeInput f hS hT
  have hzero : D.δ = 0 := (isZero_kernel_of_mono f.τ₃).eq_of_src _ _
  have hm : Mono (quotientShortComplex f).f :=
    (D.L₂'.exact_iff_mono hzero).mp D.L₂'_exact
  have he : Epi (quotientShortComplex f).g := by
    have hc : Epi (T.g ≫ cokernel.π f.τ₃) :=
      epi_comp' hT.epi_g (coequalizer.π_epi (f := f.τ₃) (g := 0))
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hc (show cokernel.π f.τ₂ ≫ (quotientShortComplex f).g =
      T.g ≫ cokernel.π f.τ₃ by simp [quotientShortComplex])
  exact { exact := D.L₃_exact }

end

open CategoryTheory Limits
section
variable {C : Type*} [Category* C] [Abelian C]
  {A B X Y : C} (f : A ⟶ X) (g : B ⟶ Y)

/-- The quotient of a direct sum is the direct sum of the actual quotients. -/
def cokernelBiprodIso : cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g where
  hom := cokernel.desc _ (biprod.map (cokernel.π f) (cokernel.π g)) (by
    ext <;> simp)
  inv := biprod.desc
    (cokernel.desc f (biprod.inl ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inl_map_assoc, cokernel.condition]; simp))
    (cokernel.desc g (biprod.inr ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inr_map_assoc, cokernel.condition]; simp))
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (biprod.map f g))).mp
    ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π f)).mp
      simp [Category.assoc]
    · apply (cancel_epi (cokernel.π g)).mp
      simp [Category.assoc]

@[reassoc (attr := simp)]
theorem cokernelBiprodIso_projection :
    cokernel.π (biprod.map f g) ≫ (cokernelBiprodIso f g).hom =
      biprod.map (cokernel.π f) (cokernel.π g) := by simp [cokernelBiprodIso]

end

end Kaplansky

end

end OAI
