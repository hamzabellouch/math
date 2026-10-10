import OAI.Algebra.OddKaplansky.AmalgamExtras

namespace OAI

section
namespace OddKaplansky.SectorGroup
noncomputable section
open scoped Classical BigOperators
open WreathFourier
variable {I G₀ H : Type} [sectionInstance66 : Fintype I] [Group G₀] [Group H] [sectionInstance67 : Fintype H]
variable (M : ℕ) [sectionInstance68 : NeZero M] (i : I → (H →* G₀))
abbrev Attached := Wreath (H := H) M
abbrev Common := Fourier.C M × H
def toBase (j : I) : Common (H := H) M →* (Fourier.C M × G₀) :=
  (MonoidHom.id (Fourier.C M)).prodMap (i j)
def toAttached (_j : I) : Common (H := H) M →* Attached (H := H) M where
  toFun a := ⟨fun _ => a.1,a.2⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
lemma toBase_injective
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (hi : ∀ j, Function.Injective (i j)) (j : I) : Function.Injective (toBase M i j) := by
  intro a b he
  change (a.1,i j a.2)=(b.1,i j b.2) at he
  exact Prod.ext (congrArg (fun x : Fourier.C M × G₀ => x.1) he) (hi j (congrArg (fun x : Fourier.C M × G₀ => x.2) he))
lemma toAttached_injective
    {I : Type}
    {H : Type}
    [Fintype.{0} I]
    [Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (j : I) : Function.Injective (toAttached (H := H) M j) := by
  intro a b he
  exact Prod.ext (congrArg (fun g : Attached (H := H) M => g.left 1) he) (congrArg RegularWreathProduct.right he)
abbrev G₁ := StarAmalgam.Amalgam (toBase M i) (toAttached (H := H) M)
def base : (Fourier.C M × G₀) →* G₁ M i := StarAmalgam.ofBase (toBase M i) (toAttached (H := H) M)
def factor (j : I) : Attached (H := H) M →* G₁ M i := StarAmalgam.ofFactor (toBase M i) (toAttached (H := H) M) j
def original : G₀ →* G₁ M i := (base M i).comp (MonoidHom.inr _ _)
def central : Fourier.C M →* G₁ M i := (base M i).comp (MonoidHom.inl _ _)
lemma base_injective (hi : ∀ j, Function.Injective (i j)) : Function.Injective (base M i) :=
  StarAmalgam.ofBase_injective _ _ (toBase_injective M i hi) (toAttached_injective M)
lemma factor_injective (hi : ∀ j, Function.Injective (i j)) (j : I) : Function.Injective (factor M i j) :=
  StarAmalgam.ofFactor_injective _ _ (toBase_injective M i hi) (toAttached_injective M) j
lemma original_injective (hi : ∀ j, Function.Injective (i j)) : Function.Injective (original M i) := by
  intro a b he
  exact congrArg Prod.snd (base_injective M i hi he)
lemma central_injective (hi : ∀ j, Function.Injective (i j)) : Function.Injective (central M i) := by
  intro a b he
  exact congrArg Prod.fst (base_injective M i hi he)
lemma identify_top
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (j : I) (h : H) : original M i (i j h) = factor M i j (top M h) := by
  convert StarAmalgam.identify (toBase M i) (toAttached (H := H) M) j (1,h) using 1 <;> rfl
lemma identify_diagonal
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (j : I) (c : Fourier.C M) : central M i c = factor M i j (SectorFourier.diagonal M c) := by
  simpa [central,base,factor,toBase,toAttached,SectorFourier.diagonal,SectorFourier.constant,WreathFourier.base] using StarAmalgam.identify (toBase M i) (toAttached (H := H) M) j (c,1)
lemma central_commute
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (c : Fourier.C M) (g : G₁ M i) : Commute (central M i c) g := by
  exact StarAmalgam.base_central (toBase M i) (toAttached (H := H) M) (c,1)
    (fun h => by change (c,1)*h=h*(c,1); ext <;> simp [mul_comm])
    (fun _ => (c,1)) (fun j => by simp [toBase])
    (fun j h => SectorFourier.diagonal_central M c h) g
instance [Group.FG G₀] : Group.FG (G₁ M i) := inferInstance
variable {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
def f : MonoidAlgebra K (G₁ M i) := CharacterIdempotents.pushed (central M i) (Fourier.cyclicCharacter M hζ)
lemma f_idempotent
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4)))))
    {K : Type}
    [contextInstance11 : Field.{0} K]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K contextInstance11)) ζ M) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M i hζ * f M i hζ=f M i hζ :=
  CharacterIdempotents.pushed_idempotent _ _ hm
lemma f_ne_zero (hi : ∀ j, Function.Injective (i j)) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M i hζ ≠ 0 :=
  CharacterIdempotents.pushed_ne_zero _ (central_injective M i hi) _ hm
lemma f_central (a : MonoidAlgebra K (G₁ M i)) : Commute (f M i hζ) a :=
  CharacterIdempotents.pushed_central _ _ (central_commute M i) a
lemma factor_f (j : I) : MonoidAlgebra.mapDomainAlgHom K K (factor M i j) (SectorFourier.f M hζ) = f M i hζ := by
  have he : (factor M i j).comp (SectorFourier.diagonal M) = central M i := MonoidHom.ext (fun c => (identify_diagonal M i j c).symm)
  simp only [SectorFourier.f,f,CharacterIdempotents.pushed,] at *
  rw [← AlgHom.comp_apply,← MonoidAlgebra.mapDomainAlgHom_comp,he]
lemma factor_original (j : I) (e : MonoidAlgebra K H) :
    MonoidAlgebra.mapDomainAlgHom K K (factor M i j) (MonoidAlgebra.mapDomainAlgHom K K (top M) e) =
      MonoidAlgebra.mapDomainAlgHom K K (original M i) (MonoidAlgebra.mapDomainAlgHom K K (i j) e) := by
  have he : (factor M i j).comp (top M) = (original M i).comp (i j) := MonoidHom.ext (fun h => (identify_top M i j h).symm)
  rw [← AlgHom.comp_apply,← MonoidAlgebra.mapDomainAlgHom_comp,he,MonoidAlgebra.mapDomainAlgHom_comp,AlgHom.comp_apply]
end
end OddKaplansky.SectorGroup

end

end OAI
