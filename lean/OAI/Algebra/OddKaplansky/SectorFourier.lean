import OAI.Algebra.OddKaplansky.OrbitBlock

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section
namespace OddKaplansky.CharacterIdempotents
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} {B : Type portUniverse3} [Field K] [Group A] [Fintype A] [Group B] [Fintype B]
lemma projector_pushed (χ : A →* Kˣ) (j : B →* A) (ψ : B →* Kˣ)
    (hc : (Fintype.card B : K) ≠ 0) :
    projector χ * pushed j ψ = if χ.comp j = ψ then projector χ else 0 := by
  rw [pushed_eq_sum,mul_smul_comm,Finset.mul_sum]
  have hh (b : B) : projector χ * MonoidAlgebra.single (j b) ((ψ b : K)⁻¹) =
      ((χ (j b) : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single (j b) ((ψ b : K)⁻¹) = (ψ b : K)⁻¹ • MonoidAlgebra.single (j b) 1 by simp]
    rw [mul_smul_comm,projector_mul_single,smul_smul,mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul,smul_smul]
  by_cases he : χ.comp j = ψ
  · rw [ite_eq_left he]
    have hv (b : B) : χ (j b)=ψ b := DFunLike.congr_fun he b
    simp [hv,hc]
  · rw [ite_eq_right he]
    have hn : χ.comp j * ψ⁻¹ ≠ 1 := by
      intro h
      apply he
      exact mul_inv_eq_one.mp h
    have hz := sum_character_eq_zero (χ.comp j * ψ⁻¹) hn
    simpa using congrArg (fun c : K => ((Fintype.card B : K)⁻¹*c) • projector χ) hz
end
end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.SectorFourier
noncomputable section
open scoped Classical BigOperators
open WreathFourier
variable {K : Type portUniverse4} {H : Type portUniverse5} [Field K] [sectionInstance45 : Group H] [sectionInstance46 : Fintype H]
variable (M : ℕ) [sectionInstance44 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
def constant : Fourier.C M →* Base (H := H) M where
  toFun c := fun _ => c
  map_one' := rfl
  map_mul' _ _ := rfl
def diagonal : Fourier.C M →* Wreath (H := H) M := (base M).comp (constant M)
def weight (lmb : Base (H := H) M) : ZMod M := ∑ x, (lmb x).toAdd
lemma weight_shift
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (g : H) (lmb : Base (H := H) M) : weight M (shift M g lmb) = weight M lmb :=
  Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun x : H => (lmb x).toAdd)
lemma character_constant
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M) (lmb : Base (H := H) M) :
    (Fourier.character M hζ lmb).comp (constant M) = Fourier.cyclicCharacter M hζ ↔ weight M lmb=1 := by
  constructor
  · intro he
    have hh := DFunLike.congr_fun he (Multiplicative.ofAdd (1 : ZMod M))
    have hh' := Fourier.cyclicCharacter_injective M hζ hh
    have hh'' := congrArg Multiplicative.toAdd hh'
    simpa [Fourier.character_apply,constant,weight] using hh''
  · intro hw
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply,Fourier.character_apply,constant,MonoidHom.coe_mk,OneHom.coe_mk,← Finset.sum_mul]
    rw [show (∑ x : H, (lmb x).toAdd)=1 from hw,one_mul,ofAdd_toAdd]
def f : MonoidAlgebra K (Wreath (H := H) M) := CharacterIdempotents.pushed (diagonal M) (Fourier.cyclicCharacter M hζ)
lemma f_eq_packet (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    f (H := H) M hζ = ∑ lmb : {lmb : Base (H := H) M // weight M lmb=1}, projector M hζ lmb.val := by
  have hp : ∀ lmb : Base (H := H) M, projector M hζ lmb * f M hζ =
      if weight M lmb=1 then projector M hζ lmb else 0 := by
    intro lmb
    have hh := congrArg (MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M))
      (CharacterIdempotents.projector_pushed (Fourier.character M hζ lmb) (constant M) (Fourier.cyclicCharacter M hζ) hm)
    have hf : MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M)
        (CharacterIdempotents.pushed (constant M) (Fourier.cyclicCharacter M hζ)) = f M hζ := by
      simp only [CharacterIdempotents.pushed,f,diagonal,MonoidAlgebra.mapDomainAlgHom_comp,AlgHom.comp_apply]
    simp only [map_mul,apply_ite,map_zero,hf,character_constant] at hh
    by_cases hw : weight M lmb=1
    · simpa only [ite_eq_left hw,projector,CharacterIdempotents.pushed] using hh
    · simpa only [ite_eq_right hw,projector,CharacterIdempotents.pushed] using hh
  calc
    f (H := H) M hζ = (∑ lmb : Base (H := H) M, projector M hζ lmb) * f M hζ := by rw [sum_projector M hζ hc,one_mul]
    _ = ∑ lmb : Base (H := H) M, if weight M lmb=1 then projector M hζ lmb else 0 := by simp only [Finset.sum_mul,hp]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
lemma diagonal_injective
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : Function.Injective (diagonal (H := H) M) := by
  intro a b he
  have hh := congrArg (fun g : Wreath (H := H) M => g.left 1) he
  exact hh
lemma diagonal_central
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (c : Fourier.C M) (g : Wreath (H := H) M) : Commute (diagonal M c) g := by
  change diagonal M c * g = g * diagonal M c
  ext x <;> simp [diagonal,constant,base,mul_comm]
lemma f_idempotent
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) : f (H := H) M hζ * f M hζ=f M hζ :=
  CharacterIdempotents.pushed_idempotent _ _ hm
lemma f_ne_zero (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) : f (H := H) M hζ ≠ 0 :=
  CharacterIdempotents.pushed_ne_zero _ (diagonal_injective M) _ hm
lemma f_central (a : MonoidAlgebra K (Wreath (H := H) M)) : Commute (f M hζ) a :=
  CharacterIdempotents.pushed_central _ _ (diagonal_central M) a
end
end OddKaplansky.SectorFourier

end

end OAI
