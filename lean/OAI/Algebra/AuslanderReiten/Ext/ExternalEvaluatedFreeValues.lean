import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluatedFreeCoordinate
import OAI.Algebra.AuslanderReiten.Bar.ExternalBarFreePure
import OAI.Algebra.AuslanderReiten.Bar.NativeBarCompositeValues

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B

-- Match the native chain maps' complex shape and scalar structures in the premises.
-- Keep the summand presentation in the conclusion so composition does not need to
-- compare expanded tensor-product structures after specializing the bar complexes.
private theorem postShuffle_native_values
    (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
    (g : (factorEvaluation k U (AbsoluteBar.complex k A)).X 0 ⟶
      (ModuleBar.complex k A M).X (c := ComplexShape.down ℕ) 0)
    (h : (factorEvaluation k V (AbsoluteBar.complex k B)).X 0 ⟶
      (ModuleBar.complex k B N).X (c := ComplexShape.down ℕ) 0)
    (a : EnvelopingBimodule k A (AbsoluteBar.moduleObject k A (0+1)))
    (b : EnvelopingBimodule k B (AbsoluteBar.moduleObject k B (0+1)))
    (x : U) (y : V) (r : A) (s : B)
    (hg : (g ≫ (ModuleBar.freeCoordinate k A M e).toModuleIso.hom)
      (@BalancedTensor.tmul k A (EnvelopingBimodule k A (AbsoluteBar.moduleObject k A (0+1))) U _ _ _ _
        (@EnvelopingBimodule.instModule_1 k A _ _ _ (AbsoluteBar.moduleObject k A (0+1))
          (moduleCatBaseModule k (A ⊗[k] Aᵐᵒᵖ) (AbsoluteBar.moduleObject k A (0+1))))
        (moduleCatBaseModule k A U) _ _ a x) = r)
    (hh : (h ≫ (ModuleBar.freeCoordinate k B N f).toModuleIso.hom)
      (@BalancedTensor.tmul k B (EnvelopingBimodule k B (AbsoluteBar.moduleObject k B (0+1))) V _ _ _ _
        (@EnvelopingBimodule.instModule_1 k B _ _ _ (AbsoluteBar.moduleObject k B (0+1))
          (moduleCatBaseModule k (B ⊗[k] Bᵐᵒᵖ) (AbsoluteBar.moduleObject k B (0+1))))
        (moduleCatBaseModule k B V) _ _ b y) = s) :
    ((summandEvaluationIso k A B U V (AbsoluteBar.complex k A) (AbsoluteBar.complex k B) 0 ⟨(0,0),rfl⟩).hom ≫
      ExternalTensor.mapHom k A B
        (show (factorEvaluation k U (AbsoluteBar.complex k A)).X 0 ⟶ (ModuleBar.complex k A M).X 0 from g)
        (show (factorEvaluation k V (AbsoluteBar.complex k B)).X 0 ⟶ (ModuleBar.complex k B N).X 0 from h) ≫
      ExternalTensor.barFreeCoordinate k A B M N e f)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B ((AbsoluteBar.complex k A).X 0) ((AbsoluteBar.complex k B).X 0)).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B U V).symm (x ⊗ₜ[k] y))) = r ⊗ₜ[k] s :=
  postShuffle_barFree_values k A B M N e f
    ((AbsoluteBar.complex k A).X 0) ((AbsoluteBar.complex k B).X 0) U V g h a b x y r s hg hh

private theorem nativePostShuffle :
    type_of% (postShuffle_native_values k A B M N e f X Y
      ((BarBalanced.nativeComplexIso k A M).hom.f 0)
      ((BarBalanced.nativeComplexIso k B N).hom.f 0)) :=
  postShuffle_native_values k A B M N e f X Y
    ((BarBalanced.nativeComplexIso k A M).hom.f 0)
    ((BarBalanced.nativeComplexIso k B N).hom.f 0)

private abbrev nativePureStart (a b : A) (c d : B) (m : M) (n : N) :=
  nativePostShuffle k A B M N e f
    (⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k A (AbsoluteBar.moduleObject k A 1))
    (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k B (AbsoluteBar.moduleObject k B 1)) m n
    (e (b • m) • a) (f (d • n) • c)

private theorem nativePureLeft (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (nativePureStart k A B M N e f a b c d m n
      (BarBalanced.nativeComposite_tensor k A M e a b m)) :=
  nativePureStart k A B M N e f a b c d m n
    (BarBalanced.nativeComposite_tensor k A M e a b m)

private theorem nativePureProof (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (nativePureLeft k A B M N e f a b c d m n
      (BarBalanced.nativeComposite_tensor k B N f c d n)) :=
  nativePureLeft k A B M N e f a b c d m n
    (BarBalanced.nativeComposite_tensor k B N f c d n)

theorem shuffledFreeEvaluation_pure (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (nativePureProof k A B M N e f a b c d m n) :=
  nativePureProof k A B M N e f a b c d m n

private abbrev summandFreeProof (a b : A) (c d : B) (m : M) (n : N) :=
  shuffledFreeEvaluation_pure k A B M N e f a b c d m n

private theorem summandFreeEvaluation_pure (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (summandFreeProof k A B M N e f a b c d m n) :=
  summandFreeProof k A B M N e f a b c d m n

private theorem valueOfComposite {R : Type*} [Ring R] {U V W : ModuleCat R}
    {inclusion : U ⟶ V} {evaluation : V ⟶ W} {composite : U ⟶ W}
    (equality : inclusion ≫ evaluation = composite) (input : U) :
    evaluation (inclusion input) = composite input := by
  rw [← ModuleCat.comp_apply, equality]

private theorem totalFreeFromSummand :
    type_of% (valueOfComposite (inclusion_totalFreeEvaluation k A B M N e f)) :=
  valueOfComposite (inclusion_totalFreeEvaluation k A B M N e f)

private abbrev barPureTensor (a b : A) (c d : B) (m : M) (n : N) :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := A) X
  letI : Module k N := moduleCatBaseModule (k := k) (R := B) Y
  BalancedTensor.tmul (k := k) (R := A ⊗[k] B)
    ((bimoduleCoordinates k A B ((P).X 0) ((Q).X 0)).symm
      ((⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k A (AbsoluteBar.moduleObject k A 1)) ⊗ₜ[k]
        (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k B (AbsoluteBar.moduleObject k B 1))))
    ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (m ⊗ₜ[k] n))

private theorem totalFreeAt (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (totalFreeFromSummand k A B M N e f
      (barPureTensor k A B M N a b c d m n)) :=
  totalFreeFromSummand k A B M N e f (barPureTensor k A B M N a b c d m n)

private theorem totalFreeProof (a b : A) (c d : B) (m : M) (n : N) :
    type_of% ((totalFreeAt k A B M N e f a b c d m n).trans
      (summandFreeEvaluation_pure k A B M N e f a b c d m n)) :=
  (totalFreeAt k A B M N e f a b c d m n).trans
    (summandFreeEvaluation_pure k A B M N e f a b c d m n)

theorem totalFreeEvaluation_pure (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (totalFreeProof k A B M N e f a b c d m n) :=
  totalFreeProof k A B M N e f a b c d m n

end ArExplicit.ExternalBalanced

end

end OAI
