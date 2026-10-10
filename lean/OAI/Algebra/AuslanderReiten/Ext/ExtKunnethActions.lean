import OAI.Algebra.AuslanderReiten.Ext.ExtTensorAction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)

def firstActionUnderKunneth (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) :=
  (extKunnethEquiv k A B P Q U V (n+3)).toLinearMap.comp
    ((Ext.bilinearCompOfLinear k (moduleObject k A B X Y) (moduleObject k A B X Y)
      (moduleObject k A B U V) 3 n (n+3) (by omega) (firstCubicExt k A B P Q p hp)).comp
        (extKunnethEquiv k A B P Q U V n).symm.toLinearMap)

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
private theorem firstActionUnderKunneth_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    firstActionUnderKunneth k A B P Q U V p hp n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) =
    coefficientFirst k A B X U Y V
      (ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp)) n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) := by
  unfold firstActionUnderKunneth
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change extKunnethEquiv k A B P Q U V (n+3)
    ((firstCubicExt k A B P Q p hp).comp (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega)) = _
  rw [firstCubicExt_elementary, elementaryExt_kunneth, elementaryExt_kunneth,
    coefficientFirst_single, ResolutionProducts.cubic_endExt_comp_extMk (k := k)]
  rfl

omit [CharP k 2] [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat A)] [HasDerivedCategory (ModuleCat B)]
  [HasDerivedCategory (ModuleCat (A ⊗[k] B))] in
private theorem coefficients_ext (n : ℕ)
    (L R : extCoefficients k A B X U Y V n →ₗ[k] extCoefficients k A B X U Y V (n+3))
    (h : ∀ (i j : ℕ) (hij : i+j=n)
      (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
      (hf : f.comp (P.complex.d (i+1) i).hom=0)
      (hg : g.comp (Q.complex.d (j+1) j).hom=0),
      L (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n hij f g hf hg)) =
      R (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n hij f g hf hg))) : L=R := by
  classical
  apply LinearMap.pi_ext
  intro d t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [Pi.single_add, map_add, ha, hb]
  | tmul x y =>
    obtain ⟨f,hf,rfl⟩ := P.extMk_surjective x (d.val.1+1) rfl
    obtain ⟨g,hg,rfl⟩ := Q.extMk_surjective y (d.val.2+1) rfl
    let hf' := congrArg ModuleCat.Hom.hom hf
    let hg' := congrArg ModuleCat.Hom.hom hg
    have he := elementaryExt_kunneth k A B P Q U V d.val.1 d.val.2 n d.property f.hom g.hom hf' hg'
    have hl := h d.val.1 d.val.2 d.property f.hom g.hom hf' hg'
    exact (congrArg L he.symm).trans (hl.trans (congrArg R he))

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstActionUnderKunneth_eq (n : ℕ) :
    firstActionUnderKunneth k A B P Q U V p hp n =
      coefficientFirst k A B X U Y V
        (ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp)) n := by
  apply coefficients_ext k A B P Q U V n
  intro i j hij f g hf hg
  exact firstActionUnderKunneth_elementary k A B P Q U V p hp i j n hij f g hf hg

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstCubicExt_kunneth (n : ℕ)
    (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((firstCubicExt k A B P Q p hp).comp x (by omega)) =
      coefficientFirst k A B X U Y V
        (ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp)) n
          (extKunnethEquiv k A B P Q U V n x) := by
  have he := LinearMap.congr_fun (firstActionUnderKunneth_eq k A B P Q U V p hp n)
    (extKunnethEquiv k A B P Q U V n x)
  simp only [firstActionUnderKunneth, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at he
  exact he

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstCubicExt_kunneth_of_class (a : Ext X X 3)
    (ha : ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp) = a)
    (n : ℕ) (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((firstCubicExt k A B P Q p hp).comp x (by omega)) =
      coefficientFirst k A B X U Y V a n (extKunnethEquiv k A B P Q U V n x) := by
  rw [← ha]
  exact firstCubicExt_kunneth k A B P Q U V p hp n x

variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

def secondActionUnderKunneth (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) :=
  (extKunnethEquiv k A B P Q U V (n+3)).toLinearMap.comp
    ((Ext.bilinearCompOfLinear k (moduleObject k A B X Y) (moduleObject k A B X Y)
      (moduleObject k A B U V) 3 n (n+3) (by omega) (secondCubicExt k A B P Q r hr)).comp
        (extKunnethEquiv k A B P Q U V n).symm.toLinearMap)

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
private theorem secondActionUnderKunneth_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    secondActionUnderKunneth k A B P Q U V r hr n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) =
    coefficientSecond k A B X U Y V
      (ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr)) n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) := by
  unfold secondActionUnderKunneth
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change extKunnethEquiv k A B P Q U V (n+3)
    ((secondCubicExt k A B P Q r hr).comp (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega)) = _
  rw [secondCubicExt_elementary, elementaryExt_kunneth, elementaryExt_kunneth,
    coefficientSecond_single, ResolutionProducts.cubic_endExt_comp_extMk (k := k)]
  rfl

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondActionUnderKunneth_eq (n : ℕ) :
    secondActionUnderKunneth k A B P Q U V r hr n =
      coefficientSecond k A B X U Y V
        (ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr)) n := by
  apply coefficients_ext k A B P Q U V n
  intro i j hij f g hf hg
  exact secondActionUnderKunneth_elementary k A B P Q U V r hr i j n hij f g hf hg

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondCubicExt_kunneth (n : ℕ)
    (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((secondCubicExt k A B P Q r hr).comp x (by omega)) =
      coefficientSecond k A B X U Y V
        (ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr)) n
          (extKunnethEquiv k A B P Q U V n x) := by
  have he := LinearMap.congr_fun (secondActionUnderKunneth_eq k A B P Q U V r hr n)
    (extKunnethEquiv k A B P Q U V n x)
  simp only [secondActionUnderKunneth, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at he
  exact he

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondCubicExt_kunneth_of_class (b : Ext Y Y 3)
    (hb : ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr) = b)
    (n : ℕ) (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((secondCubicExt k A B P Q r hr).comp x (by omega)) =
      coefficientSecond k A B X U Y V b n (extKunnethEquiv k A B P Q U V n x) := by
  rw [← hb]
  exact secondCubicExt_kunneth k A B P Q U V r hr n x

end ArExplicit.ExternalTensor

end

end OAI
