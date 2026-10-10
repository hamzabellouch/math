import OAI.Algebra.Finitistic.Bar.SuffixNaturality
import OAI.Algebra.Finitistic.Bar.BarCoordinateNaturality
import OAI.Algebra.Finitistic.Bar.ModuleMultibarCoordinates

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

/-- Prefix one original categorical X bar to a linear suffix map. -/
def barSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    ((XB).obj V).X i →ₗ[k] term k A N ((s+i)+1) :=
  (idealSuffixEmbed k D X N V s i e).comp
    ((Multibar.twoSidedBarObjIso k D X V i).hom.hom.restrictScalars k)

/-- The prefix keeps the original left D action. -/
theorem barSuffix_smul (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) (d : D) (v : ((XB).obj V).X i) :
    letI : Module A N := inflatedModule D X N
    barSuffix k D X N V s i e (d • v) =
      (inl d : A) • barSuffix k D X N V s i e v := by
  let : Module A N := inflatedModule D X N
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul x w =>
    change (inr (d • x) : A) ⊗ₜ[k] _ = ((inl d : A) * inr x) ⊗ₜ[k] _
    rw [inl_mul_inr]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw]

theorem barSuffix_ideal_zero (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) (x : X) (v : ((XB).obj V).X i) :
    letI : Module A N := inflatedModule D X N
    (inr x : A) • barSuffix k D X N V s i e v = 0 := by
  let : Module A N := inflatedModule D X N
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul y w =>
    change ((inr x : A) * inr y) ⊗ₜ[k] _ = 0
    rw [inr_mul_inr, TensorProduct.zero_tmul]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw, add_zero]

/-- Naturality uses the original bar functor, including its supplied scalar coherence. -/
theorem barSuffix_map (V W : ModuleCat.{u} D) (s i : ℕ)
    (e : W →ₗ[k] term k A N s) (f : V ⟶ W) (v : ((XB).obj V).X i) :
    barSuffix k D X N W s i e ((((XB).map f).f i).hom v) =
      barSuffix k D X N V s i (e.comp (f.hom.restrictScalars k)) v := by
  have h := congrArg (fun g => g.hom v)
    (Multibar.twoSidedBarObjIso_map k D X V W f.hom i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [h]
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact idealSuffixEmbed_termMap k D X N V W s i e f.hom _

/-- Literal recursive suffix embedding on every summand, including zero input degrees. -/
def innerEmbedding : (r n : ℕ) →
    RecursiveTotal.flat B Z r n →ₗ[k] term k A N (r+n)
  | 0, 0 => DirectSum.toModule k _ _ (fun _ => LinearMap.id)
  | 0, n+1 => 0
  | r+1, n => DirectSum.toModule k _ _ (fun t =>
      (termCast k D X N (show ((r+t.1.val.2)+t.1.val.1)+1=(r+1)+n by
        have h := t.1.property; omega)).comp
      (barSuffix k D X N (RecursiveTotal.summand B Z r t.1.val.2 t.2)
        (r+t.1.val.2) t.1.val.1
        ((innerEmbedding r t.1.val.2).comp
          ((RecursiveTotal.lof B Z r t.1.val.2 t.2).hom.restrictScalars k))))

theorem toModule_of_scalar {I : Type} [DecidableEq I]
    (V : I → Type u) [∀ t, AddCommGroup (V t)] [∀ t, Module k (V t)]
    (W : Type u) [AddCommGroup W] [Module k W]
    (f : ∀ t, V t →ₗ[k] W) (t : I) (v : V t) :
    DirectSum.toModule k I W f (DirectSum.of V t v) = f t v :=
  DirectSum.toModule_lof (M := V) (N := W) (φ := f) k t v

@[simp] theorem innerEmbedding_lof_succ (r n i q : ℕ) (h : i+q=n)
    (t : RecursiveTotal.Index r q) (v : RecursiveTotal.summand B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v) =
    termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.summand B Z r q t) (r+q) i
        ((innerEmbedding k D X N r q).comp
          ((RecursiveTotal.lof B Z r q t).hom.restrictScalars k)) v) := by
  simp only [innerEmbedding, RecursiveTotal.lof, ModuleCat.hom_ofHom]
  erw [DirectSum.lof_eq_of, toModule_of_scalar]
  rfl

theorem termCast_smul {a b : ℕ} (h : a=b) (d : A) (v : term k A N a) :
    letI : Module A N := inflatedModule D X N
    termCast k D X N h (d • v) = d • termCast k D X N h v := by
  subst b
  rfl

/-- The complete finite-sum suffix map has its original D action. -/
theorem innerEmbedding_smul (r n : ℕ) (d : D) (v : RecursiveTotal.flat B Z r n) :
    letI : Module A N := inflatedModule D X N
    innerEmbedding k D X N r n (d • v) =
      (inl d : A) • innerEmbedding k D X N r n v := by
  let : Module A N := inflatedModule D X N
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
  | of t v =>
    change innerEmbedding k D X N r n
      (d • (RecursiveTotal.lof B Z r n t).hom v) =
        (inl d : A) • innerEmbedding k D X N r n ((RecursiveTotal.lof B Z r n t).hom v)
    rw [← map_smul]
    cases r with
    | zero =>
      cases n with
      | zero =>
        simp only [innerEmbedding, RecursiveTotal.lof, ModuleCat.hom_ofHom,
          DirectSum.lof_eq_of]
        erw [toModule_of_scalar, toModule_of_scalar]
        rfl
      | succ n => simp only [innerEmbedding, LinearMap.zero_apply, smul_zero]
    | succ r =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      erw [innerEmbedding_lof_succ, innerEmbedding_lof_succ, barSuffix_smul,
        termCast_smul]

/-- Every recursive X-leading sum is killed by the square-zero ideal;
the r=0 degree-zero input is killed by the specified inflation. -/
theorem innerEmbedding_ideal_zero (r n : ℕ) (x : X) (v : RecursiveTotal.flat B Z r n) :
    letI : Module A N := inflatedModule D X N
    (inr x : A) • innerEmbedding k D X N r n v = 0 := by
  let : Module A N := inflatedModule D X N
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw, add_zero]
  | of t v =>
    change (inr x : A) • innerEmbedding k D X N r n
      ((RecursiveTotal.lof B Z r n t).hom v) = 0
    cases r with
    | zero =>
      cases n with
      | zero => exact zero_smul D _
      | succ n => simp only [innerEmbedding, LinearMap.zero_apply, smul_zero]
    | succ r =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      erw [innerEmbedding_lof_succ, ← termCast_smul, barSuffix_ideal_zero, map_zero]
end DerivedBar.ParityBridge

end

end OAI
