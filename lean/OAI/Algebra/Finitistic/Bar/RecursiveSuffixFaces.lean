import OAI.Algebra.Finitistic.Bar.RecursiveSuffixEmbedding

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
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- The original augmented parity operator commutes with degree transport. -/
theorem parity_termCast {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (v : term k A N (a+1)) :
    SquareZero.multibarAugmentedDifferential k D X N b (termCast k D X N h' v) =
      termCast k D X N h (SquareZero.multibarAugmentedDifferential k D X N a v) := by
  subst b
  rfl

/-- Positive-block face comparison for the actual categorical bar functor. -/
theorem parity_barSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : V), e (d • v) = (inl d : A) • e v)
    (v : ((XB).obj V).X (i+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (((s+1)+i)+1)
      (barSuffix k D X N V (s+1) (i+1) e v) =
    -barSuffix k D X N V (s+1) i e ((((XB).obj V).d (i+1) i).hom v) +
      (-1:k)^(i+1) • termCast k D X N (show (s+(i+1))+1=((s+1)+i)+1 by omega)
        (barSuffix k D X N V s (i+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.twoSidedBarObjIso_d k D X V i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [h]
  exact parity_idealSuffixEmbed k D X N V s i e he _

/-- Empty blocks retain the suffix face with no extra sign. -/
theorem parity_barSuffix_zero (V : ModuleCat.{u} D) (s : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ (x : X) (v : V), (inr x : A) • e v = 0)
    (v : ((XB).obj V).X 0) :
    SquareZero.multibarAugmentedDifferential k D X N (s+1)
      (barSuffix k D X N V (s+1) 0 e v) =
    barSuffix k D X N V s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v :=
  parity_idealSuffixEmbed_zero k D X N V s e he _

/-- A terminal empty block has zero face by the actual inflation of N. -/
theorem parity_barSuffix_endpoint (V : ModuleCat.{u} D)
    (e : V →ₗ[k] term k A N 0) (v : ((XB).obj V).X 0) :
    SquareZero.multibarAugmentedDifferential k D X N 0
      (barSuffix k D X N V 0 0 e v) = 0 := by
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V 0).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul x w =>
    exact SquareZero.multibarAugmented_ideal_endpoint k D X N
      (fun _ v => zero_smul D v) x (e w)
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- Prefix insertion is linear in the complete suffix map. -/
theorem barSuffix_neg (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    barSuffix k D X N V s i (-e) = -barSuffix k D X N V s i e := by
  ext v
  unfold barSuffix
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul x w =>
    change (inr x : A) ⊗ₜ[k] suffixEmbed k D X N V s (-e) i w =
      -((inr x : A) ⊗ₜ[k] suffixEmbed k D X N V s e i w)
    rw [← neg_one_smul k e, suffixEmbed_smul_map, neg_one_smul, TensorProduct.tmul_neg]
  | add v w hv hw => simp only [map_add, neg_add, hv, hw]

theorem barSuffix_zero (V : ModuleCat.{u} D) (s i : ℕ) :
    barSuffix k D X N V s i 0 = 0 := by
  ext v
  unfold barSuffix
  simp only [LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using TensorProduct.inductionOn with
  | tmul x w =>
    change (inr x : A) ⊗ₜ[k] suffixEmbed k D X N V s 0 i w = 0
    have hz := suffixEmbed_smul_map k D X N V s i (0:k) (0 : V →ₗ[k] term k A N s) w
    simp only [zero_smul] at hz
    rw [hz, TensorProduct.tmul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- Prefix insertion commutes with exact degree casts on a suffix. -/
theorem barSuffix_termCast (V : ModuleCat.{u} D) {a b : ℕ} (h : a=b) (i : ℕ)
    (e : V →ₗ[k] term k A N a) (v : ((XB).obj V).X i) :
    barSuffix k D X N V b i ((termCast k D X N h).comp e) v =
      termCast k D X N (show (a+i)+1=(b+i)+1 by omega)
        (barSuffix k D X N V a i e v) := by
  subst b
  rfl

theorem suffixEmbed_id (i : ℕ) (v : term k D N i) :
    suffixEmbed k D X N N 0 LinearMap.id i v =
      termCast k D X N (Nat.zero_add i).symm (baseEmbed k D X N i v) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, baseEmbed_tmul, ih]
      exact (termCast_tmul k D X N (Nat.zero_add i).symm
        (show i+1=(0+i)+1 by omega) (inl d) (baseEmbed k D X N i v)).symm
    | add v w hv hw => simp only [map_add, hv, hw]

theorem idealSuffixEmbed_id (i : ℕ) (v : X ⊗[k] term k D N i) :
    idealSuffixEmbed k D X N N 0 i LinearMap.id v =
      termCast k D X N (show i+1=(0+i)+1 by omega) (idealEmbed k D X N i v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    rw [idealSuffixEmbed_tmul, idealEmbed_tmul,
      termCast_tmul k D X N (Nat.zero_add i).symm, suffixEmbed_id]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The degree-zero input embedding is the identity on its sole summand. -/
theorem innerEmbedding_zero_lof (t : RecursiveTotal.Index 0 0) :
    (innerEmbedding k D X N 0 0).comp
      ((RecursiveTotal.lof B Z 0 0 t).hom.restrictScalars k) = LinearMap.id := by
  ext v
  simp only [innerEmbedding, RecursiveTotal.lof, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, DirectSum.lof_eq_of]
  erw [toModule_of_scalar]

/-- The terminal positive X bar has exactly minus its original bar differential. -/
theorem parity_barSuffix_terminal (i : ℕ) (v : ((XB).obj N).X (i+1)) :
    SquareZero.multibarAugmentedDifferential k D X N ((0+i)+1)
      (barSuffix k D X N N 0 (i+1) LinearMap.id v) =
    -barSuffix k D X N N 0 i LinearMap.id
      ((((XB).obj N).d (i+1) i).hom v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.twoSidedBarObjIso_d k D X N i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [h]
  rw [idealSuffixEmbed_id, idealSuffixEmbed_id]
  erw [parity_termCast k D X N (show i+1=(0+i)+1 by omega)
    (show (i+1)+1=((0+i)+1)+1 by omega)]
  rw [inflated_parity_idealEmbed, map_neg]

/-- The augmented bottom face vanishes at every recursive depth. -/
theorem innerEmbedding_bottom (r : ℕ) (v : RecursiveTotal.flat B Z (r+1) 0) :
    SquareZero.multibarAugmentedDifferential k D X N r
      (termCast k D X N (show (r+1)+0=r+1 by omega)
        (innerEmbedding k D X N (r+1) 0 v)) = 0 := by
  induction r with
  | zero =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      have hi : i=0 := by omega
      have hq : q=0 := by omega
      subst i; subst q
      change SquareZero.multibarAugmentedDifferential k D X N 0
        (innerEmbedding k D X N 1 0 ((RecursiveTotal.lof B Z 1 0 _).hom v)) = 0
      rw [innerEmbedding_lof_succ]
      exact parity_barSuffix_endpoint k D X N _ _ v
  | succ r ih =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      have hi : i=0 := by omega
      have hq : q=0 := by omega
      subst i; subst q
      change SquareZero.multibarAugmentedDifferential k D X N (r+1)
        (innerEmbedding k D X N (r+1+1) 0 ((RecursiveTotal.lof B Z (r+1+1) 0 _).hom v)) = 0
      rw [innerEmbedding_lof_succ]
      change SquareZero.multibarAugmentedDifferential k D X N (r+1)
        (barSuffix k D X N _ (r+1) 0 _ v) = 0
      erw [parity_barSuffix_zero k D X N _ r _
        (fun x w => innerEmbedding_ideal_zero k D X N (r+1) 0 x
          ((RecursiveTotal.lof B Z (r+1) 0 t).hom w))]
      have hz : (SquareZero.multibarAugmentedDifferential k D X N r).comp
          ((innerEmbedding k D X N (r+1) 0).comp
            ((RecursiveTotal.lof B Z (r+1) 0 t).hom.restrictScalars k)) = 0 := by
        ext w
        exact ih _
      rw [hz]
      rw [barSuffix_zero]
      rfl
end DerivedBar.ParityBridge

end

end OAI
