import OAI.Algebra.Finitistic.Bar.RecursiveSuffixDifferential

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
local instance recursiveSuffixInductionIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

theorem innerEmbedding_generator_positive (r n i q : ℕ) (h : i+(q+1)=n+1)
    (t : RecursiveTotal.Index r (q+1))
    (ih : ∀ (v : RecursiveTotal.flat B Z r (q+1)),
      SquareZero.multibarAugmentedDifferential k D X N (r+q)
        (innerEmbedding k D X N r (q+1) v) =
      -innerEmbedding k D X N r q ((RecursiveTotal.differential B Z r q).hom v))
    (v : RecursiveTotal.summand B Z (r+1) (n+1) ⟨⟨⟨i,q+1⟩,h⟩,t⟩) :
    SquareZero.multibarAugmentedDifferential k D X N ((r+1)+n)
      (innerEmbedding k D X N (r+1) (n+1)
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q+1⟩,h⟩,t⟩).hom v)) =
    -innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.differential B Z (r+1) n).hom
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q+1⟩,h⟩,t⟩).hom v)) := by
  erw [innerEmbedding_differential_lof, neg_add, innerEmbedding_lof_succ]
  have hδ := innerEmbedding_suffix_induction k D X N r q t ih
  let V := RecursiveTotal.summand B Z r (q+1) t
  let e : V →ₗ[k] term k A N ((r+q)+1) :=
    (innerEmbedding k D X N r (q+1)).comp
      ((RecursiveTotal.lof B Z r (q+1) t).hom.restrictScalars k)
  have he : ∀ (d : D) (w : V), e (d • w) = (inl d : A) • e w := by
    intro d w
    change innerEmbedding k D X N r (q+1)
      ((RecursiveTotal.lof B Z r (q+1) t).hom (d • w)) =
        (inl d : A) • innerEmbedding k D X N r (q+1)
          ((RecursiveTotal.lof B Z r (q+1) t).hom w)
    rw [map_smul]
    exact innerEmbedding_smul k D X N r (q+1) d _
  cases i with
  | zero =>
    have hn : n=q := by omega
    subst n
    erw [parity_termCast k D X N (show ((r+(q+1))+0)=(r+1)+q by omega)
      (show ((r+(q+1))+0)+1=((r+1)+q)+1 by omega)]
    erw [parity_barSuffix_zero k D X N V (r+q) e
      (fun x w => innerEmbedding_ideal_zero k D X N r (q+1) x
        ((RecursiveTotal.lof B Z r (q+1) t).hom w))]
    erw [hδ, barSuffix_neg, LinearMap.neg_apply, map_neg, innerEmbedding_vertical]
    simp only [RecursiveTotal.horizontal, ModuleCat.hom_zero, pow_zero, one_smul]
    erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
      (M₂ := RecursiveTotal.flat B Z (r+1) q) v]
    simp only [map_zero, neg_zero, zero_add]
    rfl
  | succ i =>
    erw [parity_termCast k D X N (show ((r+(q+1))+(i+1))=(r+1)+n by omega)
      (show ((r+(q+1))+(i+1))+1=((r+1)+n)+1 by omega)]
    erw [parity_barSuffix k D X N V (r+q) i e he]
    simp only [e, hδ, barSuffix_neg, map_add, map_neg, map_smul]
    erw [LinearMap.neg_apply, map_neg, map_neg, smul_neg]
    erw [innerEmbedding_horizontal k D X N r n i (q+1) h t v]
    erw [innerEmbedding_vertical k D X N r n (i+1) q h t (RecursiveTotal.differential B Z r) v]
    erw [termCast_trans k D X N
      (show ((r+q)+(i+1))+1=((r+q+1)+i)+1 by omega)
      (show ((r+q+1)+i)+1=(r+1)+n by omega)]
    rfl

/-- A zero final input term cannot contribute an element, at any recursive depth. -/
theorem innerSummand_positive_input_zero (r n : ℕ) (t : RecursiveTotal.Index r n)
    (h : RecursiveTotal.inputDegree r t ≠ 0) (v : RecursiveTotal.summand B Z r n t) : v=0 := by
  have hz := RecursiveTotal.summand_isZero B Z r n t
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 N _ h)
  exact congrArg (fun f : RecursiveTotal.summand B Z r n t ⟶
    RecursiveTotal.summand B Z r n t => f.hom v) (hz.eq_of_src (𝟙 _) 0)

/-- The only remaining generator case has suffix total degree zero. Its tail
face vanishes by the already proved augmented bottom identity. -/
theorem innerEmbedding_generator_bottom (r n i : ℕ) (h : i+0=n+1)
    (t : RecursiveTotal.Index r 0)
    (v : RecursiveTotal.summand B Z (r+1) (n+1) ⟨⟨⟨i,0⟩,h⟩,t⟩) :
    SquareZero.multibarAugmentedDifferential k D X N ((r+1)+n)
      (innerEmbedding k D X N (r+1) (n+1)
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,0⟩,h⟩,t⟩).hom v)) =
    -innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.differential B Z (r+1) n).hom
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,0⟩,h⟩,t⟩).hom v)) := by
  have hi : i=n+1 := by omega
  subst i
  erw [innerEmbedding_differential_lof, innerEmbedding_lof_succ]
  simp only [RecursiveTotal.vertical, ModuleCat.hom_zero]
  erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
    (M₂ := RecursiveTotal.flat B Z (r+1) n) v]
  simp only [map_zero, add_zero]
  erw [innerEmbedding_horizontal]
  cases r with
  | zero =>
    cases t
    erw [innerEmbedding_zero_lof]
    erw [parity_termCast k D X N (show (0+0)+(n+1)=(0+1)+n by omega)
      (show ((0+0)+(n+1))+1=((0+1)+n)+1 by omega)]
    erw [parity_barSuffix_terminal, map_neg]
    rfl
  | succ r =>
    erw [parity_termCast k D X N (show ((r+1)+0)+(n+1)=((r+1)+1)+n by omega)
      (show (((r+1)+0)+(n+1))+1=(((r+1)+1)+n)+1 by omega)]
    erw [parity_barSuffix k D X N (RecursiveTotal.summand B Z (r+1) 0 t) r n
      ((innerEmbedding k D X N (r+1) 0).comp
        ((RecursiveTotal.lof B Z (r+1) 0 t).hom.restrictScalars k))
      (fun d w => by
        change innerEmbedding k D X N (r+1) 0
          ((RecursiveTotal.lof B Z (r+1) 0 t).hom (d • w)) =
            (inl d : A) • innerEmbedding k D X N (r+1) 0
              ((RecursiveTotal.lof B Z (r+1) 0 t).hom w)
        rw [map_smul]
        exact innerEmbedding_smul k D X N (r+1) 0 d _)]
    have hz : (SquareZero.multibarAugmentedDifferential k D X N r).comp
        ((innerEmbedding k D X N (r+1) 0).comp
          ((RecursiveTotal.lof B Z (r+1) 0 t).hom.restrictScalars k)) = 0 := by
      ext w
      exact innerEmbedding_bottom k D X N r _
    simp only [hz, barSuffix_zero]
    erw [LinearMap.zero_apply]
    simp only [map_zero, smul_zero, add_zero, map_neg]

/-- The canonical inner finite-sum embedding compares the actual independently
recursive differential with minus augmented slot parity, at every depth and degree. -/
theorem innerEmbedding_differential (r n : ℕ) (v : RecursiveTotal.flat B Z r (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (r+n)
      (innerEmbedding k D X N r (n+1) v) =
    -innerEmbedding k D X N r n ((RecursiveTotal.differential B Z r n).hom v) := by
  induction r generalizing n with
  | zero =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero, neg_zero]
    | add v w hv hw => simp only [map_add, hv, hw, neg_add]
    | of t v =>
      have hv := innerSummand_positive_input_zero k D X N 0 (n+1) t (by simp [RecursiveTotal.inputDegree]) v
      subst v
      simp only [map_zero, neg_zero]
  | succ r ih =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero, neg_zero]
    | add v w hv hw => simp only [map_add, hv, hw, neg_add]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      change SquareZero.multibarAugmentedDifferential k D X N ((r+1)+n)
        (innerEmbedding k D X N (r+1) (n+1)
          ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v)) = _
      cases q with
      | zero => exact innerEmbedding_generator_bottom k D X N r n i h t v
      | succ q => exact innerEmbedding_generator_positive k D X N r n i q h t (ih q) v
end DerivedBar.ParityBridge

end

end OAI
