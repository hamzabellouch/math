import OAI.Algebra.Finitistic.Bar.LeadingTotalDifferential

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
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
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "DB" => barFunctor k D
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local notation "I" => RecursiveTotal.iter B Z
local notation "K" => barBicomplex k D
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

theorem outerCast_smul {a b : ℕ} (h : a=b) (z : k)
    (v : D ⊗[k] term k A N a) :
    outerCast k D X N h (z • v) = z • outerCast k D X N h v := by
  subst b
  simp only [outerCast_refl, LinearMap.id_apply]

theorem leadingTotalComparison_positive (r n i q : ℕ) (h : i+(q+1)=n+1)
    (v : (((DB).obj ((I r).X (q+1))).X i)) :
    SquareZero.multibarTwoSidedDifferential k D X N (r+n)
      (outerCast k D X N (show (r+(q+1))+i=r+(n+1) by omega)
        (outerBarSuffix k D X N ((I r).X (q+1)) (r+(q+1)) i
          (innerTotalEmbedding k D X N r (q+1)) v)) =
    (((K (I r)).d₁ c i (q+1) n ≫ leadingTotalEmbedding k D X N r n).hom v) +
      (((K (I r)).d₂ c i (q+1) n ≫ leadingTotalEmbedding k D X N r n).hom v) := by
  have hδ : (SquareZero.multibarAugmentedDifferential k D X N (r+q)).comp
      (innerTotalEmbedding k D X N r (q+1)) =
    -((innerTotalEmbedding k D X N r q).comp (((I r).d (q+1) q).hom.restrictScalars k)) := by
    ext w
    exact innerTotalEmbedding_differential k D X N r q w
  cases i with
  | zero =>
    have hn : n=q := by omega
    subst n
    simp only [Nat.add_zero, outerCast_refl, LinearMap.id_apply]
    erw [parity_outerBarSuffix_zero k D X N ((I r).X (q+1)) (r+q)
      (innerTotalEmbedding k D X N r (q+1))
      (fun w => innerTotalEmbedding_coefficient_of_pos k D X N r (q+1) (r+q) rfl w)]
    rw [hδ, outerBarSuffix_neg, LinearMap.neg_apply, neg_neg]
    rw [leadingTotalEmbedding_d₁_zero]
    erw [leadingTotalEmbedding_d₂ k D X N r q 0 q h v]
    simp only [ModuleCat.hom_zero,
      pow_zero, one_smul, Nat.add_zero, outerCast_refl, LinearMap.id_apply]
    erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
      (M₂ := D ⊗[k] term k A N (r+q)) v, zero_add]
  | succ i =>
    erw [twoSidedParity_outerCast k D X N
      (show (r+(q+1))+i=r+n by omega)
      (show ((r+(q+1))+i)+1=(r+n)+1 by omega)]
    erw [parity_outerBarSuffix k D X N ((I r).X (q+1)) (r+q) i
      (innerTotalEmbedding k D X N r (q+1)) (innerTotalEmbedding_smul k D X N r (q+1))]
    simp only [hδ, outerBarSuffix_neg, LinearMap.neg_apply, map_add, outerCast_smul, map_neg]
    erw [leadingTotalEmbedding_d₁ k D X N r n i (q+1) h v]
    erw [leadingTotalEmbedding_d₂ k D X N r n (i+1) q h v]
    apply congrArg₂ (· + ·) (by rfl)
    let w := outerBarSuffix k D X N ((I r).X (q+1)) (r+q) (i+1)
      ((innerTotalEmbedding k D X N r q).comp (((I r).d (q+1) q).hom.restrictScalars k)) v
    have hc := outerCast_trans k D X N
      (show (r+q)+(i+1)=(r+q+1)+i by omega)
      (show (r+q+1)+i=r+n by omega) w
    change (-1:k)^i • -(outerCast k D X N (show (r+q+1)+i=r+n by omega)
      (outerCast k D X N (show (r+q)+(i+1)=(r+q+1)+i by omega) w)) =
      (-1:k)^(i+1) • outerCast k D X N (show (r+q)+(i+1)=r+n by omega) w
    rw [hc]
    have hs : (-1:k)^(i+1) = -((-1:k)^i) := by rw [pow_succ, mul_neg_one]
    rw [hs]
    exact (smul_neg _ _).trans (_root_.neg_smul _ _).symm

theorem leadingTotalComparison_bottom (r n i : ℕ) (h : i+0=n+1)
    (v : (((DB).obj ((I r).X 0)).X i)) :
    SquareZero.multibarTwoSidedDifferential k D X N (r+n)
      (outerCast k D X N (show (r+0)+i=r+(n+1) by omega)
        (outerBarSuffix k D X N ((I r).X 0) (r+0) i
          (innerTotalEmbedding k D X N r 0) v)) =
    (((K (I r)).d₁ c i 0 n ≫ leadingTotalEmbedding k D X N r n).hom v) +
      (((K (I r)).d₂ c i 0 n ≫ leadingTotalEmbedding k D X N r n).hom v) := by
  have hi : i=n+1 := by omega
  subst i
  simp only [Nat.add_zero, outerCast_refl, LinearMap.id_apply]
  rw [leadingTotalEmbedding_d₂_zero]
  simp only [ModuleCat.hom_zero]
  erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
    (M₂ := D ⊗[k] term k A N (r+n)) v]
  simp only [add_zero]
  erw [leadingTotalEmbedding_d₁ k D X N r n n 0 h v]
  simp only [Nat.add_zero, outerCast_refl, LinearMap.id_apply]
  cases r with
  | zero =>
    rw [innerTotalEmbedding_zero]
    exact parity_outerBarSuffix_terminal k D X N n v
  | succ r =>
    erw [parity_outerBarSuffix k D X N ((I (r+1)).X 0) r n
      (innerTotalEmbedding k D X N (r+1) 0) (innerTotalEmbedding_smul k D X N (r+1) 0)]
    have hz : (SquareZero.multibarAugmentedDifferential k D X N r).comp
      (innerTotalEmbedding k D X N (r+1) 0) = 0 := by
      ext w
      exact innerTotalEmbedding_bottom k D X N r w
    simp only [hz, outerBarSuffix_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]

/-- The canonical leading total embedding intertwines its original total
horizontal/vertical differential with the literal square-zero-extension faces. -/
theorem leadingTotalEmbedding_differential (r n : ℕ) :
    leadingTotalEmbedding k D X N r (n+1) ≫
      ModuleCat.ofHom (SquareZero.multibarTwoSidedDifferential k D X N (r+n)) =
    (barTotal k D (I r)).d (n+1) n ≫ leadingTotalEmbedding k D X N r n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i q h
  erw [← Category.assoc, leadingTotalEmbedding_ι, leadingTotalEmbedding_ι_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change SquareZero.multibarTwoSidedDifferential k D X N (r+n)
    (outerCast k D X N _ (outerBarSuffix k D X N ((I r).X q) (r+q) i
      (innerTotalEmbedding k D X N r q) v)) = _
  cases q with
  | zero => exact leadingTotalComparison_bottom k D X N r n i h v
  | succ q => exact leadingTotalComparison_positive k D X N r n i q h v
end DerivedBar.ParityBridge

end

end OAI
