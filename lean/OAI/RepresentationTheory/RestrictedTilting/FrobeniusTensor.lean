import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.SteinbergDuality
import OAI.RepresentationTheory.RestrictedTilting.TensorLimits

namespace OAI

/-! Binary Frobenius multiplication and Steinberg twists of filtrations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

lemma expand_homogeneous {n : ℕ} (p : ℕ)
    (f : MvPolynomial (Fin 2) k) (hf : f.IsHomogeneous n) :
    (MvPolynomial.expand p f).IsHomogeneous (p*n) := by
  exact hf.aeval (fun i => MvPolynomial.X i ^ p)
    (fun i => by simpa using (MvPolynomial.isHomogeneous_X k i).pow p)

noncomputable def binaryFrobeniusMultiply (p b : ℕ) :
    Binary k (p-1) ⊗[k] Binary k b →ₗ[k] Binary k (p-1+p*b) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => ⟨f.val * MvPolynomial.expand p g.val,
            f.property.mul (expand_homogeneous k p g.val g.property)⟩
          map_add' := by intro g h; apply Subtype.ext; simp [mul_add]
          map_smul' := by intro c g; apply Subtype.ext; simp }
      map_add' := by intro f g; ext h : 1; apply Subtype.ext; simp [add_mul]
      map_smul' := by intro c f; ext g : 1; apply Subtype.ext; simp }

@[simp] lemma binaryFrobeniusMultiply_tmul (p b : ℕ)
    (f : Binary k (p-1)) (g : Binary k b) :
    (binaryFrobeniusMultiply k p b (f ⊗ₜ[k] g)).val =
      f.val * MvPolynomial.expand p g.val := rfl

lemma binaryFrobeniusMultiply_surjective (p b : ℕ) (hp : 0 < p) :
    Function.Surjective (binaryFrobeniusMultiply k p b) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (binaryBasis k (p-1+p*b)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have hj : i.val % p < p := Nat.mod_lt _ hp
  have hil : i.val < p*(b+1) := by have := i.isLt; nlinarith [Nat.sub_add_cancel hp]
  have hl : i.val / p < b+1 := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using hil)
  let j : Fin (p-1+1) := ⟨i.val % p, by omega⟩
  let l : Fin (b+1) := ⟨i.val / p, hl⟩
  refine ⟨binaryBasis k (p-1) j ⊗ₜ[k] binaryBasis k b l, ?_⟩
  apply Subtype.ext
  simp only [binaryFrobeniusMultiply_tmul, binaryBasis_apply, map_mul, map_pow,
    MvPolynomial.expand_X, ← pow_mul]
  rw [mul_mul_mul_comm, ← pow_add, ← pow_add]
  have hi : j.val + p*l.val = i.val := Nat.mod_add_div _ _
  have hnot : l.val ≤ b := by omega
  have h₁ : (p-1-j.val) + p*(b-l.val) = p-1+p*b-i.val := by
    rw [Nat.mul_sub_left_distrib]
    have hpj : j.val ≤ p-1 := by dsimp [j]; omega
    have hpb : p*l.val ≤ p*b := Nat.mul_le_mul_left _ hnot
    omega
  rw [h₁, hi]

lemma binaryFrobeniusMultiply_bijective (p b : ℕ) (hp : 0 < p) :
    Function.Bijective (binaryFrobeniusMultiply k p b) := by
  have he : Module.finrank k (Binary k (p-1) ⊗[k] Binary k b) =
      Module.finrank k (Binary k (p-1+p*b)) := by
    rw [Module.finrank_tensorProduct, binaryBasis_finrank, binaryBasis_finrank,
      binaryBasis_finrank]
    nlinarith [Nat.sub_add_cancel hp]
  constructor
  · apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := k)
      (V := Binary k (p-1) ⊗[k] Binary k b) (V₂ := Binary k (p-1+p*b))
      he (f := binaryFrobeniusMultiply k p b)).mpr
    exact binaryFrobeniusMultiply_surjective k p b hp
  · exact binaryFrobeniusMultiply_surjective k p b hp

variable (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable def frobeniusSL2 : SL2 k →* SL2 k :=
  Matrix.SpecialLinearGroup.map (frobenius k p)

lemma dualMatrix_frobeniusSL2 (g : SL2 k) :
    dualMatrix k (frobeniusSL2 k p g) =
      (frobenius k p).mapMatrix (dualMatrix k g) := by
  change ((↑((frobeniusSL2 k p g)⁻¹) : Matrix (Fin 2) (Fin 2) k)).transpose = _
  rw [← map_inv]
  rfl

lemma linearChange_expand (A : Matrix (Fin 2) (Fin 2) k) (f : MvPolynomial (Fin 2) k) :
    linearChange A (MvPolynomial.expand p f) =
      MvPolynomial.expand p (linearChange ((frobenius k p).mapMatrix A) f) := by
  have he : (linearChange A).comp (MvPolynomial.expand p) =
      (MvPolynomial.expand p).comp (linearChange ((frobenius k p).mapMatrix A)) := by
    ext i : 1
    simp [Fin.sum_univ_two, add_pow_char, mul_pow, frobenius_def, map_pow]
  exact AlgHom.congr_fun he f

lemma binaryFrobeniusMultiply_intertwines (b : ℕ) (g : SL2 k)
    (z : Binary k (p-1) ⊗[k] Binary k b) :
    binaryFrobeniusMultiply k p b
      (Representation.tprod (costandard k (p-1)).ρ
        ((costandard k b).ρ.comp (frobeniusSL2 k p)) g z) =
      (costandard k (p-1+p*b)).ρ g (binaryFrobeniusMultiply k p b z) := by
  change binaryFrobeniusMultiply k p b
    (TensorProduct.map (homogeneousRepresentation (p-1) (dualMatrix k g))
      (homogeneousRepresentation b (dualMatrix k (frobeniusSL2 k p g))) z) =
    homogeneousRepresentation (p-1+p*b) (dualMatrix k g) (binaryFrobeniusMultiply k p b z)
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul f h =>
    apply Subtype.ext
    change linearChange (dualMatrix k g) f.val *
      MvPolynomial.expand p (linearChange (dualMatrix k (frobeniusSL2 k p g)) h.val) =
      linearChange (dualMatrix k g) (f.val * MvPolynomial.expand p h.val)
    rw [map_mul, dualMatrix_frobeniusSL2, linearChange_expand]

end

universe u
variable (k : Type u) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

 
noncomputable def frobeniusTwist : FDRep k (SL2 k) ⥤ FDRep k (SL2 k) :=
  Action.res (FGModuleCat k) (frobeniusSL2 k p)

instance : (frobeniusTwist k p).Additive where
  map_add := by intros; rfl

lemma frobeniusTwist_shortExact (S : ShortComplex (FDRep k (SL2 k)))
    (hS : S.ShortExact) : (S.map (frobeniusTwist k p)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact fdrep_shortExact k _ (fdrep_injective k S.f) (fdrep_surjective k S.g)
    (fdrep_exact k (S := S) hS.exact)

noncomputable def frobeniusCostandardHom (b : ℕ) :
    costandard k (p-1) ⊗ (frobeniusTwist k p).obj (costandard k b) ⟶
      costandard k (p-1+p*b) :=
  fdrepHom k (binaryFrobeniusMultiply k p b) (binaryFrobeniusMultiply_intertwines k p b)

noncomputable def frobeniusCostandardIso (b : ℕ) :
    costandard k (p-1) ⊗ (frobeniusTwist k p).obj (costandard k b) ≅
      costandard k (p-1+p*b) := by
  let f := frobeniusCostandardHom k p b
  have : IsIso f := fdrepHom_isIso_of_bijective k f
    (binaryFrobeniusMultiply_bijective k p b (Fact.out : p.Prime).pos)
  exact asIso f

 

theorem HasGoodFiltration.steinberg_frobenius {A : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) :
    HasGoodFiltration k (costandard k (p-1) ⊗ (frobeniusTwist k p).obj A) := by
  induction hA with
  | zero A hA =>
    exact .zero _ ((tensorLeft (costandard k (p-1))).map_isZero
      ((frobeniusTwist k p).map_isZero hA))
  | @step A B n f g w hS hA ih =>
    let F := tensorLeft (costandard k (p-1))
    let := tensorLeft_preservesFiniteLimits (costandard k (p-1))
    let := tensorLeft_preservesFiniteColimits (costandard k (p-1))
    have hT := (frobeniusTwist_shortExact k p _ hS).map_of_exact F
    have hc := (costandard_hasGoodFiltration k (p-1+p*n)).of_iso k
      (frobeniusCostandardIso k p n).symm
    exact ih.extension k hc _ _ _ hT


lemma IsRational.frobenius {M : Type u} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (hρ : IsRational k ρ) :
    IsRational k (ρ.comp (frobeniusSL2 k p)) := by
  intro v l
  obtain ⟨P,hP⟩ := hρ v l
  refine ⟨MvPolynomial.expand p P, fun g => ?_⟩
  change l (ρ (frobeniusSL2 k p g) v) = _
  rw [hP]
  change MvPolynomial.eval₂ (RingHom.id k) (fun ij => (g ij.1 ij.2)^p) P =
    MvPolynomial.eval₂ (RingHom.id k) (fun ij => g ij.1 ij.2) (MvPolynomial.expand p P)
  rw [MvPolynomial.eval₂_expand]
  rfl

noncomputable def frobeniusDualIso (A : FDRep k (SL2 k)) :
    ((frobeniusTwist k p).obj A)ᘁ ≅ (frobeniusTwist k p).obj Aᘁ := by
  let f : ((frobeniusTwist k p).obj A)ᘁ ⟶ (frobeniusTwist k p).obj Aᘁ :=
    fdrepHom k LinearMap.id (by
      intro g l
      change Module.Dual k A at l
      rw [fdrep_dual_repr]
      change Representation.dual (A.ρ.comp (frobeniusSL2 k p)) g l =
        Aᘁ.ρ (frobeniusSL2 k p g) l
      rw [fdrep_dual_repr]
      apply LinearMap.ext
      intro x
      change l (A.ρ (frobeniusSL2 k p (g⁻¹)) x) = l (A.ρ ((frobeniusSL2 k p g)⁻¹) x)
      rw [map_inv])
  have : IsIso f := fdrepHom_isIso_of_bijective k f Function.bijective_id
  exact asIso f

variable [Infinite k]

 
theorem IsTilting.steinberg_frobenius {A : FDRep k (SL2 k)} (hA : IsTilting k A) :
    IsTilting k (costandard k (p-1) ⊗ (frobeniusTwist k p).obj A) := by
  have hr : IsRational k ((frobeniusTwist k p).obj A).ρ :=
    IsRational.frobenius k p A.ρ hA.1
  have hrt : IsRational k (costandard k (p-1) ⊗ (frobeniusTwist k p).obj A).ρ :=
    IsRational.tensor k (costandard k (p-1)).ρ ((frobeniusTwist k p).obj A).ρ
      (costandard_rational k (p-1)) hr
  refine ⟨hrt, hA.2.1.steinberg_frobenius k p, ?_⟩
  obtain ⟨hs⟩ := costandard_self_dual_of_choose_ne_zero k (p-1)
    (fun i => choose_cast_ne_zero_of_lt_char k p
      (by have := (Fact.out : p.Prime).pos; omega) (by have := i.isLt; omega))
  let e : (costandard k (p-1) ⊗ (frobeniusTwist k p).obj A)ᘁ ≅
      costandard k (p-1) ⊗ (frobeniusTwist k p).obj Aᘁ :=
    rightDualTensorIso _ _ ≪≫ (tensorIso (frobeniusDualIso k p A) hs) ≪≫
      (β_ _ _)
  exact (hA.2.2.steinberg_frobenius k p).of_iso k e.symm

end FiberFunctorProof
end

end OAI
