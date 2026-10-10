import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralLinearExtension

namespace OAI

/-! # Coordinate generators and the standard embedding of the integral lattice -/

noncomputable section
namespace PolycyclicRecognition

def integralLatticeGenerator (n : ℕ) (i : Fin n) : IntegralLatticeGroup n :=
  Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin n)) i)

theorem integralLatticeGenerator_prod (n : ℕ) (z : IntegralLatticeGroup n) :
    (∏ i, integralLatticeGenerator n i ^ z.toAdd i) = z := by
  apply Multiplicative.toAdd.injective
  simpa only [toAdd_prod, toAdd_zpow, integralLatticeGenerator, toAdd_ofAdd,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
    (Pi.basisFun ℤ (Fin n)).sum_equivFun z.toAdd

theorem integralLatticeGenerator_closure (n : ℕ) :
    Subgroup.closure (Set.range (integralLatticeGenerator n)) = ⊤ := by
  apply top_unique
  intro z _
  rw [← integralLatticeGenerator_prod n z]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _
    (Subgroup.subset_closure (Set.mem_range_self i)) _

theorem integralLattice_hom_ext {n : ℕ} {K : Type*} [Group K]
    {f g : IntegralLatticeGroup n →* K}
    (h : ∀ i, f (integralLatticeGenerator n i) = g (integralLatticeGenerator n i)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense (integralLatticeGenerator_closure n)
  rintro _ ⟨i, rfl⟩
  exact h i

def integerVectorHom (n : ℕ) : IntegralLatticeGroup n →* Multiplicative (Fin n → ℝ) where
  toFun z := Multiplicative.ofAdd (integerVectorMap n z.toAdd)
  map_one' := by apply Multiplicative.ext; exact (integerVectorMap n).map_zero
  map_mul' z w := by apply Multiplicative.ext; exact (integerVectorMap n).map_add z.toAdd w.toAdd

theorem integerVectorHom_injective (n : ℕ) : Function.Injective (integerVectorHom n) := by
  intro z w h
  exact Multiplicative.ext (integerVectorMap_injective n (congrArg Multiplicative.toAdd h))

def integerVectorRangeEquiv (n : ℕ) : IntegralLatticeGroup n ≃* (integerVectorHom n).range :=
  MulEquiv.ofBijective (integerVectorHom n).rangeRestrict
    ⟨fun _ _ h => integerVectorHom_injective n (congrArg Subtype.val h),
      (integerVectorHom n).rangeRestrict_surjective⟩

theorem integerVectorHom_range (n : ℕ) : (integerVectorHom n).range = standardVectorLattice n := by
  ext x
  change (∃ z : IntegralLatticeGroup n,
    Multiplicative.ofAdd (integerVectorMap n z.toAdd) = x) ↔
      x.toAdd ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
  constructor
  · rintro ⟨z, rfl⟩
    exact integerVectorMap_mem n z.toAdd
  · intro hx
    obtain ⟨z, hz⟩ := exists_integerVectorMap_of_mem n x.toAdd hx
    exact ⟨Multiplicative.ofAdd z, Multiplicative.ext hz⟩

theorem integerVectorHom_uniform (n : ℕ) : IsUniformLattice (integerVectorHom n).range := by
  rw [integerVectorHom_range]
  exact standardVectorLattice_uniform n

end PolycyclicRecognition

end

end OAI
