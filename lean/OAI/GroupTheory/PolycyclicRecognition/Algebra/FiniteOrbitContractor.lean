import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingAscendingBases

namespace OAI

/-! # A contractor fixed by a finite group

Products of commuting ascending actions retain an ascending base. Consequently
the product of a finite orbit of contracting elements is invariant and remains
contracting. This is the finite conjugation step in KMN, Lemma 2.2; no assertion
that an FP-infinity group supplies an initial contractor is made here.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A Q F : Type} [Group A] [Group.IsNilpotent A] [CommGroup Q]

theorem ascendingBase_finite_product (ρ : Q →* MulAut A) {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (q : ι → Q)
    (hq : ∀ i ∈ s, HasFinitelyGeneratedAscendingBase (ρ (q i))) :
    HasFinitelyGeneratedAscendingBase (ρ (∏ i ∈ s, q i)) := by
  apply Finset.prod_induction_nonempty q
    (fun x => HasFinitelyGeneratedAscendingBase (ρ x)) ?_ hs hq
  intro x y hx hy
  rw [map_mul]
  exact hx.mul hy (by
    change ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm])

variable [Group F] [Fintype F]

def finiteOrbitProduct (σ : F →* MulAut Q) (q : Q) : Q := ∏ f : F, σ f q

theorem finiteOrbitProduct_fixed (σ : F →* MulAut Q) (q : Q) (f : F) :
    σ f (finiteOrbitProduct σ q) = finiteOrbitProduct σ q := by
  unfold finiteOrbitProduct
  rw [map_prod]
  apply Fintype.prod_equiv (Equiv.mulLeft f)
  intro g
  change σ f (σ g q) = σ (f * g) q
  rw [map_mul, MulAut.mul_apply]

theorem finiteOrbitProduct_ascendingBase (σ : F →* MulAut Q)
    (ρ : Q →* MulAut A) (q : Q)
    (hq : ∀ f, HasFinitelyGeneratedAscendingBase (ρ (σ f q))) :
    HasFinitelyGeneratedAscendingBase (ρ (finiteOrbitProduct σ q)) := by
  exact ascendingBase_finite_product ρ Finset.univ Finset.univ_nonempty
    (fun f => σ f q) (fun f _ => hq f)

theorem finiteOrbitProduct_central {K : Type} [Group K]
    (σ : F →* MulAut Q) (ι : Q →* K) (π : K →* F)
    (hconj : ∀ (g : K) (q : Q), ι (σ (π g) q) = g * ι q * g⁻¹) (q : Q) :
    ι (finiteOrbitProduct σ q) ∈ Subgroup.center K := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  have h := hconj g (finiteOrbitProduct σ q)
  rw [finiteOrbitProduct_fixed] at h
  exact mul_inv_eq_iff_eq_mul.mp h.symm

theorem HasFinitelyGeneratedAscendingBase.conj {G : Type} [Group G]
    {α : MulAut G} (hα : HasFinitelyGeneratedAscendingBase α) (γ : MulAut G) :
    HasFinitelyGeneratedAscendingBase (γ * α * γ⁻¹) := by
  apply hα.of_equiv γ.symm (γ * α * γ⁻¹) α
  intro g
  change γ.symm (γ (α (γ.symm g))) = α (γ.symm g)
  exact γ.symm_apply_apply _

theorem finiteOrbitProduct_ascendingBase_of_conjugate (σ : F →* MulAut Q)
    (ρ : Q →* MulAut A) (q : Q)
    (hq : HasFinitelyGeneratedAscendingBase (ρ q))
    (hconj : ∀ f, ∃ γ : MulAut A, ρ (σ f q) = γ * ρ q * γ⁻¹) :
    HasFinitelyGeneratedAscendingBase (ρ (finiteOrbitProduct σ q)) := by
  apply finiteOrbitProduct_ascendingBase σ ρ q
  intro f
  obtain ⟨γ, hγ⟩ := hconj f
  rw [hγ]
  exact hq.conj γ

end PolycyclicRecognition

end

end OAI
