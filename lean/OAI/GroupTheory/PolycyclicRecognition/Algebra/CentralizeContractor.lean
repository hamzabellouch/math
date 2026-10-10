import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrbitContractor
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Centralizing a contractor in an abelian-by-finite group

Conjugation on an abelian normal subgroup factors through the finite quotient.
The product over that finite action is central and its action still has a
finitely generated ascending base. This constructs the central element rather
than assuming its existence.
-/

noncomputable section
namespace PolycyclicRecognition
variable {K : Type} [Group K]

def abelianNormalQuotientAction (H : Subgroup K) [H.Normal] [IsMulCommutative H] :
    K ⧸ H →* MulAut H :=
  QuotientGroup.lift H (MulAut.conjNormal (H := H)) (by
    intro h hh
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change h * (x : K) * h⁻¹ = x
    rw [setLike_mul_comm hh x.property, mul_inv_cancel_right])

theorem abelianNormalQuotientAction_mk
    (H : Subgroup K) [H.Normal] [IsMulCommutative H] (g : K) (h : H) :
    ((abelianNormalQuotientAction H ((QuotientGroup.mk' H) g) h : H) : K) =
      g * h * g⁻¹ := rfl

theorem exists_central_ascending_contractor {A : Type} [Group A] [Group.IsNilpotent A]
    (H : Subgroup K) [H.Normal] [H.FiniteIndex] [IsMulCommutative H]
    (ρ : K →* MulAut A) (t : H)
    (ht : HasFinitelyGeneratedAscendingBase (ρ t)) :
    ∃ x : H, (x : K) ∈ Subgroup.center K ∧ HasFinitelyGeneratedAscendingBase (ρ x) := by
  let : CommGroup H := { (inferInstance : Group H) with mul_comm := mul_comm' }
  let : Fintype (K ⧸ H) := Fintype.ofFinite _
  let σ := abelianNormalQuotientAction H
  let ρH := ρ.comp H.subtype
  refine ⟨finiteOrbitProduct σ t, ?_, ?_⟩
  · exact finiteOrbitProduct_central σ H.subtype (QuotientGroup.mk' H)
      (fun _ _ => rfl) t
  · apply finiteOrbitProduct_ascendingBase_of_conjugate σ ρH t ht
    intro f
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H f
    refine ⟨ρ g, ?_⟩
    change ρ (g * (t : K) * g⁻¹) = ρ g * ρ t * (ρ g)⁻¹
    rw [map_mul, map_mul, map_inv]

theorem HasFinitelyGeneratedAscendingBase.pow {G : Type} [Group G]
    {α : MulAut G} (hα : HasFinitelyGeneratedAscendingBase α)
    {r : ℕ} (hr : 0 < r) : HasFinitelyGeneratedAscendingBase (α ^ r) := by
  obtain ⟨B, hBfg, hBstable, hBcover⟩ := hα
  refine ⟨B, hBfg, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact automorphism_pow_mem_of_stable α B hBstable r hg
  · intro g
    obtain ⟨n, hn⟩ := hBcover g
    refine ⟨n, (mem_automorphismStage_iff _ _ _ _).mpr ?_⟩
    rw [← pow_mul]
    apply (mem_automorphismStage_iff _ _ _ _).mp
    apply automorphismStage_monotone α B hBstable (show n ≤ r * n by nlinarith)
    exact hn

theorem exists_central_ascending_contractor_of_finiteIndex
    {A : Type} [Group A] [Group.IsNilpotent A]
    (H : Subgroup K) [H.Normal] [H.FiniteIndex] [IsMulCommutative H]
    (ρ : K →* MulAut A) (t : K)
    (ht : HasFinitelyGeneratedAscendingBase (ρ t)) :
    ∃ x : K, x ∈ Subgroup.center K ∧ HasFinitelyGeneratedAscendingBase (ρ x) := by
  obtain ⟨r, hr, htr⟩ := (isOfFinOrder_of_finite ((QuotientGroup.mk' H) t)).exists_pow_eq_one
  have hpow : t ^ r ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' H) (t ^ r) = 1
    rw [map_pow]
    exact htr
  have hbase : HasFinitelyGeneratedAscendingBase (ρ (t ^ r)) := by
    rw [map_pow]
    exact ht.pow hr
  obtain ⟨x, hx, hxbase⟩ := exists_central_ascending_contractor H ρ ⟨t ^ r, hpow⟩ hbase
  exact ⟨x, hx, hxbase⟩

end PolycyclicRecognition

end

end OAI
