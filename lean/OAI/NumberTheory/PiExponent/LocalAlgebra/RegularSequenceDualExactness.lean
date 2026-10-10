import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open Module
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem iterateScalarCones_dual_low_exact (rs : List R) (n : ℕ)
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R)
    (e : P.X (n + 1) ≃ₗ[R] R)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I)
    (hreg : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    ∀ k, k + 1 < n + 1 + rs.length →
      LinearMap.range ((iterateScalarCones P rs).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((iterateScalarCones P rs).d (k + 2) (k + 1)).hom.dualMap := by
  induction rs generalizing n P I with
  | nil =>
    intro k hk
    exact hlow k (by simpa using hk)
  | cons r rs ih =>
    let P' := scalarConeComplex P r
    let I' := I ⊔ Ideal.span {r}
    let e' : P'.X (n + 2) ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv P r (n + 1) hbound).trans e
    let π : Dual R (P.X (n + 1)) →ₗ[R] (R ⧸ I) :=
      I.mkQ.comp (W31.topDualCoordinate e).toLinearMap
    have hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π :=
      coordinate_quotient_exact _ (W31.topDualCoordinate e) I hI
    have hr : IsSMulRegular (R ⧸ I) r :=
      ((RingTheory.Sequence.isRegular_cons_iff (R ⧸ I) r rs).mp hreg).1
    have htail : RingTheory.Sequence.IsRegular (R ⧸ I') rs :=
      PiExponentJets.RegularSequenceQuotientTail.regular_quotient_tail I r rs hreg
    have hbound' : ∀ k, n + 2 < k → Subsingleton (P'.X k) :=
      scalarCone_bounded P r (n + 1) hbound
    have hinj' : Function.Injective (P'.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective P r hinj
    have hlow' : ∀ k, k < n + 1 → LinearMap.range (P'.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P'.d (k + 2) (k + 1)).hom.dualMap :=
      scalarCone_dual_low_exact P r n π hinj hlow hπ hr
    have hI' : LinearMap.range
        ((W31.topDualCoordinate e').toLinearMap.comp (P'.d (n + 2) (n + 1)).hom.dualMap) = I' :=
      scalarCone_top_dual_image P r n hbound e I hI
    have h := ih (n + 1) P' I' e' hbound' hinj' hlow' hI' htail
    intro k hk
    exact h k (by simp only [List.length_cons] at hk; omega)

theorem regularSequenceComplex_dual_low_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    LinearMap.range ((regularSequenceComplex rs).d (n + 1) n).hom.dualMap =
      LinearMap.ker ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap := by
  cases rs with
  | nil => simp at hn
  | cons r rs =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg
    have hJ : r • (⊤ : Submodule R R) = Ideal.span ({r} : Set R) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul]
      exact Ideal.mul_top _
    change RingTheory.Sequence.IsRegular (R ⧸ (r • (⊤ : Submodule R R))) rs at htail
    rw [hJ] at htail
    let E := emptyKoszulComplex (R := R)
    have hb : ∀ k, 0 < k → Subsingleton (E.X k) :=
      fun k hk => regularSequenceComplex_bounded ([] : List R) k hk
    let P := scalarConeComplex E r
    let e : P.X 1 ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv E r 0 hb).trans (LinearEquiv.refl R R)
    have hbound : ∀ k, 1 < k → Subsingleton (P.X k) :=
      scalarCone_bounded E r 0 hb
    have hinj : Function.Injective (P.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective_of_regular E r hr
    have hlow : ∀ k, k < 0 → LinearMap.range (P.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap := by
      intro k hk
      omega
    have hI : LinearMap.range
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d 1 0).hom.dualMap) =
          Ideal.span ({r} : Set R) :=
      scalarCone_first_top_dual_image E r hb (LinearEquiv.refl R R)
    have h := iterateScalarCones_dual_low_exact rs 0 P (Ideal.span {r})
      e hbound hinj hlow hI htail
    exact h n (by simp only [List.length_cons] at hn; omega)

end PiExponentSiegelAux.W30

end

end OAI
