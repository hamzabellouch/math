import Mathlib
import OAI.Analysis.Commutator.RationalStarExtension

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [CStarAlgebra A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

local instance : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)

local instance : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

local instance : StarModule ℚ (H →L[ℂ] H) where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

omit [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] in
theorem homomorphisms_ae_of_countable_relations
    (S : StarSubalgebra ℚ A) [Countable S]
    (hd : DenseRange (fun a : S => (a:A))) (hI : Complex.I • (1:A)∈S)
    (T : A → Ω → H →L[ℂ] H)
    (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖)
    (ha : ∀ a b,∀ᵐ x ∂μ,T (a+b) x=T a x+T b x)
    (hm : ∀ a b,∀ᵐ x ∂μ,T (a*b) x=T a x*T b x)
    (hst : ∀ a,∀ᵐ x ∂μ,T (star a) x=star (T a x))
    (hsc : ∀ z : ℂ,∀ᵐ x ∂μ,T (z • (1:A)) x=z • (1:H →L[ℂ] H)) :
    ∀ᵐ x ∂μ,∃ Φ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Φ (a:A)=T (a:A) x := by
  filter_upwards [ae_all_iff.mpr (fun a : S => hb (a:A)),
    ae_all_iff.mpr (fun a : S => ae_all_iff.mpr (fun b : S => ha (a:A) (b:A))),
    ae_all_iff.mpr (fun a : S => ae_all_iff.mpr (fun b : S => hm (a:A) (b:A))),
    ae_all_iff.mpr (fun a : S => hst (a:A)),
    ae_all_iff.mpr (fun r : ℚ => hsc (r:ℂ)),hsc Complex.I] with x hx ha hm hs hc hi
  let φ : S →⋆ₐ[ℚ] (H →L[ℂ] H) :=
    { toAlgHom :=
      { toFun := fun a => T (a:A) x
        map_one' := by simpa using hc (1:ℚ)
        map_zero' := by simpa using hc (0:ℚ)
        map_add' := fun a b => ha a b
        map_mul' := fun a b => hm a b
        commutes' := by
          intro r
          change T (algebraMap ℚ A r) x=algebraMap ℚ (H →L[ℂ] H) r
          rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
          exact hc r }
      map_star' := fun a => hs a }
  obtain ⟨Φ,hΦ,hnb⟩ := RationalStarExtension.exists_complex_extension S hd φ hx hI hi
  exact ⟨Φ,hΦ⟩

end Kadison.Decomposable

end

end
end

end OAI
