import OAI.Analysis.Pureness.Quasitrace.QuasitraceFamily
import OAI.Analysis.Pureness.Cuntz.MatrixTraceCorrespondence

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

def PositiveQuasitrace.comap (T : PositiveQuasitrace E) (φ : D →⋆ₙₐ[ℂ] E) : PositiveQuasitrace D where
  toFun a := T (Positive.map φ a)
  nonneg a := T.nonneg _
  map_zero := by
    have hz : Positive.map φ Positive.zero = Positive.zero := Subtype.ext (_root_.map_zero φ)
    rw [hz,T.map_zero]
  map_add_commute a b hab := by
    have he : Positive.map φ (Positive.add a b) = Positive.add (Positive.map φ a) (Positive.map φ b) :=
      Subtype.ext (map_add φ _ _)
    rw [he,T.map_add_commute]
    change φ a.1*φ b.1 = φ b.1*φ a.1
    rw [← map_mul,← map_mul,hab.eq]
  map_smul r a := by
    have he : Positive.map φ (Positive.smul r a) = Positive.smul r (Positive.map φ a) := by
      apply Subtype.ext
      change φ ((r : ℝ) • a.1) = (r : ℝ) • φ a.1
      simpa only [← Complex.coe_smul] using _root_.map_smul φ (r : ℂ) a.1
    rw [he,T.map_smul]
  polar x := by
    have hl : Positive.map φ (Positive.starMul x) = Positive.starMul (φ x) := by
      apply Subtype.ext
      simp [Positive.map,Positive.starMul,map_mul,map_star]
    have hr : Positive.map φ (Positive.mulStar x) = Positive.mulStar (φ x) := by
      apply Subtype.ext
      simp [Positive.map,Positive.mulStar,map_mul,map_star]
    rw [hl,hr,T.polar]
  monotone := by
    intro a b hab
    apply T.monotone
    change φ a.1 ≤ φ b.1
    rw [← sub_nonneg,← map_sub]
    exact map_nonneg φ (sub_nonneg.mpr hab)

lemma PositiveQuasitrace.comap_complexValue (T : PositiveQuasitrace E) (φ : D →⋆ₙₐ[ℂ] E) (x : D) :
    (T.comap φ).complexValue x = T.complexValue (φ x) :=
  (T.complexValue_map (T.comap φ) φ (fun _ => rfl) x).symm
end CuntzPureness

end

end OAI
