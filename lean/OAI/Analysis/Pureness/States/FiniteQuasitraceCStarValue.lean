import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientOrder
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFinite
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientNormContinuity
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientBallComplete
import OAI.Analysis.Pureness.States.FiniteQuasitraceCauchyValue
import OAI.Analysis.Pureness.Stabilization.RankFunctorial

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
variable (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
variable (hfinite : ∀ x, d x ≠ ⊤)

@[instance_reducible]
def finiteQuasitraceCStarAlgebra (n : ℕ) : CStarAlgebra (FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) := inferInstance

lemma finiteQuasitraceCauchyValue_continuous (n : ℕ) :
    Continuous (finiteQuasitraceCauchyValue d hd hlsc hfinite n) :=
  PositiveQuasitrace.quotientValue_norm_continuous _ _ _

lemma finiteQuasitraceCauchyValue_square_eq_zero_iff (n : ℕ)
    (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    finiteQuasitraceCauchyValue d hd hlsc hfinite n (star x*x) = 0 ↔ x = 0 :=
  PositiveQuasitrace.quotientValue_square_eq_zero_iff _ _ _ x

lemma finiteQuasitraceCauchyValue_cfc_add (n : ℕ)
    (x : selfAdjoint (FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n))
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    finiteQuasitraceCauchyValue d hd hlsc hfinite n (cfc f x.1+cfc g x.1) =
      finiteQuasitraceCauchyValue d hd hlsc hfinite n (cfc f x.1)+
      finiteQuasitraceCauchyValue d hd hlsc hfinite n (cfc g x.1) :=
  PositiveQuasitrace.quotientValue_cfc_add _ _ _ x f g hf hg

lemma finiteQuasitraceCauchyQuotient_finite (n : ℕ)
    (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) (hx : star x*x = 1) : x*star x = 1 :=
  PositiveQuasitrace.cauchyQuotient_isometry_unitary _ _
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (n+1)) x hx

lemma finiteQuasitraceCStarValue_internal_root_rank (n : ℕ) (M : Positive (FinMatrix A (n+1))) :
    Tendsto (fun k => ENNReal.ofReal
      (finiteQuasitraceCauchyValue d hd hlsc hfinite n
        (Positive.power (Positive.rootExponent k)
          (Positive.map (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite n).toNonUnitalStarAlgHom M)).1).re)
      atTop (nhds (d (finitePositiveClass (n+1) M))) := by
  have h := finiteQuasitraceCauchyValue_root_rank d hd hlsc hfinite n M
  have he (k : ℕ) := congrArg Subtype.val
    (Positive.map_power (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite n).toNonUnitalStarAlgHom M
      (Positive.rootExponent k) (Positive.rootExponent_pos k))
  exact h.congr' (Eventually.of_forall (fun k => congrArg (fun z => ENNReal.ofReal
    (finiteQuasitraceCauchyValue d hd hlsc hfinite n z).re) (he k)))
end CuntzPureness

end

end OAI
