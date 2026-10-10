import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.TracialProjectionStrictComparison
import OAI.Analysis.JiangSu.CentralSequences.TracialIsometrySaturation

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U

 theorem tracial_projection_comparison (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hord : ∀ s : ℕ → TracialState A,((L s).functional p).re≤((L s).functional q).re) :
    ∃ w : D,star w*w=p ∧ q*w=w := by
  let t : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0<t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n≤1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose w hwn hw hqw using fun n => tracial_projection_approx_comparison U hfree
    hsimple hinf hcmp hnuc hp hq hord (ht n) (ht1 n)
  have hlim : Tendsto (fun n => Real.sqrt (t n)) atTop (𝓝 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp ht0 using 1 <;> first | rfl | rw [Real.sqrt_zero]
  exact tracial_isometry_saturation T U hfree p q w hwn
    (squeeze_zero (fun n => familyTwoNorm_nonneg L _) hw hlim)
    (squeeze_zero (fun n => familyTwoNorm_nonneg L _) hqw hlim)

 theorem tracial_projection_equivalence (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (heq : ∀ s : ℕ → TracialState A,((L s).functional p).re=((L s).functional q).re) :
    ∃ w : D,star w*w=p ∧ w*star w=q := by
  obtain ⟨w,hw,hqw⟩ := tracial_projection_comparison U hfree hsimple hinf hcmp hnuc hp hq
    (fun s => (heq s).le)
  have hwp := partialIsometry_right_support hp hw
  have hr : IsStarProjection (w*star w) := by
    constructor
    · change w*star w*(w*star w)=w*star w
      rw [mul_assoc w,←mul_assoc (star w),hw,←mul_assoc,hwp]
    · exact (mul_star_self_nonneg w).isSelfAdjoint
  have hrq : w*star w≤q := (hr.le_iff_mul_eq_right hq).mpr (by rw [←mul_assoc,hqw])
  have hz : q-w*star w=0 := by
    apply limitTrace_detects_positive_zero T U _ (sub_nonneg.mpr hrq)
    intro s
    rw [map_sub,Complex.sub_re,((L s).tracial w (star w)),hw,heq s,sub_self]
  exact ⟨w,hw,(sub_eq_zero.mp hz).symm⟩

end DirectComparison

end
end

end OAI
