import OAI.Geometry.SurfaceImmersion.Correction.PolynomialNormalBounds
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedInverseSqrt

namespace OAI

/-! Polynomial derivative bounds for the perpendicular product and its
unit normalization used by the free mode. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def crossBudget (m : ℕ) (C : ℝ) := 2*(2^m*C*C)
def minorTermBudget (m : ℕ) (C : ℝ) := 2^m*C*crossBudget m C
def perpBudget (m : ℕ) (C : ℝ) := 3*minorTermBudget m C

lemma perpBudget_nonneg (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ perpBudget m C := by
  unfold perpBudget minorTermBudget crossBudget
  positivity

lemma weighted_minor3 {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    {X Y B : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hB : ContDiffOn ℝ ∞ B U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bB : WeightedBound U s m C B) (i j k : Fin 4) :
    WeightedBound U s m (perpBudget m C) (fun x => NormalFrame.minor3 (X x) (Y x) (B x) i j k) := by
  have hy (a : Fin 4) := contDiffOn_pi.mp hY a
  have hb (a : Fin 4) := contDiffOn_pi.mp hB a
  have hx (a : Fin 4) := contDiffOn_pi.mp hX a
  have hcross (a b : Fin 4) := ((hy a).mul (hb b)).sub ((hy b).mul (hb a))
  have bcross (a b : Fin 4) : WeightedBound U s m (crossBudget m C)
      (fun x => Y x a*B x b-Y x b*B x a) := by
    have h₁ := (bY.component hU hs.le hC hY a).mul_real hU hs.le hC hC (hy a) (hb b)
      (bB.component hU hs.le hC hB b)
    have h₂ := (bY.component hU hs.le hC hY b).mul_real hU hs.le hC hC (hy b) (hb a)
      (bB.component hU hs.le hC hB a)
    convert h₁.sub hU hs.le ((hy a).mul (hb b)) ((hy b).mul (hb a)) h₂ using 1
    unfold crossBudget
    ring
  have hcb : 0 ≤ crossBudget m C := by unfold crossBudget; positivity
  have hterm (a b c : Fin 4) := (hx a).mul (hcross b c)
  have bterm (a b c : Fin 4) : WeightedBound U s m (minorTermBudget m C)
      (fun x => X x a*(Y x b*B x c-Y x c*B x b)) :=
    (bX.component hU hs.le hC hX a).mul_real hU hs.le hC hcb (hx a) (hcross b c) (bcross b c)
  have ht := ((bterm i j k).sub hU hs.le (hterm i j k) (hterm j i k) (bterm j i k)).add
    hU hs.le ((hterm i j k).sub (hterm j i k)) (hterm k i j) (bterm k i j)
  convert ht using 1 <;> first | rfl | (unfold perpBudget; ring)

lemma contDiffOn_perpProduct {U : Set E} {X Y B : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun x => NormalFrame.perpProduct (X x) (Y x) (B x)) U := by
  have hm (i j k : Fin 4) : ContDiffOn ℝ ∞
      (fun x => NormalFrame.minor3 (X x) (Y x) (B x) i j k) U := by
    unfold NormalFrame.minor3
    fun_prop
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (hm 1 2 3).neg
  · exact hm 0 2 3
  · exact (hm 0 1 3).neg
  · exact hm 0 1 2

lemma weighted_perpProduct {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    {X Y B : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hB : ContDiffOn ℝ ∞ B U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bB : WeightedBound U s m C B) :
    WeightedBound U s m (perpBudget m C) (fun x => NormalFrame.perpProduct (X x) (Y x) (B x)) := by
  have hminor (i j k : Fin 4) : ContDiffOn ℝ ∞
      (fun x => NormalFrame.minor3 (X x) (Y x) (B x) i j k) U := by
    unfold NormalFrame.minor3
    fun_prop
  apply WeightedBound.pi hU hs (perpBudget_nonneg m hC)
  · intro i
    fin_cases i
    · exact (hminor 1 2 3).neg
    · exact hminor 0 2 3
    · exact (hminor 0 1 3).neg
    · exact hminor 0 1 2
  · intro i
    fin_cases i
    · exact (weighted_minor3 hU hs hC hX hY hB bX bY bB 1 2 3).neg hU (hminor 1 2 3)
    · exact weighted_minor3 hU hs hC hX hY hB bX bY bB 0 2 3
    · exact (weighted_minor3 hU hs hC hX hY hB bX bY bB 0 1 3).neg hU (hminor 0 1 3)
    · exact weighted_minor3 hU hs hC hX hY hB bX bY bB 0 1 2

end ClosedSurfaceR4.RealModes

end

end OAI
