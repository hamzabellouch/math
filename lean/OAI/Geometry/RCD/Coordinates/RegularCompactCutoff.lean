import OAI.Geometry.RCD.Sobolev.WeakLaplacianCutoff
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # Compact cutoffs with an L² Laplacian on arbitrary open sets -/

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Qualitative cutoff data, without a fixed ratio between the two radii. -/
structure RegularCompactCutoff where
  weight : X → ℝ
  lip : ℝ≥0
  lipschitz : LipschitzWith lip weight
  compact : HasCompactSupport weight
  bounds : ∀ x, 0 ≤ weight x ∧ weight x ≤ 1
  sobolev : SobolevSpace μ hQ
  representative : SobolevSpace.toLp μ hQ sobolev =ᵐ[μ] weight
  laplacian : Lp ℝ 2 μ
  weak_laplacian : IsWeakLaplacian μ hQ sobolev laplacian

namespace RegularCompactCutoff

variable {μ hQ}

def zero : RegularCompactCutoff μ hQ where
  weight := 0
  lip := 0
  lipschitz := LipschitzWith.const 0
  compact := HasCompactSupport.zero
  bounds := by intro x; exact ⟨le_rfl,zero_le_one⟩
  sobolev := 0
  representative := by simpa using Lp.coeFn_zero ℝ 2 μ
  laplacian := 0
  weak_laplacian := by intro φ; simp [energyForm]

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
lemma abs_le (χ : RegularCompactCutoff μ hQ) (x : X) : |χ.weight x| ≤ (1 : ℝ≥0) := by
  rw [abs_of_nonneg (χ.bounds x).1]
  exact (χ.bounds x).2

/-- Combining two plateaux preserves their union and the L² Laplacian. -/
def union (χ η : RegularCompactCutoff μ hQ) : RegularCompactCutoff μ hQ := by
  let M := SobolevSpace.cutoffCLM μ hQ χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1)
  have hex := η.weak_laplacian.cutoff μ hQ η.sobolev χ.sobolev
    η.laplacian χ.laplacian χ.weak_laplacian χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1) χ.representative
    (η.representative.mono fun x hx => hx ▸ η.abs_le x)
  let q := hex.choose
  have hq := hex.choose_spec.1
  refine {
    weight := fun x => χ.weight x + η.weight x - χ.weight x * η.weight x
    lip := (χ.lip+η.lip)+(χ.lip+η.lip)
    lipschitz := ?_
    compact := (χ.compact.add η.compact).sub χ.compact.mul_right
    bounds := ?_
    sobolev := χ.sobolev+η.sobolev-M η.sobolev
    representative := ?_
    laplacian := χ.laplacian+η.laplacian-q
    weak_laplacian := ?_ }
  · exact (χ.lipschitz.add η.lipschitz).sub
      (by simpa only [one_mul,add_comm] using
        (lipschitzWith_mul_of_support_bound χ.lipschitz η.lipschitz χ.abs_le
          (fun x _ => η.abs_le x)))
  · intro x
    have hc := χ.bounds x
    have he := η.bounds x
    constructor <;> nlinarith [mul_nonneg hc.1 he.1, mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr he.2)]
  · simp only [map_sub,map_add]
    filter_upwards [Lp.coeFn_sub (SobolevSpace.toLp μ hQ χ.sobolev+SobolevSpace.toLp μ hQ η.sobolev)
      (SobolevSpace.toLp μ hQ (M η.sobolev)),
      Lp.coeFn_add (SobolevSpace.toLp μ hQ χ.sobolev) (SobolevSpace.toLp μ hQ η.sobolev),
      χ.representative,η.representative,
      SobolevSpace.cutoffCLM_coe μ hQ χ.lipschitz χ.compact χ.abs_le
        (fun x => (χ.bounds x).1) η.sobolev] with x hs ha hc he hm
    simp only [Pi.add_apply,Pi.sub_apply] at hs ha
    change _ = χ.weight x*SobolevSpace.toLp μ hQ η.sobolev x at hm
    rw [hs,ha,hc,he,hm,he]
  · intro φ
    rw [energyForm_sub_left,energyForm_add_left,χ.weak_laplacian,
      η.weak_laplacian,hq,inner_sub_left,inner_add_left]
    ring

lemma union_weight (χ η : RegularCompactCutoff μ hQ) :
    (χ.union η).weight = fun x => χ.weight x+η.weight x-χ.weight x*η.weight x := rfl

lemma union_support (χ η : RegularCompactCutoff μ hQ) :
    tsupport (χ.union η).weight ⊆ tsupport χ.weight ∪ tsupport η.weight := by
  rw [union_weight]
  exact (tsupport_sub _ _).trans (union_subset_union_left _ (tsupport_add _ _)) |>.trans
    (union_subset (subset_refl _) ((tsupport_mul_subset_left).trans subset_union_left))

lemma union_one_left (χ η : RegularCompactCutoff μ hQ) {x : X} (h : χ.weight x=1) :
    (χ.union η).weight x=1 := by
  change χ.weight x+η.weight x-χ.weight x*η.weight x=1
  rw [h]
  ring

lemma union_one_right (χ η : RegularCompactCutoff μ hQ) {x : X} (h : η.weight x=1) :
    (χ.union η).weight x=1 := by
  change χ.weight x+η.weight x-χ.weight x*η.weight x=1
  rw [h]
  ring

end RegularCompactCutoff
end RegularPointCoordinates

end

end OAI
