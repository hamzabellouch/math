import OAI.Analysis.CircleDomains.Selection.TrackedTestSequence
import OAI.Analysis.CircleDomains.Probability.SummableTestLimits
import OAI.Analysis.CircleDomains.Probability.SummableRecursiveBudget

namespace OAI

/-! The actual old coordinates have continuous sphere limits and strong
L2 gradient limits. Both stay within the total recursive error budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "d" => (fun n : ℕ => recursiveTestBudget ε n (AppendingConstructionState.tolerances (states n)))

 def sphereScalar (i : Fin T.count) (n : ℕ) : C(Sphere,ℝ) :=
  ⟨sphereFromPlaneFunction (f i n), continuous_sphereFromPlaneFunction
    (scalar_continuous hsupply hsard hsch hG hinf hTD ha hBa hε T i n)
    (scalar_compact hsupply hsard hsch hG hinf hTD ha hBa hε T i n)⟩

 theorem exists_continuous_limit (i : Fin T.count) :
    ∃ g : C(Sphere,ℝ),
      Tendsto (sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T i) atTop (𝓝 g) ∧
      ∀ z, |g z-sphereFromPlaneFunction (T.test i) z| ≤ ε/4 := by
  let F := sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T i
  have hd := summable_recursive_test_budget hε (fun n => (states n).tolerances)
    (fun n => (states n).positive)
  have hd0 : ∀ n, 0 ≤ d n := fun n => (recursiveTestBudget_pos hε n (states n).positive).le
  have hstep : ∀ n z, |F n z-F (n+1) z| ≤ d n := by
    intro n z
    change |sphereFromPlaneFunction (f i n) z-sphereFromPlaneFunction (f i (n+1)) z| ≤ d n
    cases z using OnePoint.rec with
    | infty => simpa [sphereFromPlaneFunction] using hd0 n
    | coe z =>
      have hh := step_uniform hsupply hsard hsch hG hinf hTD ha hBa hε T i n
        (complexPlaneCoordinates.symm z)
      simpa only [sphereFromPlaneFunction_coe,abs_sub_comm] using hh.le
  obtain ⟨g,hg,hbound⟩ := continuous_limit_of_summable_steps F d hd hd0 hstep
  refine ⟨g,hg,?_⟩
  intro z
  have hb := (hbound 0 z).trans (by
    simpa only [zero_add] using tsum_recursive_test_budget_le hε
      (fun n => (states n).tolerances) (fun n => (states n).positive))
  change |sphereFromPlaneFunction (T.test i) z-g z| ≤ ε/4 at hb
  rwa [abs_sub_comm] at hb

 theorem exists_gradient_limit (i : Fin T.count) :
    ∃ g : Lp EuclideanPlane 2 (volume.restrict (physicalPlaneDomain G)),
      Tendsto (fun n => (W i n).weakGrad_memLp.toLp ((W i n).weakGrad)) atTop (𝓝 g) ∧
      dist ((T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)) g ≤ ε/4 := by
  have hd := summable_recursive_test_budget hε (fun n => (states n).tolerances)
    (fun n => (states n).positive)
  have hstep : ∀ n, (eLpNorm (fun x => (W i n).weakGrad x-(W i (n+1)).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal ≤ d n := by
    intro n
    have he : (fun x => (W i n).weakGrad x-(W i (n+1)).weakGrad x) =
        -(fun x => (W i (n+1)).weakGrad x-(W i n).weakGrad x) := by
      funext x
      simp only [Pi.neg_apply,neg_sub]
    rw [he,eLpNorm_neg]
    exact (step_gradient hsupply hsard hsch hG hinf hTD ha hBa hε T i n).le
  obtain ⟨g,hg,hbound⟩ := lp_limit_of_summable_steps (volume.restrict (physicalPlaneDomain G))
    (fun n => (W i n).weakGrad) (fun n => (W i n).weakGrad_memLp) d hd hstep
  refine ⟨g,hg,?_⟩
  have hb := (hbound 0).trans (by
    simpa only [zero_add] using tsum_recursive_test_budget_le hε
      (fun n => (states n).tolerances) (fun n => (states n).positive))
  exact hb

end AppendingSequence
end CircleDomainRigidity

end

end OAI
