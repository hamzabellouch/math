import OAI.Geometry.RCD.Sobolev.DistancePoissonExtensions
import OAI.Geometry.RCD.Sobolev.DistancePoissonBudget
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # Simultaneous compact extensions and cutoffs of the actual Poisson family -/

open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}

structure DistancePoissonMeanData (F : DistancePoissonFamily μ Q n κ B J C p r hr) where
  bound : ℝ
  bound_pos : 0<bound
  cutoffConstant : ℝ
  cutoff_one_le : 1≤cutoffConstant
  extension : ℕ → compactLaplacianCore μ Q univ
  laplacian : ℕ → Lp ℝ 2 μ
  cutoff : ∀ k, GoodLaplacianCutoff μ Q (p k) (12*(r k/512)) cutoffConstant
  weak_laplacian : ∀ k, IsWeakLaplacian μ Q (extension k).val (laplacian k)
  replacement_eq : ∀ k, SobolevSpace.toLp μ Q (extension k).val
    =ᵐ[μ.restrict (ball (p k) (r k/16))] SobolevSpace.toLp μ Q (F.replacement k)
  source_eq : ∀ k, laplacian k =ᵐ[μ.restrict (ball (p k) (r k/16))]
    fun _ => (n:ℝ)+κ*(4*r k)^2
  gradient_le : ∀ k, ∀ᵐ x ∂μ.restrict (ball (p k) (r k/16)),
    localGamma μ Q (extension k).val (extension k).val x≤(bound*r k)^2

theorem NoncollapsedRCD.distance_poisson_mean_data {K : ℝ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hK : K≤0) (p₀ : X) (hκ : 0≤κ)
    (F : DistancePoissonFamily (hausdorff n X) hX.quadratic n κ B J C p r hr)
    (hscale : ∀ k, r k≤1 ∧ -1≤K*(64*r k)^2) :
    let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    Nonempty (DistancePoissonMeanData F) := by
  let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  dsimp only
  obtain ⟨A,hA,hExt⟩ := hX.distance_poisson_family_extensions hn hK p₀ hκ (B := B)
  obtain ⟨Cχ,hCχ,hcut⟩ := hX.goodCutoffInput hn
  choose G d hd hGF hda hgrad using fun k =>
    hExt p r hr J C F k (hscale k).1 (hscale k).2
  have hχ k : Nonempty (GoodLaplacianCutoff (hausdorff n X) hX.quadratic
      (p k) (12*(r k/512)) Cχ) := by
    have hk := hr k
    apply hcut (p k) (12*(r k/512)) (by positivity)
    nlinarith only [(hscale k).2]
  exact ⟨{
    bound := A
    bound_pos := hA
    cutoffConstant := Cχ
    cutoff_one_le := hCχ
    extension := G
    laplacian := d
    cutoff := fun k => Classical.choice (hχ k)
    weak_laplacian := hd
    replacement_eq := hGF
    source_eq := hda
    gradient_le := hgrad }⟩

namespace DistancePoissonMeanData
variable {F : DistancePoissonFamily μ Q n κ B J C p r hr} (D : DistancePoissonMeanData F)

def budget (K : ℝ) (k : ℕ) : ℝ :=
  (D.cutoffConstant/(12*(r k/512))^2)*((J+B/2)*(r k)^2*(F.source k).real (ball (p k) (r k)))-
    K*weightedGamma μ Q (D.cutoff k).weight (D.extension k).val (D.extension k).val

theorem budget_nonneg {K : ℝ} (hK : K≤0) (hBJ : 0≤J+B/2) (k : ℕ) :
    0≤D.budget K k :=
  (F.shifted_budget_bound hK (zero_le_one.trans D.cutoff_one_le) hBJ k
    (D.extension k).val (D.cutoff k) (D.gradient_le k)).1

theorem normalized_budget_tendsto_zero {K : ℝ} (hK : K≤0) (hBJ : 0≤J+B/2)
    (hV : ∀ k, 0<μ.real (ball (p k) (r k))) (hr0 : Tendsto r atTop (𝓝 0))
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => D.budget K k/μ.real (ball (p k) (r k))) atTop (𝓝 0) :=
  F.normalized_shifted_budget_tendsto_zero hK (zero_le_one.trans D.cutoff_one_le)
    hBJ (fun k => (D.extension k).val) D.cutoff D.gradient_le hV hr0 hmass

end DistancePoissonMeanData
end RegularPointCoordinates

end

end OAI
