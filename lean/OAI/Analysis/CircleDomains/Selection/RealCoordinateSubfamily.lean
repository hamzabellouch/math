import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateData

namespace OAI

/-! The actual real coordinates retained inside a finite masked family. -/

open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure RealCoordinateSubfamily {S A L : Type*} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : S → Sphere} (C : L → MaskedCoordinateData G U π σ)
    (ι : A → L) where
  physical : A → (ℝ × ℝ) → ℝ
  quotient : A → Sphere → ℝ
  bound : A → ℝ
  bounded : ∀ j x, x ∈ U → |quotient j x| ≤ bound j
  full_mask : ∀ j, (C (ι j)).mask = univ
  smooth : ∀ j, ContDiffOn ℝ ∞ (physical j) (realChartDomain G)
  energy : ∀ j, MemLp (planarGradient (physical j)) 2 (volume.restrict (realChartDomain G))
  pullback : ∀ j x, x ∈ realChartDomain G →
    quotient j (π (Complex.equivRealProdCLM.symm x : Sphere)) = physical j x
  projection : ∀ j x, (physical j x : UnitAddCircle) = (C (ι j)).physical x
  width : ∀ j s, limsup (quotient j) (𝓝[U] (σ s)) -
    liminf (quotient j) (𝓝[U] (σ s)) ≤ (C (ι j)).upper s - (C (ι j)).lower s

def RealCoordinateSubfamily.reindex
    {S A L B D : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : L → MaskedCoordinateData G U π σ} {ι : A → L}
    (R : RealCoordinateSubfamily C ι) (label : B → L) (realIndex : D → A)
    (slot : D → B) (hlabel : ∀ j, label (slot j) = ι (realIndex j)) :
    RealCoordinateSubfamily (fun l => C (label l)) slot where
  physical j := R.physical (realIndex j)
  quotient j := R.quotient (realIndex j)
  bound j := R.bound (realIndex j)
  bounded j := R.bounded (realIndex j)
  full_mask j := by simpa only [hlabel] using R.full_mask (realIndex j)
  smooth j := R.smooth (realIndex j)
  energy j := R.energy (realIndex j)
  pullback j := R.pullback (realIndex j)
  projection j := by simpa only [hlabel] using R.projection (realIndex j)
  width j := by simpa only [hlabel] using R.width (realIndex j)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
