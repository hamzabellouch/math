import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.FarAngularEnergy
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePlaneWaveSub2

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate
variable {n : ℕ}

noncomputable def originalCellTransformND
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (h : ℕ) (M : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (X : Fin (n+1) → ℤ) (p : ℝ × EuclideanSpace ℝ (Fin (n+1))) : ℂ :=
  sourceAngularTransformND ρ (ambientGridCell h X) M b p.1 p.2

lemma original_partition_multiplierND (N : ℕ) (ma mb : ℝ) :
    ((((2:ℝ)^N)^(-ma))⁻¹)*((2:ℝ)^N)^(-mb) = ((2:ℝ)^N)^(-(mb-ma)) := by
  rw [← Real.rpow_neg (by positivity : (0:ℝ)≤(2:ℝ)^N),← Real.rpow_add (by positivity : (0:ℝ)<(2:ℝ)^N)]
  congr 1
  ring

theorem physical_near_far_profile_boundND {N : ℕ} (hN : 0<N)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {a h : ℕ} (hah : a≤h) (X Y : Fin (n+1) → ℤ)
    (hX : ρ (ambientGridCell a X)≠0) (hY : κ (ambientGridCell a Y)≠0)
    (v ma mb err : ℝ)
    (hl₁ : ∀ Q∈occupiedDescendantsND ρ a h X, ((2:ℝ)^N)^(-mb-err)≤(ρ (ambientGridCell h Q)).toReal)
    (hl₂ : ∀ Q∈occupiedDescendantsND κ a h Y, ((2:ℝ)^N)^(-mb-err)≤(κ (ambientGridCell h Q)).toReal)
    (hu₁ : (ρ (ambientGridCell a X)).toReal≤((2:ℝ)^N)^(-ma+err))
    (hu₂ : (κ (ambientGridCell a Y)).toReal≤((2:ℝ)^N)^(-ma+err))
    (b c : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖≤C)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (hΨpos : ∀ r, 0≤Ψ r) :
    let A := occupiedDescendantsND ρ a h X
    let D := occupiedDescendantsND κ a h Y
    let hAD : (A.product D).Nonempty := (original_occupied_nonemptyND ρ hah X hX).product
      (original_occupied_nonemptyND κ hah Y hY)
    let μ := canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
    let U := originalCellTransformND ρ h (((2:ℝ)^N)^(-mb)) b
    let W := originalCellTransformND κ h (((2:ℝ)^N)^(-mb)) c
    Attempt4Near.sourceAngularHND (n+1) μ a v Ψ
      (originalCellTransformND ρ a (((2:ℝ)^N)^(-ma)) b X)
      (originalCellTransformND κ a (((2:ℝ)^N)^(-ma)) c Y) ≤
      (20*((n+1:ℕ)+1:ℝ)+5)^(2*(n+1))*
        ((2:ℝ)^N)^(-2*((mb-(n+1:ℝ)*(h:ℝ)/(2*N))-(ma-(n+1:ℝ)*(a:ℝ)/(2*N)))+4*err)*
        Attempt4Near.graphChildMaxND (n+1) μ h v Ψ A D hAD U W +
      Attempt4Near.farAngularEnergyND (n+1) μ a h v (((2:ℝ)^N)^(-(mb-ma)))
        (((2:ℝ)^N)^(-(mb-ma))) Ψ A D U W := by
  classical
  let A := occupiedDescendantsND ρ a h X
  let D := occupiedDescendantsND κ a h Y
  let μ := canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
  let U := originalCellTransformND ρ h (((2:ℝ)^N)^(-mb)) b
  let W := originalCellTransformND κ h (((2:ℝ)^N)^(-mb)) c
  have hAD : (A.product D).Nonempty := (original_occupied_nonemptyND ρ hah X hX).product
    (original_occupied_nonemptyND κ hah Y hY)
  have hUm : ∀ Q∈A, Measurable (U Q) := fun Q _ => sourceAngularTransformND_measurable ρ _ _ hb
  have hWm : ∀ Q∈D, Measurable (W Q) := fun Q _ => sourceAngularTransformND_measurable κ _ _ hc
  let Bs := fun Q => |(((2:ℝ)^N)^(-mb))⁻¹| *(ρ (ambientGridCell h Q)).toReal*B
  let Cs := fun Q => |(((2:ℝ)^N)^(-mb))⁻¹| *(κ (ambientGridCell h Q)).toReal*C
  have hUb : ∀ Q∈A, ∀ r, ∀ᵐ w ∂μ, ‖U Q (r,w)‖≤Bs Q := by
    intro Q _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le ρ _ _ b r w (fun x => hbd x w hw)
  have hWb : ∀ Q∈D, ∀ r, ∀ᵐ w ∂μ, ‖W Q (r,w)‖≤Cs Q := by
    intro Q _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le κ _ _ c r w (fun x => hcd x w hw)
  have hnt : ((2:ℝ)^N)^(-mb)≠0 := ne_of_gt (by positivity)
  have hpu : ∀ r, ∀ᵐ w ∂μ, originalCellTransformND ρ a (((2:ℝ)^N)^(-ma)) b X (r,w) =
      (((2:ℝ)^N)^(-(mb-ma))) • ∑ Q∈A, U Q (r,w) := by
    intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact (sourceAngularTransformND_parent_partition ρ hah X _ _ r hnt b hb w (fun x => hbd x w hw)).trans
      (by rw [original_partition_multiplierND]; rfl)
  have hpw : ∀ r, ∀ᵐ w ∂μ, originalCellTransformND κ a (((2:ℝ)^N)^(-ma)) c Y (r,w) =
      (((2:ℝ)^N)^(-(mb-ma))) • ∑ Q∈D, W Q (r,w) := by
    intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact (sourceAngularTransformND_parent_partition κ hah Y _ _ r hnt c hc w (fun x => hcd x w hw)).trans
      (by rw [original_partition_multiplierND]; rfl)
  have hin₁ : ∀ Q∈A, Attempt4Near.ambientGridCell h Q⊆ambientGridCell a X := by
    intro Q hQ
    exact ambientDescendantsND_subset hah (Finset.mem_filter.mp hQ).1
  have hin₂ : ∀ Q∈D, Attempt4Near.ambientGridCell h Q⊆ambientGridCell a Y := by
    intro Q hQ
    exact ambientDescendantsND_subset hah (Finset.mem_filter.mp hQ).1
  have hs := Attempt4Near.sourceAngularHND_near_far_profile_bound (n+1) hN μ ρ κ a h v ma mb err
    A D hAD (ambientGridCell a X) (ambientGridCell a Y) hin₁ hin₂ hl₁ hl₂ hu₁ hu₂
    U W hUm hWm Bs Cs hUb hWb hmΨ hΨ hΨpos
  have hp := sourceAngularHND_congr_ae μ a v Ψ
    (originalCellTransformND ρ a (((2:ℝ)^N)^(-ma)) b X)
    (fun p => (((2:ℝ)^N)^(-(mb-ma))) • ∑ Q∈A, U Q p)
    (originalCellTransformND κ a (((2:ℝ)^N)^(-ma)) c Y)
    (fun p => (((2:ℝ)^N)^(-(mb-ma))) • ∑ Q∈D, W Q p) hpu hpw
  simpa only [Nat.cast_add,Nat.cast_one] using hp.le.trans hs

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
