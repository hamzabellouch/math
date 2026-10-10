import OAI.MeasureTheory.Falconer.Angular.AngularNearProfile
import OAI.MeasureTheory.Falconer.Angular.AngularNearIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularCellKernels

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem regularized_angular_near_bound
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (N B₀ : ℕ) (hN : 0 < N) (δ lam : ℝ) (m₁ m₂ : ℝ → ℝ)
    (hd₁ : RegularizedProfileData Q₁ ρ N B₀ δ lam m₁)
    (hd₂ : RegularizedProfileData Q₂ ν N B₀ δ lam m₂)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) (hp : a+n ≤ N)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    let R := (2:ℝ)^N
    let Uc := angularCellTransform Q₁ ρ (R^(-m₁ (a+n))) β
    let Vc := angularCellTransform Q₂ ν (R^(-m₂ (a+n))) γ
    ‖angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ
        (R^(-m₁ a)) (R^(-m₂ a)) (R^(-m₁ (a+n))) (R^(-m₂ (a+n)))
        β γ (angularNear Q₁ Q₂ (a+n))‖ ≤
      15352201216*R^(-(m₁ (a+n)-((a:ℝ)+n)/N-(m₁ a-(a:ℝ)/N))
        -(m₂ (a+n)-((a:ℝ)+n)/N-(m₂ a-(a:ℝ)/N))+12*lam)*
      finiteEnergyMaximum (sourceProductVertices Q₁ Q₂ ρ ν A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) := by
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let Uc := angularCellTransform Q₁ ρ (((2:ℝ)^N)^(-m₁ (a+n))) β
  let Vc := angularCellTransform Q₂ ν (((2:ℝ)^N)^(-m₂ (a+n))) γ
  have h1 : 0 < ((2:ℝ)^N)^(-m₁ (a+n)) := by positivity
  have h2 : 0 < ((2:ℝ)^N)^(-m₂ (a+n)) := by positivity
  have hh := angularNearIntegral_bound Q₁ Q₂ hQ₁ hQ₂ (a+n) C
    (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB) Uc Vc
    (angularCellTransform_measurable Q₁ ρ _ β hβ)
    (angularCellTransform_measurable Q₂ ν _ γ hγ)
    (B := D₁*(ρ univ).toReal/((2:ℝ)^N)^(-m₁ (a+n)))
    (D := D₂*(ν univ).toReal/((2:ℝ)^N)^(-m₂ (a+n))) (by positivity) (by positivity)
    (fun P z => sourceAngularTransform_global_bound ρ _ h1 β hD₁ hbβ z.1 z.2)
    (fun P z => sourceAngularTransform_global_bound ν _ h2 γ hD₂ hbγ z.1 z.2)
    v hΨ hpos hs hW hw
  simp only [Nat.cast_add] at hh
  have hc := sourceProductVertices_profile_count Q₁ Q₂ hQ₁ hQ₂ ρ ν N B₀ δ lam m₁ m₂ hd₁ hd₂ A B a n hA hB hp
  have hm := angular_near_profile_sum_bound C
    (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) N hN m₁ m₂ a (a+n) lam hc
  dsimp only
  unfold angularCellContribution
  rw [angularKernelIntegral_outer a (a+n) v _ (by positivity)]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  simpa only [Nat.cast_add,C,Uc,Vc] using hm

end PlanarFalconer

end OAI
