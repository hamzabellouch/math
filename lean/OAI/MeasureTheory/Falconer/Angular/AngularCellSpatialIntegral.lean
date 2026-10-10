import OAI.MeasureTheory.Falconer.Angular.AngularFourSpatialIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularCellKernels

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def angularCellSpatialIntegral (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (row col : CellPath × CellPath) (v : ℝ) (Ψ : ℝ → ℝ) : ℂ :=
  ∫ x, ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
    graphFourKernel ![β,β,γ,γ] (fun _ => 1) x r u w
      ∂sourceArcLength ∂sourceArcLength)
    ∂Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict
      (![ (Q₁.descendant row.1).carrier, (Q₁.descendant col.1).carrier,
          (Q₂.descendant row.2).carrier, (Q₂.descendant col.2).carrier] i))

theorem angular_pair_spatial_integral (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (row col : CellPath × CellPath) (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    angularKernelIntegral a v Ψ (fun z => angularPairTerm
      (fun P => angularCellTransform Q₁ ρ M₁ β P (z.1,z.2.1))
      (fun Q => angularCellTransform Q₂ ν M₂ γ Q (z.1,z.2.2)) row col) =
      ((2:ℝ)^(2*(v-a))) • ((M₁^2*M₂^2)⁻¹ •
        angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  let U := angularCellTransform Q₁ ρ M₁ β
  let V := angularCellTransform Q₂ ν M₂ γ
  have hu := angularCellTransform_measurable Q₁ ρ M₁ β hβ
  have hv := angularCellTransform_measurable Q₂ ν M₂ γ hγ
  have hm : Measurable (fun z : ℝ × (UnitCircle × UnitCircle) =>
      angularPairTerm (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col) := by
    unfold angularPairTerm
    fun_prop
  have hb : ∀ z : ℝ × (UnitCircle × UnitCircle),
      ‖angularPairTerm (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col‖ ≤
        (D₁*(ρ univ).toReal/M₁)^2*(D₂*(ν univ).toReal/M₂)^2 := by
    intro z
    simp only [angularPairTerm,norm_mul,Complex.norm_conj,pow_two]
    apply mul_le_mul
      (mul_le_mul (sourceAngularTransform_global_bound ρ _ hM₁ β hD₁ hbβ _ _)
        (sourceAngularTransform_global_bound ρ _ hM₁ β hD₁ hbβ _ _) (norm_nonneg _) (by positivity))
      (mul_le_mul (sourceAngularTransform_global_bound ν _ hM₂ γ hD₂ hbγ _ _)
        (sourceAngularTransform_global_bound ν _ hM₂ γ hD₂ hbγ _ _) (norm_nonneg _) (by positivity))
      (by positivity) (by positivity)
  rw [angularKernelIntegral_original a v hΨ hpos hz _ hm hb]
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let bs : Fin 4 → Plane → UnitCircle → ℂ := ![β,β,γ,γ]
  let Ds : Fin 4 → ℝ := ![D₁,D₁,D₂,D₂]
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier, (Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier, (Q₂.descendant col.2).carrier]
  let : ∀ index, IsFiniteMeasure (ρs index) := by
    intro index
    fin_cases index <;> dsimp [ρs] <;> infer_instance
  have he := sourceGraphFourTransform_original_spatial ρs X ![M₁,M₁,M₂,M₂] bs (fun _ => 1)
    (by intro l; fin_cases l <;> assumption) measurable_const Ds
    (by intro l; fin_cases l <;> assumption)
    (by intro l; fin_cases l <;> assumption) (by intro p; simp)
    hΨ hs hW (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t)
    (by positivity : (0:ℝ) < (2:ℝ)^v)
  congr 1
  simpa only [sourceGraphFourTransform,angularPairTerm,angularCellTransform,
    angularCellSpatialIntegral,ρs,bs,Ds,X,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    one_mul,pow_two,U,V,angularCellTransform] using he

end PlanarFalconer

end OAI
