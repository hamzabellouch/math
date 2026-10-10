import OAI.NumberTheory.DirichletL.Descent.SecondDeletedAllModes

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ)
    (hDensity : Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J t.1*coordinateHeight J t.2*‖density t‖))
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_deleted_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
      K ho hslots₁ hslots₂ w hw (A*(tripleHeight J t.1*coordinateHeight J t.2))
      (by unfold tripleHeight coordinateHeight; positivity) (hleft t) (hright t)
    exact hh.trans_eq (by dsimp only [C]; ring)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),C*(tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul C)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI
