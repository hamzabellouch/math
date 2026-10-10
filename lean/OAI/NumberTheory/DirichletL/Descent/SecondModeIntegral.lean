import OAI.NumberTheory.DirichletL.Descent.SecondModeEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem second_geometric_energy_of_bound (K : ℕ) (labels : Finset (Ideal Eis))
    (rows : Finset Eis) (Γ : Finset OuterTriple) (F G : SecondChild → ℂ)
    (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ Γ,secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ Γ,secondLabelEnergy K labels rows G γ ≤ E) :
    Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ) (hP : ∀ γ ∈ Γ,secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  calc
    _ ≤ Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) *
        Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

theorem actual_second_mode_integral_of_child_bound
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1)
    (gwin : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),
      ∀ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),
      ∀ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),fullProfileDensity gwin b₁ b₂ b₃ t *
      ∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t‖ ≤
      (A * ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ) *
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*
        ‖fullProfileDensity gwin b₁ b₂ b₃ t‖ := by
  let Γ := actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂)
  let mass := ∑ γ ∈ Γ,tripleDivisorWeight K γ
  let H := fun t : Frequency × (Fin 6 → ℝ) => tripleHeight J t.1*coordinateHeight J t.2
  have hH (t : Frequency × (Fin 6 → ℝ)) : 0 ≤ H t := by
    unfold H tripleHeight coordinateHeight
    positivity
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t‖ ≤ (A*H t)*mass := by
    apply (actual_second_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t
      labels hlabels hrows K ho hJ₁ hJ₂ w hw).trans
    exact second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
      Γ _ _ (A*H t) (mul_nonneg hA (hH t)) (hright t) (hleft t)
  have hi := (fullProfileDensity_weighted_integrable gwin b₁ b₂ b₃ J).const_mul (A*mass)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),(A*mass)*(tripleHeight J t.1*coordinateHeight J t.2*
        ‖fullProfileDensity gwin b₁ b₂ b₃ t‖) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by dsimp only [H]; ring)
    _ = _ := by rw [integral_const_mul]

end
end SevenEighths.InverseMoment

end OAI
