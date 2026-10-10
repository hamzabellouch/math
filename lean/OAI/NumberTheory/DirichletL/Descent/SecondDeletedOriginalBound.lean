import OAI.NumberTheory.DirichletL.Descent.SecondModeIntegral
import OAI.NumberTheory.DirichletL.Descent.SecondDeletedModeEnergy
import OAI.NumberTheory.DirichletL.Descent.SecondWholeMass

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈J₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈J₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖∑ x∈source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := (actualSecondTriples_mono p u v
    (show varyingAssignedSource source J₁ J₂ lists₁ lists₂
      (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)⊆
      assignedSecondSource source J₁ J₂ lists₁ lists₂ from Finset.filter_subset _ _)).trans
      (assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂)
  apply (actual_second_deleted_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hΓ (fun γ _ _=>tripleDivisorWeight_nonneg K γ)) hA

end
end SevenEighths.InverseMoment

end OAI
