import OAI.NumberTheory.DirichletL.Descent.SecondOriginalBound
import OAI.NumberTheory.DirichletL.Descent.SecondSectorAssembly

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondFullModeSum
  apply Finset.sum_congr rfl
  intro uv huv
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem actual_second_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
      (fun i hi => ha₁ i (Finset.mem_powerset.mp hJ₁ hi))
      (fun i hi => ha₂ i (Finset.mem_powerset.mp hJ₂ hi)) ω₁ ω₂ G E V B X R t labels
      (fun x hx => hlabels x (hsub hx)) (fun x hx => hrows x (hsub hx)) K ho
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₁)).trans hslots₁)
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₂)).trans hslots₂)
      w (fun x hx => hw x (hsub hx)) A hA
      (fun γ hγ => hleft J₁ hJ₁ γ (ht hγ)) (fun γ hγ => hright J₂ hJ₂ γ (ht hγ))
    exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun γ _ _ => tripleDivisorWeight_nonneg K γ)) hA)
  calc
    _ ≤ ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
        ‖∑ x∈secondSourceSector source sector uv,
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro uv huv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact norm_sum_le _ _
    _ ≤ ∑ _uv : Eisˣ × Eisˣ,∑ _J₁∈slots₁.powerset,∑ _J₂∈slots₂.powerset,A*mass := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact Finset.sum_le_sum (fun J₂ hJ₂ => hbound uv J₁ hJ₁ J₂ hJ₂)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,
        second_unit_sector_card,Nat.cast_pow,Nat.cast_ofNat,mass]
      ring

end
end SevenEighths.InverseMoment

end OAI
