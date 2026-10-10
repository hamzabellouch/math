import OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondChild_erase {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

theorem actualSecondChild_neg_frequency {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  simp only [actualSecondChild,secondChild,originalSecondTuple,markedSecondOriginal,cubeSecondSource,
    secondUnitFrequency_neg,mul_neg]

include hp hcop in
theorem actual_second_marked_weighted_count
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  let S := assignedSecondSource source J₁ J₂ L₁ L₂
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card) =>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hs' : ActualSecondSourceConditions p S := assignedSecondSource_conditions p source hs J₁ J₂ L₁ L₂
  have herase : ∀ x ∈ S, eraseSecondSlots x ∈ source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  have hw' : ∀ x ∈ S, ‖w' x‖ ≤ 1 := by
    intro x hx
    rw [show w' x = w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ x hx)
  have hc' : ∀ x ∈ S, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := assignedSecondSource_sum_marks source J₁ J₂ L₁ L₂ a₁ a₂ w
    (fun x => F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end
end SevenEighths.InverseMoment

end OAI
