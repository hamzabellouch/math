import OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy
import OAI.NumberTheory.DirichletL.Descent.SecondPuncture

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_marked_energy_varying_puncture
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
        (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
