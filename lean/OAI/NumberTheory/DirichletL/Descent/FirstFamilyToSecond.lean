import OAI.NumberTheory.DirichletL.Descent.FirstFamilyEnergy
import OAI.NumberTheory.DirichletL.Descent.FirstOldEnergy
import OAI.NumberTheory.DirichletL.Descent.FirstToSecond

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_family_original_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) →
      ∀ (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ i∈B,0 < v i) → ∀ (negative : Bool) (Ψ : Eis →* ℂ) (m : Eis),
      (∀ a,‖Ψ a‖ ≤ 1) → ∀ (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x∈rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      firstFamilyEnergy p hg source F (fun _ => selector)
        (fun x => firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m H) c d x.1) w negative ω X t Prod.snd ≤
      M*K*Y^ε * ((32*512)*
        ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
          (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H ω X c d core t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_block_old_label_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B selector v ε₁ ε₂ hv negative Ψ m hΨ
    H ω X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  have h := hpush p hp hinj hcop hg F B selector v ε₁ ε₂ hv negative
    (multiplicativeCoreColumn p Ψ m H) ω X t hX c d source rows w M Y hM hY.le
    hs hmap hrows hnorm hw
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ((32*512)*∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H ω X c d core t Y).re) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left
        (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative
          (if negative then r.1 else r.2) Ψ m H ω X c d t rows Y hY hnorm (hΨ _)) (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro core hcore
      ring

end
end SevenEighths.InverseMoment

end OAI
