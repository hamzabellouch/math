import OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondVariableCutoff {Jo : ℕ} (parent : SecondParentSource ι Jo) (R : Finset ι → Finset ι → ℝ)
    (G E : Finset ι) : Finset Eis :=
  childFrequencyBall (secondParentDivisor p parent*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_original_support {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : SecondExpansionData ι)
    (hx : x∈secondDyadicSector pool (secondVariableCutoff p parent R) residual label j) :
    x.sourceCommon ⊆ pool ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ pool ∧
    x.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent x)) (R x.sourceCommon x.divisor) := by
  obtain ⟨hx,hlabel⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hresidual⟩ := Finset.mem_filter.mp hx
  exact (mem_secondExpansionPool _ _ _).mp hx

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_attached_rows {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : MarkedSecondSource ι Jo 0)
    (hx : x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
      (attachSecondExpansion parent)) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R x.second.sourceCommon x.second.divisor) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact (second_variable_original_support p parent pool residual R label j y hy).2.2.2

theorem truncated_second_attached_variable [Fintype κ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) =
    truncatedSecondZero p hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) +
    ∑ z : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient z *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
          (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
            actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
              slots slots lists lists a a W W Φ Y X := by
  rw [truncatedSecondSource_eq_zero_add_dyadic p hp hcop hg hinj hc hpr
    pool Ψ (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y (secondVariableCutoff p parent R) label]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  exact secondExpansionSource_attached p hp hcop hg hinj hpr parent _
    (fun x hx => (second_variable_original_support p parent pool residual R label j x hx).2.1)
    pool Ψ m z slots slots lists lists a a W W Φ X Y

end
end SevenEighths.InverseMoment

end OAI
