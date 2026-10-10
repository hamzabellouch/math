import OAI.NumberTheory.DirichletL.Descent.SecondVariableCutoff

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι γ δ κ : Type*} [DecidableEq ι] [DecidableEq γ] [DecidableEq δ] [DecidableEq κ]

def secondCenterLabel (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (residual : Finset ι)
    (x : SecondExpansionData ι) : γ × δ × κ :=
  (gIndex x.sourceCommon,thetaIndex x.divisor,other residual x)

theorem second_center_sector_rows (p : ι→Eis)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (R : γ→δ→ℝ)
    (j : γ × δ × κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈(secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>R (gIndex G) (thetaIndex E))) residual
      (secondCenterLabel gIndex thetaIndex other) j).image (attachSecondExpansion parent)) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R j.1 j.2.1) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hlabel := (Finset.mem_filter.mp hy).2
  have hg : gIndex y.sourceCommon=j.1 := congrArg Prod.fst hlabel
  have ht : thetaIndex y.divisor=j.2.1 := congrArg (fun a : γ×δ×κ=>a.2.1) hlabel
  obtain ⟨hy,_⟩ := Finset.mem_filter.mp hy
  obtain ⟨hy,_⟩ := Finset.mem_filter.mp hy
  have hs := ((mem_secondExpansionPool _ _ _).mp hy).2.2.2
  change y.frequency ∈ nonzeroChildFrequencyBall
    (actualSecondMultiplier p (attachSecondExpansion parent y)) (R (gIndex y.sourceCommon) (thetaIndex y.divisor)) at hs
  change y.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent y)) (R j.1 j.2.1)
  simpa only [hg,ht] using hs

theorem second_center_sector_empty (p : ι→Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (R : γ→δ→ℝ)
    (j : γ × δ × κ) (hR : R j.1 j.2.1<1) :
    secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>R (gIndex G) (thetaIndex E))) residual
      (secondCenterLabel gIndex thetaIndex other) j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hs := second_center_sector_rows p parent pool residual gIndex thetaIndex other R j
    (attachSecondExpansion parent y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
  have ha : actualSecondMultiplier p (attachSecondExpansion parent y) ≠ 0 :=
    mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)
  rw [nonzeroChildFrequencyBall_empty _ ha _ hR] at hs
  exact Finset.notMem_empty _ hs

theorem second_center_sector_nonnegative (p : ι→Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (M : γ→δ→ℝ) (Z : ℝ) (hZ : 1<Z)
    (j : γ × δ × κ)
    (hne : (secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>Z^(M (gIndex G) (thetaIndex E)))) residual
      (secondCenterLabel gIndex thetaIndex other) j).Nonempty) : 0≤M j.1 j.2.1 := by
  by_contra hn
  have hlt : Z^(M j.1 j.2.1)<1 := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  rw [second_center_sector_empty p parent pool residual gIndex thetaIndex other
    (fun a b=>Z^(M a b)) j hlt] at hne
  exact Finset.not_nonempty_empty hne

end
end SevenEighths.InverseMoment

end OAI
