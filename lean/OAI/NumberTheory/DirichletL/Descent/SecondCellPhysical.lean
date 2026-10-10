import OAI.NumberTheory.DirichletL.Descent.PriorityProfile
import OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def secondCellColumnExponent (Z X:ℝ) (d:BlockIndex):ℝ :=
  Real.logb Z (X/(scales d 0*scales d 2))

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

theorem second_cell_physical_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)=X := by
  rw [second_cell_column_scale Z X d hZ hX]
  field_simp [scales,ne_of_gt (dyadScale_pos (d 0)),ne_of_gt (dyadScale_pos (d 2))]

theorem second_cell_clipping_ratio (Z X b:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X)
    (hb:1≤b) (hsource:scales d 0*scales d 2≤b*X) :
    1≤Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

theorem actual_priority_cell_profile {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) (d:BlockIndex) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
        (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)) := by
  rw [second_cell_physical_scale Z X d hZ hX]
  exact actual_priority_profile_common p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    om lo hi hlo hs negative t Φ Y X hX

theorem actual_priority_cells {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo:ℕ} (source:Finset (MarkedSecondSource ι Jo 0))
    (pool:Finset ι) (Ψ:O→*ℂ) (m:O) (ray:SecondRayIndex)
    (slots₁ slots₂:Finset σ) (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (deleted₁ deleted₂:MarkedSecondSource ι Jo 0→Finset ι)
    (w:MarkedSecondSource ι Jo 0→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    (Y:ℂ)*secondRayCoefficient ray *
      (∑x∈source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X) =
    ∑d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑x∈cell p source d,(w x*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
          (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d))) := by
  intro g θ
  refine (physical_source_partition p hp hcop hg source pool Ψ m ray slots₁ slots₂ lists₁ lists₂
    a₁ a₂ deleted₁ deleted₂ w (principalWindow om lo hi hlo hs negative t)
    (principalWindow om lo hi hlo hs negative t) Φ Y X).trans ?_
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg ((Y : ℂ) * secondRayCoefficient ray * ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg ((w x * actualSecondSignedWeight p hp hcop hg Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) * ·)
    (actual_priority_cell_profile p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hs negative t Φ Y X Z hX hZ d)

theorem actual_source_block_ratios {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (d:BlockIndex)
    (hcell:∀x∈source,index p x=d) (hk:∀x∈source,x.second.frequency≠0) :
    ∀x∈source,∀i,InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i∈Set.Icc 1 2 := by
  intro x hx i
  have hxcell:x∈cell p source d:=(mem_cell p source d x).mpr ⟨hx,hcell x hx⟩
  have hr:=cell_ratios p hp source hk d x hxcell i
  have he:InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i=outerNorms p x i/scales d i := by
    fin_cases i <;> simp [InverseSecondChildWindows.actualOuterRatios,outerNorms,
      primeSubsetGenerator_norm_eq_productNorm]
  rw [he]
  exact ⟨hr.1,hr.2.le⟩

end SevenEighths.InverseMoment

end

end OAI
