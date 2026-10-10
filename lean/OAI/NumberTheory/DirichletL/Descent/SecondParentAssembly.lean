import OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
@[simp] theorem secondParentOf_attach {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : secondParentOf (attachSecondExpansion parent x) = parent := rfl

def attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι)) :
    Finset (MarkedSecondSource ι Jo 0) :=
  parents.biUnion (fun parent => (source parent).image (attachSecondExpansion parent))

omit [DecidableEq ι] in
theorem mem_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (x : MarkedSecondSource ι Jo 0) :
    x∈attachedSecondFamily parents source ↔
      secondParentOf x∈parents ∧ x.second∈source (secondParentOf x) := by
  simp only [attachedSecondFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨parent,hp,y,hy,rfl⟩
    exact ⟨hp,hy⟩
  · rintro ⟨hp,hx⟩
    exact ⟨secondParentOf x,hp,x.second,hx,attachSecondExpansion_recover x⟩

omit [DecidableEq ι] in
theorem sum_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    {A : Type*} [AddCommMonoid A] (H : MarkedSecondSource ι Jo 0 → A) :
    ∑ x∈attachedSecondFamily parents source,H x =
      ∑ parent∈parents,∑ x∈source parent,H (attachSecondExpansion parent x) := by
  unfold attachedSecondFamily
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro parent hp
    exact Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hy
    exact hab (congrArg secondParentOf he).symm

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_family_conditions {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (ha : ∀ parent∈parents,parent.cube.Admissible)
    (hC : ∀ parent∈parents,Disjoint parent.firstCommon parent.cube.support)
    (hD : ∀ parent∈parents,parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ parent∈parents,∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : ∀ parent∈parents,parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (attachedSecondFamily parents source) := by
  have h (x : MarkedSecondSource ι Jo 0) (hx : x∈attachedSecondFamily parents source) :=
    (mem_attachedSecondFamily parents source x).mp hx
  constructor
  · intro x hx; exact ha (secondParentOf x) (h x hx).1
  · intro x hx; exact hC (secondParentOf x) (h x hx).1
  · intro x hx; exact hD (secondParentOf x) (h x hx).1
  · intro x hx; exact hE (secondParentOf x) (h x hx).1 x.second (h x hx).2
  · intro x hx i; exact hold (secondParentOf x) (h x hx).1 i
  · intro x hx i; exact Fin.elim0 i
  · intro x hx; exact hq (secondParentOf x) (h x hx).1

theorem secondExpansionSource_whole_parent_family
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (w : SecondParentSource ι Jo → ℂ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ parent∈parents,w parent*secondExpansionSource p hp hcop hg pool Ψ
      (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
      z (source parent)
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈attachedSecondFamily parents source,
        (w (secondParentOf x)*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parent hparent
  rw [secondExpansionSource_attached p hp hcop hg hinj hpr parent (source parent) (hE parent hparent)]
  rw [Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end
end SevenEighths.InverseMoment

end OAI
