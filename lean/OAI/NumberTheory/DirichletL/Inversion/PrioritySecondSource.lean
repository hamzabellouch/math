import OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents
import OAI.NumberTheory.DirichletL.Descent.SecondFullSource

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def quotientSupport (y : SecondParentSource ι Jo) : Finset ι :=
  Function.extend (sourceIdeal p) id (fun _=>∅) y.quotient

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

def residualLists (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) : Finset ι :=
  lists i \ (((if negative then y.cube.rightDivisor else y.cube.leftDivisor)∪y.firstCommon)∪
    quotientSupport p y)

omit [DecidableEq σ] in
theorem residualLists_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative lists (attach p J q)=
      fun i=>lists i\extractedSupport negative q.1 := by
  funext i
  unfold residualLists
  rw [quotientSupport_attach p hinj]
  rfl

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem residualLists_disjoint (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) :
    Disjoint (residualLists p negative lists y i) (quotientSupport p y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hd
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hd)

theorem assigned_quotient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) :
    y.quotient=sourceIdeal p (quotientSupport p y) := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [quotientSupport_attach p hinj]
  rfl

def retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) : Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondDyadicSector pool (secondVariableCutoff p y (R y))
    residual (label y) j)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0) :
    x∈retainedPool p pool parents R label residual j ↔
      secondParentOf x∈parents ∧ x.second∈secondDyadicSector pool
        (secondVariableCutoff p (secondParentOf x) (R (secondParentOf x))) residual
        (label (secondParentOf x)) j := mem_attachedSecondFamily _ _ _

theorem retainedPool_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (assignedParents p source negative J lists) R label residual j) := by
  apply assigned_family_conditions p hp source hs negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem retainedPool_original_support
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈retainedPool p pool parents R label residual j) :
    x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
    x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
      (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  have hh := (mem_retainedPool p pool parents R label residual j x).mp hx
  simpa only [attachSecondExpansion_recover] using
    second_variable_original_support p (secondParentOf x) pool residual (R (secondParentOf x))
      (label (secondParentOf x)) j x.second hh.2

def attachOriginal (J : Finset σ)
    (q : (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) × SecondExpansionData ι) :
    MarkedSecondSource ι (Jo+(J.card+J.card)) 0 :=
  attachSecondExpansion (attach p J q.1) q.2

omit [DecidableEq σ] in
theorem attachOriginal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) : Function.Injective (attachOriginal p (Jo:=Jo) J) := by
  intro q r he
  apply Prod.ext
  · apply attach_injective p hinj J
    exact congrArg secondParentOf he
  · exact congrArg MarkedSecondSource.second he

theorem retainedPool_iff_original
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :
    x∈retainedPool p pool (assignedParents p source negative J lists) R label residual j ↔
      ∃ s∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative s))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative s)),
        ∃ e∈secondDyadicSector pool (secondVariableCutoff p (attach p J (s,q)) (R (attach p J (s,q))))
          residual (label (attach p J (s,q))) j,attachOriginal p J ((s,q),e)=x := by
  constructor
  · intro hx
    obtain ⟨hy,he⟩ := (mem_retainedPool p _ _ _ _ _ _ x).mp hx
    obtain ⟨s,hs,q,hq,ha⟩ := (mem_assignedParents p source negative J lists (secondParentOf x)).mp hy
    refine ⟨s,hs,q,hq,x.second,?_,?_⟩
    · simpa only [ha] using he
    · unfold attachOriginal
      rw [ha,attachSecondExpansion_recover]
  · rintro ⟨s,hs,q,hq,e,he,rfl⟩
    apply (mem_retainedPool p _ _ _ _ _ _ _).mpr
    refine ⟨?_,he⟩
    exact (mem_assignedParents p source negative J lists _).mpr ⟨s,hs,q,hq,rfl⟩

omit [DecidableEq σ] in
theorem attached_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (e : SecondExpansionData ι) :
    coefficient p J a w (secondParentOf (attachOriginal p J (q,e)))=
      w q.1*pairedSlotWeight J J a a q.2 := coefficient_attach p hinj J a w q

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_lists_parent_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo→Finset (SecondExpansionData ι))
    (hE : ∀ y∈parents,∀ x∈source y,x.divisor⊆x.sourceCommon)
    (w : SecondParentSource ι Jo→ℂ) (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : SecondParentSource ι Jo→σ→Finset ι)
    (a₁ a₂ : σ→ι→ℂ) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ y∈parents,w y*secondExpansionSource p hp hcop hg pool Ψ
      (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y) z (source y)
      (fun U=>primeMark slots₁ (lists₁ y) a₁ U*W₁ (primeProductNorm p U/X))
      (fun U=>primeMark slots₂ (lists₂ y) a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y:ℂ)*secondRayCoefficient z * ∑ x∈attachedSecondFamily parents source,
      (w (secondParentOf x)*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ (secondParentOf x)) (lists₂ (secondParentOf x)) a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [secondExpansionSource_attached p hp hcop hg hinj hpr y (source y) (hE y hy)]
  rw [Finset.sum_image (fun x hx z hz he=>attachSecondExpansion_injective y he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def parentPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (y : SecondParentSource ι Jo) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool (quotientSupport p y) y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (residualLists p negative lists y) a) ω X
    (∏ i∈y.firstCommon,p i) (secondParentDivisor p y) core t Y

theorem parentPoisson_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a ω X t Y r core (attach p J q)=
      priorityPoisson p hp hg hinj pool q.1.cube q.1.firstCommon negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) q.1.firstDivisor)
        slots J lists a ω X t Y r core q.1.quotientSupport := by
  unfold parentPoisson
  rw [quotientSupport_attach p hinj,residualLists_attach p hinj]
  rfl

def retainedRow (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  actualSecondSignedWeight p hp hcop hg Ψ
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
    actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      (slots\J) (slots\J) (residualLists p negative lists (secondParentOf x))
      (residualLists p negative lists (secondParentOf x)) a a V V rowMajorant Y X

theorem parentPoisson_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (y : SecondParentSource ι Jo) (pool : Finset ι)
    (hq : y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := secondVariableCutoff p y R
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y =
      truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K := by
  intro Ψ₀ V H K
  have hsum : (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          actualSecondSignedWeight p hp hcop hg Ψ₀
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m ray)
            (slots\J) (slots\J) (residualLists p negative lists y) (residualLists p negative lists y)
            a a V V rowMajorant Y X) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro residual hresidual
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg ((Y:ℂ)*secondRayCoefficient ray * ·)
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  have he := first_parent_full_second_source p hp hcop hg hinj hc hpr y pool (quotientSupport p y) hq
    negative (if negative then r.1 else r.2) Ψ m (slots\J) (residualLists p negative lists y) a
    (fun i _=>residualLists_disjoint p negative lists y i) om lo hi hlo hs X t Y hX hY core R label
  exact he.trans (congrArg (fun z : ℂ=>truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K + z +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K) hsum)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem retained_sum
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (w : SecondParentSource ι Jo→ℂ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y))
      residual (label y) j).image (attachSecondExpansion y),H x) =
    ∑ x∈retainedPool p pool parents R label residual j,w (secondParentOf x)*H x := by
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h),Finset.mul_sum]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
private theorem commute_parent_sectors [Fintype κ]
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (H : SecondParentSource ι Jo→SecondRayIndex→Finset ι→κ→ℂ) :
    (∑ y∈parents,∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,H y ray residual j) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,∑ y∈parents,H y ray residual j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro residual hresidual
  rw [Finset.sum_comm]

theorem parent_family_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (hq : ∀ y∈parents,y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := fun y=>secondVariableCutoff p y (R y)
    (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈retainedPool p pool parents R label residual j,
          w (secondParentOf x)*retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
    (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ V H K
  have he : (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    ∑ y∈parents,w y*(truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y) +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool (K y) residual (label y) j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [parentPoisson_full p hp hcop hg hinj hc hpr y pool (hq y hy) negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core (R y) (label y)]
  rw [he]
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  congr 1
  simp only [Finset.mul_sum]
  rw [commute_parent_sectors]
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h)]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [secondParentOf_attach]
  ring

def fullSource [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) : ℂ :=
  let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
  let K := fun y=>secondVariableCutoff p y (R y)
  (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
  (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
    (Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈retainedPool p pool parents R label residual j,
        w (secondParentOf x)*retainedRow p hp hcop hg pool negative Ψ m slots J lists a V X Y ray x) +
  (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))

theorem first_priority_physical_source [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj pool b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a om X t Y r core D).re) =
    (fullSource p hp hcop hg hinj
      (assignedParents p (fixedSource pool b C E old) negative J lists) pool negative
      (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core) m slots J lists a
      (coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)))
      (principalWindow om lo hi hlo hs negative t) X Y R label).re := by
  rw [first_priority_physical_slice p hp hg hinj]
  have hfun (y : SecondParentSource ι (Jo+(J.card+J.card)))
      (hy : y∈assignedParents p (fixedSource pool b C E old) negative J lists) :
      parentFunction p (fun x=>priorityPoisson p hp hg hinj pool b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a om X t Y r core x.quotientSupport) (forgetAppended y) =
      parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y := by
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p _ negative J lists y).mp hy
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hx
    rw [forget_attach,parentFunction_parent p hinj,parentPoisson_attach p hp hg hinj]
    rfl
  have he := parent_family_full p hp hcop hg hinj hc hpr
    (assignedParents p (fixedSource pool b C E old) negative J lists) pool
    (fun y hy=>assigned_quotient p hinj _ negative J lists y hy)
    negative Ψ m slots J lists a
    (coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)))
    om lo hi hlo hs X t Y hX hY r core R label
  apply congrArg Complex.re
  calc
    _ = ∑ y∈assignedParents p (fixedSource pool b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hfun y hy]
    _ = _ := he

include hp in

theorem fixed_retained_conditions
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,∀ i,(old i).val∣sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p (retainedPool p pool
      (assignedParents p (fixedSource pool b C E old) negative J lists) R label residual j) := by
  apply retainedPool_conditions p hp
  intro x hx
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨hb,hC,hE,hold D hD⟩

end SevenEighths.InversePrioritySecondSource

end

end OAI
