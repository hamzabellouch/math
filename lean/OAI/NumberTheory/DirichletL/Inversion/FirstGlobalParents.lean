import OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceEnergy
import OAI.NumberTheory.DirichletL.Descent.GlobalParentEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def ofOriginal (k : FirstOriginalOuter ι) : Source ι 0 where
  cube := k.1
  firstCommon := k.2.1
  firstDivisor := k.2.2
  quotientSupport := ∅
  oldAssigned := Fin.elim0

def toOriginal (x : Source ι 0) : FirstOriginalOuter ι :=
  ⟨x.cube,⟨x.firstCommon,x.firstDivisor⟩⟩

omit [DecidableEq ι] in
@[simp] theorem toOriginal_ofOriginal (k : FirstOriginalOuter ι) :
    toOriginal (ofOriginal k)=k := by cases k with | mk b k => cases k; rfl

omit [DecidableEq ι] in
@[simp] theorem toOriginal_fill (x : Source ι 0) (D : Finset ι) :
    toOriginal (fillFirstQuotient x D)=toOriginal x := rfl

omit [DecidableEq ι] in
theorem ofOriginal_injective : Function.Injective (ofOriginal (ι:=ι)) :=
  Function.LeftInverse.injective toOriginal_ofOriginal

omit [DecidableEq ι] in
theorem ofOriginal_toOriginal (x : Source ι 0) :
    ofOriginal (toOriginal x)=eraseFirstQuotient x := by
  apply Source.ext <;> try rfl
  exact funext (fun i=>Fin.elim0 i)

omit [DecidableEq ι] in

theorem fill_ofOriginal_injective : Function.Injective
    (fun q : FirstOriginalOuter ι × Finset ι=>fillFirstQuotient (ofOriginal q.1) q.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [toOriginal_fill,toOriginal_ofOriginal] using congrArg toOriginal h
  · exact congrArg Source.quotientSupport h

def originalOuterSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (Source ι 0) :=
  (firstOriginalOuter pool Q).image ofOriginal

theorem originalOuterSource_empty (pool : Finset ι) (Q : Finset (ι→₀ℕ)) :
    ∀x∈originalOuterSource pool Q,x.quotientSupport=∅ := by
  intro x hx
  obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
  rfl

theorem sum_originalOuterSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (H : Source ι 0→A) :
    (∑x∈originalOuterSource pool Q,H x)=∑k∈firstOriginalOuter pool Q,H (ofOriginal k) := by
  exact Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)

def originalSelector (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (x : Source ι 0) (D : Finset ι) : ℂ := selector (toOriginal x) D

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) (D : Finset ι) :
    originalSelector selector (ofOriginal k) D=selector k D := by
  simp only [originalSelector,toOriginal_ofOriginal]

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal_fun (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) : originalSelector selector (ofOriginal k)=selector k :=
  funext (originalSelector_ofOriginal selector k)

def originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) : Finset (Source ι 0) :=
  globalParentSource (originalOuterSource pool Q) pool (originalSelector selector)

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i

theorem originalParentSource_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,SourceValid p x := by
  intro x hx
  obtain ⟨k,hk,D,hD,hs,rfl⟩:=(mem_originalParentSource pool Q selector x).mp hx
  exact original_fill_valid p pool Q k hk D

theorem sum_originalParentSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→A) :
    (∑x∈originalParentSource pool Q selector,H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset.filter (fun D=>selector k D≠0),
        H (fillFirstQuotient (ofOriginal k) D) := by
  rw [originalParentSource,sum_globalParentSource _ _ _ (originalOuterSource_empty pool Q),
    sum_originalOuterSource]
  simp only [originalSelector_ofOriginal]

theorem signed_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,selector (toOriginal x) x.quotientSupport*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        selector k D*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem real_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℝ) :
    (∑x∈originalParentSource pool Q selector,‖selector (toOriginal x) x.quotientSupport‖*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        ‖selector k D‖*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem original_supports (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (k : FirstOriginalOuter ι)
    (hk : k∈firstOriginalOuter pool Q) :
    k.1.leftExponent∈Q ∧ k.1.rightExponent∈Q ∧
      k.1.support⊆pool ∧ k.2.1⊆pool ∧ k.2.2⊆pool := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  have hb' := (mem_reopenedCubeFamily Q k.1).mp hb
  have hs := reopenedCubeFamily_support pool Q hQ k.1 hb
  have hc : k.2.1⊆pool := (Finset.mem_powerset.mp hC).trans Finset.sdiff_subset
  refine ⟨hb'.1,hb'.2.1,hs,hc,?_⟩
  exact (Finset.mem_powerset.mp hE).trans (Finset.union_subset hc
    ((Finset.filter_subset _ _).trans hs))

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem original_principal_extra (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,
      cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit ⊆ x.cube.support := by
  intro x hx
  exact Finset.filter_subset _ _

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem original_parent_data (k : FirstOriginalOuter ι) (D : Finset ι) :
    (parent p (fillFirstQuotient (ofOriginal k) D)).cube=k.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstCommon=k.2.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstDivisor=k.2.2 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).quotient=sourceIdeal p D :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem original_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈assignedParents p (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (assignedParents p (originalParentSource pool Q selector) negative J lists) expansion) :=
  assigned_family_conditions p hp _ (originalParentSource_valid p pool Q selector)
    negative J lists expansion hE

theorem original_whole_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈wholeAssignedParents p
      (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit)
      (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (wholeAssignedParents p
        (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)
        (originalParentSource pool Q selector) negative J lists) expansion) :=
  whole_assigned_family_conditions p hp _ _ (originalParentSource_valid p pool Q selector)
    (original_principal_extra pool Q selector) negative J lists expansion hE

variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_priority_slice
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (ray : RayCharacter×RayCharacter)
    (core : FirstCoreIndex) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
      (priorityOuter p hg k.1 negative Ψ m (selector k) ray core D:ℂ)*
        H (fillFirstQuotient (ofOriginal k) D) := by
  have h:=global_original_priority_slice p hg (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) negative Ψ m ray core H
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

theorem original_second_energy_source
    (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (extra : CubeCoordinates ι→Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (om : ℝ→ℂ) (X t Y : ℝ) :
    (∑k∈firstOriginalOuter pool Q,
      firstWholePrioritySecondEnergy p hp hg hinj pool k.1 k.2.1 (extra k.1)
        negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
        slots lists a (selector k) om X t Y)=
    (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,
      ∑J∈slots.powerset,(∑x∈originalParentSource pool Q selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re := by
  have h:=global_second_energy_source p hg hp hinj (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) extra negative Ψ m
    slots lists a om X t Y
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

end SevenEighths.InverseFirstGlobalParents

end

end OAI
