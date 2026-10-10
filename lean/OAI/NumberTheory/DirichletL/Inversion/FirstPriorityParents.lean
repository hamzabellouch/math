import OAI.NumberTheory.DirichletL.Descent.FirstActualPriorityEnergy
import OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
import OAI.NumberTheory.DirichletL.Descent.SecondParentAssembly

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Source (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotientSupport : Finset ι
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def extractedSupport (negative : Bool) (x : Source ι Jo) : Finset ι :=
  ((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪x.quotientSupport

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def parent (x : Source ι Jo) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := sourceIdeal p x.quotientSupport
  oldAssigned := x.oldAssigned

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

def appendParent {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : SecondParentSource ι (Jo+Jn) where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := Fin.addCases x.oldAssigned q

def forgetAppended {Jn : ℕ} (x : SecondParentSource ι (Jo+Jn)) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := fun i=>x.oldAssigned (Fin.castAdd Jn i)

omit [DecidableEq ι] in
@[simp] theorem forget_append {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : forgetAppended (appendParent x q)=x := by
  apply SecondParentSource.ext <;> try rfl
  funext i
  simp only [forgetAppended,appendParent,Fin.addCases_left]

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→SmoothMobiusCorrection.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

def attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) : SecondParentSource ι (Jo+(J.card+J.card)) :=
  appendParent (parent p q.1) (fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→SmoothMobiusCorrection.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem forget_attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    forgetAppended (attach p J q)=parent p q.1 := forget_append _ _

def assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈extractedSupport negative q.1)

def assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (assignmentSource source negative J lists).image (attach p J)

theorem sum_assignmentSource {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈assignmentSource source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (x,q) := by
  rw [assignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_assignedParents (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈assignedParents p source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (attach p J (x,q)) := by
  rw [assignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_assignmentSource source negative J lists _

def coefficient (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) :
    SecondParentSource ι (Jo+(J.card+J.card))→ℂ :=
  Function.extend (attach p J) (fun q=>w q.1*pairedSlotWeight J J a a q.2) (fun _=>0)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

theorem paired_parent_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (extractedSupport negative x))*
      primeMark J lists a (extractedSupport negative x))*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_assignedParents p hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem paired_parent_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    paired_parent_sum p hinj source negative J lists a w H

lemma mem_assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈assignmentSource source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)) := by
  rw [←paired_assignment_filter]
  simp only [assignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈assignedParents p source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),attach p J (x,q)=y := by
  simp only [assignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_assignmentSource source negative J lists x q).mp hq |>.1,
      q,(mem_assignmentSource source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_assignmentSource source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

structure SourceValid (x : Source ι Jo) : Prop where
  admissible : x.cube.Admissible
  common_disjoint : Disjoint x.firstCommon x.cube.support
  first_divisor : x.firstDivisor⊆x.firstCommon∪x.cube.support
  old_support : ∀ i,(x.oldAssigned i).val∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

theorem attach_old_support (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
      (J.pi (fun i=>lists i∩extractedSupport negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      extracted_prime_dvd p x hx.admissible negative _ (hh k)

omit [DecidableEq σ] in

theorem attach_physical_data (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (m : O) :
    secondParentLabel p (attach p J q)=secondParentLabel p (parent p q.1) ∧
    secondParentDivisor p (attach p J q)=secondParentDivisor p (parent p q.1) ∧
    secondParentPuncture p m (attach p J q)=secondParentPuncture p m (parent p q.1) :=
  ⟨rfl,rfl,rfl⟩

theorem coefficient_norm (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) : ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

theorem assigned_family_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈assignedParents p source negative J lists,∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily (assignedParents p source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact attach_old_support p negative J lists x (hs x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

def fixedPoint (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (D : Finset ι) : Source ι Jo :=
  ⟨b,C,E,D,old⟩

def fixedSource (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Finset (Source ι Jo) :=
  F.powerset.image (fixedPoint b C E old)

omit [DecidableEq ι] in
theorem fixedPoint_injective (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Function.Injective (fixedPoint b C E old) := by
  intro D D' h
  exact congrArg Source.quotientSupport h

def parentFunction (H : Source ι Jo→ℂ) : SecondParentSource ι Jo→ℂ :=
  Function.extend (parent p) H (fun _=>0)

theorem parentFunction_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (H : Source ι Jo→ℂ) (x : Source ι Jo) : parentFunction p H (parent p x)=H x :=
  (parent_injective p hinj).extend_apply _ _ _

theorem paired_source_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w H : Source ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H x) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*parentFunction p H (forgetAppended y) := by
  simpa only [parentFunction_parent p hinj] using
    paired_parent_sq_sum p hinj source negative J lists a w (parentFunction p H)

theorem fixed_priority_complex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w H : Finset ι→ℂ) :
    (∑ D∈F.powerset,w D*(‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 : ℝ)*H D) =
    ∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>w x.quotientSupport) y *
        parentFunction p (fun x=>H x.quotientSupport) (forgetAppended y) := by
  have he := paired_source_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>w x.quotientSupport) (fun x=>H x.quotientSupport)
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  simpa only [fixedPoint,extractedSupport,fixedSource] using he

theorem fixed_priority_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Finset ι→ℝ) :
    (∑ D∈F.powerset,w D*‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(w x.quotientSupport:ℂ)) y).re := by
  have he := paired_parent_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>(w x.quotientSupport:ℂ)) (fun _=>1)
  simp only [mul_one] at he
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    fixedPoint,extractedSupport,fixedSource] using hr

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityOuter (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℝ :=
  (‖RayFourExpansion.crossCoeff r.1 r.2‖*‖selector D‖) *
    ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖

def priorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)) a U)
    ω X (∏i∈C,p i) d core t Y

theorem first_priority_physical_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter) (core : FirstCoreIndex) :
    (∑ D∈F.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core D).re) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
      parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  have he := fixed_priority_complex p hinj F b C E old negative J lists a
    (fun D=>(priorityOuter p hg b negative Ψ m selector r core D:ℂ))
    (priorityPoisson p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots J lists a ω X t Y r core)
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using hr

theorem first_priority_energy_reindex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) :
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector ω X t Y =
    (32*512)*(2:ℝ)^slots.card *
      ∑ r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
      (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
        coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
          slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  simp_rw [←first_priority_physical_slice p hp hg hinj]
  unfold firstPrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter priorityPoisson
  ring

end SevenEighths.InverseFirstPriorityParents

end

end OAI
