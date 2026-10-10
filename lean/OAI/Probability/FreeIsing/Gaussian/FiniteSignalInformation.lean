import OAI.Probability.FreeIsing.Conditioning.ObservationInformation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

@[reducible] def finiteSignalField {Ω ι : Type*} (m : ι → MeasurableSpace Ω) (I : Finset ι) :
    MeasurableSpace Ω := ⨆ i ∈ I, m i

theorem finiteSignalField_le {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ) (I : Finset ι) :
    finiteSignalField m I ≤ mΩ := iSup_le fun i => iSup_le fun _ => hm i

@[simp] theorem finiteSignalField_singleton {Ω ι : Type*} [DecidableEq ι]
    (m : ι → MeasurableSpace Ω) (i : ι) : finiteSignalField m {i} = m i := by
  simp [finiteSignalField]

@[simp] theorem finiteSignalField_insert {Ω ι : Type*} [DecidableEq ι]
    (m : ι → MeasurableSpace Ω) (I : Finset ι) (i : ι) :
    finiteSignalField m (insert i I) = m i ⊔ finiteSignalField m I := by
  simp [finiteSignalField, Finset.mem_insert, iSup_or, iSup_sup_eq]

theorem indep_finiteSignalField_of_not_mem {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {mu : Measure Ω} {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ)
    (hInd : iIndep m mu) {I : Finset ι} {a : ι} (ha : a ∉ I) :
    Indep (finiteSignalField m I) (m a) mu := by
  have hd : Disjoint (I : Set ι) ({a} : Set ι) := by
    simpa only [Set.disjoint_singleton_right, Finset.mem_coe] using ha
  simpa [finiteSignalField] using indep_iSup_of_disjoint hm hInd hd

theorem condExp_spin_sup_eq_binaryFusion
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a})) :
    rho[fun y => spinSign (S y) | m₁ ⊔ m₂] =ᵐ[rho]
      fun x => binaryFusion (rho[fun y => spinSign (S y) | m₁] x)
        (rho[fun y => spinSign (S y) | m₂] x) := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hq : @Measurable Ω ℝ m₁ inferInstance
      (rho[fun y => spinSign (S y) | m₁]) := stronglyMeasurable_condExp.measurable
  have hr : @Measurable Ω ℝ m₂ inferInstance
      (rho[fun y => spinSign (S y) | m₂]) := stronglyMeasurable_condExp.measurable
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_spin_given_observation_pair_eq_binaryFusion
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂]) hq hr
    (by simp) (by simp) h₁ h₂ hfair hI
  change rho[fun y => spinSign (S y) |
    (m₁.prod m₂).comap (fun x : Ω => (id x, id x))] =ᵐ[rho] _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

theorem abs_condExp_spin_sup_lt_one
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a})) :
    ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁ ⊔ m₂] x| < 1 := by
  filter_upwards [condExp_spin_sup_eq_binaryFusion hm₁ hm₂ hS h₁ h₂ hfair hInd,
    h₁, h₂] with x hx hx₁ hx₂
  rw [hx]
  exact abs_binaryFusion_lt_one hx₁ hx₂

theorem abs_condExp_spin_finiteSignalField_lt_one
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] {m : ι → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ mΩ) {S : Ω → IsingSpin} (hS : Measurable S)
    (hstrict : ∀ i, ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m i] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, iIndep m (cond rho {x | S x = a}))
    (I : Finset ι) (hI : I.Nonempty) :
    ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | finiteSignalField m I] x| < 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert a I ha ih =>
      by_cases hIn : I.Nonempty
      · rw [finiteSignalField_insert, sup_comm]
        exact abs_condExp_spin_sup_lt_one (finiteSignalField_le hm I) (hm a) hS
          (ih hIn) (hstrict a) hfair
          (fun b => indep_finiteSignalField_of_not_mem hm (hInd b) ha)
      · have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIn
        subst I
        simpa using hstrict a

def spinInformation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (rho : Measure Ω) (S : Ω → IsingSpin) (m : MeasurableSpace Ω) : ℝ :=
  ∫ x, (rho[fun y => spinSign (S y) | m] x) ^ 2 ∂rho

theorem spinInformation_sup_le_add
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a}))
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) :
    spinInformation rho S (m₁ ⊔ m₂) ≤
      spinInformation rho S m₁ + spinInformation rho S m₂ := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_observation_pair_secondMoment_le_add
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂])
    stronglyMeasurable_condExp.measurable stronglyMeasurable_condExp.measurable
    (by simp) (by simp) h₁ h₂ hfair hI hsym
  change spinInformation rho S
    ((m₁.prod m₂).comap (fun x : Ω => (id x, id x))) ≤ _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

theorem spinInformation_sup_le_sub_loss
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a}))
    {theta : ℝ}
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| ≤ theta)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| ≤ theta)
    (htheta : theta < 1)
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) :
    spinInformation rho S (m₁ ⊔ m₂) ≤
      spinInformation rho S m₁ + spinInformation rho S m₂ -
        2 * (1 - theta ^ 2) * spinInformation rho S m₁ * spinInformation rho S m₂ := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_observation_pair_secondMoment_le
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂])
    stronglyMeasurable_condExp.measurable stronglyMeasurable_condExp.measurable
    (by simp) (by simp) hfair hI theta h₁ h₂ htheta hsym
  change spinInformation rho S
    ((m₁.prod m₂).comap (fun x : Ω => (id x, id x))) ≤ _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

section FiniteFamily

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {rho : Measure Ω}
  [IsProbabilityMeasure rho] {m : ι → MeasurableSpace Ω}
  (hm : ∀ i, m i ≤ mΩ) {S : Ω → IsingSpin} (hS : Measurable S)
  (hstrict : ∀ i, ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m i] x| < 1)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hInd : ∀ a : IsingSpin, iIndep m (cond rho {x | S x = a}))
  (hsym : ∀ i, Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m i]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m i]) rho)

include hm hS hstrict hfair hInd hsym

theorem spinInformation_finiteSignalField_union_le [DecidableEq ι]
    (J : Finset ι) (hJ : J.Nonempty) (I : Finset ι) (hIJ : Disjoint I J) :
    spinInformation rho S (finiteSignalField m (I ∪ J)) ≤
      (∑ i ∈ I, spinInformation rho S (m i)) + spinInformation rho S (finiteSignalField m J) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      have hI : Disjoint I J := (Finset.disjoint_insert_left.mp hIJ).2
      have haJ : a ∉ J := (Finset.disjoint_insert_left.mp hIJ).1
      have haIJ : a ∉ I ∪ J := by simp [ha, haJ]
      have hne : (I ∪ J).Nonempty := hJ.mono Finset.subset_union_right
      have hbound := spinInformation_sup_le_add (finiteSignalField_le hm (I ∪ J))
        (hm a) hS
        (abs_condExp_spin_finiteSignalField_lt_one hm hS hstrict hfair hInd (I ∪ J) hne)
        (hstrict a) hfair
        (fun b => indep_finiteSignalField_of_not_mem hm (hInd b) haIJ) (hsym a)
      have hih := ih hI
      rw [Finset.insert_union, finiteSignalField_insert, sup_comm]
      rw [Finset.sum_insert ha]
      linarith

theorem spinInformation_finiteSignalField_le_sum
    (I : Finset ι) (hI : I.Nonempty) :
    spinInformation rho S (finiteSignalField m I) ≤
      ∑ i ∈ I, spinInformation rho S (m i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert a I ha ih =>
      by_cases hIn : I.Nonempty
      · have hbound := spinInformation_sup_le_add (finiteSignalField_le hm I) (hm a) hS
          (abs_condExp_spin_finiteSignalField_lt_one hm hS hstrict hfair hInd I hIn)
          (hstrict a) hfair
          (fun b => indep_finiteSignalField_of_not_mem hm (hInd b) ha) (hsym a)
        rw [finiteSignalField_insert, sup_comm, Finset.sum_insert ha]
        linarith [ih hIn]
      · have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIn
        subst I
        simp

theorem spinInformation_finiteSignalField_le_sum_sub_loss
    (I : Finset ι) {a b : ι} (hab : a ≠ b) (ha : a ∈ I) (hb : b ∈ I)
    {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m a] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m b] x| ≤ theta)
    (htheta : theta < 1) :
    spinInformation rho S (finiteSignalField m I) ≤
      (∑ i ∈ I, spinInformation rho S (m i)) -
        2 * (1 - theta ^ 2) * spinInformation rho S (m a) * spinInformation rho S (m b) := by
  classical
  have hJsub : ({a, b} : Finset ι) ⊆ I := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ha
    · have hc' : c = b := Finset.mem_singleton.mp hc
      simpa only [hc'] using hb
  have hdisj : Disjoint (I \ {a, b}) ({a, b} : Finset ι) := by
    apply Finset.disjoint_left.mpr
    intro c hc hcJ
    exact (Finset.mem_sdiff.mp hc).2 hcJ
  have hunion := spinInformation_finiteSignalField_union_le hm hS hstrict hfair hInd hsym
    {a, b} (by simp) (I \ {a, b}) hdisj
  rw [Finset.sdiff_union_of_subset hJsub] at hunion
  have hpairInd (s : IsingSpin) : Indep (m a) (m b) (cond rho {x | S x = s}) := by
    simpa using indep_finiteSignalField_of_not_mem hm (hInd s)
      (I := {a}) (a := b) (by simp [Ne.symm hab])
  have hpair := spinInformation_sup_le_sub_loss (hm a) (hm b) hS hfair hpairInd
    haTheta hbTheta htheta (hsym b)
  have hsum := Finset.sum_sdiff (f := fun i => spinInformation rho S (m i)) hJsub
  simp only [finiteSignalField_insert, finiteSignalField_singleton] at hunion
  simp [hab] at hsum
  linarith

end FiniteFamily

end Problem367

end

end OAI
