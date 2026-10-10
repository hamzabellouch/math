import OAI.Combinatorics.ContingencyTables.Transport.ObservableBounds

namespace OAI

/-!
# The manuscript's original omission coordinates

Complementation reverses defect labels and their multipliers. We prove the
actual chain energy, conditional projection, and variance identities before
transferring the variance and observable inequalities back to the original
factorial lift f. The final theorems assume its omission property.
-/

namespace ContingencyTables.ComplementChain

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion PairedComplement ObservableVariance ObservableBounds

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] [DecidableEq Γ] in
lemma plain_complement (gs : List (Γ × Γ)) (S : Set Γ) :
    PlainState gs Sᶜ ↔ PlainState gs S := by
  unfold PlainState PairSingle
  simp only [Set.mem_compl_iff]
  constructor <;> intro h p hp <;> have hh := h p hp <;> tauto

omit [Fintype Γ] [DecidableEq Γ] in
lemma defect_complement (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) :
    DefectState gs p r Sᶜ ↔ DefectState gs r p S := by
  unfold DefectState PairEmpty PairFull PairSingle
  simp only [Set.mem_compl_iff, not_not]
  constructor
  · rintro ⟨hp,hr,hpr,hep,hfr,hs⟩
    refine ⟨hr,hp,hpr.symm,hfr,hep,?_⟩
    intro t ht htr htp
    have h := hs t ht htp htr
    tauto
  · rintro ⟨hr,hp,hrp,her,hfp,hs⟩
    refine ⟨hp,hr,hrp.symm,hfp,her,?_⟩
    intro t ht htp htr
    have h := hs t ht htr htp
    tauto

omit [Fintype Γ] [DecidableEq Γ] in
lemma state_complement (gs : List (Γ × Γ)) (S : Set Γ) :
    ChainState gs Sᶜ ↔ ChainState gs S := by
  unfold ChainState
  rw [plain_complement]
  constructor
  · rintro (h | ⟨p,r,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,p,(defect_complement gs p r S).mp h⟩
  · rintro (h | ⟨p,r,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,p,(defect_complement gs r p S).mpr h⟩

omit [Fintype Γ] [DecidableEq Γ] in
lemma adjacent_complement (S T : Set Γ) : ExchangeAdjacent Sᶜ Tᶜ ↔ ExchangeAdjacent S T := by
  have hf (S T : Set Γ) (h : ExchangeAdjacent S T) : ExchangeAdjacent Sᶜ Tᶜ := by
    obtain ⟨A,a,b,hab,ha,hb,rfl,rfl⟩ := h
    let B := (insert a (insert b A))ᶜ
    refine ⟨B,b,a,hab.symm,?_,?_,?_,?_⟩
    · simp [B]
    · simp [B]
    · ext x
      simp only [B, Set.mem_compl_iff, Set.mem_insert_iff]
      constructor
      · intro hx
        by_cases hxb : x = b
        · exact Or.inl hxb
        · exact Or.inr (by tauto)
      · intro hx
        rcases hx with rfl | hx
        · exact not_or.mpr ⟨hab.symm, hb⟩
        · tauto
    · ext x
      simp only [B, Set.mem_compl_iff, Set.mem_insert_iff]
      constructor
      · intro hx
        by_cases hxa : x = a
        · exact Or.inl hxa
        · exact Or.inr (by tauto)
      · intro hx
        rcases hx with rfl | hx
        · exact not_or.mpr ⟨hab, ha⟩
        · tauto
  exact ⟨fun h => by simpa using hf Sᶜ Tᶜ h, hf S T⟩

omit [Fintype Γ] [DecidableEq Γ] in
def complementEquiv : Set Γ ≃ Set Γ where
  toFun := compl
  invFun := compl
  left_inv := compl_compl
  right_inv := compl_compl

omit [Fintype Γ] [DecidableEq Γ] in
def reverseMultiplier (w : (Γ × Γ) → (Γ × Γ) → ℝ) : (Γ × Γ) → (Γ × Γ) → ℝ :=
  fun p r => w r p

lemma multiplier_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (S : Set Γ) :
    chainMultiplier gs (reverseMultiplier w) Sᶜ = chainMultiplier gs w S := by
  by_cases he : ∃ p r, DefectState gs p r S
  · obtain ⟨p,r,h⟩ := he
    rw [chainMultiplier_defect gs _ Sᶜ ((defect_complement gs r p S).mpr h),
      chainMultiplier_defect gs w S h]
    rfl
  · have hec : ¬ ∃ p r, DefectState gs p r Sᶜ := by
      rintro ⟨p,r,h⟩
      exact he ⟨r,p,(defect_complement gs p r S).mp h⟩
    simp only [chainMultiplier, dite_eq_right he, dite_eq_right hec]

lemma weight_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (S : Set Γ) :
    chainWeight gs (reverseMultiplier w) (complementWeight f) Sᶜ = chainWeight gs w f S := by
  simp only [chainWeight, multiplier_complement, complementWeight, compl_compl]

lemma chain_sum_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f J : Set Γ → ℝ) :
    (∑ S ∈ chainStates gs, chainWeight gs (reverseMultiplier w) (complementWeight f) S * J S) =
      ∑ S ∈ chainStates gs, chainWeight gs w f S * J Sᶜ := by
  simp only [chainStates, Finset.sum_filter]
  apply Fintype.sum_equiv complementEquiv
  intro S
  change (if ChainState gs S then _ else 0) = (if ChainState gs Sᶜ then _ else 0)
  rw [state_complement]
  by_cases h : ChainState gs S
  · simp only [ite_eq_left h]
    have hw := weight_complement gs w f Sᶜ
    simp only [compl_compl] at hw
    rw [hw]
    simp only [complementEquiv, Equiv.coe_fn_mk, compl_compl]
  · simp only [ite_eq_right h]

lemma total_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) :
    chainTotal gs (reverseMultiplier w) (complementWeight f) = chainTotal gs w f := by
  simpa only [chainTotal, mul_one] using chain_sum_complement gs w f (fun _ => 1)

lemma mean_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    chainMean gs (reverseMultiplier w) (complementWeight f) (complementWeight H) = chainMean gs w f H := by
  unfold chainMean
  rw [total_complement, chain_sum_complement]
  simp only [complementWeight, compl_compl]

lemma variance_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    chainVariance gs (reverseMultiplier w) (complementWeight f) (complementWeight H) =
      chainVariance gs w f H := by
  unfold chainVariance
  rw [total_complement, mean_complement, chain_sum_complement]
  simp only [complementWeight, compl_compl]

lemma conductance_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (ST : Set Γ × Set Γ) :
    chainConductance gs (reverseMultiplier w) (complementWeight f) (ST.1ᶜ,ST.2ᶜ) =
      chainConductance gs w f ST := by
  simp only [chainConductance, multiplier_complement, complementWeight, compl_compl]

lemma energy_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    restrictedEnergy (chainEdges gs) (chainConductance gs (reverseMultiplier w) (complementWeight f))
        (complementWeight H) ∅ ∅ =
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  have hr (ST : Set Γ × Set Γ) : EdgeRespects ∅ ∅ ST := by simp [EdgeRespects, Respects]
  unfold restrictedEnergy
  simp only [hr, ite_true, chainEdges, Finset.sum_filter]
  congr 1
  let E : (Set Γ × Set Γ) ≃ (Set Γ × Set Γ) := Equiv.prodCongr complementEquiv complementEquiv
  apply Fintype.sum_equiv E
  intro ST
  change (if ChainState gs ST.1 ∧ ChainState gs ST.2 ∧ ExchangeAdjacent ST.1 ST.2 then _ else 0) =
    (if ChainState gs ST.1ᶜ ∧ ChainState gs ST.2ᶜ ∧ ExchangeAdjacent ST.1ᶜ ST.2ᶜ then _ else 0)
  rw [state_complement, state_complement, adjacent_complement]
  by_cases h : ChainState gs ST.1 ∧ ChainState gs ST.2 ∧ ExchangeAdjacent ST.1 ST.2
  · simp only [ite_eq_left h]
    have hc := conductance_complement gs w f (ST.1ᶜ,ST.2ᶜ)
    simp only [compl_compl] at hc
    rw [hc]
    rfl
  · simp only [ite_eq_right h]

lemma dirichlet_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    chainDirichlet gs (reverseMultiplier w) (complementWeight f) (complementWeight H) =
      chainDirichlet gs w f H := by
  unfold chainDirichlet
  rw [total_complement, energy_complement]

lemma plain_mass_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) :
    slotTotal gs (complementWeight f) ∅ = slotTotal gs f ∅ := by
  exact slotTotal_complement gs f ∅ ∅ (by simp) (by simpa using hgs) (by simpa using hcover)

lemma defect_mass_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ)
    (p r : Γ × Γ) (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    slotDefect gs (complementWeight f) ∅ p r = slotDefect gs f ∅ r p := by
  exact slotDefect_complement gs f ∅ ∅ (by simp) (by simpa using hgs) (by simpa using hcover) p r hp hr hpr

lemma projection_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f H : Set Γ → ℝ) :
    observableProjection gs (complementWeight f) (complementWeight H) =
      complementWeight (observableProjection gs f H) := by
  have hmul : (fun S => complementWeight f S * complementWeight H S) =
      complementWeight (fun S => f S * H S) := rfl
  funext S
  change observableProjection gs (complementWeight f) (complementWeight H) S =
    observableProjection gs f H Sᶜ
  by_cases he : ∃ p r, DefectState gs p r S
  · obtain ⟨p,r,h⟩ := he
    have hc : DefectState gs r p Sᶜ := (defect_complement gs r p S).mpr h
    rw [observableProjection_defect gs _ _ S h, observableProjection_defect gs f H Sᶜ hc]
    unfold defectMean
    rw [hmul, defect_mass_complement gs hgs hcover _ p r h.1 h.2.1 h.2.2.1,
      defect_mass_complement gs hgs hcover f p r h.1 h.2.1 h.2.2.1]
  · have hec : ¬ ∃ p r, DefectState gs p r Sᶜ := by
      rintro ⟨p,r,h⟩
      exact he ⟨r,p,(defect_complement gs p r S).mp h⟩
    simp only [observableProjection, dite_eq_right he, dite_eq_right hec, complementWeight]

lemma slotVariance_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f H : Set Γ → ℝ) :
    slotVariance gs (complementWeight f) (complementWeight H) ∅ = slotVariance gs f H ∅ := by
  unfold slotVariance
  change slotTotal gs (complementWeight (fun S => f S*(H S)^2)) ∅ -
    (slotTotal gs (complementWeight (fun S => f S*H S)) ∅)^2/slotTotal gs (complementWeight f) ∅ = _
  rw [plain_mass_complement gs hgs hcover, plain_mass_complement gs hgs hcover,
    plain_mass_complement gs hgs hcover]

/-- The actual manuscript variance theorem in original omission coordinates. -/
theorem omission_twoLift_transversal_variance (gs : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : OmissionProperty f gs.length) (hsigg : AdditionProperty g gs.length)
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ)*q^2)*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  have hcard := slots_ground_card gs hgs hcover
  have hhalf : Fintype.card Γ - gs.length = gs.length := by omega
  have hfc : DegreePositive (complementWeight f) gs.length := by
    simpa only [hhalf] using complement_degreePositive f gs.length (by omega) hf
  have hgc : DegreePositive (complementWeight g) gs.length := by
    simpa only [hhalf] using complement_degreePositive g gs.length (by omega) hg
  have hsf : AdditionProperty (complementWeight f) gs.length := by
    simpa only [OmissionProperty, hhalf] using hsigf
  have hsg : OmissionProperty (complementWeight g) gs.length := by
    have hcc : complementWeight (complementWeight g) = g := by funext S; simp [complementWeight]
    simpa only [OmissionProperty, hhalf, hcc] using hsigg
  have hgood' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs (complementWeight f) ∅/(4*slotDefect gs (complementWeight f) ∅ p r) ≤ reverseMultiplier w p r := by
    intro p hp r hr hpr
    rw [plain_mass_complement gs hgs hcover, defect_mass_complement gs hgs hcover f p r hp hr hpr]
    exact hgood r hr p hp hpr.symm
  have ht := validDegree_twoLift_transversal_variance gs (complementWeight f) (complementWeight g)
    (complementWeight H) (reverseMultiplier w) q hq hfc hgc hsf hsg hgs hcover
    (fun p r => hw r p) hgood'
    (fun S hS => hagree Sᶜ ((plain_complement gs S).mpr hS))
    (fun S hS => hcompare Sᶜ ((state_complement gs S).mpr hS))
  rwa [slotVariance_complement gs hgs hcover f H, energy_complement gs w f H] at ht

/-- The paper's observable Poincaré theorem for the literal first factorial
lift, assuming its omission property only at the actual subset degree. -/
theorem omission_observable_poincare (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ)
    (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainVariance gs w f (observableProjection gs f H) ≤
      observableConstant gs.length q * chainDirichlet gs w f H := by
  have hcard := slots_ground_card gs hgs hcover
  have hhalf : Fintype.card Γ - gs.length = gs.length := by omega
  have hfc : DegreePositive (complementWeight f) gs.length := by
    simpa only [hhalf] using complement_degreePositive f gs.length (by omega) hf
  have hsf : AdditionProperty (complementWeight f) gs.length := by
    simpa only [OmissionProperty, hhalf] using hsig
  have hl : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs (complementWeight f) ∅/(4*slotDefect gs (complementWeight f) ∅ p r) ≤ reverseMultiplier w p r := by
    intro p hp r hr hpr
    rw [plain_mass_complement gs hgs hcover, defect_mass_complement gs hgs hcover f p r hp hr hpr]
    exact hlower r hr p hp hpr.symm
  have hu : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      reverseMultiplier w p r ≤ 4*slotTotal gs (complementWeight f) ∅/slotDefect gs (complementWeight f) ∅ p r := by
    intro p hp r hr hpr
    rw [plain_mass_complement gs hgs hcover, defect_mass_complement gs hgs hcover f p r hp hr hpr]
    exact hupper r hr p hp hpr.symm
  have ht := validDegree_observable_poincare gs hgs hne hcover (reverseMultiplier w)
    (fun p r => hw r p) (complementWeight f) (complementWeight H) hfc hsf q hq hl hu
  rwa [projection_complement gs hgs hcover, variance_complement, dirichlet_complement] at ht

end ContingencyTables.ComplementChain

end OAI
