import OAI.Combinatorics.ContingencyTables.Transport.ObservableVariance

namespace OAI

/-!
# Observable and trace bounds on the actual valid-degree chain

Positive completion is used only to instantiate the existing finite-chain
constructor. All its state weights, conductances, and conditional projections
are proved equal to the original valid-degree quantities.
-/

namespace ContingencyTables.ObservableBounds

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableVariance

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The manuscript's observable constant. -/
def observableConstant (p q : ℝ) : ℝ :=
  10*p^4*(9*(p*(1+8*p*q^2))+2*(8+32*p*q^3))

lemma observableConstant_lower (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    338*p^5 ≤ observableConstant p q := by
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hprod : 1 ≤ p*q^2 := hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hq2 hp0])
  have hbig : 81*p ≤ 9*(p*(1+8*p*q^2)) := by nlinarith
  have htail : 0 ≤ 2*(8+32*p*q^3) := by positivity
  have hi : (338/10 : ℝ)*p ≤ 9*(p*(1+8*p*q^2))+2*(8+32*p*q^3) := by nlinarith
  calc
    338*p^5 = 10*p^4*((338/10 : ℝ)*p) := by ring
    _ ≤ observableConstant p q := mul_le_mul_of_nonneg_left hi (by positivity)

/-- A sharper direct consequence of the existing proved projection bound.
The finite defect-type count is retained until its last numerical estimate. -/
theorem observable_poincare_sharp (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (hsig : HasSlotSignature f)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainVariance gs w f (observableProjection gs f H) ≤
      338*(gs.length:ℝ)^5*chainDirichlet gs w f H := by
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hm := finite_center_min (chainStates gs) (chainWeight gs w f)
    (observableProjection gs f H) (plainMean gs f H) hΛ
  have hb := projection_center_bound gs hgs hcover w hw f H hf hsig hlower hupper
  let n : ℝ := gs.length
  let D := restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅
  have hD : 0 ≤ D := restrictedEnergy_nonneg _ _ _ _ _ (by
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast List.length_pos_iff.mpr hne
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcard : ((defectTypes gs).card:ℝ) ≤ n^2 := by
    dsimp only [n]
    exact_mod_cast (show (defectTypes gs).card ≤ gs.length^2 by simpa [pow_two] using defectTypes_card_le gs)
  have hc : n*(1+8*n)+4*((defectTypes gs).card:ℝ)*(8+32*n) ≤ 169*n^3 := by
    have hn2 : n ≤ n^2 := by nlinarith
    have hn3 : n^2 ≤ n^3 := by nlinarith [mul_le_mul_of_nonneg_left hn2 hn0.le]
    have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 4*(8+32*n) by positivity)
    nlinarith
  have hbound := (hm.trans hb).trans (mul_le_mul_of_nonneg_right hc hD)
  change chainVariance gs w f (observableProjection gs f H) ≤ 338*n^5*(D/(2*n^2*chainTotal gs w f))
  unfold chainVariance chainMean
  apply (div_le_iff₀ hΛ).mpr
  have he : 338*n^5*(D/(2*n^2*chainTotal gs w f))*chainTotal gs w f = 169*n^3*D := by
    field_simp
    ; ring
  rw [he]
  exact hbound

lemma slotDefect_completion_mul (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps (fun S => completeDegree f k S * H S) A p r =
      slotDefect ps (fun S => f S * H S) A p r := by
  have heq : completeDegree (fun S => completeDegree f k S * H S) k =
      completeDegree (fun S => f S * H S) k := by
    funext S
    unfold completeDegree
    split_ifs with h
    · simp [h]
    · rfl
  rw [← slotDefect_completeDegree ps (fun S => completeDegree f k S * H S) k A hdegree hps p r hp hr hpr,
    heq, slotDefect_completeDegree ps (fun S => f S * H S) k A hdegree hps p r hp hr hpr]

lemma observableProjection_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (hgs : SlotsFresh gs ∅) (S : Set Γ) :
    observableProjection gs (completeDegree f gs.length) H S = observableProjection gs f H S := by
  by_cases he : ∃ p r, DefectState gs p r S
  · obtain ⟨p,r,hpr⟩ := he
    rw [observableProjection_defect gs _ H S hpr, observableProjection_defect gs f H S hpr]
    unfold defectMean
    rw [slotDefect_completion_mul gs f H gs.length ∅ (by simp) hgs p r hpr.1 hpr.2.1 hpr.2.2.1,
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hpr.1 hpr.2.1 hpr.2.2.1]
  · simp only [observableProjection, dite_eq_right he]

lemma chainTotal_completion (gs : List (Γ × Γ)) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : chainTotal gs w (completeDegree f gs.length) = chainTotal gs w f := by
  unfold chainTotal chainWeight
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [completeDegree, hd, ite_true]

lemma chainMean_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : chainMean gs w (completeDegree f gs.length) H = chainMean gs w f H := by
  unfold chainMean
  rw [chainTotal_completion gs f w hgs hcover]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [chainWeight, completeDegree, hd, ite_true]

lemma chainVariance_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) :
    chainVariance gs w (completeDegree f gs.length) H = chainVariance gs w f H := by
  unfold chainVariance
  rw [chainTotal_completion gs f w hgs hcover, chainMean_completion gs f H w hgs hcover]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [chainWeight, completeDegree, hd, ite_true]

lemma chainDirichlet_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) :
    chainDirichlet gs w (completeDegree f gs.length) H = chainDirichlet gs w f H := by
  unfold chainDirichlet
  rw [chainTotal_completion gs f w hgs hcover, restrictedEnergy_completeDegree gs f H w hgs hcover ∅ ∅]

/-- Observable Poincaré on the original valid-degree weights, with the exact
manuscript constant. Off-degree positivity is absent from its assumptions. -/
theorem validDegree_observable_poincare (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ)
    (hf : DegreePositive f gs.length) (hsig : AdditionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainVariance gs w f (observableProjection gs f H) ≤
      observableConstant gs.length q * chainDirichlet gs w f H := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  have hsF := completeDegree_hasSlotSignature f gs.length hf hsig
  have hlower' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs F ∅/(4*slotDefect gs F ∅ p r) ≤ w p r := by
    intro p hp r hr hpr
    dsimp [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hlower p hp r hr hpr
  have hupper' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs F ∅/slotDefect gs F ∅ p r := by
    intro p hp r hr hpr
    dsimp [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hupper p hp r hr hpr
  have ht := observable_poincare_sharp gs hgs hne hcover w hw F H hF hsF hlower' hupper'
  have hproj : observableProjection gs F H = observableProjection gs f H :=
    funext (observableProjection_completion gs f H hgs)
  rw [hproj, chainVariance_completion gs f _ w hgs hcover,
    chainDirichlet_completion gs f H w hgs hcover] at ht
  have hD : 0 ≤ chainDirichlet gs w f H := by
    rw [← chainDirichlet_completion gs f H w hgs hcover]
    unfold chainDirichlet
    apply div_nonneg
    · exact restrictedEnergy_nonneg _ _ _ _ _ (by
        intro ST _
        exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hF _).le)
          (mul_nonneg (chainMultiplier_pos gs w hw _).le (hF _).le))
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (chainTotal_pos gs hgs hcover w F hF hw).le
  exact ht.trans (mul_le_mul_of_nonneg_right
    (observableConstant_lower gs.length q (by exact_mod_cast List.length_pos_iff.mpr hne) hq) hD)

end ContingencyTables.ObservableBounds

end OAI
