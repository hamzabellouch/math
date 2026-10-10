import OAI.Geometry.UnitDistances.Integration

namespace OAI

namespace PlanarUnitDistances.ActualScoreBook
open MeasureTheory FiniteLaw LevelSnapshot ActualSlots ScoreBook FiniteLawIntegral
  FiniteStarCoupling RareRows RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

abbrev ActualBook (V P Q H : Type) [Fintype V] [Fintype P] [Fintype Q] :=
  Book (Data V (P×Q)) P Q H (V → Bool)

def mass (S : Finset K) := (LevelScale.measure S).real Set.univ

def make (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) : ActualBook V P Q H where
  levels := compress (LevelScale.measure S) hm
    (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
    (measurable_snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
  graph := π
  bit := fun a p q => a.1 (p,q)
  point := fun a p => a.2 (x p)
  center := fun a q => a.2 (y q)
  history := h
  epsilon := ε
  good := good
  label := label

lemma average (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) (F : Data V (P×Q) → ℝ) :
    (∫a,F (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*avg (make S z w x y u π h ε good label hm).levels F := by
  have he := compress_avg (LevelScale.measure S) hm
    (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
    (measurable_snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u) F
  exact (mul_comm _ _).trans ((eq_div_iff hm.ne').mp he) |>.symm

lemma active_point (σ : Law (Data V (P×Q))) (π : Law (P×Q)) (x : P → V)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool)) :
    avg (left π) (fun p => avg σ (fun a => active ε π good label (x p) a))=
      event σ (fun a => PlaceScore.common ε (ActualSlots.frequency π a))+
      cut σ (fun a => ¬PlaceScore.common ε (ActualSlots.frequency π a) ∧ good a)
        (fun a => RareMoments.hp π (fun p q => a.1 (p,q)) (fun p => a.2 (x p)) (label a)) := by
  rw [avg_comm]
  unfold active
  simp_rw [avg_add,avg_const]
  congr 1
  apply avg_congr
  intro a
  by_cases hc : PlaceScore.common ε (ActualSlots.frequency π a)
  · simp [rareException,hc,ind,avg_const]
  · by_cases hg : good a
    · simp only [rareException,hc,hg,not_false_eq_true,true_and,ind,ite_true]
      rfl
    · simp [rareException,hc,hg,ind,avg_const]

lemma point_activity (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) :
    let B := make S z w x y u π h ε good label hm
    avg (left π) (fun p => ∫a,active ε π good label (x p)
      (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*(B.WC+B.HP) := by
  dsimp only
  simp_rw [average S z w x y u π h ε good label hm]
  rw [avg_smul,active_point]
  rfl

lemma active_center (σ : Law (Data V (P×Q))) (π : Law (P×Q)) (y : Q → V)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool)) :
    avg (right π) (fun q => avg σ (fun a => active ε π good label (y q) a))=
      event σ (fun a => PlaceScore.common ε (ActualSlots.frequency π a))+
      cut σ (fun a => ¬PlaceScore.common ε (ActualSlots.frequency π a) ∧ good a)
        (fun a => RareMoments.hq π (fun p q => a.1 (p,q)) (fun q => a.2 (y q)) (label a)) := by
  rw [avg_comm]
  unfold active
  simp_rw [avg_add,avg_const]
  congr 1
  apply avg_congr
  intro a
  by_cases hc : PlaceScore.common ε (ActualSlots.frequency π a)
  · simp [rareException,hc,ind,avg_const]
  · by_cases hg : good a
    · simp only [rareException,hc,hg,not_false_eq_true,true_and,ind,ite_true]
      rfl
    · simp [rareException,hc,hg,ind,avg_const]

lemma center_activity (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) :
    let B := make S z w x y u π h ε good label hm
    avg (right π) (fun q => ∫a,active ε π good label (y q)
      (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*(B.WC+B.HQ) := by
  dsimp only
  simp_rw [average S z w x y u π h ε good label hm]
  rw [avg_smul,active_center]
  rfl
end
end PlanarUnitDistances.ActualScoreBook

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
omit [Fintype Y] in
lemma fiber_average (μ : Law X) (φ : X → Y) (y : Y) (f : X → ℝ) :
    fiberMass μ φ y*avg (cond μ φ y) f=avg μ (fun x => if φ x=y then f x else 0) := by
  simp only [avg,mul_sum,←mul_assoc,cond_weight]
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp
lemma cut_average (μ : Law X) (c : X → Prop) (f : X → ℝ) :
    event μ c*avg (cond μ (fun x => decide (c x)) true) f=avg μ (fun x => if c x then f x else 0) := by
  simpa only [fiberMass,decide_eq_true_eq] using fiber_average μ (fun x => decide (c x)) true f
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.GraphPrediction
open Finset FiniteLaw FiniteStarCoupling CommonTemplate CrossPrediction CrossSampling StrictCross
open scoped Classical
noncomputable section
variable {P Q A B H D C : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype H] [Fintype D] [Fintype C] [Nonempty C]

lemma mixture_col (π : Law (P×Q)) : mixture (right π) (col π)=left π := by
  apply law_ext
  intro p
  simp only [mixture,avg,col_weight,FiniteStarCoupling.left_val]

omit [Fintype H] in
lemma prediction_eq (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B) :
    predictionError π h x y=1-predicted (right π) (col π) h x y := by
  unfold predicted
  rw [mixture_col,col_avg]
  unfold predictionError
  rw [avg_sub,avg_const]
  congr 1
  apply avg_congr
  intro pq
  simp only [crossMass,posteriorState,event,push_avg,Hashing.indicator]

omit [Fintype A] [Fintype B] in
lemma actual_error (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×B) (y : Q → A×B) :
    1-actual (right π) (col π) x y ≤
      event π (fun pq => ¬CrossStructure.Consistent (b pq.1 pq.2) (x pq.1) (y pq.2)) := by
  unfold actual
  rw [col_avg,←avg_const π 1,←avg_sub]
  apply avg_mono
  intro pq
  have hc (h : CrossStructure.Consistent (b pq.1 pq.2) (x pq.1) (y pq.2)) : Adj (x pq.1) (y pq.2) := by
    cases hb : b pq.1 pq.2
    · exact Or.inr (by simpa [hb,CrossStructure.Consistent] using h)
    · exact Or.inl (by simpa [hb,CrossStructure.Consistent] using h)
  dsimp [Hashing.indicator]
  by_cases h : CrossStructure.Consistent (b pq.1 pq.2) (x pq.1) (y pq.2)
  · simp [h,hc h]
  · simp only [h,not_false_eq_true,ite_true]
    split_ifs <;> norm_num

theorem exists_common_history (σ : Law D) (π : Law (P×Q)) (hμ : ∀p,0<(left π).val p)
    (c : D → Prop) (b : D → P → Q → Bool) (x : D → P → A×B) (y : D → Q → A×B)
    (K : ℕ) (hK : 0<K) :
    ∃ n<K,∃h : P → FiniteInformation.History (C×C) n,
      (univ.image h).card ≤ (Fintype.card C)^(2*K) ∧
      avg σ (fun s => if c s then predictionError π h (x s) (y s) else 0) ≤
        avg σ (fun s => if c s then event π (fun pq =>
          ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2)) else 0)+
        event σ c*(4/(Fintype.card C:ℝ)+18*(FiniteInformation.KL
          (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
          (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(K:ℝ))^(1/4:ℝ)) := by
  let ν := cond σ (fun s => decide (c s)) true
  obtain ⟨n,hn,h,hcard,hb⟩ := exists_cross_history (C := C) (right π) (col π)
    (by simpa only [mixture_col] using hμ) ν x y K hK
  rw [mixture_col] at hb
  refine ⟨n,hn,h,hcard,?_⟩
  have he := avg_mono ν (f := fun s => predictionError π h (x s) (y s))
    (g := fun s => event π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))+
      (actual (right π) (col π) (x s) (y s)-predicted (right π) (col π) h (x s) (y s))) (fun s => by
    have ha := actual_error π (b s) (x s) (y s)
    rw [prediction_eq π h (x s) (y s)]
    exact (show 1-predicted (right π) (col π) h (x s) (y s) ≤
      event π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))+
      (actual (right π) (col π) (x s) (y s)-predicted (right π) (col π) h (x s) (y s)) by linarith))
  rw [avg_add] at he
  have hh := mul_le_mul_of_nonneg_left (he.trans (add_le_add_right hb _)) (event_nonneg σ c)
  rw [mul_add] at hh
  simp only [ν,cut_average] at hh
  exact hh
end
end PlanarUnitDistances.GraphPrediction

namespace PlanarUnitDistances.LawStable
open Finset FiniteLaw StarScore FiniteStarCoupling LawExpansion
open scoped Classical
noncomputable section
variable {X P Q : Type*} [Fintype X] [Fintype P] [Fintype Q]

def majority (μ : Law X) (b : X → Bool) : Bool := !(LevelScores.minority (frequency μ b))
def minorityFrequency (μ : Law X) (b : X → Bool) : ℝ := min (frequency μ b) (1-frequency μ b)

lemma minority_le_half (μ : Law X) (b : X → Bool) : minorityFrequency μ b ≤ 1/2 := by
  unfold minorityFrequency
  have h₁ := min_le_left (frequency μ b) (1-frequency μ b)
  have h₂ := min_le_right (frequency μ b) (1-frequency μ b)
  linarith
lemma minority_event (μ : Law X) (b : X → Bool) (l : Bool) :
    minorityFrequency μ b ≤ event μ (fun x => b x≠l) := by
  have hf : event μ (fun x => b x≠true)=1-frequency μ b := by
    simpa only [frequency,ne_eq] using event_compl μ (fun x => b x=true)
  cases l
  · have he : event μ (fun x => b x≠false)=frequency μ b := by
      apply avg_congr
      intro x
      cases b x <;> simp
    rw [he]
    exact min_le_left _ _
  · rw [hf]
    exact min_le_right _ _
lemma majority_error (μ : Law X) (b : X → Bool) :
    event μ (fun x => b x≠majority μ b)=minorityFrequency μ b := by
  have he : event μ (fun x => b x≠majority μ b)=
      event μ (fun x => b x=LevelScores.minority (frequency μ b)) := by
    apply avg_congr
    intro x
    simp only [majority]
    have hb : ∀u v : Bool,u≠(!v) ↔ u=v := by decide
    simp only [hb]
    split_ifs <;> rfl
  rw [he]
  exact RareMass.minority_mass μ b
lemma majority_le_variation (μ : Law X) (b : X → Bool) :
    event μ (fun x => b x≠majority μ b) ≤ variation μ b := by
  rw [majority_error]
  unfold minorityFrequency variation
  have h₀ := frequency_nonneg μ b
  have h₁ := frequency_le_one μ b
  by_cases h : frequency μ b ≤ 1/2
  · rw [min_eq_left (by linarith)]
    nlinarith
  · rw [min_eq_right (by linarith)]
    nlinarith

theorem stable {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃ ξ₀ C : ℝ,0<ξ₀ ∧ 0<C ∧
    ∀ (P Q : Type) [Fintype P] [Fintype Q],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q) (b : P → Q → Bool),
    (∀p,γ*U.val p ≤ (left π).val p) →
    (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    minorityFrequency π (fun pq => b pq.1 pq.2) ≤ C*(VP π b+VQ π b) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hmatch⟩ := matching hγ hη
  refine ⟨ξ₀,max (C+1) (1/(2*s₀)),hξ,lt_of_lt_of_le (by linarith) (le_max_left _ _),?_⟩
  intro P Q _ _ π U W b hl hr ξ hξ0 hξb hexp
  let a := fun p => majority (row π p) (b p)
  let d := fun q => majority (col π q) (fun p => b p q)
  have hp : event π (fun pq => b pq.1 pq.2≠a pq.1) ≤ VP π b := by
    rw [←row_event π (fun p q => b p q≠a p)]
    exact avg_mono (left π) (fun p => majority_le_variation (row π p) (b p))
  have hq : event π (fun pq => b pq.1 pq.2≠d pq.2) ≤ VQ π b := by
    rw [←col_event π (fun p q => b p q≠d q)]
    exact avg_mono (right π) (fun q => majority_le_variation (col π q) (fun p => b p q))
  have hvp : 0 ≤ VP π b := avg_nonneg _ (fun p => variation_nonneg _ _)
  have hvq : 0 ≤ VQ π b := avg_nonneg _ (fun q => variation_nonneg _ _)
  have hm : event π (fun pq => a pq.1≠d pq.2) ≤ VP π b+VQ π b := by
    refine (event_mono π (fun pq h => show b pq.1 pq.2≠a pq.1 ∨ b pq.1 pq.2≠d pq.2 from ?_)).trans
      ((event_union_le π _ _).trans (add_le_add hp hq))
    by_contra! he
    exact h (he.1.symm.trans he.2)
  by_cases hv : VP π b+VQ π b ≤ s₀
  · obtain ⟨l,he⟩ := hmatch P Q Bool π U W a d hl hr ξ hξ0 hξb hexp (hm.trans hv)
    have hleft := event_nonneg (right π) (fun q => d q≠l)
    have he' : event π (fun pq => a pq.1≠l) ≤ C*(VP π b+VQ π b) := by
      have ha : event π (fun pq => a pq.1≠l)=event (left π) (fun p => a p≠l) :=
        (push_event π Prod.fst (fun p => a p≠l)).symm
      rw [ha]
      have hh := mul_le_mul_of_nonneg_left hm hC.le
      linarith
    have hevent : event π (fun pq => b pq.1 pq.2≠l) ≤ (C+1)*(VP π b+VQ π b) := by
      have hh := (event_mono π (fun pq (h : b pq.1 pq.2≠l) =>
        show b pq.1 pq.2≠a pq.1 ∨ a pq.1≠l from by
          by_contra! he; exact h (he.1.trans he.2))).trans (event_union_le π _ _)
      nlinarith
    exact (minority_event π (fun pq => b pq.1 pq.2) l).trans (hevent.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hvp hvq)))
  · have hs' : 0<2*s₀ := by linarith
    have hh : 1/2 ≤ (1/(2*s₀))*(VP π b+VQ π b) := by
      have he : (VP π b+VQ π b)/(2*s₀)= (1/(2*s₀))*(VP π b+VQ π b) := by ring
      rw [←he]
      apply (le_div_iff₀ hs').mpr
      linarith
    exact (minority_le_half π (fun pq => b pq.1 pq.2)).trans (hh.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hvp hvq)))
end
end PlanarUnitDistances.LawStable

namespace PlanarUnitDistances.SelectedBook
open FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook LevelBookkeeping
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C L : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧ 0<L ∧
    ∀(D P Q A T : Type) [Fintype D] [Fintype P] [Fintype Q] [Fintype A]
      [Nonempty A] [Fintype T] [Nonempty T],
    ∀(σ : Law D) (π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,0<(left π).val p) →
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0 ≤ ε → 0 ≤ τ → 0<d → ε+τ ≤ s₀ →
    ∀(b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A),
    ∀K : ℕ,0<K → ∃n<K,∃h : P → FiniteInformation.History (T×T) n,∃l : D → A×A,
      (Finset.univ.image h).card ≤ (Fintype.card T)^(2*K) ∧
      (∀s,minorityMass π (b s) ≤ L*(FiniteStarCoupling.VP π (b s)+FiniteStarCoupling.VQ π (b s))) ∧
      (∀s,goodRare ε τ π (b s) (x s) (y s) →
        hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s) ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
        minorityMass π (b s) ≤ hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+error π (b s) (x s) (y s) ∧
        joint π (b s) (x s) (y s) (l s) ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)) ∧
        wedge π (b s) (x s) (l s) ≤ (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π (b s) (x s) (l s)) ∧
      cut σ (fun s => PlaceScore.common ε (StarScore.frequency π (fun pq => b s pq.1 pq.2)))
        (fun s => CommonTemplate.predictionError π h (x s) (y s)) ≤
        avg σ (fun s => error π (b s) (x s) (y s))+
        event σ (fun s => PlaceScore.common ε (StarScore.frequency π (fun pq => b s pq.1 pq.2)))*
          (4/(Fintype.card T:ℝ)+18*(FiniteInformation.KL
            (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
            (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(K:ℝ))^(1/4:ℝ)) := by
  obtain ⟨s₀,ξ₁,C,hs,hξ₁,hC,hr⟩ := LevelBookkeeping.select hγ hη
  obtain ⟨ξ₂,L,hξ₂,hL,hstable⟩ := LawStable.stable hγ hη
  refine ⟨s₀,min ξ₁ ξ₂,C,L,hs,lt_min hξ₁ hξ₂,hC,hL,?_⟩
  intro D P Q A T _ _ _ _ _ _ _ σ π U W hμ hl hr' ξ hξ0 hξ hexp ε τ d hε hτ hd hsum b x y K hK
  obtain ⟨l,hl⟩ := hr D P Q A π U W hl hr' ξ hξ0 (hξ.trans (min_le_left _ _)) hexp ε τ d hε hτ hd hsum b x y
  obtain ⟨n,hn,h,hcard,hpred⟩ := GraphPrediction.exists_common_history (C := T) σ π hμ
    (fun s => PlaceScore.common ε (StarScore.frequency π (fun pq => b s pq.1 pq.2))) b x y K hK
  refine ⟨n,hn,h,l,hcard,?_,hl,?_⟩
  · intro s
    exact hstable P Q π U W (b s) ‹∀p,γ*U.val p ≤ (left π).val p› hr' ξ hξ0
      (hξ.trans (min_le_right _ _)) hexp
  · exact hpred.trans (add_le_add (cut_le_avg σ _ _ (fun s => event_nonneg π _)) le_rfl)
end
end PlanarUnitDistances.SelectedBook

namespace PlanarUnitDistances.PreparedSelection
open FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook LevelBookkeeping
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C L : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧ 0<L ∧
    ∀(D P Q A T : Type) [Fintype D] [Fintype P] [Fintype Q] [Fintype A]
      [Nonempty A] [Fintype T] [Nonempty T],
    ∀(σ : Law D) (π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,0<(left π).val p) →
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0<ε → 0<τ → 0<d → ε+τ ≤ s₀ →
    ∀(b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A),
    ∀K : ℕ,0<K → ∃n<K,∃h : P → FiniteInformation.History (T×T) n,∃l : D → A×A,
      let B : Book D P Q (FiniteInformation.History (T×T) n) A :=
        ⟨σ,π,b,x,y,h,ε,(fun s => error π (b s) (x s) (y s)≤τ),l⟩
      (Fintype.card (FiniteInformation.History (T×T) n)) ≤ (Fintype.card T)^(2*K) ∧
      (∀s,minorityMass π (b s) ≤ L*(VP π (b s)+VQ π (b s))) ∧
      (∀s,B.R s → minorityMass π (b s) ≤ hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+error π (b s) (x s) (y s)) ∧
      B.WC ≤ B.S/ε ∧ B.WB ≤ B.M/τ ∧ B.HP+B.HQ ≤ C*(B.S+B.M) ∧
      B.J ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(B.HP+B.HQ) ∧
      cut σ B.R (fun s => wedge π (b s) (x s) (l s)) ≤
        (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*B.HP ∧
      B.EP ≤ B.M+B.WC*(4/(Fintype.card T:ℝ)+18*(FiniteInformation.KL (FiniteInformation.wedge (right π).val (fun q => (col π q).val)) (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(K:ℝ))^(1/4:ℝ)) := by
  obtain ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,hh⟩ := SelectedBook.constants hγ hη
  refine ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,?_⟩
  intro D P Q A T _ _ _ _ _ _ _ σ π U W hμ hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum b x y K hK
  obtain ⟨n,hn,h,l,_,hst,hl',hpred⟩ := hh D P Q A T σ π U W hμ hl hr ξ hξ0 hξb hexp
    ε τ d hε.le hτ.le hd hsum b x y K hK
  let B : Book D P Q (FiniteInformation.History (T×T) n) A :=
    ⟨σ,π,b,x,y,h,ε,(fun s => error π (b s) (x s) (y s)≤τ),l⟩
  have hw := widths σ π b x y hε hτ
  have hm := moments σ π b x y l hC.le
    (fun s hs => ⟨(hl' s hs).1,(hl' s hs).2.2.1,(hl' s hs).2.2.2⟩)
  refine ⟨n,hn,h,l,?_,hst,?_,hw.1,?_,hm.1,hm.2.1,hm.2.2,hpred⟩
  · rw [FiniteInformation.history_card,Fintype.card_prod,←pow_two,←pow_mul]
    exact Nat.pow_le_pow_right (Fintype.card_pos) (Nat.mul_le_mul_left 2 hn.le)
  · intro s hs
    exact (hl' s hs).2.1
  · change event σ (fun s => ¬PlaceScore.common ε (event π (fun pq => b s pq.1 pq.2 = true)) ∧ ¬error π (b s) (x s) (y s)≤τ) ≤ (avg σ (fun s => error π (b s) (x s) (y s)))/τ
    simpa only [LevelBookkeeping.damaged,not_le] using hw.2
end
end PlanarUnitDistances.PreparedSelection

namespace PlanarUnitDistances.LevelStates
open MeasureTheory Set Real FiniteLaw PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

theorem exists_bounded_states_support (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (hu : ∀e,0<μ.val e → (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1) :
    ∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      (∫a,meanError μ S z w src tgt u a ∂LevelScale.measure S) ≤ 2*log 2+4 := by
  obtain ⟨u,hf,hb⟩ := exists_bounded_states (support μ) S z w
    (fun e => src e.val) (fun e => tgt e.val) (fun e => hu e.val e.property)
  refine ⟨u,hf,?_⟩
  convert hb using 1
  apply integral_congr_ae
  filter_upwards [] with a
  exact (support_avg μ (edgeError S z w src tgt u a)).symm
end
end PlanarUnitDistances.LevelStates

namespace PlanarUnitDistances.ActualPreparation
open MeasureTheory FiniteLaw LevelSnapshot ActualScoreBook ScoreBook
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

lemma scale_le_mass (π : Law (P×Q)) (S : Finset K) (d : P×Q → K) :
    LevelScale.scale π S d ≤ mass S := by
  calc
    _ ≤ ∫_a : PlaceLevels.Place K S×ℝ,(1:ℝ) ∂LevelScale.measure S :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun a => (LevelScale.minority_bounds π S d a).1))
        (integrable_const 1) (Filter.Eventually.of_forall (fun a => (LevelScale.minority_bounds π S d a).2))
    _ = _ := by simp [mass]

omit [Fintype V] in
lemma frequency (π : Law (P×Q)) (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : PlaceLevels.Place K S×ℝ) :
    RareLabels.minorityMass π (fun p q => (snapshot S z w (fun pq : P×Q => x pq.1)
      (fun pq : P×Q => y pq.2) u a).1 (p,q))=
    LevelScale.minority π S (fun pq => z (x pq.1)-z (y pq.2)) a := by
  unfold RareLabels.minorityMass LevelScale.minority
  apply congrArg (fun t : ℝ => min t (1-t))
  unfold LevelScale.prob ThresholdProfiles.frequency event avg
  apply Finset.sum_congr rfl
  intro e _
  apply congrArg (fun r : ℝ => π.val e*r)
  simp only [snapshot, LevelStates.bit, ThresholdProfiles.bit, LevelScale.cut, decide_eq_true_eq]
  rfl

omit [Fintype V] in
lemma inconsistency (π : Law (P×Q)) (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : PlaceLevels.Place K S×ℝ) :
    RareLabels.error π (fun p q => (snapshot S z w (fun pq : P×Q => x pq.1)
      (fun pq : P×Q => y pq.2) u a).1 (p,q))
      (fun p => (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a).2 (x p))
      (fun q => (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a).2 (y q))=
    LevelStates.meanError π S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a := by
  unfold RareLabels.error event LevelStates.meanError
  apply avg_congr
  intro pq
  simp only [snapshot,LevelStates.edgeError]
  split_ifs <;> simp_all

theorem states (π : Law (P×Q)) (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hS : 0<LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2))) :
    ∃hm : 0 < mass S, ∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      ∀(h : P → H) (ε : ℝ) (good : Data V (P×Q) → Prop)
        (label : Data V (P×Q) → (V → Bool)×(V → Bool)),
      let B := make S z w x y u π h ε good label hm
      mass S*B.S=LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2)) ∧
      mass S*B.M ≤ 2*Real.log 2+4 := by
  have hm := hS.trans_le (scale_le_mass π S _)
  obtain ⟨u,hf,hb⟩ := LevelStates.exists_bounded_states_support π S z w
    (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) (fun pq hh => hu pq.1 pq.2 hh)
  refine ⟨hm,u,hf,?_⟩
  intro h ε good label
  dsimp only
  have ha := average S z w x y u π h ε good label hm
  constructor
  · change mass S*avg (make S z w x y u π h ε good label hm).levels
        (fun s => RareLabels.minorityMass π (fun p q => s.1 (p,q)))=_
    rw [←ha (fun s => RareLabels.minorityMass π (fun p q => s.1 (p,q)))]
    exact integral_congr_ae (Filter.Eventually.of_forall (frequency π S z w x y u))
  · change mass S*avg (make S z w x y u π h ε good label hm).levels
        (fun s => RareLabels.error π (fun p q => s.1 (p,q)) (fun p => s.2 (x p)) (fun q => s.2 (y q)))≤_
    rw [←ha (fun s => RareLabels.error π (fun p q => s.1 (p,q))
      (fun p => s.2 (x p)) (fun q => s.2 (y q)))]
    simpa only [inconsistency] using hb
end
end PlanarUnitDistances.ActualPreparation

namespace PlanarUnitDistances.ActualPrepared
open MeasureTheory FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  LevelSnapshot ActualScoreBook LevelBookkeeping
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃s₀ ξ₀ C L : ℝ,0 < s₀ ∧ 0 < ξ₀ ∧ 0 < C ∧ 0 < L ∧
    ∀(K V P Q : Type) [Field K] [NumberField K] [Fintype V] [Fintype P] [Fintype Q],
    ∀(S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
      (π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p q,0 < π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1) →
    (∀p,0 < (left π).val p) →
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ε τ d : ℝ,0 < ε → 0 < τ → 0 < d → ε+τ ≤ s₀ →
    0 < LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2)) →
    ∀m N : ℕ,0 < m → 0 < N →
    ∃hm : 0 < mass S,∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
    ∃n < N,∃h : P → FiniteInformation.History (Fin m×Fin m) n,
    ∃l : Data V (P×Q) → (V → Bool)×(V → Bool),
      let good := fun a : Data V (P×Q) => error π (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) ≤ τ
      let B := make S z w x y u π h ε good l hm
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      mass S*B.S=LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2)) ∧
      mass S*B.M ≤ 2*Real.log 2+4 ∧
      Fintype.card (FiniteInformation.History (Fin m×Fin m) n) ≤ m^(2*N) ∧
      (∀a,minorityMass π (B.bit a) ≤ L*(VP π (B.bit a)+VQ π (B.bit a))) ∧
      (∀a,B.R a → minorityMass π (B.bit a) ≤ hp π (B.bit a) (B.point a) (l a)+
        hq π (B.bit a) (B.center a) (l a)+error π (B.bit a) (B.point a) (B.center a)) ∧
      B.WC ≤ B.S/ε ∧ B.WB ≤ B.M/τ ∧ B.HP+B.HQ ≤ C*(B.S+B.M) ∧
      B.J ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(B.HP+B.HQ) ∧
      cut B.levels B.R (fun a => wedge π (B.bit a) (B.point a) (l a)) ≤
        (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*B.HP ∧
      B.EP ≤ B.M+B.WC*(4/(m:ℝ)+18*(FiniteInformation.KL
        (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
          (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(N:ℝ))^(1/4:ℝ)) := by
  obtain ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,hsel⟩ := PreparedSelection.constants hγ hη
  refine ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,?_⟩
  intro K V P Q _ _ _ _ _ S z w x y π U W hu hp hU hW ξ hξ0 hξb hexp ε τ d hε hτ hd hsum hscale m N hm hN
  obtain ⟨hM,u,hfrac,hstate⟩ := ActualPreparation.states (H:=Unit) π S z w x y hu hscale
  let B₀ := make S z w x y u π (fun _ => ()) ε (fun _ => True) (fun _ => (fun _ => false,fun _ => false)) hM
  let : NeZero m := ⟨by omega⟩
  obtain ⟨n,hn,h,l,hcard,hstable,hrare,hWC,hWB,hH,hJ,hwed,hEP⟩ :=
    hsel (Data V (P×Q)) P Q (V → Bool) (Fin m) B₀.levels π U W hp hU hW
      ξ hξ0 hξb hexp ε τ d hε hτ hd hsum
      (fun a p q => a.1 (p,q)) (fun a p => a.2 (x p)) (fun a q => a.2 (y q)) N hN
  refine ⟨hM,u,n,hn,h,l,hfrac,?_,?_,?_,hstable,hrare,hWC,hWB,hH,hJ,hwed,?_⟩
  · exact (hstate (fun _ => ()) ε (fun _ => True) (fun _ => (fun _ => false,fun _ => false))).1
  · exact (hstate (fun _ => ()) ε (fun _ => True) (fun _ => (fun _ => false,fun _ => false))).2
  · simpa only [Fintype.card_fin] using hcard
  · simpa only [Fintype.card_fin, B₀, make] using hEP
end
end PlanarUnitDistances.ActualPrepared

end OAI
