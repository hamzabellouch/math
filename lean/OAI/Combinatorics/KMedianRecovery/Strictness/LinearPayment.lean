import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestDistance

namespace OAI

namespace MetricKMedianRecovery.OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

noncomputable def linearPayment (loc : D → X) (t v z : ℝ) (W : Finset X) (i : X)
    (tau : D → ℝ) : ℝ := by
  classical
  exact ∑ j, if activeAt loc t z W j then
    if dist i (loc j) ≤ v*z then tau j-t*dist i (loc j)
    else max (z-t*dist i (loc j)) 0
    else max (t*nearestDistance (loc j) W-t*dist i (loc j)) 0

lemma near_bid_nonnegative (v z d tau : ℝ) (hv : 0 < v) (hv1 : v < 1/6)
    (hz : 0 ≤ z) (hd : 0 ≤ d) (hnear : d ≤ v*z) (htau : z ≤ tau) :
    0 ≤ tau-(1-3*v)*d := by
  have ht : 0 ≤ 1-3*v := by linarith
  have ht1 : 1-3*v ≤ 1 := by linarith
  have hd1 : d ≤ z := hnear.trans (by nlinarith)
  have hm : (1-3*v)*d ≤ d := by nlinarith
  linarith

lemma payment_eq_linear (loc : D → X) (W : Finset X) (v z : ℝ) (i : X) (tau : D → ℝ)
    (hv : 0 < v) (hv1 : v < 1/6) (hz : 0 ≤ z)
    (hb : admissibleBids loc (1-3*v) (1+v^2) v z W i tau) :
    openingPayment loc (1-3*v) z W i tau = linearPayment loc (1-3*v) v z W i tau := by
  classical
  unfold openingPayment linearPayment
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : activeAt loc (1-3*v) z W j
  · simp only [ite_eq_left ha]
    by_cases hn : dist i (loc j) ≤ v*z
    · rw [ite_eq_left hn,max_eq_left (near_bid_nonnegative v z _ _ hv hv1 hz dist_nonneg hn (hb j ha).1)]
    · rw [ite_eq_right hn,(hb j ha).2.2.2 (lt_of_not_ge hn)]
  · simp only [ite_eq_right ha]

noncomputable def dualTerm (loc : D → X) (t z : ℝ) (W : Finset X) (i₀ : X)
    (tau : D → ℝ) (a j : D) : ℝ := by
  classical
  exact if activeAt loc t z W j then tau j-dist i₀ (loc j)
    else tau a-2*dist i₀ (loc j)-dist i₀ (loc a)

lemma dual_eq (loc : D → X) (t z : ℝ) (W : Finset X) (i₀ : X) (tau : D → ℝ) (a : D) :
    openingDual loc t z W i₀ tau a = ∑ j, max (dualTerm loc t z W i₀ tau a j) 0 := by
  classical
  unfold openingDual dualTerm
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

noncomputable def Feasible (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (tau : D → ℝ) (y : F → D → D → ℝ) : Prop :=
  admissibleBids loc (1-3*v) (1+v^2) v z W i tau ∧
  lam-(Fintype.card D:ℝ)*eta ≤ linearPayment loc (1-3*v) v z W i tau ∧
  (∀ f : F, ∀ a, activeAt loc (1-3*v) z W a →
    (∀ j, 0 ≤ y f a j ∧ dualTerm loc (1-3*v) z W f tau a j ≤ y f a j) ∧
    ∑ j, y f a j ≤ lam)

theorem openable_iff_linear_feasible (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (hv : 0 < v) (hv1 : v < 1/6) (hz : 0 ≤ z) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i ↔
      ∃ tau : D → ℝ, ∃ y : F → D → D → ℝ, Feasible loc F W v z lam eta i tau y := by
  classical
  constructor
  · rintro ⟨tau,hb,hp,hd⟩
    refine ⟨tau,(fun f a j => max (dualTerm loc (1-3*v) z W f tau a j) 0),hb,?_,?_⟩
    · rwa [←payment_eq_linear loc W v z i tau hv hv1 hz hb]
    · intro f a ha
      refine ⟨fun j => ⟨le_max_right _ _,le_max_left _ _⟩,?_⟩
      rw [←dual_eq]
      exact hd f f.property a ha
  · rintro ⟨tau,y,hb,hp,hd⟩
    refine ⟨tau,hb,?_,?_⟩
    · rwa [payment_eq_linear loc W v z i tau hv hv1 hz hb]
    · intro f hf a ha
      rw [dual_eq]
      have hy := hd ⟨f,hf⟩ a ha
      exact (Finset.sum_le_sum (fun j _ => max_le (hy.1 j).2 (hy.1 j).1)).trans hy.2

omit [PseudoMetricSpace X] in

lemma variable_count (F : Finset X) :
    Fintype.card (D ⊕ (F × D × D)) = Fintype.card D + F.card*(Fintype.card D)^2 := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,pow_two]

end MetricKMedianRecovery.OpenabilityLinearization

end OAI
