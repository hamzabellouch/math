import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realWeakJetSuccessor (U : List (Fin 4) → Coord 4 → ℝ)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Coord 4 → ℝ) (N : ℕ) : List (Fin 4) → Coord 4 → ℝ
  | i::a::ds => if ds.length=N then H ds a i else U (i::a::ds)
  | es => U es

lemma realWeakJetSuccessor_lower (U : List (Fin 4) → Coord 4 → ℝ)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Coord 4 → ℝ) (N : ℕ)
    (es : List (Fin 4)) (hh : es.length ≤ N+1) : realWeakJetSuccessor U H N es=U es := by
  cases es with
  | nil => rfl
  | cons i es =>
    cases es with
    | nil => rfl
    | cons a ds =>
      have hne : ds.length ≠ N := by simp only [List.length_cons] at hh; omega
      simp only [realWeakJetSuccessor,ite_eq_right hne]

lemma realWeakJetSuccessor_top (U : List (Fin 4) → Coord 4 → ℝ)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Coord 4 → ℝ) (N : ℕ)
    (ds : List (Fin 4)) (hh : ds.length=N) (a i : Fin 4) :
    realWeakJetSuccessor U H N (i::a::ds)=H ds a i := by
  simp only [realWeakJetSuccessor,ite_eq_left hh]

theorem real_finite_weak_jet_extension {Q L : Set (Coord 4)} (hQ : IsCompact Q)
    (hL : MeasurableSet L) (hsub : Q ⊆ L) (N : ℕ)
    (U : List (Fin 4) → Coord 4 → ℝ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict L))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∫ x in L, U es x*coordPartial psi x i)=-(∫ x in L, U (i::es) x*psi x))
    (E K : ℝ) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hUE : ∀ es, es.length ≤ N+1 → (∫ x in L, (U es x)^2) ≤ E)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict Q))
    (hH : ∀ ds, ds.length=N → (∑ a, ∑ i, ‖H ds a i‖^2) ≤ K*E)
    (hpair : ∀ ds, ds.length=N → ∀ a i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U (a::ds) x*coordPartial psi x i)=-(∫ x in Q, H ds a i x*psi x)) :
    let V := realWeakJetSuccessor U (fun ds a i ↦ H ds a i) N
    (∀ es, es.length ≤ N+1 → V es=U es) ∧
    (∀ es, es.length ≤ N+2 → MemLp (V es) 2 (volume.restrict Q) ∧
      (∫ x in Q, (V es x)^2) ≤ (K+1)*E) ∧
    ∀ es, es.length ≤ N+1 → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      IntegrableOn (fun x ↦ V es x*coordPartial psi x i) Q ∧
      IntegrableOn (fun x ↦ V (i::es) x*psi x) Q ∧
      (∫ x in Q, V es x*coordPartial psi x i)=-(∫ x in Q, V (i::es) x*psi x) := by
  let V := realWeakJetSuccessor U (fun ds a i ↦ H ds a i) N
  have hlo := realWeakJetSuccessor_lower U (fun ds a i ↦ H ds a i) N
  have htop := realWeakJetSuccessor_top U (fun ds a i ↦ H ds a i) N
  have hsmall : E ≤ (K+1)*E := by nlinarith only [mul_nonneg hK hE]
  have hlarge : K*E ≤ (K+1)*E := by nlinarith only [hE]
  have hbound (es : List (Fin 4)) (he : es.length ≤ N+2) :
      MemLp (V es) 2 (volume.restrict Q) ∧ (∫ x in Q, (V es x)^2) ≤ (K+1)*E := by
    dsimp only [V]
    by_cases hle : es.length ≤ N+1
    · rw [hlo es hle]
      refine ⟨(hU es hle).mono_measure (Measure.restrict_mono hsub le_rfl),?_⟩
      have hm := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (U es x))) (hU es hle).integrable_sq
      exact hm.trans ((hUE es hle).trans hsmall)
    · cases es with
      | nil => simp at hle
      | cons i es =>
        cases es with
        | nil => simp at hle
        | cons a ds =>
          have hd : ds.length=N := by simp only [List.length_cons] at he hle; omega
          change MemLp (realWeakJetSuccessor U _ N (i::a::ds)) _ _ ∧ _
          rw [htop ds hd a i]
          have hb := real_Lp_restricted_square_le le_rfl (H ds a i)
          have h1 := Finset.single_le_sum (f := fun k ↦ ‖H ds a k‖^2)
            (fun k _ ↦ sq_nonneg _) (Finset.mem_univ i)
          have h2 := Finset.single_le_sum (f := fun b ↦ ∑ k, ‖H ds b k‖^2)
            (fun b _ ↦ Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)) (Finset.mem_univ a)
          exact ⟨hb.1,hb.2.trans (h1.trans (h2.trans ((hH ds hd).trans hlarge)))⟩
  refine ⟨hlo,hbound,?_⟩
  intro es he i psi hp hc hs
  have hes : (i::es).length ≤ N+2 := by simp only [List.length_cons]; omega
  refine ⟨((hbound es (by omega)).1).integrable_mul
      (real_continuous_memLp_compact hQ _ (real_coordPartial_smooth psi hp i).continuous),
    ((hbound (i::es) hes).1).integrable_mul (real_continuous_memLp_compact hQ psi hp.continuous),?_⟩
  by_cases hle : es.length ≤ N
  · rw [hlo es he,hlo (i::es) (by simp only [List.length_cons]; omega)]
    exact ((real_interior_weak_restrict hQ hL hsub (U es) (U (i::es)) (hU es he)
      (hU _ (by simp only [List.length_cons]; omega)) i (hweak es hle i)).2.2 psi hp hc hs).2.2
  · cases es with
    | nil => simp at hle
    | cons a ds =>
      have hd : ds.length=N := by simp only [List.length_cons] at he hle; omega
      change (∫ x in Q, realWeakJetSuccessor U _ N (a::ds) x*coordPartial psi x i)=
        -(∫ x in Q, realWeakJetSuccessor U _ N (i::a::ds) x*psi x)
      rw [hlo (a::ds) he,htop ds hd a i]
      exact hpair ds hd a i psi hp hc hs

end
end Yau

end OAI
