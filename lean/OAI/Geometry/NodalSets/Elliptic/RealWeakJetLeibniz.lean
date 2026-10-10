import OAI.Geometry.NodalSets.Elliptic.RealWeakJetPairings
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetProducts

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

def realWeakJetExpansion (A : Jets.Coord → ℝ) (U : List (Fin 4) → Jets.Coord → ℝ)
    (extra ds : List (Fin 4)) (x : Jets.Coord) : ℝ :=
  A x*U (extra++ds) x+realWeakJetProductSum A U (realJetErrorTerms extra ds) x

lemma real_weak_jet_product_memLp {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4)))
    (hU : ∀ t ∈ ts, MemLp (U t.2) 2 (volume.restrict Q)) :
    MemLp (realWeakJetProductSum A U ts) 2 (volume.restrict Q) := by
  induction ts with
  | nil => exact MemLp.zero
  | cons t ts ih =>
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ _ (partialJet_smooth A hA t.1).continuous
    exact ((hb _ (hU t (by simp))).1).add (ih (fun s hs ↦ hU s (List.mem_cons_of_mem _ hs)))

lemma real_weak_jet_expansion_memLp {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length ≤ N) :
    MemLp (realWeakJetExpansion A U extra ds) 2 (volume.restrict Q) := by
  obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ A hA.continuous
  exact ((hb _ (hU _ (by simp only [List.length_append]; omega))).1).add
    (real_weak_jet_product_memLp hQ A hA U _ (fun t ht ↦ hU _
      (((realJetErrorTerms_orders extra ds he t ht).2.trans hd).trans (Nat.le_succ N))))

theorem real_weak_jet_expansion_derivative {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length < N) (i : Fin 4) :
    MemLp (realWeakJetExpansion A U extra ds) 2 (volume.restrict Q) ∧
    MemLp (realWeakJetExpansion A U extra (i::ds)) 2 (volume.restrict Q) ∧
    ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      IntegrableOn (fun x ↦ realWeakJetExpansion A U extra ds x*coordPartial psi x i) Q ∧
      IntegrableOn (fun x ↦ realWeakJetExpansion A U extra (i::ds) x*psi x) Q ∧
      (∫ x in Q, realWeakJetExpansion A U extra ds x*coordPartial psi x i) =
        -(∫ x in Q, realWeakJetExpansion A U extra (i::ds) x*psi x) := by
  have hord : (extra++ds).length ≤ N := by simp only [List.length_append]; omega
  have hnew : (extra++i::ds).length ≤ N+1 := by simp only [List.length_append,List.length_cons]; omega
  have hcanonical : ∀ psi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U (extra++ds) x*coordPartial psi x i) =
        -(∫ x in Q, U (extra++i::ds) x*psi x) := by
    intro psi hp hc hs
    rw [hweak _ hord i psi hp hc hs]
    congr 1
    exact real_weak_jet_pairing_perm U (N+1) (fun es hh ↦ hweak es (by omega))
      (by simp only [List.length_cons]; omega) List.perm_middle.symm psi hp hc hs
  have hm := real_interior_weak_product hQ (U (extra++ds)) (U (extra++i::ds)) A
    (hU _ (hord.trans (Nat.le_succ N))) (hU _ hnew) hA i hcanonical
  have ht := real_weak_jet_product_derivative hQ A hA U (realJetErrorTerms extra ds) i
    (fun t ht ↦ hU _ (by have h := (realJetErrorTerms_orders extra ds he t ht).2; omega))
    (fun t ht ↦ hU _ (by
      have h := (realJetErrorTerms_orders extra ds he t ht).2
      simp only [List.length_cons]; omega))
    (fun t ht ↦ hweak _ (by have h := (realJetErrorTerms_orders extra ds he t ht).2; omega) i)
  have ha := real_interior_weak_add hQ _ _ _ _ hm.1 ht.1 hm.2.1 ht.2.1 i
    (fun psi hp hc hs ↦ (hm.2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (ht.2.2 psi hp hc hs).2.2)
  have heq : (fun x ↦ A x*U (extra++i::ds) x+coordPartial A x i*U (extra++ds) x+
      realWeakJetProductSum A U ((realJetErrorTerms extra ds).map (fun t ↦ (i::t.1,t.2))++
        (realJetErrorTerms extra ds).map (fun t ↦ (t.1,i::t.2))) x) =
      realWeakJetExpansion A U extra (i::ds) := by
    funext x
    simp only [realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,List.map_append,
      List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,partialJet,coordPartial]
    ring
  rw [heq] at ha
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at ha
  exact ha

theorem real_weak_jet_leibniz_pairing {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length ≤ N)
    (psi : Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, realWeakJetExpansion A U extra ds x*psi x) =
      (-1:ℝ)^ds.length * (∫ x in Q, A x*U extra x*partialJet psi ds.reverse x) := by
  have h := real_weak_jet_test_reversal (realWeakJetExpansion A U extra) N
    (fun es hh i psi hp hc hs ↦
      ((real_weak_jet_expansion_derivative hQ A hA U N hU hweak extra es he hh i).2.2
        psi hp hc hs).2.2) ds hd psi hp hc hs
  simpa only [realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,List.append_nil,
    List.map_nil,List.sum_nil,add_zero] using h

end
end Yau

end OAI
