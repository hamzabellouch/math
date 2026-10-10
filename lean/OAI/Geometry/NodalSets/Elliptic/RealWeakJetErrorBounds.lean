import OAI.Geometry.NodalSets.Elliptic.RealWeakJetProductBound

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

theorem real_weak_jet_error_H1_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (N : ℕ) (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hs : ds.length ≤ N)
    (i : Fin 4) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ psi : Jets.Coord → ℝ,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      let ts := realJetErrorTerms extra ds
      let V := realWeakJetProductSum A U ts
      let D := realWeakJetProductSum A U
        (ts.map (fun t ↦ (i::t.1,t.2)) ++ ts.map (fun t ↦ (t.1,i::t.2)))
      (MemLp V 2 (volume.restrict Q) ∧ (∫ x in Q, (V x)^2) ≤ C*E) ∧
      (MemLp D 2 (volume.restrict Q) ∧ (∫ x in Q, (D x)^2) ≤ C*E) ∧
      ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        IntegrableOn (fun x ↦ V x*coordPartial psi x i) Q ∧
        IntegrableOn (fun x ↦ D x*psi x) Q ∧
        (∫ x in Q, V x*coordPartial psi x i)=-(∫ x in Q, D x*psi x) := by
  let ts := realJetErrorTerms extra ds
  let ss := ts.map (fun t ↦ (i::t.1,t.2)) ++ ts.map (fun t ↦ (t.1,i::t.2))
  have hord (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ts) : t.2.length ≤ N :=
    ((realJetErrorTerms_orders extra ds he t ht).2).trans hs
  have hdord (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ss) : t.2.length ≤ N+1 := by
    simp only [ss,List.mem_append,List.mem_map] at ht
    rcases ht with ⟨s,hmem,rfl⟩ | ⟨s,hmem,rfl⟩
    · exact (hord s hmem).trans (Nat.le_succ N)
    · simpa only [List.length_cons] using Nat.succ_le_succ (hord s hmem)
  obtain ⟨B,hB,hb⟩ := real_weak_jet_product_bound hQ A hA ts
  obtain ⟨D,hD,hd⟩ := real_weak_jet_product_bound hQ A hA ss
  refine ⟨B+D,by positivity,fun U hU hweak E hE hUE ↦ ?_⟩
  dsimp only
  have hts (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ts) : t.2.length ≤ N+1 :=
    (hord t ht).trans (Nat.le_succ N)
  have hv := hb U (fun t ht ↦ hU _ (hts t ht)) E hE (fun t ht ↦ hUE _ (hts t ht))
  have hdv := hd U (fun t ht ↦ hU _ (hdord t ht)) E hE (fun t ht ↦ hUE _ (hdord t ht))
  have hw := real_weak_jet_product_derivative hQ A hA U ts i
    (fun t ht ↦ hU _ (hts t ht))
    (fun t ht ↦ hU _ (by simpa only [List.length_cons] using Nat.succ_le_succ (hord t ht)))
    (fun t ht ↦ hweak _ (hord t ht))
  exact ⟨⟨hv.1,hv.2.trans (mul_le_mul_of_nonneg_right (by linarith) hE)⟩,
    ⟨hdv.1,hdv.2.trans (mul_le_mul_of_nonneg_right (by linarith) hE)⟩,hw.2.2⟩

end
end Yau

end OAI
