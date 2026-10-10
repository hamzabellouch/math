import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetErrorBounds
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetLeibniz

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

def realWeakJetFluxError (C : Jets.Coord → Fin 4 → Fin 4 → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (ds : List (Fin 4)) (j : Fin 4) (x : Jets.Coord) : ℝ :=
  ∑ a, realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds) x

def realWeakJetFluxErrorDerivative (C : Jets.Coord → Fin 4 → Fin 4 → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (ds : List (Fin 4)) (j i : Fin 4) (x : Jets.Coord) : ℝ :=
  ∑ a, realWeakJetProductSum (fun y ↦ C y a j) U
    ((realJetErrorTerms [a] ds).map (fun t ↦ (i::t.1,t.2)) ++
      (realJetErrorTerms [a] ds).map (fun t ↦ (t.1,i::t.2))) x

theorem real_weak_jet_expansion_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (N : ℕ) (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length ≤ N) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      MemLp (realWeakJetExpansion A U extra ds) 2 (volume.restrict Q) ∧
      (∫ x in Q, (realWeakJetExpansion A U extra ds x)^2) ≤ C*E := by
  let ts := ([],extra++ds)::realJetErrorTerms extra ds
  have hord (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ts) : t.2.length ≤ N+1 := by
    rcases List.mem_cons.mp ht with rfl | ht
    · simp only [List.length_append]; omega
    · have h := (realJetErrorTerms_orders extra ds he t ht).2; omega
  obtain ⟨C,hC,hb⟩ := real_weak_jet_product_bound hQ A hA ts
  refine ⟨C,hC,fun U hU E hE hUE ↦ ?_⟩
  exact hb U (fun t ht ↦ hU _ (hord t ht)) E hE (fun t ht ↦ hUE _ (hord t ht))

theorem real_weak_jet_forcing_H1_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (C : Jets.Coord → Fin 4 → Fin 4 → ℝ) (B : Jets.Coord → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (hB : ContDiff ℝ ∞ B)
    (N : ℕ) (ds : List (Fin 4)) (hd : ds.length ≤ N) :
    ∃ K > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      (MemLp (realWeakJetExpansion B U [] ds) 2 (volume.restrict Q) ∧
        (∫ x in Q, (realWeakJetExpansion B U [] ds x)^2) ≤ K*E) ∧
      ∀ j i,
        (MemLp (realWeakJetFluxError C U ds j) 2 (volume.restrict Q) ∧
          (∫ x in Q, (realWeakJetFluxError C U ds j x)^2) ≤ K*E) ∧
        (MemLp (realWeakJetFluxErrorDerivative C U ds j i) 2 (volume.restrict Q) ∧
          (∫ x in Q, (realWeakJetFluxErrorDerivative C U ds j i x)^2) ≤ K*E) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          IntegrableOn (fun x ↦ realWeakJetFluxError C U ds j x*coordPartial psi x i) Q ∧
          IntegrableOn (fun x ↦ realWeakJetFluxErrorDerivative C U ds j i x*psi x) Q ∧
          (∫ x in Q, realWeakJetFluxError C U ds j x*coordPartial psi x i) =
            -(∫ x in Q, realWeakJetFluxErrorDerivative C U ds j i x*psi x) := by
  obtain ⟨S,hS,hs⟩ := real_weak_jet_expansion_bound hQ B hB N [] ds (by simp) hd
  have hex (a j i : Fin 4) := real_weak_jet_error_H1_bound hQ (fun x ↦ C x a j) (hC a j)
    N [a] ds (by simp) hd i
  choose T hT ht using hex
  obtain ⟨M,hM,hm⟩ := real_finite_positive_majorant (fun t : Fin 4 × Fin 4 × Fin 4 ↦ T t.1 t.2.1 t.2.2)
  obtain ⟨D,hD,hdb⟩ := real_compact_fintype_coefficient_common_bound hQ
    (fun (_ : Jets.Coord) (_ : Fin 4) ↦ (1:ℝ)) (fun _ ↦ continuous_const)
  refine ⟨S+D*M,by positivity,fun U hU hw E hE hUE ↦ ?_⟩
  have hscalar := hs U hU E hE hUE
  refine ⟨⟨hscalar.1,hscalar.2.trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [mul_pos hD hM]) hE)⟩,?_⟩
  intro j i
  have hall (a : Fin 4) := ht a j i U hU (fun es he ↦ hw es he i) E hE hUE
  have hsum := real_interior_weak_sum hQ _ _ (fun a ↦ (hall a).1.1)
    (fun a ↦ (hall a).2.1.1) i (fun a psi hp hc hs ↦ ((hall a).2.2 psi hp hc hs).2.2)
  have hb1 := hdb (fun a ↦ realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds))
    (fun a ↦ (hall a).1.1) (M*E) (mul_nonneg hM.le hE)
    (fun a ↦ ((hall a).1.2).trans (mul_le_mul_of_nonneg_right (hm ⟨a,j,i⟩) hE))
  have hb2 := hdb (fun a ↦ realWeakJetProductSum (fun y ↦ C y a j) U
      ((realJetErrorTerms [a] ds).map (fun t ↦ (i::t.1,t.2)) ++
        (realJetErrorTerms [a] ds).map (fun t ↦ (t.1,i::t.2))))
    (fun a ↦ (hall a).2.1.1) (M*E) (mul_nonneg hM.le hE)
    (fun a ↦ ((hall a).2.1.2).trans (mul_le_mul_of_nonneg_right (hm ⟨a,j,i⟩) hE))
  simp only [one_mul] at hb1 hb2
  have hbound : D*(M*E) ≤ (S+D*M)*E := by nlinarith only [mul_nonneg hS.le hE]
  exact ⟨⟨hsum.1,hb1.2.trans hbound⟩,⟨hsum.2.1,hb2.2.trans hbound⟩,hsum.2.2⟩

end
end Yau

end OAI
