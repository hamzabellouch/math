import OAI.Geometry.NodalSets.Elliptic.RealWeakJetLeibniz

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

lemma partialJet_coordPartial_word {n : ℕ} (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin n)) (j : Fin n) :
    partialJet (fun x ↦ coordPartial f x j) ds = fun x ↦ coordPartial (partialJet f ds) x j := by
  change partialJet (partialJet f [j]) ds = partialJet f (j::ds)
  rw [← partialJet_append_word]
  exact partialJet_perm_word f hf (List.perm_append_singleton j ds)

theorem real_finite_weak_jet_equation {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (C : Jets.Coord → Fin 4 → Fin 4 → ℝ) (B : Jets.Coord → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (hB : ContDiff ℝ ∞ B)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∑ a, ∑ j, ∫ x in Q, C x a j*U [a] x*coordPartial psi x j) =
        ∫ x in Q, B x*U [] x*psi x)
    (ds : List (Fin 4)) (hd : ds.length ≤ N) :
    let F := fun x ↦ B x*U ds x+realWeakJetProductSum B U (realJetErrorTerms [] ds) x
    let G := fun j x ↦ ∑ a, realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds) x
    MemLp F 2 (volume.restrict Q) ∧ (∀ j, MemLp (G j) 2 (volume.restrict Q)) ∧
    ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∀ a j, IntegrableOn (fun x ↦ C x a j*U (a::ds) x*coordPartial psi x j) Q) ∧
      IntegrableOn (fun x ↦ F x*psi x) Q ∧
      (∀ j, IntegrableOn (fun x ↦ G j x*coordPartial psi x j) Q) ∧
      (∑ a, ∑ j, ∫ x in Q, C x a j*U (a::ds) x*coordPartial psi x j) =
        (∫ x in Q, F x*psi x)-∑ j, ∫ x in Q, G j x*coordPartial psi x j := by
  let err (a j : Fin 4) := realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds)
  have hm (a j : Fin 4) : MemLp (fun x ↦ C x a j*U (a::ds) x) 2 (volume.restrict Q) := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ _ (hC a j).continuous
    exact (hb _ (hU _ (by simp only [List.length_cons]; omega))).1
  have herr (a j : Fin 4) : MemLp (err a j) 2 (volume.restrict Q) :=
    real_weak_jet_product_memLp hQ _ (hC a j) U _ (fun t ht ↦ hU _ (by
      have ht' := (realJetErrorTerms_orders [a] ds (by simp) t ht).2; omega))
  have hg (j : Fin 4) : MemLp (fun x ↦ ∑ a, err a j x) 2 (volume.restrict Q) :=
    memLp_finsetSum _ (fun a _ ↦ herr a j)
  have hf := real_weak_jet_expansion_memLp hQ B hB U N hU [] ds (by simp) hd
  refine ⟨hf,hg,?_⟩
  intro psi hp hc hs
  have hdt (j : Fin 4) := real_continuous_memLp_compact hQ _ (real_coordPartial_smooth psi hp j).continuous
  have hi (a j : Fin 4) := (hm a j).integrable_mul (hdt j)
  have hei (a j : Fin 4) := (herr a j).integrable_mul (hdt j)
  refine ⟨hi,hf.integrable_mul (real_continuous_memLp_compact hQ psi hp.continuous),
    fun j ↦ (hg j).integrable_mul (hdt j),?_⟩
  have hflux (a j : Fin 4) := real_weak_jet_leibniz_pairing hQ (fun x ↦ C x a j) (hC a j)
    U N hU hweak [a] ds (by simp) hd (fun x ↦ coordPartial psi x j)
    (real_coordPartial_smooth psi hp j) (hc.fderiv_apply ℝ (Pi.single j 1))
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hs)
  have hscalar := real_weak_jet_leibniz_pairing hQ B hB U N hU hweak [] ds (by simp) hd psi hp hc hs
  have htotal : (∑ a, ∑ j, ∫ x in Q,
      realWeakJetExpansion (fun y ↦ C y a j) U [a] ds x*coordPartial psi x j) =
      ∫ x in Q, realWeakJetExpansion B U [] ds x*psi x := by
    simp_rw [hflux,partialJet_coordPartial_word psi hp]
    simp_rw [← Finset.mul_sum]
    rw [heq _ (partialJet_smooth psi hp ds.reverse) (partialJet_compactSupport psi hc ds.reverse)
      ((partialJet_tsupport_subset psi ds.reverse).trans hs)]
    exact hscalar.symm
  have hsplit (a j : Fin 4) : (∫ x in Q,
      realWeakJetExpansion (fun y ↦ C y a j) U [a] ds x*coordPartial psi x j) =
      (∫ x in Q, C x a j*U (a::ds) x*coordPartial psi x j)+
        ∫ x in Q, err a j x*coordPartial psi x j := by
    simp only [realWeakJetExpansion,List.cons_append,List.nil_append,add_mul]
    exact integral_add (hi a j) (hei a j)
  have hgsplit (j : Fin 4) : (∫ x in Q, (∑ a, err a j x)*coordPartial psi x j) =
      ∑ a, ∫ x in Q, err a j x*coordPartial psi x j := by
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun a _ ↦ hei a j)
  simp_rw [hsplit,Finset.sum_add_distrib] at htotal
  change _ = _ - ∑ j, ∫ x in Q, (∑ a, err a j x)*coordPartial psi x j
  simp_rw [hgsplit]
  rw [Finset.sum_comm (f := fun j a ↦ ∫ x in Q, err a j x*coordPartial psi x j)]
  exact eq_sub_iff_add_eq.mpr htotal

end
end Yau

end OAI
