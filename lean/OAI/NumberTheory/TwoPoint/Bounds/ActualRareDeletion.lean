import OAI.NumberTheory.TwoPoint.Walks.ProhibitedRowComparison
import OAI.NumberTheory.TwoPoint.Bounds.PrimePairCatalog

namespace OAI

/-! The prohibited-site part of the deletion estimate. The rare-event
cost is controlled after summing the actual positive tuple/padding row;
only the finite-interval comparison error pays for individual pairs. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma padding_pair_count_le (D : Finset ℕ) (padding : ℕ → Finset ℕ)
    (pairs : Finset (ℕ × ℕ))
    (hp : ∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ pairs) :
    (∑ d ∈ D, (padding d).card) ≤ pairs.card := by
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun z : (d : ℕ) × ℕ => (z.1, z.2))
  · intro z hz
    obtain ⟨hd, hq⟩ := mem_sigma.mp hz
    exact hp z.1 hd z.2 hq
  · intro x _ y _ hxy
    exact Sigma.ext (congrArg Prod.fst hxy) (by simpa using congrArg Prod.snd hxy)

theorem ModFiveThetaInput.eventually_prohibited_model_row (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B s : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      ∀ (A : ℝ), 0 ≤ A → A ≤ Real.exp (C * Real.log L) → ∀ site : ℤ,
      A * (data.residueLaw B hB).average (fun x =>
        prohibitedPositiveRow data s D padding (data.residueOrigin x + site)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [hP.eventually_actual_rare_row E W C hW hC,
    eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h M B s data hp hq hB hprob D hD padding hpadding A hA hAcap site
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  let bad := fun x : ↥(data.P ∪ data.Q) → Fin B =>
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)
  have hpbad : (data.residueLaw B hB).probability bad ≤
      Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
    rw [data.prohibited_probability_translate hB s site]
    exact hprob
  have hrow (x : ↥(data.P ∪ data.Q) → Fin B) :
      prohibitedPositiveRow data s D padding (data.residueOrigin x + site) ≤
        primeRowMajorant P data.Q (data.residueOrigin x + site) * if bad x then 1 else 0 := by
    apply prohibitedPositiveRow_le data s P (centeredPrimeBands_prime E _ W _)
      (centeredPrimeBands_disjoint E _ W _ (Real.rpow_nonneg (by linarith) _) (by linarith))
      D hD padding hpadding
  exact (mul_le_mul_of_nonneg_left ((data.residueLaw B hB).average_mono hrow) hA).trans
    (hb h M B data hp hq hB site bad hpbad A hA hAcap)

theorem BravermanDepth22Input.eventually_actual_prohibited_deletion
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h M B s cap : ℕ) (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      (primeSupplyCount W L : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      (∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ data.pairs) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        prohibitedPositiveRow data s D padding ((a + x.val : ℤ) + site)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) +
            T * data.pairs.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hc⟩ := hBr.eventually_prohibited_row_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hc, hP.eventually_prohibited_model_row E W C hW hC,
    eventually_ge_atTop (1 : ℝ)] with L hc hm hL
  intro h M B s cap data hp hq hB hpool hBL hs hcap hpair hdegree hprob hJ D hD
    padding hpadding hqdegree hpairs T hT hTcap site a N hN
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  have hprime := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  have hdisj := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
    (Real.rpow_nonneg (by linarith) _) (by linarith : 0 ≤ W)
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisj (hD hd)
  have hsupport (d : ℕ) (hmem : d ∈ D) : d.primeFactors ⊆ data.P ∪ data.Q := by
    apply (hd d hmem).2.2.trans
    rw [hp]
    exact subset_union_left
  have hcard (d : ℕ) (hmem : d ∈ D) : (d.primeFactors.card : ℝ) ≤ L ^ 2 := by
    rw [(hd d hmem).2.1]
    exact hJ
  have hcompare := hc h (primeSupplyCount W L) M B s cap data hB hpool hBL hs hcap
    hpair hdegree D hsupport hcard padding hpadding hqdegree site a N hN
  have hmodel := hm h M B s data hp hq hB hprob D hD padding hpadding T hT hTcap site
  have hcount : ((∑ d ∈ D, (padding d).card : ℕ) : ℝ) ≤ data.pairs.card := by
    exact_mod_cast padding_pair_count_le D padding data.pairs hpairs
  have hdiff := (le_abs_self _).trans hcompare
  have hdiffT := mul_le_mul_of_nonneg_left hdiff hT
  have hcountT := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcount (Real.exp_pos (-(L ^ 9))).le) hT
  nlinarith

end TwoPointCorrelations

end OAI
