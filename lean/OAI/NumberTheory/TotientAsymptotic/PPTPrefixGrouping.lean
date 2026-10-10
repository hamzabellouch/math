import OAI.NumberTheory.TotientAsymptotic.PPTMaximalSuffix
import OAI.NumberTheory.TotientAsymptotic.PPTBadWitness

namespace OAI

/-!
Finite maximal-prefix grouping in the full-fiber sieve.  The injective
choice is made on each residual family, after the maximal-prefix
argument has proved the largest-prime mismatch for every nontrivial
residual preimage.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptPrefixProduct (p : ℕ → ℕ) (j : ℕ) : ℕ := ∏ i ∈ Finset.Ico 0 j, p i

lemma ppt_prefix_suffix_product (p : ℕ → ℕ) {N j : ℕ} (hj : j ≤ N) :
    pptSuffixProduct p N 0 = pptPrefixProduct p j*pptSuffixProduct p N j := by
  exact (Finset.prod_Ico_consecutive p (Nat.zero_le j) hj).symm

lemma ppt_suffix_largest_prime {p : ℕ → ℕ} {N j : ℕ} (hj : j < N)
    (hprime : ∀ i < N, (p i).Prime)
    (horder : ∀ i k : ℕ, i < k → k < N → p k < p i) :
    largestPrimeFactor (pptSuffixProduct p N j) = p j := by
  have hpos := ppt_suffix_product_pos (j := j) hprime
  have hdiv : p j ∣ pptSuffixProduct p N j :=
    Finset.dvd_prod_of_mem p (Finset.mem_Ico.mpr ⟨le_rfl, hj⟩)
  have hp := hprime j hj
  have hmem : p j ∈ (pptSuffixProduct p N j).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdiv, hpos.ne'⟩
  apply le_antisymm
  · unfold largestPrimeFactor
    apply max_le hp.one_lt.le
    apply Finset.sup_le
    intro q hq
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqdvd := Nat.dvd_of_mem_primeFactors hq
    obtain ⟨i, hi, hqi⟩ := (hqprime.prime.dvd_finsetProd_iff p).mp hqdvd
    have hi' := Finset.mem_Ico.mp hi
    have hqi' := (Nat.prime_dvd_prime_iff_eq hqprime (hprime i hi'.2)).mp hqi
    rcases hi'.1.eq_or_lt with he | he
    · simpa only [← he, hqi', id_eq] using (le_refl (p j))
    · exact hqi' ▸ (horder j i he hi'.2).le
  · exact (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)

/-- The elementary residual facts supplied by maximal-prefix selection.
This is an internal grouping invariant, not a published-input assumption. -/
def PPTBadResidual (d r : ℕ) : Prop :=
  0 < r ∧
  (∀ p : ℕ, p.Prime → p ∣ r → d+1 < p) ∧
  (∃ u : ℕ, 0 < u ∧ u.totient = d*r.totient ∧ ¬r ∣ u) ∧
  ∀ u : ℕ, 0 < u → u.totient = d*r.totient → ¬r ∣ u →
    largestPrimeFactor u ≠ largestPrimeFactor r

/-- Each failed rough prime product has a maximal prefix.  All nontrivial
preimages of its residual have a different largest prime. -/
theorem ppt_maximal_prefix_grouping {d N : ℕ} (hd : 0 < d)
    (S : Finset ℕ) (p : ℕ → ℕ → ℕ)
    (hrep : ∀ n ∈ S, n = pptSuffixProduct (p n) N 0)
    (hprime : ∀ n ∈ S, ∀ i < N, (p n i).Prime)
    (horder : ∀ n ∈ S, ∀ i k : ℕ, i < k → k < N → p n k < p n i)
    (hlarge : ∀ n ∈ S, ∀ i < N, d+1 < p n i)
    (hbad : ∀ n ∈ S, ¬FullFiber d n) :
    ∃ j : ℕ → ℕ, ∀ n ∈ S,
      j n < N ∧ 0 < pptPrefixProduct (p n) (j n) ∧
      n = pptPrefixProduct (p n) (j n)*pptSuffixProduct (p n) N (j n) ∧
      PPTBadResidual d (pptSuffixProduct (p n) N (j n)) := by
  classical
  have hex (n : ℕ) : ∃ j : ℕ, n ∈ S →
      j < N ∧ 0 < pptPrefixProduct (p n) j ∧
      n = pptPrefixProduct (p n) j*pptSuffixProduct (p n) N j ∧
      PPTBadResidual d (pptSuffixProduct (p n) N j) := by
    by_cases hn : n ∈ S
    · have hnpos : 0 < n := by rw [hrep n hn]; exact ppt_suffix_product_pos (hprime n hn)
      have hrough : ∀ q : ℕ, q.Prime → q ∣ n → d+1 < q := by
        rw [hrep n hn]
        exact primeProduct_rough (Finset.Ico 0 N) (p n) d
          (fun i hi => hprime n hn i (Finset.mem_Ico.mp hi).2)
          (fun i hi => hlarge n hn i (Finset.mem_Ico.mp hi).2)
      have hnot : ¬ ∀ u : ℕ, 0 < u → u.totient = d*n.totient → n ∣ u := by
        intro hall
        exact hbad n hn ((fullFiber_iff_all_preimages_dvd hd hnpos hrough).mpr hall)
      push Not at hnot
      have hnot' : ∃ u : ℕ, 0 < u ∧
          u.totient = d*(pptSuffixProduct (p n) N 0).totient ∧
          ¬pptSuffixProduct (p n) N 0 ∣ u := by
        simpa only [← hrep n hn] using hnot
      obtain ⟨j, hj, hwitness, hmismatch⟩ := ppt_maximal_prefix_mismatch hd (p n)
        (hprime n hn) (horder n hn) (fun i hi => by have := hlarge n hn i hi; omega) hnot'
      refine ⟨j, fun _ => ⟨hj, ?_, ?_, ?_⟩⟩
      · apply Finset.prod_pos
        intro i hi
        exact (hprime n hn i ((Finset.mem_Ico.mp hi).2.trans hj)).pos
      · exact (hrep n hn).trans (ppt_prefix_suffix_product (p n) hj.le)
      · refine ⟨ppt_suffix_product_pos (hprime n hn), ?_, ?_, ?_⟩
        · exact primeProduct_rough (Finset.Ico j N) (p n) d
            (fun i hi => hprime n hn i (Finset.mem_Ico.mp hi).2)
            (fun i hi => hlarge n hn i (Finset.mem_Ico.mp hi).2)
        · obtain ⟨u, hu, hφ, hnotu, _⟩ := hwitness
          exact ⟨u, hu, hφ, hnotu⟩
        · intro u hu hφ hnotu
          simpa only [ppt_suffix_largest_prime hj (hprime n hn) (horder n hn)] using
            hmismatch u hu hφ hnotu
    · exact ⟨0, fun h => False.elim (hn h)⟩
  choose j hj using hex
  exact ⟨j, hj⟩

def pptPrefixCell (S : Finset ℕ) (j pref : ℕ → ℕ) (J c : ℕ) : Finset ℕ :=
  S.filter (fun n => j n = J ∧ pref n = c)

/-- Fixing the removed prefix makes the residual map injective. -/
lemma ppt_prefix_cell_residual_injective (S : Finset ℕ) (j pref residual : ℕ → ℕ)
    (hfactor : ∀ n ∈ S, n = pref n*residual n) (J c : ℕ) :
    Set.InjOn residual (pptPrefixCell S j pref J c : Set ℕ) := by
  intro n hn m hm he
  have hn' := Finset.mem_filter.mp hn
  have hm' := Finset.mem_filter.mp hm
  rw [hfactor n hn'.1, hfactor m hm'.1, hn'.2.2, hm'.2.2, he]

lemma ppt_prefix_cell_residual_card (S : Finset ℕ) (j pref residual : ℕ → ℕ)
    (hfactor : ∀ n ∈ S, n = pref n*residual n) (J c : ℕ) :
    ((pptPrefixCell S j pref J c).image residual).card =
      (pptPrefixCell S j pref J c).card :=
  Finset.card_image_of_injOn (ppt_prefix_cell_residual_injective S j pref residual hfactor J c)

/-- Apply the injective bad-witness choice only after the residual family
is fixed.  The largest-prime mismatch and the nonsingleton seed branch
are both retained. -/
theorem ppt_prefix_cell_bad_witness {d q : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient = d)
    (S : Finset ℕ) (j pref residual : ℕ → ℕ)
    (hbad : ∀ n ∈ S, PPTBadResidual d (residual n)) (J c : ℕ) :
    let R := (pptPrefixCell S j pref J c).image residual
    ∃ F : ℕ → ℕ, Set.InjOn F (R : Set ℕ) ∧
      (∀ r ∈ R, 0 < F r ∧ (F r).totient = d*r.totient ∧ ¬r ∣ F r ∧
        largestPrimeFactor (F r) ≠ largestPrimeFactor r) ∧
      ∀ r ∈ R, (∃ s ∈ R, s ≠ r ∧ s.totient = r.totient) →
        ∃ s ∈ R, F r = s*q := by
  classical
  dsimp only
  let R := (pptPrefixCell S j pref J c).image residual
  have hR (r : ℕ) (hr : r ∈ R) : PPTBadResidual d r := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    exact hbad n (Finset.mem_filter.mp hn).1
  obtain ⟨F, hFinj, hF, hseed⟩ := ppt_injective_bad_preimages_seed_branch hd hqpos hq R
    (fun r hr => ⟨(hR r hr).1, (hR r hr).2.1⟩)
    (fun r hr => (hR r hr).2.2.1)
  refine ⟨F, hFinj, ?_, hseed⟩
  intro r hr
  have hf := hF r hr
  exact ⟨hf.1, hf.2.1, hf.2.2, (hR r hr).2.2.2 (F r) hf.1 hf.2.1 hf.2.2⟩

/-- The actual chosen prefix index and prefix product cover the original
family by finitely many residual cells. -/
lemma ppt_prefix_cells_cover (S : Finset ℕ) (j pref : ℕ → ℕ) (N : ℕ)
    (hindex : ∀ n ∈ S, j n < N) :
    S ⊆ (Finset.range N).biUnion (fun J =>
      (S.image pref).biUnion (fun c => pptPrefixCell S j pref J c)) := by
  classical
  intro n hn
  apply Finset.mem_biUnion.mpr
  refine ⟨j n, Finset.mem_range.mpr (hindex n hn), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨pref n, Finset.mem_image.mpr ⟨n, hn, rfl⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨hn, rfl, rfl⟩

/-- Counting the original failed candidates reduces to counting the
distinct residuals in each fixed-prefix cell. -/
lemma ppt_prefix_group_count_le (S : Finset ℕ) (j pref residual : ℕ → ℕ) (N : ℕ)
    (hindex : ∀ n ∈ S, j n < N)
    (hfactor : ∀ n ∈ S, n = pref n*residual n) :
    (S.card : ℝ) ≤ ∑ J ∈ Finset.range N, ∑ c ∈ S.image pref,
      (((pptPrefixCell S j pref J c).image residual).card : ℝ) := by
  classical
  simp_rw [ppt_prefix_cell_residual_card S j pref residual hfactor]
  have hnat : S.card ≤ ∑ J ∈ Finset.range N, ∑ c ∈ S.image pref,
      (pptPrefixCell S j pref J c).card := by
    apply (Finset.card_le_card (ppt_prefix_cells_cover S j pref N hindex)).trans
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun J _ => Finset.card_biUnion_le)
  exact_mod_cast hnat

/-- Only prefixes selected at index `J` enter its reciprocal mass. -/
def pptPrefixesAt (S : Finset ℕ) (j pref : ℕ → ℕ) (J : ℕ) : Finset ℕ :=
  (S.filter (fun n => j n=J)).image pref

lemma mem_pptPrefixesAt {S : Finset ℕ} {j pref : ℕ → ℕ} {J c : ℕ} :
    c ∈ pptPrefixesAt S j pref J ↔ ∃ n ∈ S, j n=J ∧ pref n=c := by
  classical
  constructor
  · intro hc
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hc
    have hh := Finset.mem_filter.mp hn
    exact ⟨n, hh.1, hh.2, he⟩
  · rintro ⟨n, hn, hj, hc⟩
    exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, hj⟩, hc⟩

lemma ppt_prefix_cells_exact_cover (S : Finset ℕ) (j pref : ℕ → ℕ) (N : ℕ)
    (hindex : ∀ n ∈ S, j n < N) :
    S ⊆ (Finset.range N).biUnion (fun J =>
      (pptPrefixesAt S j pref J).biUnion (fun c => pptPrefixCell S j pref J c)) := by
  classical
  intro n hn
  apply Finset.mem_biUnion.mpr
  refine ⟨j n, Finset.mem_range.mpr (hindex n hn), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨pref n, mem_pptPrefixesAt.mpr ⟨n, hn, rfl, rfl⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨hn, rfl, rfl⟩

/-- The exact-index partition preserves each prefix length before
bounding its reciprocal totient mass.  Residual injectivity is applied
inside the fixed-prefix cell, as required by the bad-witness map. -/
lemma ppt_prefix_group_count_exact (S : Finset ℕ) (j pref residual : ℕ → ℕ) (N : ℕ)
    (hindex : ∀ n ∈ S, j n < N)
    (hfactor : ∀ n ∈ S, n = pref n*residual n) :
    (S.card : ℝ) ≤ ∑ J ∈ Finset.range N, ∑ c ∈ pptPrefixesAt S j pref J,
      (((pptPrefixCell S j pref J c).image residual).card : ℝ) := by
  classical
  simp_rw [ppt_prefix_cell_residual_card S j pref residual hfactor]
  have hnat : S.card ≤ ∑ J ∈ Finset.range N, ∑ c ∈ pptPrefixesAt S j pref J,
      (pptPrefixCell S j pref J c).card := by
    apply (Finset.card_le_card (ppt_prefix_cells_exact_cover S j pref N hindex)).trans
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun J _ => Finset.card_biUnion_le)
  exact_mod_cast hnat

end TotientAsymptotic

end

end OAI
