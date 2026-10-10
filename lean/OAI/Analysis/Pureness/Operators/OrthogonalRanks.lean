import OAI.Analysis.Pureness.Divisibility.CommonMinorant

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_mul_eq_zero {h k x y : A}
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier k) (hhk : h * k = 0) :
    x * y = 0 := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  have hz (j : ℕ) : u j * v j = 0 := by
    obtain ⟨a, ha⟩ := hu j
    obtain ⟨b, hb⟩ := hv j
    rw [← ha, ← hb]
    calc
      _ = h * a * (h * k) * b * k := by simp only [mul_assoc]
      _ = 0 := by rw [hhk]; simp
  have ht := hux.mul hvy
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma orthogonal_add_le_one (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hab : a * b = 0) : a + b ≤ 1 := by
  have hba : b * a = 0 := by
    simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star hab
  have hcomm : Commute (1 - a) (1 - b) := by
    show (1 - a) * (1 - b) = (1 - b) * (1 - a)
    noncomm_ring [hab, hba]
  have hpos := Commute.mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1) hcomm
  have heq : (1 - a) * (1 - b) = 1 - (a + b) := by noncomm_ring [hab]
  rw [heq] at hpos
  exact sub_nonneg.mp hpos

lemma orthogonal_sum_le_one {ι : Type*} (I : Finset ι) (a : ι → A)
    (ha : ∀ i ∈ I, 0 ≤ a i) (ha1 : ∀ i ∈ I, a i ≤ 1)
    (horth : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i * a j = 0) :
    ∑ i ∈ I, a i ≤ 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    apply orthogonal_add_le_one (a i) (∑ j ∈ I, a j)
      (ha i (Finset.mem_insert_self i I))
      (Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (ha1 i (Finset.mem_insert_self i I))
    · exact ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hjk => horth j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun heq => hi (heq ▸ hj))

theorem orthogonal_rank_sum_le_one (τ : TracialState A) {ι : Type*} (I : Finset ι)
    (a : ι → A) (ha : ∀ i ∈ I, 0 ≤ a i)
    (horth : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i * a j = 0) :
    ∑ i ∈ I, normalizedRootRank τ (a i) ≤ 1 := by
  have ht : Tendsto (fun n => ∑ i ∈ I, ENNReal.ofReal (τ.functional (normalizedRoot (a i) n)).re)
      atTop (𝓝 (∑ i ∈ I, normalizedRootRank τ (a i))) :=
    tendsto_finsetSum I (fun i hi => normalizedRootRank_tendsto τ (a i) (ha i hi))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro n
  have hs : ∑ i ∈ I, normalizedRoot (a i) n ≤ 1 := by
    apply orthogonal_sum_le_one I (fun i => normalizedRoot (a i) n)
      (fun i _ => normalizedRoot_nonneg (a i) n)
      (fun i hi => normalizedRoot_le_one (a i) (ha i hi) n)
    intro i hi j hj hij
    exact hereditary_mul_eq_zero
      (normalizedRoot_mem_hereditary (ha i hi) (self_mem_hereditary _ (ha i hi)) (ha i hi) n)
      (normalizedRoot_mem_hereditary (ha j hj) (self_mem_hereditary _ (ha j hj)) (ha j hj) n)
      (horth i hi j hj hij)
  have hreal : (τ.functional (∑ i ∈ I, normalizedRoot (a i) n)).re ≤ 1 := by
    have hτ : τ.functional (∑ i ∈ I, normalizedRoot (a i) n) ≤ τ.functional 1 :=
      τ.functional.monotone hs
    rw [τ.normalized] at hτ
    exact (Complex.le_def.mp hτ).1
  have hn (i : ι) (hi : i ∈ I) : 0 ≤ (τ.functional (normalizedRoot (a i) n)).re :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (normalizedRoot_nonneg (a i) n))).1
  rw [← ENNReal.ofReal_sum_of_nonneg hn]
  apply ENNReal.ofReal_le_one.mpr
  simpa only [map_sum, Complex.re_sum] using hreal

theorem small_rank_of_orthogonal_family [Nontrivial A] (hsimple : TopologicallySimple A)
    (N : ℕ) (hN : 1 ≤ N) (a : Fin N → A) (ha : ∀ i, 0 ≤ a i)
    (ha0 : ∀ i, a i ≠ 0) (horth : ∀ i j, i ≠ j → a i * a j = 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      (∀ i, CuntzSubequiv h (a i)) ∧
      (∀ τ : TracialState A, normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞)) := by
  obtain ⟨h, hh, hh0, hhC, hhR⟩ := exists_finite_common_minorant hsimple Finset.univ a
    (fun i _ => ha i) (fun i _ => ha0 i)
  refine ⟨h, hh, hh0, fun i => hhC i (Finset.mem_univ i), ?_⟩
  intro τ
  have hsum : (N : ℝ≥0∞) * normalizedRootRank τ h ≤ 1 := by
    calc
      _ = ∑ i : Fin N, normalizedRootRank τ h := by simp [nsmul_eq_mul]
      _ ≤ ∑ i : Fin N, normalizedRootRank τ (a i) :=
        Finset.sum_le_sum (fun i hi => hhR τ i hi)
      _ ≤ 1 := orthogonal_rank_sum_le_one τ Finset.univ a
        (fun i _ => ha i) (fun i _ j _ hij => horth i j hij)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (Nat.ne_of_gt hN))) (by simp)).mpr
  simpa only [mul_comm] using hsum
end CuntzPureness

end OAI
