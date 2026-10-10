import OAI.NumberTheory.JointDickman.Amplification.CandidateGraphEncoding

namespace OAI

/-! # Recovering endpoint candidates from nonzero arithmetic graph terms -/

namespace JointDickman
open Finset Classical

noncomputable def graphBlockCandidate {M : ℕ} (i k : Fin M)
    (g : GraphCoefficientTriple) : BlockCandidateIndex M := ((i,k),(g.2.2,g.2.1))

theorem graphBlockCandidate_quotient {B T M : ℕ} {i k : Fin M}
    {g : GraphCoefficientTriple} (hik : i < k)
    (hg : g ∈ supportedGraphTriples B T ((k.val-i.val : ℕ) : ℤ)) :
    candidateQuotient (graphBlockCandidate i k g) = ∏ p ∈ g.1, p := by
  have hj : 0 < k.val-i.val := Nat.sub_pos_of_lt hik
  have he := graphTriple_positive_relation hg
  change ((∏ p ∈ g.2.1, p)-(∏ p ∈ g.2.2, p))/(k.val-i.val) = _
  rw [he,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ hj]

theorem graphBlockCandidate_roundtrip {B T M : ℕ} {i k : Fin M}
    {g : GraphCoefficientTriple} (hik : i < k)
    (hg : g ∈ supportedGraphTriples B T ((k.val-i.val : ℕ) : ℤ)) :
    candidateGraphTriple B (graphBlockCandidate i k g) = g := by
  have hs := graphTriple_subsets (mem_filter.mp hg).1
  unfold candidateGraphTriple
  rw [graphBlockCandidate_quotient hik hg,coefficientPrimeSet_primeProduct hs.1]
  rfl

theorem candidateGraphTriple_roundtrip {B M : ℕ} {i k : Fin M}
    {e : BlockCandidateIndex M} (he : e.1 = (i,k)) :
    graphBlockCandidate i k (candidateGraphTriple B e) = e := by
  exact Prod.ext he.symm rfl

theorem graphTripleWeight_nonzero_regular {B L T n : ℕ} {τ C : ℝ}
    {g : GraphCoefficientTriple} (hg : g ∈ arithmeticGraphTriples B T)
    (hw : graphTripleWeight B L τ C T g n ≠ 0) :
    RegularPrimeSet B L τ C g.1 ∧
    RegularPrimeSet B L τ C g.2.1 ∧
    RegularPrimeSet B L τ C g.2.2 ∧
    RegularPrimeSet B L τ C (coefficientPrimeSet B (n/(∏ p ∈ g.2.2, p))) ∧
    RegularPrimeSet B L τ C
      (coefficientPrimeSet B (((n : ℤ)+graphTripleLag g).toNat/(∏ p ∈ g.2.1, p))) := by
  have hs := graphTriple_subsets hg
  have hc (d : ℕ) (h : regularCoefficientWeight B L τ C d ≠ 0) :
      RegularPrimeSet B L τ C (coefficientPrimeSet B d) := by
    by_contra hn
    exact h (by simp [regularCoefficientWeight,hn])
  have hr (d : ℕ) (h : arithmeticResidueWeight B L τ C d ≠ 0) :
      RegularPrimeSet B L τ C (coefficientPrimeSet B d) := by
    by_contra hn
    exact h (by simp [arithmeticResidueWeight,regularResidueWeight,hn])
  change (_ * _ * _) * (_ * _ * _) * (_ * _ * _) ≠ 0 at hw
  obtain ⟨hca,heb⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hcc,hea⟩ := mul_ne_zero_iff.mp hca
  obtain ⟨huc,_⟩ := mul_ne_zero_iff.mp hcc
  obtain ⟨_,hregc⟩ := mul_ne_zero_iff.mp huc
  obtain ⟨hara,_⟩ := mul_ne_zero_iff.mp hea
  obtain ⟨hrega,hra⟩ := mul_ne_zero_iff.mp hara
  obtain ⟨hbrb,_⟩ := mul_ne_zero_iff.mp heb
  obtain ⟨hregb,hrb⟩ := mul_ne_zero_iff.mp hbrb
  refine ⟨?_,?_,?_,hr _ hra,hr _ hrb⟩
  · simpa only [coefficientPrimeSet_primeProduct hs.1] using hc _ hregc
  · simpa only [coefficientPrimeSet_primeProduct hs.2.1] using hc _ hrega
  · simpa only [coefficientPrimeSet_primeProduct hs.2.2] using hc _ hregb

theorem graphBlockCandidate_mem {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) {i k : Fin M} (hik : i < k)
    (hH : H < k.val-i.val) {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T)
    (hlag : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ))
    (hn : u+(i.val+1) ∈ graphTripleEdges N g)
    (hw : graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0)
    (hsq : ¬ BlockSquareHit B M u) :
    graphBlockCandidate i k g ∈ blockCandidates B L T H M τ C
      (fun l => coefficientPrimeSet B (u+(l.val+1))) := by
  have hs := graphTriple_subsets hg
  have hsup := graphTripleWeight_nonzero_supported hB hT τ C hg hlag hw
  have hq := graphBlockCandidate_quotient hik hsup
  have hreg := graphTripleWeight_nonzero_regular hg hw
  have hj : 0 < k.val-i.val := Nat.sub_pos_of_lt hik
  have hshift : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g).toNat = u+(k.val+1) := by
    rw [hlag,Int.ofNat_sub hik.le]
    omega
  have hbdiv : (∏ p ∈ g.2.2, p) ∣ u+(i.val+1) := (mem_filter.mp hn).2.1
  have hadiv : (∏ p ∈ g.2.1, p) ∣ u+(k.val+1) := by
    have h := (mem_filter.mp hn).2.2.1
    have he : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g) = (u+(k.val+1) : ℕ) := by
      rw [hlag,Int.ofNat_sub hik.le]
      push_cast
      ring
    rw [he] at h
    exact_mod_cast h
  have hno (l : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) : ¬ p^2 ∣ u+(l.val+1) :=
    fun hd => hsq ⟨l,p,hp,hd⟩
  have hcompb := coefficientPrimeSet_quotient hs.2.2 hbdiv (hno i)
  have hcompa := coefficientPrimeSet_quotient hs.2.1 hadiv (hno k)
  have hrega : RegularPrimeSet B L τ C (coefficientPrimeSet B (u+(k.val+1)) \ g.2.1) := by
    rw [hshift,hcompa] at hreg
    exact hreg.2.2.2.2
  have hregb : RegularPrimeSet B L τ C (coefficientPrimeSet B (u+(i.val+1)) \ g.2.2) := by
    rw [hcompb] at hreg
    exact hreg.2.2.2.1
  apply mem_blockCandidates.mpr
  refine ⟨⟨mem_endpointSplits.mpr ⟨(primeProduct_dvd_site_iff hs.2.2).mp hbdiv,
    hreg.2.2.1,hregb⟩,mem_endpointSplits.mpr
    ⟨(primeProduct_dvd_site_iff hs.2.1).mp hadiv,hreg.2.1,hrega⟩⟩,?_⟩
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hadm := (mem_filter.mp hg).2
  have he : ((∏ p ∈ g.2.1, p : ℕ) : ℤ)-(∏ p ∈ g.2.2, p) =
      graphTripleLag g*(∏ p ∈ g.1, p) := hadm.2.2.2.1
  have hm := (divisorEdge_inverse_mem ha hc he hadm.2.2.2.2 hn).1
  have hca := (coprime_of_divisor_linear_succ (mem_filter.mp hm).2.2.2.1).1
  have hcb := (coprime_of_divisor_linear_succ (mem_filter.mp hm).2.2.2.2).1
  have hab := divisor_edge_coprime hca hadm.2.2.2.2 he
  have hwa := (mem_amplificationCoefficientPairs hB).mp (mem_filter.mp hsup).2.2.1
  have hwb := (mem_amplificationCoefficientPairs hB).mp (mem_filter.mp hsup).2.2.2
  unfold BlockCandidateAdmissible
  change i < k ∧ H < k.val-i.val ∧ k.val-i.val < T ∧
    0 < candidateQuotient (graphBlockCandidate i k g) ∧ _
  rw [hq]
  refine ⟨hik,hH,?_,hc,graphTriple_positive_relation hsup,hab.symm,hcb,hca,?_,?_,?_,?_,
    hwb.2.2.1,hwb.2.2.2.le,hwa.2.2.1,hwa.2.2.2.le⟩
  · have hjlt : (graphTripleLag g).natAbs < T := hadm.2.2.1
    simpa only [hlag,Int.natAbs_natCast] using hjlt
  · rw [coefficientPrimeSet_primeProduct hs.1]
  · simpa only [coefficientPrimeSet_primeProduct hs.1] using hreg.1
  · exact (Real.le_log_iff_exp_le (by positivity)).mpr hwa.1
  · exact (Real.log_le_iff_le_exp (by positivity)).mpr hwa.2.1

end JointDickman

end OAI
