import OAI.NumberTheory.JointDickman.Probability.EndpointResiduePartition
import OAI.NumberTheory.JointDickman.Probability.ManuscriptHistogramFourier
import OAI.NumberTheory.JointDickman.Amplification.LogOscillatoryTest
import Mathlib.Order.Interval.Set.Union

namespace OAI

/-! # Exact endpoint-to-histogram identity on the actual grid -/

namespace JointDickman
open Finset

theorem channelCells_cover {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Ioc (1/2 : ℝ) 3) :
    ∃ i : Fin n, x ∈ Set.Ioc (channelLower n i) (channelUpper n i) := by
  let f := fun i : ℕ => (1/2 : ℝ)+(i : ℝ)*channelMesh n
  have hend : f n = 3 := by
    dsimp [f,channelMesh]
    field_simp
    ring
  have hstart : f 0 = 1/2 := by simp [f]
  have hx' : x ∈ Set.Ioc (f 0) (f n) := by rwa [hstart,hend]
  obtain ⟨i,hi,hcell⟩ := Set.mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc n f hx')
  refine ⟨⟨i,mem_range.mp hi⟩,?_⟩
  simpa only [f,channelLower,channelUpper,Nat.cast_add,Nat.cast_one] using hcell

theorem primeSplitProductSupport_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (hk : k ∈ primeSplitProductSupport P) : 0 < k := by
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hk
  exact prod_pos (fun p hp => (hP p (mem_powerset.mp hA hp)).pos)

theorem primeSplitProductSupport_coprime {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {q k : ℕ} (hq : q ≠ 0) (hcut : ∀ p ∈ P, q < p)
    (hk : k ∈ primeSplitProductSupport P) : k.Coprime q := by
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hk
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  have hpP := mem_powerset.mp hA hp
  apply (hP p hpP).coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt (hcut p hpP)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdiv)

/-- With the full product support and the actual logarithmic cells, (38)
is exactly a residue Fourier transform before any averaging of the test. -/
theorem endpoint_histogram_identity {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {N : ℝ} (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ) (h : ZMod q) (ν : ℝ)
    (hsupp : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3) :
    (∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B),
      (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) k*w (k/N) : ℝ)*
        additivePhase ((k : ℝ)*(h.val/(q : ℝ)+ν))) =
      unitResidueFourier (fun r => ∑ i : Fin (channelFineCount m B),
        manuscriptCellSum m B q g (logOscillatoryTest w B N (ν*N)) i r) h := by
  classical
  let n := channelFineCount m B
  let P := auxiliaryPrimes B
  let γ := signedSplitProductMass P (subsetSiteTest P g)
  have hn := channelFineCount_pos hm hB
  have hsupport (k : ℕ) (hk : k ∈ primeSplitProductSupport P)
      (hc : (γ k*w (k/N) : ℝ) ≠ (0 : ℂ)) :
      ∃ i ∈ (univ : Finset (Fin n)), ∃ r : (ZMod q)ˣ,
        logResidueCell B q (channelLower n) (channelUpper n) k = some (i,r) := by
    have hw : w (k/N) ≠ 0 := by intro hw; simp [hw] at hc
    obtain ⟨i,hi⟩ := channelCells_cover hn (hsupp k hk hw)
    have hcop := primeSplitProductSupport_coprime (auxiliaryPrimes_prime B) (NeZero.ne q)
      (fun p hp => hcut.trans_lt (by exact_mod_cast (mem_filter.mp hp).2)) hk
    refine ⟨i,mem_univ _,ZMod.unitOfCoprime k hcop,?_⟩
    exact (logResidueCell_eq_some B q (channelLower n) (channelUpper n)
      (channelCells_disjoint hn) k i _).mpr ⟨hi,rfl⟩
  have he := endpoint_residue_partition (B := B) (channelLower n) (channelUpper n)
    (channelCells_disjoint hn) (primeSplitProductSupport P) univ
    (fun k => ((γ k*w (k/N) : ℝ) : ℂ)) h ν hsupport
  rw [he]
  congr 1
  funext r
  apply sum_congr rfl
  intro i _
  unfold manuscriptCellSum
  apply sum_congr rfl
  intro k hk
  dsimp only [n,P,γ]
  by_cases hc : logResidueCell B q (channelLower (channelFineCount m B))
    (channelUpper (channelFineCount m B)) k = some (i,r)
  · simp only [hc,ite_true]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast primeSplitProductSupport_pos (auxiliaryPrimes_prime B) hk
    have hlog := logOscillatoryTest_majorArc w (B := (B : ℝ)) (N := N)
      (j := 1) (X := 1) (k := (k : ℝ)) (ξ := ν) (by exact_mod_cast hB.ne') hN.ne' hk0
    simp only [mul_one,div_one] at hlog
    rw [hlog,Complex.ofReal_mul]
    ring_nf
  · simp only [hc,ite_false]

end JointDickman

end OAI
