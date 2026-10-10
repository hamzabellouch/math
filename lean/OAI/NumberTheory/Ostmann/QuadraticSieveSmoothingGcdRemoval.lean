import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingGcd

namespace OAI

namespace Ostmann.QuadraticSieve

theorem smoothing_large_gcd_removal_dual_sub_complement (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M K N D : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      0<M → S ⊆ oddSquarefreeUpTo N → 0<D →
      smoothingEnergy M K S a ≤
        (∑ d ∈ Finset.Icc 1 D,
          ‖dualCorrelation sieveWeight (M:ℝ) d (quotientSupport S d) (fun n => a (d*n)) -
            complementaryCorrelation sieveWeight (M:ℝ) K d
              (quotientSupport S d) (fun n => a (d*n))‖) +
        C*(N:ℝ)^ε*smoothingNorm M K (oddSquarefreeUpTo (N/D))*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := smoothing_large_gcd_removal ε hε
  refine ⟨C,hC,?_⟩
  intro M K N D S a hM hS hD
  have he : (∑ d ∈ Finset.Icc 1 D,
      ‖weightedGcdCorrelation (smoothingRows M K) S (smoothingWeight M) a d‖) =
      ∑ d ∈ Finset.Icc 1 D,
        ‖dualCorrelation sieveWeight (M:ℝ) d (quotientSupport S d) (fun n => a (d*n)) -
          complementaryCorrelation sieveWeight (M:ℝ) K d
            (quotientSupport S d) (fun n => a (d*n))‖ := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [smoothing_gcdCorrelation_eq_of_oddSquarefree hM (Finset.mem_Icc.mp hd).1 K S a hS]
  simpa only [he] using hbound M K N D S a hS hD

theorem smoothing_quotient_transform_support {S : Finset ℕ} {N d : ℕ} {N₀ : ℝ}
    (hS : S ⊆ oddSquarefreeUpTo N) (hd : 0<d) (hdN : (d:ℝ)<N₀)
    (hdyadic : ∀ n ∈ S, N₀<(n:ℝ) ∧ (n:ℝ)≤2*N₀) :
    quotientSupport S d ⊆ oddSquarefreeUpTo (N/d) ∧
      ∀ n ∈ quotientSupport S d,
        n.Coprime d ∧ 1<n ∧ N₀/d<(n:ℝ) ∧ (n:ℝ)≤2*N₀/d := by
  refine ⟨quotientSupport_subset_oddSquarefreeUpTo hS,?_⟩
  intro n hn
  exact ⟨quotientSupport_coprime
      (fun m hm => (mem_oddSquarefreeUpTo.mp (hS hm)).2.2.2) hn,
    quotientSupport_one_lt hdN (fun m hm => (hdyadic m hm).1) hn,
    quotientSupport_dyadic hd hdyadic hn⟩

end Ostmann.QuadraticSieve

end OAI
