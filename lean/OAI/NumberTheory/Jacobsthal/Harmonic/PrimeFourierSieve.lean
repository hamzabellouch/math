import OAI.NumberTheory.Jacobsthal.Partitions.IntervalSpectrumCoefficients

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem prime_reduced_residues (p : ℕ) (hp : Nat.Prime p) :
    (Finset.range p).erase 0 = (Finset.range p).filter (fun a => Nat.Coprime a p) := by
  ext a
  simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_filter]
  constructor
  · rintro ⟨ha0,hap⟩
    refine ⟨hap,?_⟩
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hd
    exact (not_le_of_gt hap) (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hd)
  · rintro ⟨hap,hcop⟩
    refine ⟨?_,hap⟩
    intro ha0
    subst a
    have hh : p = 1 := by simpa using hcop
    exact hp.ne_one hh

theorem prime_variance_large_sieve (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (Q J : ℕ) (M : ℤ) (S : Finset ℤ) (hS : S ⊆ Finset.Ico M (M+(J : ℤ)))
    (hQ : ∀ p ∈ P,p ≤ Q) :
    (∑ p ∈ P,(p : ℝ)*integerResidueVariance p S) ≤
      (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ) := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (p : ℝ)*integerResidueVariance p S =
        ∑ a ∈ (Finset.range p).filter (fun a => a.Coprime p),‖exponentialSum S a p‖^2 := by
    let : NeZero p := ⟨(hP p hp).ne_zero⟩
    rw [integer_variance_fourier,prime_reduced_residues p (hP p hp)]
  have hsub : P ⊆ Finset.Icc 1 Q := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).one_le,hQ p hp⟩
  have hals := AdditiveLargeSieve.additive_large_sieve Q J M (indicatorCoefficient S)
  simp_rw [indicator_exponential_sum S M J hS] at hals
  rw [indicator_energy S M J hS] at hals
  calc
    _ = ∑ p ∈ P,∑ a ∈ (Finset.range p).filter (fun a => a.Coprime p),‖exponentialSum S a p‖^2 :=
      Finset.sum_congr rfl hpoint
    _ ≤ ∑ p ∈ Finset.Icc 1 Q,∑ a ∈ (Finset.range p).filter (fun a => a.Coprime p),‖exponentialSum S a p‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ _ := hals

end ErdosInverseSpectrum

end

end Erdos970

end OAI
