import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyFinite
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyMoebius

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_positive_frequency_jacobi_moebius {L M : ℕ}
    (hL : Squarefree L) (hM : Squarefree M) (B : ℕ) (F : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 B, (jacobiSym (u : ℤ) M : ℂ) * F u) =
      ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
        ∑ v ∈ L.divisors,
          (jacobiSym (s : ℤ) M : ℂ) * (jacobiSym (v : ℤ) M : ℂ) *
            ∑ P ∈ M.divisors, (-1 : ℂ) ^ P.primeFactors.card *
              ∑ w ∈ (Finset.Icc 1 B).filter (fun w => s * v * w ^ 2 ≤ B ∧ P ∣ w),
                F (s * v * w ^ 2) := by
  rw [sum_positive_frequency_nested hL B]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro v hv
  simpa only [Finset.filter_filter] using positive_frequency_square_sum_moebius s v hM
    ((Finset.Icc 1 B).filter (fun w => s * v * w ^ 2 ≤ B)) (fun w => F (s * v * w ^ 2))

theorem finsupp_positive_sum_eq_Icc {A : Type*} [AddCommMonoid A] (F : ℕ →₀ A) :
    F.sum (fun n a => if 0 < n then a else 0) =
      ∑ u ∈ Finset.Icc 1 (F.support.sup id), F u := by
  classical
  change (∑ n ∈ F.support, if 0 < n then F n else 0) = _
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro u hu
    obtain ⟨hu, hup⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_Icc.mpr ⟨hup, Finset.le_sup (f := id) hu⟩
  · intro u hu hnot
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    exact hnot (Finset.mem_filter.mpr ⟨hmem, (Finset.mem_Icc.mp hu).1⟩)

theorem finsupp_positive_frequency_reindex {L : ℕ} (hL : Squarefree L) (F : ℕ →₀ ℂ) :
    F.sum (fun u a => if 0 < u then a else 0) =
      ∑ s ∈ (Finset.Icc 1 (F.support.sup id)).filter
          (fun s => Squarefree s ∧ s.Coprime L),
        ∑ v ∈ L.divisors,
          ∑ w ∈ (Finset.Icc 1 (F.support.sup id)).filter
              (fun w => s * v * w ^ 2 ≤ F.support.sup id), F (s * v * w ^ 2) := by
  rw [finsupp_positive_sum_eq_Icc, sum_positive_frequency_nested hL]

end Ostmann.QuadraticCenter

end

end OAI
