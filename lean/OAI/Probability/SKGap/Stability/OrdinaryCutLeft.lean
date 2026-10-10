import Mathlib
import OAI.Probability.SKGap.Stability.Ordinary

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]

lemma ordinary_cut_left (j : ℝ) (P K R T : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (P++K++R++(.noise::T)) i =
      (∑ s : NoiseSplit P, j*mean (ordinary j (s.after++K++R))*ordinary j (s.before++T) i) +
      (∑ s : NoiseSplit K, j*mean (ordinary j (s.after++R))*ordinary j (P++s.before++T) i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.after)*ordinary j (P++K++s.before++T) i) +
      (∑ s : NoiseSplit T, j*mean (ordinary j s.before)*ordinary j (P++K++R++s.after) i) := by
  have hh := expect_at j (id : (ι→ℝ)→ι→ℝ) (P++(K++R)) T i
  rw [NoiseSplit.sum_append P (K++R) (fun U V =>
    j*mean (expect j id V)*expect j id (U++T) i)] at hh
  rw [NoiseSplit.sum_append K R (fun U V =>
    j*mean (expect j id V)*expect j id ((P++U)++T) i)] at hh
  simpa only [ordinary,List.append_assoc,add_assoc] using hh

lemma inverse_partner_left (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ)))
    (n : ℕ) (i : ι) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
      j*mean (ordinary j (s.after++R))*ordinary j (P++s.before++T) i) =
      ∑ k : Fin (n+1), j*mean (inverseCoefficient j a [] R (n-k.val))*
        inverseCoefficient j a P (.diag a::T) k.val i := by
  rw [sum_marked_chain j a n (fun U V =>
    j*mean (ordinary j (V++R))*ordinary j (P++U++T) i)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum,mean_inverseCoefficient]
  simp only [inverseCoefficient,List.append_assoc,List.nil_append]

theorem inverseCoefficient_left (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    inverseCoefficient j a P (R++(.noise::T)) (n+1) i =
      (∑ s : NoiseSplit P, j*mean (inverseCoefficient j a s.after R (n+1))*
        ordinary j (s.before++T) i) +
      (∑ k : Fin (n+1), j*mean (inverseCoefficient j a [] R (n-k.val))*
        inverseCoefficient j a P (.diag a::T) k.val i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.after)*
        inverseCoefficient j a P (s.before++T) (n+1) i) +
      (∑ s : NoiseSplit T, j*mean (ordinary j s.before)*
        inverseCoefficient j a P (R++s.after) (n+1) i) := by
  have hh : inverseCoefficient j a P (R++(.noise::T)) (n+1) i =
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit P, j*mean (ordinary j (s.after++chain j a bs.val++R))*
        ordinary j (s.before++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
        j*mean (ordinary j (s.after++R))*ordinary j (P++s.before++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit R, j*mean (ordinary j s.after)*
        ordinary j (P++chain j a bs.val++s.before++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit T, j*mean (ordinary j s.before)*
        ordinary j (P++chain j a bs.val++R++s.after) i) := by
    unfold inverseCoefficient
    have hcut (bs : Blocks (n+1)) := ordinary_cut_left j P (chain j a bs.val) R T i
    have he := Finset.sum_congr rfl (fun bs (_ : bs∈(Finset.univ : Finset (Blocks (n+1)))) => hcut bs)
    simpa only [List.append_assoc,Finset.sum_add_distrib] using he
  rw [hh,inverse_partner_left]
  congr 2
  · congr 2
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul,← Finset.mul_sum,← mean_inverseCoefficient]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
    simp only [inverseCoefficient,List.append_assoc]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
    simp only [inverseCoefficient,List.append_assoc]

end WordSeries
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
