import Mathlib
import OAI.Probability.SKGap.Localization.Map
import OAI.Probability.SKGap.Terminal.Map

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
namespace SKGap.Noncrossing
open Diagram InverseDiagram
namespace WordSeries
variable {ι : Type*} [Fintype ι]

def ordinary (j : ℝ) (F : List (Letter (ι→ℝ))) : ι→ℝ := expect j id F
def chain (j : ℝ) (a : ι→ℝ) (bs : List Bool) : List (Letter (ι→ℝ)) :=
  (expandBlocks bs).map (Letter.map (blockLabel j a))
def inverseCoefficient (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) : ℝ :=
  ∑ bs : Blocks n, ordinary j (P++chain j a bs.val++Q) i

@[simp] lemma chain_nil (j : ℝ) (a : ι→ℝ) : chain j a []=[] := rfl
@[simp] lemma chain_append (j : ℝ) (a : ι→ℝ) (p q : List Bool) :
    chain j a (p++q)=chain j a p++chain j a q := by simp [chain]
@[simp] lemma chain_true (j : ℝ) (a : ι→ℝ) (p : List Bool) :
    chain j a (true::p)=.diag a::.noise::chain j a p := rfl
@[simp] lemma chain_false (j : ℝ) (a : ι→ℝ) (p : List Bool) :
    chain j a (false::p)=.diag (fun i => -(j*mean a)*a i)::chain j a p := rfl

lemma blocks_zero (bs : Blocks 0) : bs.val=[] := by
  have h := (mem_blockEnumerate bs.val 0).mpr bs.property
  simpa [blockEnumerate] using h
instance blocksZeroUnique : Unique (Blocks 0) where
  default := ⟨[],rfl⟩
  uniq bs := Subtype.ext (blocks_zero bs)

@[simp] lemma inverseCoefficient_zero (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (i : ι) :
    inverseCoefficient j a P Q 0 i=ordinary j (P++Q) i := by
  simp [inverseCoefficient,blocks_zero]

lemma inverseCoefficient_empty (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    inverseCoefficient j a [] [] n i=if n=0 then 1 else 0 := by
  have he : inverseCoefficient j a [] [] n i=literalCoefficient j a n i := by
    simp only [inverseCoefficient,List.nil_append,List.append_nil,ordinary,chain,expect_map,
      Function.id_comp]
    symm
    change (∑ z : Σ bs : Blocks n, Paired (expandBlocks bs.val), _) = _
    rw [Fintype.sum_sigma]
    rfl
  rw [he,literalCoefficient_eq]

lemma mean_inverseCoefficient (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (n : ℕ) :
    mean (inverseCoefficient j a P Q n) =
      ∑ bs : Blocks n, mean (ordinary j (P++chain j a bs.val++Q)) := by
  simp only [mean,inverseCoefficient]
  rw [Finset.sum_comm,Finset.sum_div]

lemma sum_marked_chain {M : Type*} [AddCommMonoid M] (j : ℝ) (a : ι→ℝ) (n : ℕ)
    (f : List (Letter (ι→ℝ))→List (Letter (ι→ℝ))→M) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val), f s.before s.after) =
      ∑ k : Fin (n+1), ∑ p : Blocks k.val, ∑ q : Blocks (n-k.val),
        f (chain j a p.val++[.diag a]) (chain j a q.val) := by
  calc
    _ = ∑ bs : Blocks (n+1), ∑ s : NoiseSplit (expandBlocks bs.val),
        f (s.before.map (Letter.map (blockLabel j a)))
          (s.after.map (Letter.map (blockLabel j a))) := by
      apply Finset.sum_congr rfl
      intro bs _
      symm
      apply Fintype.sum_equiv (NoiseSplit.mapEquiv (blockLabel j a) (expandBlocks bs.val))
      intro s; rfl
    _ = _ := by
      simpa only [List.map_append,List.map_cons,List.map_nil,Letter.map,blockLabel,chain] using
        sum_marked_blocks n (fun P Q => f (P.map (Letter.map (blockLabel j a)))
          (Q.map (Letter.map (blockLabel j a))))

lemma inverse_partner_right (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ)))
    (n : ℕ) (i : ι) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
      j*mean (ordinary j (R++s.before))*ordinary j (P++s.after++T) i) =
      ∑ k : Fin (n+1), j*mean (inverseCoefficient j a R [.diag a] k.val)*
        inverseCoefficient j a P T (n-k.val) i := by
  rw [sum_marked_chain j a n (fun P' Q' =>
    j*mean (ordinary j (R++P'))*ordinary j (P++Q'++T) i)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [List.append_assoc]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum,mean_inverseCoefficient]
  simp only [inverseCoefficient,List.append_assoc]

end WordSeries
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]

lemma ordinary_cut_right (j : ℝ) (P R K T : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j ((P++(.noise::R))++K++T) i =
      (∑ s : NoiseSplit P, j*mean (ordinary j s.after)*ordinary j (s.before++R++K++T) i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.before)*ordinary j (P++s.after++K++T) i) +
      (∑ s : NoiseSplit K, j*mean (ordinary j (R++s.before))*ordinary j (P++s.after++T) i) +
      (∑ s : NoiseSplit T, j*mean (ordinary j (R++K++s.before))*ordinary j (P++s.after) i) := by
  have hh := expect_at j (id : (ι→ℝ)→ι→ℝ) P (R++(K++T)) i
  rw [NoiseSplit.sum_append R (K++T) (fun U V =>
    j*mean (expect j id U)*expect j id (P++V) i)] at hh
  rw [NoiseSplit.sum_append K T (fun U V =>
    j*mean (expect j id (R++U))*expect j id (P++V) i)] at hh
  simpa only [ordinary,List.append_assoc,List.cons_append,add_assoc] using hh

theorem inverseCoefficient_right (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    inverseCoefficient j a (P++(.noise::R)) T (n+1) i =
      (∑ s : NoiseSplit P, j*mean (ordinary j s.after)*
        inverseCoefficient j a (s.before++R) T (n+1) i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.before)*
        inverseCoefficient j a (P++s.after) T (n+1) i) +
      (∑ k : Fin (n+1), j*mean (inverseCoefficient j a R [.diag a] k.val)*
        inverseCoefficient j a P T (n-k.val) i) +
      (∑ s : NoiseSplit T, j*mean (inverseCoefficient j a R s.before (n+1))*
        ordinary j (P++s.after) i) := by
  have hh : inverseCoefficient j a (P++(.noise::R)) T (n+1) i =
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit P, j*mean (ordinary j s.after)*
        ordinary j (s.before++R++chain j a bs.val++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit R, j*mean (ordinary j s.before)*
        ordinary j (P++s.after++chain j a bs.val++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
        j*mean (ordinary j (R++s.before))*ordinary j (P++s.after++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit T, j*mean (ordinary j (R++chain j a bs.val++s.before))*
        ordinary j (P++s.after) i) := by
    unfold inverseCoefficient
    simp_rw [ordinary_cut_right,Finset.sum_add_distrib]
  rw [hh,inverse_partner_right]
  congr 2
  · congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      rfl
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      rfl
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul,← Finset.mul_sum,← mean_inverseCoefficient]

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

end OAI
