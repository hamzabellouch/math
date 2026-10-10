import Mathlib
import OAI.Combinatorics.KMedian.Reduction.RationalThreshold
import OAI.Combinatorics.KMedian.Reduction.Sparsification

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def witnessedRestriction (I : Instance) (F : Finset (Fin I.n))
    (P : Finset (Fin I.n × Fin I.n)) : Finset (Fin I.n) :=
  F.filter (fun i => ∀ p ∈ P, I.distance p.1 p.2 ≤ I.distance p.1 i)

def sparseBranches (I : Instance) (F : Finset (Fin I.n)) (b : ℕ) : Finset (Finset (Fin I.n)) :=
  (deletionChoices (F ×ˢ F) b).image (witnessedRestriction I F)

theorem sparseBranches_card (I : Instance) (F : Finset (Fin I.n)) (b : ℕ) :
    (sparseBranches I F b).card ≤ (b+1)*(F.card*F.card+1)^b := by
  calc
    _ ≤ (deletionChoices (F ×ˢ F) b).card := card_image_le
    _ ≤ _ := by simpa only [card_product] using card_deletionChoices (F ×ˢ F) b

theorem sparseBranches_sub (I : Instance) (F : Finset (Fin I.n)) (b : ℕ)
    {F' : Finset (Fin I.n)} (h : F' ∈ sparseBranches I F b) : F' ⊆ F := by
  obtain ⟨P,_,rfl⟩ := mem_image.mp h
  exact filter_subset _ _

variable {I : Instance}
local instance sparsifyEnumerationPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

theorem sparse_branch_exists (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hcost : 0 < cost I O) (ρ : ℝ) (hρ : 0 < ρ) (b : ℕ) (hb : (3/2:ℝ) ≤ b*ρ) :
    ∃ F' ∈ sparseBranches I F b, O ⊆ F' ∧ Sparse (I:=I) F' O ρ := by
  classical
  obtain ⟨P,hPF,hcount,hOP,hsp⟩ := sparsify F O hOF hO hcost ρ hρ
  have hcard : P.card ≤ b := by
    have hh : (P.card:ℝ) ≤ b := (mul_le_mul_iff_left₀ hρ).mp (hcount.trans hb)
    exact_mod_cast hh
  choose q hq he using fun p : Fin I.n => I.nearest_attained p O hO
  let W := P.image (fun p => (p,q p))
  have hWsub : W ⊆ F ×ˢ F := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
    exact mem_product.mpr ⟨hPF hp,hOF (hq p)⟩
  have hWcard : W.card ≤ b := (card_image_le).trans hcard
  have hWeq : witnessedRestriction I F W=F.filter (fun i => ∀ p ∈ P, nearest I p O ≤ dist p i) := by
    ext i
    simp only [witnessedRestriction,mem_filter]
    constructor
    · rintro ⟨hi,hh⟩
      refine ⟨hi,fun p hp => ?_⟩
      have hqdist := hh (p,q p) (mem_image_of_mem _ hp)
      change I.distance p (q p) ≤ I.distance p i at hqdist
      rw [he p]
      change (I.distance p (q p):ℝ) ≤ (I.distance p i:ℝ)
      exact_mod_cast hqdist
    · rintro ⟨hi,hh⟩
      refine ⟨hi,fun w hw => ?_⟩
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
      have hd := hh p hp
      rw [he p] at hd
      change (I.distance p (q p):ℝ) ≤ (I.distance p i:ℝ) at hd
      exact_mod_cast hd
  refine ⟨_,mem_image_of_mem _ ((mem_deletionChoices _ _ _).mpr ⟨hWsub,hWcard⟩),?_,?_⟩
  · rw [hWeq]; exact hOP
  · rw [hWeq]; exact hsp

end MetricKMedian.Reduction
end
end

end OAI
