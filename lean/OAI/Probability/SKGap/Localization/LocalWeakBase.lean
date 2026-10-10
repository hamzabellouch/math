import Mathlib
import OAI.Probability.SKGap.Localization.ResidualMultiplier

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Classical
variable {n : ℕ}

def flipNeighborhood (E : Set (Spin n)) : Set (Spin n) :=
  {x | x∈E ∨ ∃i,flip x i∈E}

def edgeCut (E : Set (Spin n)) (U : VectorFields n) : VectorFields n :=
  fun x i=>if x∈E ∨ flip x i∈E then U x i else 0

lemma halfDiff_edgeCut (E : Set (Spin n)) (U : VectorFields n) (x : Spin n) (i : Fin n) :
    halfDiff i (fun y=>edgeCut E U y i) x=
      if x∈E ∨ flip x i∈E then halfDiff i (fun y=>U y i) x else 0 := by
  classical
  by_cases he : x∈E ∨ flip x i∈E
  · have hf : flip x i∈E ∨ x∈E:=he.symm
    simp [halfDiff_as_flip,edgeCut,he,hf]
  · have hf : ¬(flip x i∈E ∨ x∈E):=by tauto
    simp [halfDiff_as_flip,edgeCut,he,hf]

lemma edgeCut_size (E : Set (Spin n)) (U : VectorFields n) {B : ℝ}
    (hU : ∀x∈flipNeighborhood E,∑i,(U x i)^2≤B^2) :
    ∀x,∑i,(edgeCut E U x i)^2≤B^2 := by
  classical
  intro x
  by_cases hx:x∈flipNeighborhood E
  · apply (Finset.sum_le_sum (fun i _=>show (edgeCut E U x i)^2≤(U x i)^2 by
      dsimp [edgeCut]; split_ifs <;> simp [sq_nonneg])).trans (hU x hx)
  · have hh : ∀i,¬(x∈E ∨ flip x i∈E):=by
      intro i hi; exact hx (hi.elim Or.inl (fun h=>Or.inr ⟨i,h⟩))
    simp [edgeCut,hh,sq_nonneg]

lemma edgeCut_diagonal (E : Set (Spin n)) (U : VectorFields n) {A : ℝ}
    (hA : 0≤A) (hD : ∀x∈flipNeighborhood E,∑i,|halfDiff i (fun y=>U y i) x|≤A) :
    ∀x,∑i,|halfDiff i (fun y=>edgeCut E U y i) x|≤A := by
  classical
  intro x
  by_cases hx:x∈flipNeighborhood E
  · apply (Finset.sum_le_sum (fun i _=>show
        |halfDiff i (fun y=>edgeCut E U y i) x|≤|halfDiff i (fun y=>U y i) x| by
      rw [halfDiff_edgeCut]; split_ifs <;> simp)).trans (hD x hx)
  · have hh : ∀i,¬(x∈E ∨ flip x i∈E):=by
      intro i hi; exact hx (hi.elim Or.inl (fun h=>Or.inr ⟨i,h⟩))
    simpa only [halfDiff_edgeCut,hh,↓reduceIte,abs_zero,Finset.sum_const_zero] using hA

theorem local_signed_base_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (hp : ∑x,P x=1)
    (E : Set (Spin n)) (G : Observables n) (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hG : ∀x,x∉E→G x=0)
    (hD : ∀x∈flipNeighborhood E,∑i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀x∈flipNeighborhood E,∑i,(U x i)^2≤B^2) :
    |∑x,P x*G x*∑i,(spin x i-conditionalMean P x i)*U x i|≤
      (2*B+5*A)*starNorm P G := by
  classical
  have hh:=signed_base_star P hP hp G (edgeCut E U) hA hB (edgeCut_diagonal E U hA hD)
    (edgeCut_size E U hU)
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx:x∈E
  · simp [edgeCut,hx]
  · simp [hG x hx]

end SKGapCutoff.Static

end
end

end OAI
