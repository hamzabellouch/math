import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.FilterStationarity
import OAI.MathematicalPhysics.PEPSFilters.Bipartite

namespace OAI

/-! Conjugation across disjoint regions and reduction to one crossing. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

lemma liftLocal_commute_complement (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (C : Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ) :
    Commute (liftLocal A B) (liftLocal Aᶜ C) := by
  change liftLocal A B * liftLocal Aᶜ C = liftLocal Aᶜ C * liftLocal A B
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ)).injective
  change asMap _ = asMap _
  apply ContinuousLinearMap.ext
  intro ψ
  rw [asMap_mul, asMap_mul]
  apply coefficientMatrix_injective A
  dsimp only
  rw [coefficientMatrix_asMap_liftLocal, coefficientMatrix_asMap_liftComplement,
    coefficientMatrix_asMap_liftComplement, coefficientMatrix_asMap_liftLocal, Matrix.mul_assoc]

lemma SupportedOn.commute_disjoint {A S : Finset (Vertex L)} {B C : Operator L q}
    (hB : SupportedOn B A) (hC : SupportedOn C S) (hAS : Disjoint A S) : Commute B C := by
  have hsub : S ⊆ Aᶜ := by
    intro x hx
    simpa only [Finset.mem_compl] using (Finset.disjoint_left.mp hAS · hx)
  obtain ⟨B, rfl⟩ := hB
  obtain ⟨C, rfl⟩ := hC.mono hsub
  exact liftLocal_commute_complement A B C

lemma conjugation_disjoint (A S : Finset (Vertex L))
    (F : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (hF : IsUnit F.det) (H : Operator L q) (hH : SupportedOn H S) (hAS : Disjoint A S) :
    liftLocal A F * H * liftLocal A F⁻¹ = H := by
  have hc : Commute (liftLocal A F) H := SupportedOn.commute_disjoint ⟨F, rfl⟩ hH hAS
  rw [hc.eq, Matrix.mul_assoc, ← liftLocal_mul, Matrix.mul_nonsing_inv F hF, liftLocal_one, Matrix.mul_one]

lemma conjugation_of_commute (A : Finset (Vertex L))
    (F : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (hF : IsUnit F.det) (H : Operator L q) (hc : Commute (liftLocal A F) H) :
    liftLocal A F * H * liftLocal A F⁻¹ = H := by
  rw [hc.eq, Matrix.mul_assoc, ← liftLocal_mul, Matrix.mul_nonsing_inv F hF,
    liftLocal_one, Matrix.mul_one]

lemma propagate_single_crossing {m : ℕ} (v : State L q)
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hc : ∀ j, Commute (F j).matrix (reducedDensity v (X j)))
    (H : Operator L q) (j : Fin m)
    (hbefore : ∀ k, k < j → Commute (liftLocal (X k) (F k).matrix) H)
    (hafter : ∀ k, j < k → SupportedOn H (X k)) :
    inner ℂ v (asMap (propagateConjugation
      (fun k => liftLocal (X k) (F k).matrix)
      (fun k => liftLocal (X k) (F k).matrix⁻¹) H) v) =
    inner ℂ v (asMap (liftLocal (X j) (F j).matrix * H *
      liftLocal (X j) (F j).matrix⁻¹) v) := by
  revert hbefore hafter
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hb ha
      rw [propagateConjugation]
      apply propagate_trace_strip v (fun k => X k.succ)
        (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h)) (fun k => F k.succ)
        (fun k => hdet k.succ) (fun k => hc k.succ)
      intro k
      have hsub : X 0 ⊆ X k.succ := hX (Fin.zero_le _)
      exact ((PolynomialPEPS.PinnedEntropy.SupportedOn.mul
        (PolynomialPEPS.PinnedEntropy.SupportedOn.mono
          (⟨_, rfl⟩ : SupportedOn (liftLocal (X 0) (F 0).matrix) (X 0)) hsub)
        (ha k.succ (Fin.succ_pos _))).mul
        (PolynomialPEPS.PinnedEntropy.SupportedOn.mono
          (⟨_, rfl⟩ : SupportedOn (liftLocal (X 0) (F 0).matrix⁻¹) (X 0)) hsub))
    · intro hb ha
      rw [propagateConjugation, conjugation_of_commute (X 0) (F 0).matrix (hdet 0) H
        (hb 0 (Fin.succ_pos _))]
      exact ih (fun k => X k.succ) (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h))
        (fun k => F k.succ) (fun k => hdet k.succ) (fun k => hc k.succ) j
        (fun k h => hb k.succ (Fin.succ_lt_succ_iff.mpr h))
        (fun k h => ha k.succ (Fin.succ_lt_succ_iff.mpr h))

lemma propagate_no_crossing {m : ℕ} (v : State L q)
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hc : ∀ j, Commute (F j).matrix (reducedDensity v (X j)))
    (H : Operator L q)
    (hclassify : ∀ k, Commute (liftLocal (X k) (F k).matrix) H ∨ SupportedOn H (X k)) :
    inner ℂ v (asMap (propagateConjugation
      (fun k => liftLocal (X k) (F k).matrix)
      (fun k => liftLocal (X k) (F k).matrix⁻¹) H) v) = inner ℂ v (asMap H v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases hclassify 0 with h | h
    · rw [propagateConjugation, conjugation_of_commute (X 0) (F 0).matrix (hdet 0) H h]
      exact ih (fun k => X k.succ) (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h))
        (fun k => F k.succ) (fun k => hdet k.succ) (fun k => hc k.succ)
        (fun k => hclassify k.succ)
    · exact propagate_trace_strip v X hX F hdet hc H
        (fun k => h.mono (hX (Fin.zero_le k)))

lemma transported_ground_equation {m : ℕ}
    (T I : Fin m → Operator L q) (hI : ∀ j, I j * T j = 1)
    (H : Operator L q) (Ω : State L q) (E : ℝ)
    (hΩ : asMap H Ω = (E : ℂ) • Ω) (z : ℂ) :
    asMap (propagateConjugation T I H) (z • matrixOutput T Ω) =
      (E : ℂ) • (z • matrixOutput T Ω) := by
  rw [map_smul, ← matrixOutput_propagate T I hI, hΩ, matrixOutput_smul, smul_comm z]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
