import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Point

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def schurBlock (T X : H d) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Matrix.fromBlocks (T : Mat d) 1 1 (X : Mat d)

lemma schurBlock_psd_iff (T X : H d) (hX : X ∈ pd d) :
    (schurBlock T X).PosSemidef ↔ invH X ≤ T := by
  let : Invertible (X : Mat d) := hX.isUnit.invertible
  have hh := Matrix.PosDef.fromBlocks₂₂ (T : Mat d) (1 : Mat d) hX
  simp only [Matrix.conjTranspose_one,one_mul,mul_one] at hh
  change (schurBlock T X).PosSemidef ↔ ((T-invH X : H d) : Mat d).PosSemidef at hh
  rw [← mem_psdCone,mem_psd_iff_nonneg,sub_nonneg] at hh
  exact hh

def valueBlock₁ (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :=
  schurBlock (z.1 • (Hermitian.one : H d)-S-η z.2.2) z.2.1

def valueBlock₂ (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :=
  schurBlock (z.1 • (Hermitian.one : H d)+S-η z.2.1) z.2.2

lemma valueBlocks_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d)
    (hX : z.2.1 ∈ pd d) (hY : z.2.2 ∈ pd d) :
    (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef ↔ z ∈ feasible S η := by
  rw [valueBlock₁,valueBlock₂,schurBlock_psd_iff _ _ hX,schurBlock_psd_iff _ _ hY,feasible_iff]
  have h₁ : (invH z.2.1 ≤ z.1 • (Hermitian.one : H d)-S-η z.2.2) ↔
      invH z.2.1+S+η z.2.2 ≤ z.1 • (Hermitian.one : H d) := by
    rw [le_sub_iff_add_le,le_sub_iff_add_le]
    rw [show invH z.2.1+η z.2.2+S = invH z.2.1+S+η z.2.2 by module]
  have h₂ : (invH z.2.2 ≤ z.1 • (Hermitian.one : H d)+S-η z.2.1) ↔
      invH z.2.2-S+η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
    rw [le_sub_iff_add_le,← sub_le_iff_le_add]
    rw [show invH z.2.2+η z.2.1-S = invH z.2.2-S+η z.2.1 by module]
  rw [h₁,h₂]
  exact ⟨fun h => ⟨hX,hY,h.1,h.2⟩,fun h => ⟨h.2.2.1,h.2.2.2⟩⟩

def oracleBox (ε : ℝ) (z : Point d) : Prop :=
  z.1 ∈ Icc 0 100 ∧
  ((1/400 : ℝ) • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (200/ε) • Hermitian.one) ∧
  ((1/400 : ℝ) • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (200/ε) • Hermitian.one)

def valueSpectrahedron (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) : Set (Point d) :=
  {z | oracleBox ε z ∧ (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef}

lemma mem_valueSpectrahedron (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ valueSpectrahedron ε S η ↔ oracleBox ε z ∧ z ∈ feasible S η := by
  constructor
  · rintro ⟨hb,h₁,h₂⟩
    exact ⟨hb,(valueBlocks_iff S η z
      (pd_of_lower (by norm_num : (0:ℝ)<1/400) hb.2.1.1)
      (pd_of_lower (by norm_num : (0:ℝ)<1/400) hb.2.2.1)).mp ⟨h₁,h₂⟩⟩
  · rintro ⟨hb,hz⟩
    obtain ⟨hX,hY,_,_⟩ := (feasible_iff S η z).mp hz
    exact ⟨hb,(valueBlocks_iff S η z hX hY).mpr hz⟩

lemma sublevel_oracleBox [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hS₁ : -(100:ℝ) • (Hermitian.one : H d) ≤ S)
    (hS₂ : S ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible S η) (hf : objective ε z ≤ 100) : oracleBox ε z := by
  obtain ⟨ht,hX,hY⟩ := sublevel_box S η hη hε (show (0:ℝ)<100 by norm_num) hS₁ hS₂ hz hf
  have hl : (1/400 : ℝ) • (Hermitian.one : H d) ≤ (2*100:ℝ)⁻¹ • Hermitian.one :=
    scalar_one_mono (by norm_num)
  have hu : (100/ε : ℝ) • (Hermitian.one : H d) ≤ (200/ε) • Hermitian.one :=
    scalar_one_mono (div_le_div_of_nonneg_right (by norm_num) hε.le)
  exact ⟨ht,⟨hl.trans hX.1,hX.2.trans hu⟩,⟨hl.trans hY.1,hY.2.trans hu⟩⟩

end
end CurrentKS.Variational

end OAI
