import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.HermitianMat

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

def invH (A : H d) : H d := ⟨(A : Mat d)⁻¹, A.property.inv⟩

@[simp] theorem invH_val (A : H d) : (invH A : Mat d) = (A : Mat d)⁻¹ := rfl

def pd (d : ℕ) : Set (H d) := {A | (A : Mat d).PosDef}

lemma pd_smul {A : H d} (hA : A ∈ pd d) {a : ℝ} (ha : 0 < a) :
    a • A ∈ pd d := by
  change ((a : ℂ) • (A : Mat d)).PosDef
  exact hA.smul (by exact_mod_cast ha)

lemma psd_smul {A : H d} (hA : A ∈ psdCone d) {a : ℝ} (ha : 0 ≤ a) :
    a • A ∈ psdCone d := by
  change ((a : ℂ) • (A : Mat d)).PosSemidef
  exact hA.smul (by exact_mod_cast ha)

lemma convex_pd : Convex ℝ (pd d) := by
  intro A hA B hB a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa [show b = 1 by linarith] using hB
  · exact (pd_smul hA ha').add_posSemidef (psd_smul hB.posSemidef hb)

theorem inverse_convex {A B : H d} (hA : A ∈ pd d) (hB : B ∈ pd d)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • invH A + b • invH B - invH (a • A + b • B) ∈ psdCone d := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  let : Invertible (B : Mat d) := hB.isUnit.invertible
  have hc : a • A + b • B ∈ pd d := convex_pd hA hB ha hb hab
  let : Invertible ((a • A + b • B : H d) : Mat d) := hc.isUnit.invertible
  have hAb : (fromBlocks (A : Mat d) 1 1 (A : Mat d)⁻¹).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ 1 (A : Mat d)⁻¹ hA).mpr
      (by simpa using (Matrix.PosSemidef.zero (n := Fin d) (R := ℂ)) : ((A : Mat d)⁻¹ - (1 : Mat d)ᴴ * (A : Mat d)⁻¹ * 1).PosSemidef)
  have hBb : (fromBlocks (B : Mat d) 1 1 (B : Mat d)⁻¹).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ 1 (B : Mat d)⁻¹ hB).mpr
      (by simpa using (Matrix.PosSemidef.zero (n := Fin d) (R := ℂ)) : ((B : Mat d)⁻¹ - (1 : Mat d)ᴴ * (B : Mat d)⁻¹ * 1).PosSemidef)
  have hs := (hAb.smul (a := (a : ℂ)) (by exact_mod_cast ha)).add
    (hBb.smul (a := (b : ℂ)) (by exact_mod_cast hb))
  have hoff : (a : ℂ) • (1 : Mat d) + (b : ℂ) • (1 : Mat d) = 1 := by
    rw [← add_smul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_smul]
  rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, hoff] at hs
  have he := (Matrix.PosDef.fromBlocks₁₁ 1
    ((a : ℂ) • (A : Mat d)⁻¹ + (b : ℂ) • (B : Mat d)⁻¹) hc).mp (by simpa using hs)
  simpa using he

lemma isClosed_lowerBound (a : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A} := by
  change IsClosed ((fun A : H d => A - a • one) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_id.sub continuous_const)

lemma isClosed_upperBound (b : ℝ) :
    IsClosed {A : H d | A ≤ (b • one : H d)} := by
  change IsClosed ((fun A : H d => b • one - A) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_const.sub continuous_id)

lemma isClosed_orderBox (a b : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} :=
  (isClosed_lowerBound a).inter (isClosed_upperBound b)

open scoped Matrix.Norms.L2Operator

theorem inverse_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨u, rfl⟩ := hA.isUnit
  obtain ⟨v, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hab

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

lemma scalar_inv (a : ℝ) : (((a : ℂ) • (1 : Mat d))⁻¹) = (a⁻¹ : ℂ) • (1 : Mat d) := by
  by_cases ha : a = 0
  · simp [ha]
  · let : Invertible (a : ℂ) := invertibleOfNonzero (by exact_mod_cast ha)
    rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv]
    simp

theorem le_trace_smul_one {A : Mat d} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • (1 : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have heig (i : Fin d) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hc : 0 ≤ cfc (fun x : ℝ => A.trace.re - x) A := by
    apply (cfc_nonneg_iff _ A).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hA.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact sub_nonneg.mpr (heig i)
  rw [cfc_sub (fun _ : ℝ => A.trace.re) (fun x : ℝ => x),
    cfc_const _ A hA.isHermitian.isSelfAdjoint] at hc
  change 0 ≤ (algebraMap ℝ (Mat d)) A.trace.re - cfc (id : ℝ → ℝ) A at hc
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint] at hc
  have hmap : (algebraMap ℝ (Mat d)) A.trace.re = (A.trace.re : ℂ) • (1 : Mat d) := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply]
  rw [hmap] at hc
  exact sub_nonneg.mp hc

theorem isCompact_orderBox (a b : ℝ) :
    IsCompact {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} := by
  let : CStarAlgebra (Mat d) := {}
  let : ProperSpace (H d) := FiniteDimensional.proper ℝ (H d)
  apply (isCompact_closedBall (a • one : H d) ‖(b-a) • (one : H d)‖).of_isClosed_subset
    (isClosed_orderBox a b)
  intro A hA
  rw [Metric.mem_closedBall]
  change dist (A : Mat d) (a • (1 : Mat d)) ≤ ‖(b-a) • (1 : Mat d)‖
  rw [dist_eq_norm]
  have h₁ : a • (1 : Mat d) ≤ (A : Mat d) := hA.1
  have h₂ : (A : Mat d) ≤ b • (1 : Mat d) := hA.2
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg _ (sub_nonneg.mpr h₁)
  have hh := sub_le_sub_right h₂ (a • (1 : Mat d))
  convert hh using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Complex.ofReal_sub]
  ring

end
end CurrentKS.Hermitian

end OAI
