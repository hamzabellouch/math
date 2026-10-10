import OAI.Analysis.Mahler.SpecialJacobian
import OAI.Analysis.Mahler.FiniteStripReduction

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set Filter Finset MeasureTheory
open scoped Topology ENNReal
open MahlerConformal
variable {n N : ℕ}

/-- Real determinant of the actual holomorphic derivative's Hermitian Gram matrix. -/
noncomputable def specialGramDet (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) : ℝ :=
  ((specialJacobianMatrix A m z).conjTranspose * specialJacobianMatrix A m z).det.re

lemma specialGramDet_eq_stripHessianDet (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ}
    (hm : 1 ≤ m) (z : Fin n → ℂ) :
    specialGramDet A m z = stripHessianDet A m (complexToReal z) := by
  unfold specialGramDet
  rw [specialJacobian_gram A hm z]
  have hd := (algebraMap ℝ ℂ).map_det
    (weightedGram A (fun j => hessianWeight m (inverseF (complexRow A j z))
      (deriv inverseF (complexRow A j z))))
  have hd' := congrArg Complex.re hd.symm
  simpa only [stripHessianDet,complexRow_eq_stripCoordinate,Complex.ofReal_re] using! hd'

noncomputable def specialSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) : Set (Fin n → ℂ) :=
  {z | z ∈ complexStripDomain A ∧ specialTau A m z < 1}

lemma specialSublevel_eq_preimage (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    specialSublevel A m = complexToReal ⁻¹' stripSublevel A m := by
  ext z
  simp only [specialSublevel,stripSublevel,complexStripDomain_eq_preimage,
    specialTau_eq_stripTau,mem_ofPred_eq,Set.mem_preimage,mem_inter_iff]

lemma measurableEmbedding_complexToReal : MeasurableEmbedding (complexToReal (n := n)) :=
  complexRealEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding

theorem specialGram_integral_eq (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (∫⁻ z in specialSublevel A m, ENNReal.ofReal (specialGramDet A m z)) =
      ∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z) := by
  rw [specialSublevel_eq_preimage]
  simp_rw [specialGramDet_eq_stripHessianDet A hm]
  simpa using! (volume_preserving_complexToReal (n := n)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_complexToReal (n := n))
    (fun z => ENNReal.ofReal (stripHessianDet A m z)) (stripSublevel A m)

/-- The n! factor converts the complex mass inequality into
the mass premise for the finite-strip reduction. -/
theorem stripMassBound_of_special_gram_mass (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m)
    (hmass : ENNReal.ofReal ((Real.pi*(m : ℝ))^n) ≤
      ∫⁻ z in specialSublevel A m, ENNReal.ofReal ((Nat.factorial n : ℝ)*specialGramDet A m z)) :
    StripMassBound A m := by
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  have hI : (∫⁻ z in specialSublevel A m, ENNReal.ofReal ((Nat.factorial n : ℝ)*specialGramDet A m z)) =
      ENNReal.ofReal (Nat.factorial n : ℝ)*
        (∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z)) := by
    simp_rw [ENNReal.ofReal_mul hf.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,specialGram_integral_eq A (by omega)]
  rw [hI] at hmass
  apply (ENNReal.mul_le_mul_iff_right (show ENNReal.ofReal (Nat.factorial n : ℝ) ≠ 0 by positivity)
    ENNReal.ofReal_ne_top).mp
  rw [← ENNReal.ofReal_mul hf.le]
  have he : (Nat.factorial n : ℝ)*((Real.pi*(m : ℝ))^n/(Nat.factorial n : ℝ)) =
      (Real.pi*(m : ℝ))^n := by field_simp
  rw [he]
  exact hmass

end SymmetricMahler

end OAI
