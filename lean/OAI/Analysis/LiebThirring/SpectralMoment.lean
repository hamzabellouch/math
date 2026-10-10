import OAI.Analysis.LiebThirring.SchrodingerOperator

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology ENNReal

def IsOperatorEigenfunction (A : L2C →ₗ.[ℂ] L2C) (e : ℝ) (f : L2C) : Prop :=
  ∃ hf : f ∈ A.domain, A ⟨f,hf⟩ = (e:ℂ) • f

/-- The entire negative eigenvalue moment, with multiplicity, of an actual
partially defined operator. Energies here are the eigenvalues `e`, not scales. -/
def eigenvalueMoment (γ : ℝ) (A : L2C →ₗ.[ℂ] L2C) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (f : Fin N → L2C) (e : Fin N → ℝ)
    (_ : Orthonormal ℂ f) (_ : ∀ i, e i < 0 ∧ IsOperatorEigenfunction A (e i) (f i)),
      ∑ i, (ENNReal.ofReal |e i|)^γ

lemma energy_weight (k γ : ℝ) (hk : 0 ≤ k) :
    (ENNReal.ofReal |-(k^2)|)^γ = (ENNReal.ofReal k)^(2*γ) := by
  rw [abs_neg,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_pow hk]
  simpa only [Nat.cast_ofNat] using (ENNReal.rpow_natCast_mul (ENNReal.ofReal k) 2 γ).symm

lemma negativeMoment_eq_eigenvalueMoment {W : ℝ → ℝ} {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsAssociated W A) (γ : ℝ) : negativeMoment γ W = eigenvalueMoment γ A := by
  classical
  apply le_antisymm
  · unfold negativeMoment
    refine iSup_le (fun N ↦ iSup_le (fun u ↦ iSup_le (fun k ↦
      iSup_le (fun hu ↦ iSup_le (fun hk ↦ ?_)))))
    let f := fun i ↦ (u i).val_memLp.toLp (u i).val
    have hf : Orthonormal ℂ f := orthonormal_iff_ite.mpr (fun i j ↦ by
      simpa only [f,l2Pairing_eq_inner] using hu i j)
    have he : ∀ i, -(k i)^2 < 0 ∧ IsOperatorEigenfunction A (-(k i)^2) (f i) := by
      intro i
      refine ⟨neg_neg_of_pos (sq_pos_of_pos (hk i).1),?_⟩
      simpa only [IsOperatorEigenfunction,f,Complex.ofReal_neg] using
        ((negativeEigenfunction_iff_operator hA (k i) (u i)).mp (hk i)).2
    have hle : (∑ i, (ENNReal.ofReal |-(k i)^2|)^γ) ≤ eigenvalueMoment γ A :=
      le_iSup_of_le N (le_iSup_of_le f (le_iSup_of_le (fun i ↦ -(k i)^2)
        (le_iSup_of_le hf (le_iSup_of_le he le_rfl))))
    simpa only [energy_weight _ γ ((hk _).1.le)] using hle
  · unfold eigenvalueMoment
    refine iSup_le (fun N ↦ iSup_le (fun f ↦ iSup_le (fun e ↦
      iSup_le (fun hf ↦ iSup_le (fun he ↦ ?_)))))
    have hex : ∀ i, ∃ u : H1, u.val_memLp.toLp u.val = f i ∧
        ∀ v : H1, schrodingerForm W v u = inner ℂ (v.val_memLp.toLp v.val) ((e i : ℂ) • f i) := by
      intro i
      exact (hA _ _).mp (he i).2
    choose u hu hq using hex
    let k := fun i ↦ Real.sqrt (-e i)
    have hkp : ∀ i, 0 < k i := fun i ↦ Real.sqrt_pos.mpr (neg_pos.mpr (he i).1)
    have hks : ∀ i, -(k i)^2 = e i := fun i ↦ by
      rw [show (k i)^2 = -e i from Real.sq_sqrt (le_of_lt (neg_pos.mpr (he i).1)),neg_neg]
    have hne : ∀ i, IsNegativeEigenfunction W (k i) (u i) := by
      intro i
      rw [negativeEigenfunction_iff_operator hA]
      refine ⟨hkp i,?_⟩
      have hc : -(↑((k i)^2):ℂ) = (e i:ℂ) := by exact_mod_cast hks i
      simpa only [IsOperatorEigenfunction,hc,hu i] using (he i).2
    have hon : IsOrthonormalFamily u := by
      intro i j
      rw [l2Pairing_eq_inner,hu i,hu j]
      exact orthonormal_iff_ite.mp hf i j
    have hle : (∑ i, (ENNReal.ofReal (k i))^(2*γ)) ≤ negativeMoment γ W :=
      le_iSup_of_le N (le_iSup_of_le u (le_iSup_of_le k
        (le_iSup_of_le hon (le_iSup_of_le hne le_rfl))))
    calc
      _ = ∑ i, (ENNReal.ofReal (k i))^(2*γ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hks i,energy_weight _ _ (hkp i).le]
      _ ≤ _ := hle

end SharpLiebThirring.OperatorProof

end

end OAI
