import Mathlib
import OAI.Analysis.Commutator.DyadicSpectral

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalized_positive_general {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {T : A} (hT : IsSelfAdjoint T) :
    0≤(2*‖T‖+1)⁻¹ • (T+‖T‖ • (1 : A)) ∧
    (2*‖T‖+1)⁻¹ • (T+‖T‖ • (1 : A))≤1 := by
  have hn : 0<2*‖T‖+1 := by positivity
  have hlo : -(‖T‖ • (1 : A))≤T := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hT.neg_algebraMap_norm_le_self
  have hhi : T≤‖T‖ • (1 : A) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hT.le_algebraMap_norm_self
  have hpos : 0≤T+‖T‖ • (1 : A) := by
    simpa only [neg_add_cancel] using _root_.add_le_add_left hlo (‖T‖ • (1 : A))
  refine ⟨smul_nonneg (inv_nonneg.mpr hn.le) hpos,?_⟩
  have hbound : T+‖T‖ • (1 : A)≤(2*‖T‖+1) • (1 : A) := by
    calc
      T+‖T‖ • (1 : A)≤‖T‖ • (1 : A)+‖T‖ • (1 : A) := _root_.add_le_add_left hhi _
      _=(2*‖T‖) • (1 : A) := by module
      _≤(2*‖T‖+1) • (1 : A) := smul_le_smul_of_nonneg_right (by linarith) zero_le_one
  have h := smul_le_smul_of_nonneg_left hbound (inv_nonneg.mpr hn.le)
  simpa only [smul_smul,inv_mul_cancel₀ hn.ne',one_smul] using h

theorem exists_selfadjoint_spectral_sum (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hTM : T∈M) (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, ∃ p : Fin n → H →L[ℂ] H, ∃ c : Fin n → ℝ,
      (∀ i,p i∈M ∧ IsStarProjection (p i)) ∧
      (∀ i j,Commute (p i) (p j)) ∧ ‖T-∑ i,c i • p i‖<ε := by
  classical
  let r : ℝ := 2*‖T‖+1
  have hr : 0<r := by dsimp [r]; positivity
  let S : H →L[ℂ] H := r⁻¹ • (T+‖T‖ • (1 : H →L[ℂ] H))
  have hh : ‖T‖ • (1 : H →L[ℂ] H)∈M :=
    (M.toSubalgebra.restrictScalars ℝ).smul_mem M.one_mem ‖T‖
  have hSM : S∈M :=
    (M.toSubalgebra.restrictScalars ℝ).smul_mem (M.add_mem hTM hh) r⁻¹
  have hb := normalized_positive_general hT
  obtain ⟨n,p,c,hp,hc,he⟩ := exists_positive_spectral_sum M hSM hb.1 hb.2 (div_pos hε hr)
  let q : Fin (n+1) → H →L[ℂ] H := Fin.cons 1 p
  let d : Fin (n+1) → ℝ := Fin.cons (-‖T‖) (fun i => r*c i)
  refine ⟨n+1,q,d,?_,?_,?_⟩
  · intro i
    refine Fin.cases ⟨M.one_mem,IsStarProjection.one _⟩ (fun j => hp j) i
  · intro i j
    refine Fin.cases (Commute.one_left _) (fun i => ?_) i
    exact Fin.cases (Commute.one_right _) (fun j => hc i j) j
  · have heq : T-∑ i,d i • q i=r • (S-∑ i,c i • p i) := by
      rw [Fin.sum_univ_succ]
      simp only [d,q,Fin.cons_zero,Fin.cons_succ,smul_sub,Finset.smul_sum,smul_smul]
      have hid : r • S=T+‖T‖ • (1 : H →L[ℂ] H) := by
        dsimp [S]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
      rw [hid]
      module
    rw [heq,norm_smul,Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left he hr).trans_eq (mul_div_cancel₀ ε hr.ne')

end Kadison.Polar

end

end
end

end OAI
