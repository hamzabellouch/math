import OAI.NumberTheory.CubicMoment.Decomposition.StoppedKernelRange

namespace OAI

/-! Exact independent sharp side dyads for the stopped matrices. The
squarefree product envelope supplies the side support; no coprimality
restriction or boundary contribution is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedFactorSupport (P : Finset Eisenstein) (X : ℝ) : Finset Eisenstein :=
  P.filter (fun a => Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X)

lemma centralProduct_factor_support {X : ℝ} {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : a*b ∈ centralProductEnvelope X) :
    (Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X) ∧
      (Squarefree b ∧ norm b ≤ Real.exp primeProductWeights.radius*X) := by
  have hs := centralProductEnvelope_spec hab
  have hn := primary_ne_zero (primary_mul ha hb)
  exact ⟨⟨hs.2.1.of_mul_left,
    (norm_le_of_dvd hn (dvd_mul_right a b)).trans hs.2.2⟩,
    ⟨hs.2.1.of_mul_right,(norm_le_of_dvd hn (dvd_mul_left b a)).trans hs.2.2⟩⟩

lemma stopped_matrix_side_support (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β K : Eisenstein → ℂ) (X : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*
      (if a*b ∈ centralProductEnvelope X then K (a*b) else 0)) =
    ∑ a ∈ stoppedFactorSupport P X, ∑ b ∈ stoppedFactorSupport Q X,
      α a*β b*(if a*b ∈ centralProductEnvelope X then K (a*b) else 0) := by
  unfold stoppedFactorSupport
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hsa : Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X
  · rw [ite_eq_left hsa]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hsb : Squarefree b ∧ norm b ≤ Real.exp primeProductWeights.radius*X
    · rw [ite_eq_left hsb]
    · have hz : a*b ∉ centralProductEnvelope X :=
        fun hab => hsb (centralProduct_factor_support (hP a ha) (hQ b hb) hab).2
      simp only [ite_eq_right hsb,ite_eq_right hz,mul_zero]
  · rw [ite_eq_right hsa]
    apply Finset.sum_eq_zero
    intro b hb
    have hz : a*b ∉ centralProductEnvelope X :=
      fun hab => hsa (centralProduct_factor_support (hP a ha) (hQ b hb) hab).1
    simp only [ite_eq_right hz,mul_zero]

lemma finite_matrix_stopped_dyads (P Q : Finset Eisenstein)
    (F : Eisenstein → Eisenstein → ℂ) :
    (∑ a ∈ P, ∑ b ∈ Q, F a b) =
      ∑ j ∈ P.image stoppedNormDyadIndex, ∑ k ∈ Q.image stoppedNormDyadIndex,
        ∑ a ∈ stoppedNormDyad P j, ∑ b ∈ stoppedNormDyad Q k, F a b := by
  rw [stoppedNormDyad_partition P]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ a ∈ stoppedNormDyad P j, ∑ k ∈ Q.image stoppedNormDyadIndex,
        ∑ b ∈ stoppedNormDyad Q k, F a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact stoppedNormDyad_partition Q (F a)
    _ = _ := Finset.sum_comm

lemma stopped_matrix_dyadic (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β K : Eisenstein → ℂ) (X : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*
      (if a*b ∈ centralProductEnvelope X then K (a*b) else 0)) =
      ∑ j ∈ (stoppedFactorSupport P X).image stoppedNormDyadIndex,
        ∑ k ∈ (stoppedFactorSupport Q X).image stoppedNormDyadIndex,
          ∑ a ∈ stoppedNormDyad (stoppedFactorSupport P X) j,
            ∑ b ∈ stoppedNormDyad (stoppedFactorSupport Q X) k,
              α a*β b*(if a*b ∈ centralProductEnvelope X then K (a*b) else 0) := by
  rw [stopped_matrix_side_support P Q hP hQ α β K X]
  exact finite_matrix_stopped_dyads _ _ _

lemma stoppedFactorSupport_log_count :
    ∃ D : ℝ, 0 < D ∧ ∀ (X : ℝ), 1 ≤ X → ∀ P : Finset Eisenstein,
      (((stoppedFactorSupport P X).image stoppedNormDyadIndex).card:ℝ) ≤
        D*(1+Real.log X) := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  let R := primeProductWeights.radius
  refine ⟨C*(1+R),by dsimp [R]; positivity [primeProductWeights.radius_nonneg],?_⟩
  intro X hX P
  have hF : 1 ≤ Real.exp R*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have hc := stoppedNormDyad_count (stoppedFactorSupport P X)
    (fun n hn => (Finset.mem_filter.mp hn).2.2)
  have hm : Nat.log 2 ⌊Real.exp R*X⌋₊+1 ≤ Nat.log 2 ⌊3*(Real.exp R*X)⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by nlinarith))) 1
  calc
    _ ≤ ((Nat.log 2 ⌊3*(Real.exp R*X)⌋₊+1:ℕ):ℝ) := Nat.cast_le.mpr (hc.trans hm)
    _ ≤ C*(1+Real.log (Real.exp R*X)) := hcount _ hF
    _ ≤ C*(1+R)*(1+Real.log X) := by
      rw [Real.log_mul (Real.exp_pos _).ne' (zero_lt_one.trans_le hX).ne',Real.log_exp]
      have hR : 0 ≤ R := primeProductWeights.radius_nonneg
      have hL := Real.log_nonneg hX
      calc
        _ ≤ C*((1+R)*(1+Real.log X)) := mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg hR hL]) hC.le
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
