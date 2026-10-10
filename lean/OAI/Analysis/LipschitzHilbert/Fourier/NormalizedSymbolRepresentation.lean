import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolFamily

namespace OAI

/-! Exact Fourier separation on the bounded frequency windows used for
the annular packet decomposition. Constants precede both scale parameters. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolPoint_norm_le (X Y U : ℝ) :
    ‖symbolPoint X Y U‖≤|X|+|Y|+|U| := by
  have hs : ‖symbolPoint X Y U‖^2=X^2+Y^2+U^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, symbolPoint, Fin.sum_univ_succ]
    ring
  nlinarith only [hs, norm_nonneg (symbolPoint X Y U), abs_nonneg X,
    abs_nonneg Y, abs_nonneg U, sq_abs X, sq_abs Y, sq_abs U,
    mul_nonneg (abs_nonneg X) (abs_nonneg Y),
    mul_nonneg (abs_nonneg X) (abs_nonneg U),
    mul_nonneg (abs_nonneg Y) (abs_nonneg U)]

/-- A cutoff which is one wherever the windowed annular symbol can be nonzero. -/
theorem normalizedSchwartzSymbol_eq (psi : SchwartzMap ℝ ℂ)
    (A B c M R : ℝ) (hR : 0<R) (hc : 0<c)
    (hpsi : ∀ s : ℝ, M < |s| → psi s=0)
    (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R)
    (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=psi (X+(v+t*Y)*U) := by
  by_cases hzero : psi (X+(v+t*Y)*U)=0
  · rw [normalizedSchwartzSymbol_apply, hzero, zero_mul]
  · have hann : |X+(v+t*Y)*U|≤M := by
      by_contra h
      exact hzero (hpsi _ (lt_of_not_ge h))
    have hU : |U|≤(M+A)/c := by
      have h := normalized_selector_upper X (v+t*Y) U c (4*A) M hc hV
        (by nlinarith only [hX]) hann
      simpa only [mul_div_cancel_left₀ A (by norm_num : (4:ℝ)≠0)] using h
    apply normalizedSchwartzSymbol_one
    · exact (symbolPoint_norm_le X Y U).trans ((add_le_add (add_le_add hX hY) hU).trans hsize)
    · exact hp

def symbolRadius (A B c C M : ℝ) : ℝ := 1+A+B+(M+A)/c+C

theorem symbolRadius_pos (A B c C M : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hc : 0<c) (hC : 0≤C) (hM : 0≤M) : 0<symbolRadius A B c C M := by
  unfold symbolRadius
  positivity

/-- The coefficient and weight bounds are uniform over every vertical bin and
averaging scale satisfying the normalized annulus geometry. -/
theorem exists_normalized_symbol_representation (psi : SchwartzMap ℝ ℂ)
    (A B c C M : ℝ) (hA : 0≤A) (hB : 0≤B) (hc : 0<c) (hC : 0≤C) (hM : 0≤M)
    (hpsi : ∀ s : ℝ, M < |s| → psi s=0) (q : ℕ) :
    ∃ R : ℝ, ∃ hR : 0<R, ∃ D : ℝ, 0<D ∧
      (∀ v t : ℝ, ∀ nu : SymbolSpace, ∀ U : ℝ,
        ‖weightedSelector (normalizedSchwartzSymbol psi R hR v t) q nu U‖≤D*symbolWeight q nu) ∧
      (∀ v t X Y U : ℝ, |v|≤C → |t|≤1 → |X|≤A → |Y|≤B → c≤v+t*Y →
        psi (X+(v+t*Y)*U)=∫ nu : SymbolSpace,
          (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
            (symbolWeight q nu : ℂ)*
              weightedSelector (normalizedSchwartzSymbol psi R hR v t) q nu U) := by
  let R := symbolRadius A B c C M
  have hR : 0<R := symbolRadius_pos A B c C M hA hB hc hC hM
  obtain ⟨D,hD,hbound⟩ := normalizedSchwartzSymbol_uniform psi R hR q
  refine ⟨R,hR,D,hD,?_,?_⟩
  · intro v t nu U
    exact (weightedSelector_bound _ q nu U).trans
      (mul_le_mul_of_nonneg_right (hbound v t) (symbolWeight_pos q nu).le)
  · intro v t X Y U hv ht hX hY hV
    have hdiv : 0≤(M+A)/c := div_nonneg (add_nonneg hM hA) hc.le
    have hp : ‖(v,t)‖≤R := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      apply max_le
      · exact hv.trans (by dsimp [R,symbolRadius]; linarith only [hA,hB,hdiv])
      · exact ht.trans (by dsimp [R,symbolRadius]; linarith only [hA,hB,hdiv,hC])
    rw [← normalizedSchwartzSymbol_eq psi A B c M R hR hc hpsi
      (by dsimp [R,symbolRadius]; linarith only [hC]) v t X Y U hp hX hY hV]
    exact weighted_symbol_identity _ q X Y U

end LipschitzHilbert.PacketRepresentation

end

end OAI
