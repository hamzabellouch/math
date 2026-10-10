import OAI.NumberTheory.DirichletL.Foundation

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondOuterBall (Y E X₁ X₂ H : ℝ) : Finset Eis :=
  secondFrequencyCutoff (Y / (E * X₁ * X₂)) H

theorem secondOuterBall_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (Y E X₁ X₂ H : ℝ)
    (hY : 0 < Y) (hE : 0 < E) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (e : Eis) (he : e ≠ 0) (heE : ‖eisEmbedding e‖^2 ≤ E)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : primeProductNorm p S ≤ X₁) (hT : primeProductNorm p T ≤ X₂)
    (k : Eis) (hk : k ∉ secondOuterBall Y E X₁ X₂ H) :
    H ≤ (Y / (‖eisEmbedding e‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have hs : 0 < Y/(E*X₁*X₂) := by positivity
  have hn : 0 < ‖eisEmbedding e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  have hprod : ‖eisEmbedding e‖^2 * primeProductNorm p S * primeProductNorm p T ≤ E*X₁*X₂ := by
    exact mul_le_mul (mul_le_mul heE hS (primeProductNorm_pos p hp S).le hE.le)
      hT (primeProductNorm_pos p hp T).le (mul_pos hE hX₁).le
  have hb : Y/(E*X₁*X₂) ≤
      Y/(‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2) := by
    rw [active_norm_sq_disjoint p S T hd]
    apply div_le_div_of_nonneg_left hY.le
    · exact mul_pos hn (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T))
    · simpa only [mul_assoc] using hprod
  exact (outside_secondFrequencyCutoff _ H hs k hk).le.trans
    (mul_le_mul_of_nonneg_right hb (sq_nonneg _))

theorem secondOuterBall_remainder {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y E X₁ X₂ H : ℝ),
      0 < Y → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (e : Eis), e ≠ 0 → ‖eisEmbedding e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      ‖∑' k : {k : Eis // k ∉ secondOuterBall Y E X₁ X₂ H},
        secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro W Y E X₁ X₂ H hY hE hX₁ hX₂ hH e he heE S T hd hS hT
  exact hb S T e he W Y H hY hH (secondOuterBall Y E X₁ X₂ H)
    (fun k hk => secondOuterBall_raw_tail p hp Y E X₁ X₂ H hY hE hX₁ hX₂ e he heE S T hd hS hT k hk)

end
end SevenEighths.InverseMoment

end OAI
