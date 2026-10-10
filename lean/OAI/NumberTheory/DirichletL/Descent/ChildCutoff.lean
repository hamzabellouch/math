import OAI.NumberTheory.DirichletL.Descent.PoissonTails

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def childFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (secondFrequencyCutoff (‖eisEmbedding a‖^2) R).filter
    (fun k => ‖eisEmbedding (a*k)‖^2 ≤ R)

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma outside_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis)
    (hk : k ∉ childFrequencyBall a R) : R < ‖eisEmbedding (a*k)‖^2 :=
  lt_of_not_ge (fun h => hk ((mem_childFrequencyBall a ha R k).mpr h))

def nonzeroChildFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (childFrequencyBall a R).erase 0

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

lemma nonzeroChildFrequencyBall_empty (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : R < 1) :
    nonzeroChildFrequencyBall a R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hm := (mem_nonzeroChildFrequencyBall a ha R k).mp hk
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm
  exact (not_le_of_gt hR) ((EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq
    (a*k) (mul_ne_zero ha hk0)).trans hm.2)

def childOuterRadius (Y A E X₁ X₂ H : ℝ) : ℝ := A*E*X₁*X₂*H/Y

theorem childFrequencyBall_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (Y A E X₁ X₂ H : ℝ)
    (hY : 0 < Y) (hA : 0 < A) (hE : 0 < E)
    (hX₁ : 0 < X₁) (_hX₂ : 0 < X₂) (hH : 0 ≤ H)
    (a e : Eis) (ha : a ≠ 0) (he : e ≠ 0)
    (haA : ‖eisEmbedding a‖^2 ≤ A) (heE : ‖eisEmbedding e‖^2 ≤ E)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : primeProductNorm p S ≤ X₁) (hT : primeProductNorm p T ≤ X₂)
    (k : Eis) (hk : k ∉ childFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)) :
    H ≤ (Y / (‖eisEmbedding e‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have haN : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  have heN : 0 < ‖eisEmbedding e‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  have hden : ‖eisEmbedding a‖^2 * ‖eisEmbedding e‖^2 *
      primeProductNorm p S * primeProductNorm p T ≤ A*E*X₁*X₂ := by
    exact mul_le_mul (mul_le_mul (mul_le_mul haA heE heN.le hA.le)
      hS (primeProductNorm_pos p hp S).le (mul_pos hA hE).le)
      hT (primeProductNorm_pos p hp T).le (by positivity)
  have hchild := (outside_childFrequencyBall a ha _ k hk).le
  simp only [map_mul,norm_mul,mul_pow,childOuterRadius] at hchild
  have hbound : H * (‖eisEmbedding a‖^2 * ‖eisEmbedding e‖^2 *
      primeProductNorm p S * primeProductNorm p T) ≤
      Y * (‖eisEmbedding a‖^2 * ‖eisEmbedding k‖^2) := by
    calc
      _ ≤ H*(A*E*X₁*X₂) := mul_le_mul_of_nonneg_left hden hH
      _ ≤ _ := by nlinarith [(div_le_iff₀ hY).mp hchild]
  have hcancel : H * (‖eisEmbedding e‖^2 * primeProductNorm p S *
      primeProductNorm p T) ≤ Y * ‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ haN).mp
    nlinarith [hbound]
  rw [active_norm_sq_disjoint p S T hd]
  have hdpos : 0 < ‖eisEmbedding e‖^2 * (primeProductNorm p S * primeProductNorm p T) :=
    mul_pos heN (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T))
  rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
  simpa only [mul_assoc] using hcancel

theorem childFrequencyBall_remainder {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y A E X₁ X₂ H : ℝ),
      0 < Y → 0 < A → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (a e : Eis), a ≠ 0 → e ≠ 0 →
      ‖eisEmbedding a‖^2 ≤ A → ‖eisEmbedding e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      ‖∑' k : {k : Eis // k ∉ childFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)},
        secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^order)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc order
  refine ⟨s,C,hC,?_⟩
  intro W Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH a e ha he haA heE S T hd hS hT
  exact hb S T e he W Y H hY hH _
    (fun k hk => childFrequencyBall_raw_tail p hp Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH
      a e ha he haA heE S T hd hS hT k hk)

theorem nonzeroChildFrequencyBall_absolute_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y A E X₁ X₂ H : ℝ),
      0 < Y → 0 < A → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (a e : Eis), a ≠ 0 → e ≠ 0 →
      ‖eisEmbedding a‖^2 ≤ A → ‖eisEmbedding e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : Eis // k ≠ 0 ∧ k ∉ nonzeroChildFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^order)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_tail p hp hg hinj hc order
  refine ⟨s,C,hC,?_⟩
  intro W Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH a e ha he haA heE S T hd hS hT
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set Eis := {k | k ≠ 0 ∧ k ∉ nonzeroChildFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)}
  let large : Set Eis := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  have hmap : ∀ k : small, k.val ∈ large := by
    intro k
    apply childFrequencyBall_raw_tail p hp Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH
      a e ha he haA heE S T hd hS hT k.val
    intro hk
    exact k.property.2 (Finset.mem_erase.mpr ⟨k.property.1,hk⟩)
  let f : small → large := fun k => ⟨k.val,hmap k⟩
  have hi : Function.Injective f := by
    intro x y h; exact Subtype.ext (congrArg (fun z : large => z.val) h)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

end
end SevenEighths.InverseMoment

end OAI
