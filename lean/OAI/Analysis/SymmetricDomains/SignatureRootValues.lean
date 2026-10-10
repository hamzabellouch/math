import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

section
open QuadraticMap
open scoped Classical

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]

lemma sigPos_comp_le (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N) :
    sigPos (Q.comp f) ≤ sigPos Q := by
  obtain ⟨V,hV,hp⟩ := exists_finrank_eq_sigPos_and_posDef (Q.comp f)
  let g := f.domRestrict V
  have hg : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro v hv
      have he : f v = 0 := hv
      by_contra hn
      have hv0 : v ≠ 0 := by simpa using hn
      have hh := hp v hv0
      simp only [QuadraticMap.restrict_apply,QuadraticMap.comp_apply,he,map_zero] at hh
      exact lt_irrefl _ hh
    · exact bot_le
  let e := LinearEquiv.ofInjective g hg
  have hpos : (Q.restrict g.range).PosDef := by
    intro y hy
    obtain ⟨v,rfl⟩ := e.surjective y
    have hv : v ≠ 0 := by
      intro hv
      apply hy
      simp [hv]
    exact hp v hv
  rw [← hV, e.finrank_eq]
  exact le_sigPos_of_posDef Q hpos

lemma sigPos_comp_surjective (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N)
    (hf : Function.Surjective f) : sigPos (Q.comp f) = sigPos Q := by
  apply le_antisymm (sigPos_comp_le Q f)
  obtain ⟨g,hg⟩ := LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hf)
  have hh := sigPos_comp_le (Q.comp f) g
  have he : (Q.comp f).comp g = Q := by
    ext x
    simpa only [comp_apply,LinearMap.comp_apply,LinearMap.id_apply] using
      congrArg Q (LinearMap.congr_fun hg x)
  rwa [he] at hh

lemma sigNeg_comp_surjective (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N)
    (hf : Function.Surjective f) : sigNeg (Q.comp f) = sigNeg Q := by
  change sigPos (-(Q.comp f)) = sigPos (-Q)
  have he : -(Q.comp f) = (-Q).comp f := by ext; rfl
  rw [he]
  exact sigPos_comp_surjective (-Q) f hf

end

open QuadraticMap Finset
open scoped BigOperators Classical

noncomputable def signedSignature {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) : ℝ := (sigPos Q : ℝ) - (sigNeg Q : ℝ)

lemma signature_weightedSumSquares {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    signedSignature (weightedSumSquares ℝ w) = ∑ i, (SignType.sign (w i) : ℝ) := by
  rw [signedSignature,QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares]
  have hp : (({i | 0 < w i} : Set ι).ncard : ℝ) =
      ∑ i, if 0 < w i then (1:ℝ) else 0 := by simp [Set.ncard_eq_toFinset_card']
  have hn : (({i | w i < 0} : Set ι).ncard : ℝ) =
      ∑ i, if w i < 0 then (1:ℝ) else 0 := by simp [Set.ncard_eq_toFinset_card']
  rw [hp,hn,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rcases lt_trichotomy (w i) 0 with h | h | h
  · simp [h,not_lt_of_ge h.le,sign_neg h]
  · simp [h]
  · simp [h,not_lt_of_ge h.le,sign_pos h]

noncomputable def squareRootOrOne (q : ℂ) : ℂ :=
  if q = 0 then 1 else (IsAlgClosed.exists_pow_nat_eq q (by norm_num : 0 < (2:ℕ))).choose

lemma squareRootOrOne_sq {q : ℂ} (h : q ≠ 0) : squareRootOrOne q ^ 2 = q := by
  simp only [squareRootOrOne,ite_eq_right h]
  exact (IsAlgClosed.exists_pow_nat_eq q (by norm_num : 0 < (2:ℕ))).choose_spec

lemma squareRootOrOne_ne_zero (q : ℂ) : squareRootOrOne q ≠ 0 := by
  by_cases h : q = 0
  · simp [squareRootOrOne,h]
  · intro hz
    have hh := squareRootOrOne_sq h
    simp [hz] at hh
    exact h hh.symm

noncomputable def rootCoordinates {α β : Type*} (q : β → ℂ) :
    ((α → ℝ) × (β → ℂ)) ≃ₗ[ℝ] ((α ⊕ (β ⊕ β)) → ℝ) where
  toFun v := Sum.elim v.1 (Sum.elim
    (fun b => (squareRootOrOne (q b) * v.2 b).re)
    (fun b => (squareRootOrOne (q b) * v.2 b).im))
  invFun v := (fun a => v (.inl a),fun b =>
    ((v (.inr (.inl b)) : ℂ) + (v (.inr (.inr b)) : ℂ)*Complex.I) /
      squareRootOrOne (q b))
  left_inv v := by
    ext a
    · rfl
    · simp only [Sum.elim_inr,Sum.elim_inl,Complex.re_add_im]
      exact mul_div_cancel_left₀ _ (squareRootOrOne_ne_zero _)
  right_inv v := by
    funext a
    rcases a with a | b
    · rfl
    · rcases b with b | b <;>
        simp [mul_div_cancel₀ _ (squareRootOrOne_ne_zero _)]
  map_add' v w := by
    ext a
    rcases a with a | b
    · rfl
    · rcases b with b | b <;> simp [mul_add]
  map_smul' r v := by
    ext a
    rcases a with a | b
    · rfl
    · rcases b with b | b <;> simp <;> ring

theorem signature_of_root_values
    {M α β : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    [Fintype α] [Fintype β] (Q : QuadraticForm ℝ M)
    (f : M →ₗ[ℝ] ((α → ℝ) × (β → ℂ))) (hf : Function.Surjective f)
    (wr : α → ℝ) (m : β → ℝ) (q : β → ℂ)
    (hQ : ∀ v, Q v = ∑ a, wr a * (f v).1 a ^ 2 +
      ∑ b, 2 * m b * (q b * (f v).2 b ^ 2).re) :
    signedSignature Q = ∑ a, (SignType.sign (wr a) : ℝ) := by
  let t : β → ℝ := fun b => if q b = 0 then 0 else 2*m b
  let w : α ⊕ (β ⊕ β) → ℝ := Sum.elim wr (Sum.elim t (fun b => -t b))
  let e := rootCoordinates (α := α) q
  let g := e.toLinearMap.comp f
  have hg : Function.Surjective g := e.surjective.comp hf
  have hpair (b : β) (z : ℂ) :
      t b * (squareRootOrOne (q b) * z).re^2 +
        (-t b) * (squareRootOrOne (q b) * z).im^2 =
          2*m b * (q b * z^2).re := by
    by_cases h : q b = 0
    · simp [t,h]
    · have he : q b * z^2 = (squareRootOrOne (q b) * z)^2 := by
        rw [mul_pow,squareRootOrOne_sq h]
      rw [he]
      simp only [t,ite_eq_right h,pow_two,Complex.mul_re]
      ring
  have he : Q = (weightedSumSquares ℝ w).comp g := by
    ext v
    rw [hQ v,comp_apply,weightedSumSquares_apply]
    simp only [Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,
      g,e,LinearMap.comp_apply,rootCoordinates,
      smul_eq_mul]
    simp only [← pow_two]
    rw [← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro b _
    exact (hpair b ((f v).2 b)).symm
  rw [he,signedSignature,sigPos_comp_surjective _ _ hg,sigNeg_comp_surjective _ _ hg]
  change signedSignature (weightedSumSquares ℝ w) = _
  rw [signature_weightedSumSquares]
  simp only [w,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Left.sign_neg,
    SignType.coe_neg,sum_neg_distrib,add_neg_cancel,add_zero]

end Release061.SignElimination

end

end OAI
