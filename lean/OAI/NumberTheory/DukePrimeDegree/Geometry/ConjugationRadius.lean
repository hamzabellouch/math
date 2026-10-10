import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogProper

namespace OAI

/-! # Quantitative conjugation of local matrix balls

The logarithmic displacement length gives an explicit exponential loss
when a local quotient chart is transported by a group element.
-/

noncomputable section
open Set Matrix
open scoped Matrix.Norms.Operator Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrix_entry_abs_le_operator_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  have H : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k => ∑ l, ‖A k l‖₊) (Finset.mem_univ i))
  change ‖A i j‖ ≤ ‖A‖
  exact_mod_cast H

lemma matrix_operator_norm_le_card_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hA : ∀ i j, |A i j| ≤ r) : ‖A‖ ≤ (n:ℝ)*r := by
  change ‖fun i => WithLp.toLp 1 (A i)‖ ≤ (n:ℝ)*r
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hr)]
  intro i
  rw [PiLp.norm_eq_of_L1]
  change (∑ j, ‖A i j‖) ≤ (n:ℝ)*r
  calc
    _ ≤ ∑ _j : Fin n, r := Finset.sum_le_sum (fun j _ => by simpa only [Real.norm_eq_abs] using hA i j)
    _ = _ := by simp

lemma specialLinear_norm_le_exp_length {n : ℕ} (hn : 0 < n) (g : G n) :
    ‖g.val‖ ≤ Real.exp (matrixLogLength g) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have h := norm_add_le (g.val-1) (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [sub_add_cancel,norm_one] at h
  have H := norm_sub_one_le_exp_matrixLogLength g
  linarith

lemma conjugation_matrixBall_exp_bound {n : ℕ} (hn : 0 < n)
    (g : G n) {r : ℝ} (hr : 0 < r) :
    (MulAut.conj g) '' matrixBall n (r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))) ⊆
      matrixBall n r := by
  rintro _ ⟨u,hu,rfl⟩ i j
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 ≤ r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g)) := by positivity
  have hU := matrix_operator_norm_le_card_mul (u.val-1) hs
    (fun i j => (hu i j).le)
  have hg := specialLinear_norm_le_exp_length hn g
  have hgi := specialLinear_norm_le_exp_length hn g⁻¹
  rw [matrixLogLength_inv] at hgi
  have hgg : g.val*(g⁻¹).val=(1 : Matrix (Fin n) (Fin n) ℝ) := by
    change (g*g⁻¹).val=1
    simp
  have he : (MulAut.conj g u).val-1=g.val*(u.val-1)*(g⁻¹).val := by
    change g.val*u.val*(g⁻¹).val-1= _
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hgg]
  have hb : ‖(MulAut.conj g u).val-1‖ ≤
      Real.exp (matrixLogLength g)*((n:ℝ)*(r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))))*
        Real.exp (matrixLogLength g) := by
    rw [he]
    calc
      _ ≤ (‖g.val‖*‖u.val-1‖)*‖(g⁻¹).val‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := mul_le_mul (mul_le_mul hg hU (norm_nonneg _) (Real.exp_pos _).le)
        hgi (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg n) hs))
  have hc : Real.exp (matrixLogLength g)*
      ((n:ℝ)*(r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))))*
      Real.exp (matrixLogLength g)=r/2 := by
    have he : Real.exp (2*matrixLogLength g)=Real.exp (matrixLogLength g)*Real.exp (matrixLogLength g) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he]
    field_simp [hnp.ne',Real.exp_ne_zero]
  rw [hc] at hb
  have hentry := matrix_entry_abs_le_operator_norm ((MulAut.conj g u).val-1) i j
  change |(MulAut.conj g u).val i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| < r
  exact hentry.trans hb |>.trans_lt (by linarith)

lemma localInjectivityAt_exp_translate {n : ℕ} (hn : 0 < n)
    (g : G n) {r : ℝ} (hr : 0 < r) {x : X n} (hx : LocalInjectivityAt r x) :
    LocalInjectivityAt (r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))) (rightAction x g) :=
  localInjectivityAt_translate g (conjugation_matrixBall_exp_bound hn g hr) hx

/-- Explicit exponential chart radii on every logarithmic-distance ball. -/
theorem exists_uniform_logarithmic_injectivity_radius {n : ℕ} (hn : 0 < n) :
    ∃ r > 0, ∀ (R : ℝ) (x : X n),
      quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
      LocalInjectivityAt (r/(2*(n:ℝ)*Real.exp (2*(R+1)))) x := by
  let x₀ : X n := Quotient.mk _ (1 : G n)
  obtain ⟨U,hU,hx,r,hr,hinj⟩ := local_uniform_chart_injective x₀
  have hbase : LocalInjectivityAt r x₀ := ⟨U,hU,hx,hinj⟩
  refine ⟨r,hr,?_⟩
  intro R x hxR
  obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt x₀ x (by norm_num : (0:ℝ)<1)
  have hbound : matrixLogLength g ≤ R+1 := by
    dsimp [x₀] at hlen
    linarith
  have hden : 2*(n:ℝ)*Real.exp (2*matrixLogLength g) ≤
      2*(n:ℝ)*Real.exp (2*(R+1)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have ht := localInjectivityAt_exp_translate hn g hr hbase
  rw [hg] at ht
  apply ht.mono
  exact div_le_div_of_nonneg_left hr.le (by positivity) hden

end DukePrimeDegree

end

end OAI
