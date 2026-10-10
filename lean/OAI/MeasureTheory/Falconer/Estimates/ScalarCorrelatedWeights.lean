import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace OAI

/-! The same coefficient is used at every porous scale. The following
 finite Jensen estimate averages products without any independence
 assumption on the exceptional sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem finite_correlated_product_mean {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hB : B.Nonempty) (w : ι → β → ℝ) (ell : ι → ℝ)
    (hw : ∀ i ∈ I, ∀ b ∈ B, 0 < w i b)
    (hlog : ∀ i ∈ I, (B.card : ℝ)*ell i ≤ ∑ b ∈ B, Real.log (w i b)) :
    Real.exp (∑ i ∈ I, ell i) ≤
      (∑ b ∈ B, ∏ i ∈ I, w i b)/(B.card : ℝ) := by
  classical
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hp : ∀ b ∈ B, 0 < ∏ i ∈ I, w i b := fun b hb => Finset.prod_pos (fun i hi => hw i hi b hb)
  have hs : (B.card : ℝ)*(∑ i ∈ I, ell i) ≤
      ∑ b ∈ B, Real.log (∏ i ∈ I, w i b) := by
    calc
      _ = ∑ i ∈ I, (B.card : ℝ)*ell i := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, ∑ b ∈ B, Real.log (w i b) := Finset.sum_le_sum hlog
      _ = ∑ b ∈ B, ∑ i ∈ I, Real.log (w i b) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun b hb => (Real.log_prod (fun i hi => (hw i hi b hb).ne')).symm)
  have he : (∑ i ∈ I, ell i) ≤
      (∑ b ∈ B, Real.log (∏ i ∈ I, w i b))/(B.card : ℝ) := by
    apply (le_div_iff₀ hn).2
    simpa only [mul_comm] using hs
  have hweight : ∑ _b ∈ B, 1/(B.card : ℝ) = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel hn.ne'
  have hj := convexOn_exp.map_sum_le
    (fun _b (_hb : _b ∈ B) => (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hn.le))
    hweight (fun b (_hb : b ∈ B) => Set.mem_univ (Real.log (∏ i ∈ I, w i b)))
  have hsumlog : (∑ b ∈ B, (1/(B.card : ℝ))*Real.log (∏ i ∈ I, w i b)) =
      (∑ b ∈ B, Real.log (∏ i ∈ I, w i b))/(B.card : ℝ) := by
    rw [← Finset.mul_sum]
    ring
  simp only [smul_eq_mul] at hj
  rw [hsumlog] at hj
  have hexp : (∑ b ∈ B, (1/(B.card : ℝ))*Real.exp (Real.log (∏ i ∈ I, w i b))) =
      (∑ b ∈ B, ∏ i ∈ I, w i b)/(B.card : ℝ) := by
    calc
      _ = ∑ b ∈ B, (1/(B.card : ℝ))*(∏ i ∈ I, w i b) :=
        Finset.sum_congr rfl (fun b hb => by rw [Real.exp_log (hp b hb)])
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [hexp] at hj
  exact (Real.exp_le_exp.mpr he).trans hj

noncomputable def scalarCollisionWeight {β : Type*} (L : ℝ) (G : Finset β) (b : β) : ℝ :=
  if b ∈ G then L⁻¹ else 1

 theorem scalarCollisionWeight_pos {β : Type*} {L : ℝ} (hL : 0 < L) (G : Finset β) (b : β) :
    0 < scalarCollisionWeight L G b := by
  unfold scalarCollisionWeight
  split_ifs <;> positivity

 theorem scalarCollisionWeight_log_sum {β : Type*} (B G : Finset β) (hGB : G ⊆ B) (L : ℝ) :
    (∑ b ∈ B, Real.log (scalarCollisionWeight L G b)) = -(G.card : ℝ)*Real.log L := by
  classical
  have hf : B.filter (fun b => b ∈ G) = G := by ext b; simp only [Finset.mem_filter]; exact ⟨And.right,fun hb => ⟨hGB hb,hb⟩⟩
  calc
    _ = ∑ b ∈ B, if b ∈ G then -Real.log L else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbg : b ∈ G <;> simp [scalarCollisionWeight,hbg,Real.log_inv]
    _ = ∑ _b ∈ B.filter (fun b => b ∈ G), -Real.log L := (Finset.sum_filter _ _).symm
    _ = _ := by rw [hf]; simp

 theorem scalarCollisionWeight_log_bound {β : Type*} (B G : Finset β)
    (hGB : G ⊆ B) {L p : ℝ} (hL : 1 ≤ L) (hcard : (G.card : ℝ) ≤ p*(B.card : ℝ)) :
    (B.card : ℝ)*(-p*Real.log L) ≤
      ∑ b ∈ B, Real.log (scalarCollisionWeight L G b) := by
  rw [scalarCollisionWeight_log_sum B G hGB]
  have h := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hL)
  nlinarith

end Falconer

end OAI
