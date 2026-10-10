import OAI.MeasureTheory.Falconer.Graphs.RoundedProjectionGraph

namespace OAI

/-! Original cardinality bounds supply both coordinate comparability and
graph density; no balance or density condition is added to the point set. -/
namespace Falconer

 theorem coordinate_graph_scaled_bounds {X Y G n F K : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hn : 0 < n) (hF : 0 < F) (hK : 0 ≤ K)
    (hXN : X ≤ F*n) (hYN : Y ≤ F*n) (hG : G ≤ X*Y) (hlarge : n^2 ≤ K*G) :
    X ≤ (K*F^2)*Y ∧ Y ≤ (K*F^2)*X ∧
      n ≤ K*F*X ∧ n ≤ K*F*Y ∧ X*Y ≤ (K*F^2)*G := by
  have hN : 0 < F*n := mul_pos hF hn
  have hK' : 0 ≤ K*F^2 := mul_nonneg hK (sq_nonneg F)
  have hlarge' : (F*n)^2 ≤ (K*F^2)*G := by
    have hh := mul_le_mul_of_nonneg_left hlarge (sq_nonneg F)
    nlinarith
  obtain ⟨hcX,hcY⟩ := coordinate_graph_comparable hX hY hK' hXN hYN hG hlarge'
  obtain ⟨hlX,hlY⟩ := coordinate_graph_factor_lower hN hX.le hY.le hK' hXN hYN hG hlarge'
  have hlX' : n ≤ K*F*X := by
    apply (mul_le_mul_iff_right₀ hF).1
    nlinarith [hlX]
  have hlY' : n ≤ K*F*Y := by
    apply (mul_le_mul_iff_right₀ hF).1
    nlinarith [hlY]
  have hp : X*Y ≤ (F*n)^2 := by
    have hh := mul_le_mul hXN hYN hY.le hN.le
    nlinarith
  exact ⟨hcX,hcY,hlX',hlY',hp.trans hlarge'⟩

 theorem roundedProjectionCoordinates_coordinate_upper {δ σ a b : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (U : Finset (Space 2)) (m P : ℕ)
    (hm : δ ≤ (m:ℝ)*σ)
    (ha : (projectionCells δ a U).card ≤ P) (hb : (projectionCells δ b U).card ≤ P)
    (i : Fin 2) :
    (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p i)).card:ℝ) ≤
      (5*(2*(m:ℝ)+3))*(P:ℝ) := by
  have hh := roundedProjectionCoordinates_coordinate_card (a := a) (b := b) hσ hδ U m hm i
  have hp : (projectionCells δ (if i = 0 then a else b) U).card ≤ P := by
    split_ifs <;> assumption
  have hc := hh.trans (Nat.mul_le_mul_left (5*(2*m+3)) hp)
  exact_mod_cast hc

 theorem scalar_dilation_separated {δ σ M c : ℝ} (hM : 0 < M)
    (hscale : δ*M ≤ σ) (hc : c ≠ 0) (hcM : |c⁻¹| ≤ M)
    (Y : Finset ℝ) (hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → σ ≤ |x-y|) :
    ∀ x ∈ Y.image (fun y => c*y), ∀ y ∈ Y.image (fun y => c*y), x ≠ y → δ ≤ |x-y| := by
  intro x hx y hy hxy
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
  have huv : u ≠ v := fun h => hxy (by rw [h])
  have hs := hsep u hu v hv huv
  have he : |u-v| = |c⁻¹| * |c*u-c*v| := by
    rw [← mul_sub,abs_mul,← mul_assoc,← abs_mul,inv_mul_cancel₀ hc,abs_one,one_mul]
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_right hcM (abs_nonneg (c*u-c*v))
  apply (mul_le_mul_iff_right₀ hM).1
  nlinarith

end Falconer

end OAI
