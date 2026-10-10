import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.ConeRepresentation

namespace OAI

/-! Spectral size. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma laplacian_centered_energy (G : MultiGraph n m) (x : Fin n → ℝ) :
    qform (G.laplacian univ) (centering n *ᵥ x)=qform (G.laplacian univ) x := by
  rw [←qform_centered,centered_eq (G.laplacian_psd univ).isHermitian (laplacian_ones G)]

lemma range_le_edge_variation (G : MultiGraph n m) (hc : G.Connected univ)
    (x : Fin n → ℝ) (a b : Fin n)
    (ha : ∀i, x a ≤ x i) (hb : ∀i, x i ≤ x b) :
    x b-x a ≤ ∑e : Fin m, |x (G.left e)-x (G.right e)| := by
  have he : G.EdgeConnected 1 := fun S hS hp => card_pos.mpr (hc S hS hp)
  have h := G.clamped_variation_lower he x (ha b) ⟨a,le_rfl⟩ ⟨b,le_rfl⟩
  have hcl (i : Fin n) : Geometry.clamp (x a) (x b) (x i)=x i := by
    simp only [Geometry.clamp,max_eq_right (ha i),min_eq_right (hb i)]
  simpa only [Nat.cast_one,one_mul,hcl] using h

theorem laplacian_poincare (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : ∑i, x i=0) :
    (∑i, x i^2) ≤ (n : ℝ)*m*qform (G.laplacian univ) x := by
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  obtain ⟨a,_,ha⟩ := exists_min_image univ x hne
  obtain ⟨b,_,hb⟩ := exists_max_image univ x hne
  have ha' : ∀i, x a ≤ x i := fun i => ha i (mem_univ _)
  have hb' : ∀i, x i ≤ x b := fun i => hb i (mem_univ _)
  have hna : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha0 : x a ≤ 0 := by
    have h := sum_le_sum (fun i (_ : i ∈ univ) => ha' i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hx] at h
    nlinarith only [h,hna]
  have hb0 : 0 ≤ x b := by
    have h := sum_le_sum (fun i (_ : i ∈ univ) => hb' i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hx] at h
    nlinarith only [h,hna]
  have hnorm : (∑i, x i^2) ≤ (n : ℝ)*(x b-x a)^2 := by
    have h (i : Fin n) : x i^2 ≤ (x b-x a)^2 := by
      have hh : |x i| ≤ x b-x a := abs_le.mpr ⟨by linarith [ha' i],by linarith [hb' i]⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) hh 2
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
      sum_le_sum (fun i (_ : i ∈ univ) => h i)
  have hvar := range_le_edge_variation G hc x a b ha' hb'
  have hsqr : (x b-x a)^2 ≤ (∑e : Fin m, |x (G.left e)-x (G.right e)|)^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr (ha' b)) hvar 2
  have hCS := sq_sum_le_card_mul_sum_sq (s := univ)
    (f := fun e : Fin m => |x (G.left e)-x (G.right e)|)
  simp only [card_univ,Fintype.card_fin,sq_abs,←G.laplacian_qform] at hCS
  exact hnorm.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hsqr.trans hCS) hna.le)

def graphSize (n m : ℕ) : ℝ := n+m+2

lemma graphSize_pos : 0 < graphSize n m := by
  dsimp [graphSize]
  positivity

lemma vertex_edge_le_size_cube : (n : ℝ)*m ≤ (graphSize n m)^3 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnP : (n : ℝ) ≤ graphSize n m := by dsimp [graphSize]; linarith
  have hmP : (m : ℝ) ≤ graphSize n m := by dsimp [graphSize]; linarith
  have hP : 1 ≤ graphSize n m := by dsimp [graphSize]; linarith
  have hsq : (n : ℝ)*m ≤ (graphSize n m)^2 := by
    simpa only [pow_two] using mul_le_mul hnP hmP hm (le_trans hn hnP)
  exact hsq.trans (by
    have h := mul_le_mul_of_nonneg_left hP (sq_nonneg (graphSize n m))
    nlinarith only [h])

theorem laplacian_spectral_gap (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : ∑i, x i=0) :
    (graphSize n m)^(-3 : ℤ)*(∑i, x i^2) ≤ qform (G.laplacian univ) x := by
  have hbound : (∑i, x i^2) ≤ (graphSize n m)^3*qform (G.laplacian univ) x :=
    (laplacian_poincare G hn hc x hx).trans
      (mul_le_mul_of_nonneg_right vertex_edge_le_size_cube (qform_nonneg (G.laplacian_psd univ) x))
  simp only [_root_.zpow_neg,zpow_ofNat] 
  rw [inv_mul_le_iff₀ (pow_pos graphSize_pos 3)]
  exact hbound

lemma qform_one_sum_sq (x : Fin n → ℝ) :
    qform (1 : Matrix (Fin n) (Fin n) ℝ) x=∑i, x i^2 := by
  simp only [qform,one_mulVec,dotProduct,pow_two]

lemma centering_idempotent (hn : 0 < n) : centering n*centering n=centering n :=
  mul_centering_of_ones (centering_ones hn)

lemma qform_centering_sum_sq (hn : 0 < n) (x : Fin n → ℝ) :
    qform (centering n) x=∑i, (centering n *ᵥ x) i^2 := by
  rw [←qform_one_sum_sq,←qform_centered]
  simp only [centered,mul_one,centering_idempotent hn]

lemma centering_psd (hn : 0 < n) : (centering n).PosSemidef := by
  have h := centered_psd (PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
  simpa only [centered,mul_one,centering_idempotent hn] using h

theorem laplacian_lower_order (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ) :
    (graphSize n m)^(-3 : ℤ) • centering n ≤ G.laplacian univ := by
  apply Matrix.le_iff.mpr
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    ((G.laplacian_psd univ).isHermitian.sub
      ((centering_psd hn).smul (zpow_nonneg graphSize_pos.le _)).isHermitian)
  intro x
  change 0 ≤ qform (G.laplacian univ-(graphSize n m)^(-3 : ℤ) • centering n) x
  rw [qform_sub,qform_smul,qform_centering_sum_sq hn]
  have h := laplacian_spectral_gap G hn hc (centering n *ᵥ x) (centering_mulVec_sum hn x)
  rw [laplacian_centered_energy G x] at h
  linarith only [h]

lemma qform_outer (b x : Fin n → ℝ) : qform (vecMulVec b b) x=(b ⬝ᵥ x)^2 := by
  simp only [qform,vecMulVec_mulVec,dotProduct_smul,IsCentralScalar.op_smul_eq_smul,smul_eq_mul]
  rw [dotProduct_comm x b,pow_two]

lemma qform_outer_le (b x : Fin n → ℝ) :
    qform (vecMulVec b b) x ≤ (b ⬝ᵥ b)*(∑i, x i^2) := by
  simpa only [qform_outer,dotProduct,pow_two] using sum_mul_sq_le_sq_mul_sq univ b x

lemma difference_outer_le {a b : Fin n} (hab : a ≠ b) (x : Fin n → ℝ) :
    qform (vecMulVec (difference a b) (difference a b)) x ≤ 2*(∑i, x i^2) := by
  simpa only [difference_norm_sq hab] using qform_outer_le (difference a b) x

theorem laplacian_upper_energy (G : MultiGraph n m) (x : Fin n → ℝ) :
    qform (G.laplacian univ) x ≤ 2*m*(∑i, x i^2) := by
  have h (e : Fin m) : (x (G.left e)-x (G.right e))^2 ≤ 2*(∑i, x i^2) := by
    have h := difference_outer_le (G.loopless e) x
    rw [qform_outer,dotProduct_comm] at h
    change (x ⬝ᵥ G.incidence e)^2 ≤ _ at h
    simpa only [dotProduct,G.eval_incidence] using h
  rw [G.laplacian_qform]
  calc
    _ ≤ ∑e : Fin m, 2*(∑i, x i^2) := sum_le_sum (fun e _ => h e)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem laplacian_upper_order (G : MultiGraph n m) :
    G.laplacian univ ≤ (2*m : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  apply Matrix.le_iff.mpr
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    ((PosSemidef.one.smul (by positivity : (0 : ℝ) ≤ 2*m)).isHermitian.sub (G.laplacian_psd univ).isHermitian)
  intro x
  change 0 ≤ qform ((2*m : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)-G.laplacian univ) x
  rw [qform_sub,qform_smul,qform_one_sum_sq]
  exact sub_nonneg.mpr (laplacian_upper_energy G x)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
