import OAI.Geometry.NodalSets.Elliptic.RealCutoffAbsorption

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma real_inhomogeneous_pointwise (k L M : ℝ) (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, B i j=B j i)
    (hlo : ∀ z : Yau.Jets.Coord, k*(∑ i, z i^2) ≤ coordMatrixForm B z z)
    (hhi : ∀ z : Yau.Jets.Coord, coordMatrixForm B z z ≤ L*(∑ i, z i^2))
    (eta W V f : ℝ) (hV : |V| ≤ M) (g d F : Yau.Jets.Coord) :
    k/2*(eta^2*(∑ i, g i^2)) ≤
      (eta^2*coordMatrixForm B g g+2*eta*W*coordMatrixForm B d g -
        eta^2*W*V*W - (eta^2*(∑ i, g i*F i)+2*eta*W*(∑ i, d i*F i)) +eta^2*W*f) +
      (M+4*L+k⁻¹+3)*((eta^2+(∑ i, d i^2))*W^2+eta^2*f^2+eta^2*(∑ i, F i^2)) := by
  have hn (z : Yau.Jets.Coord) : 0 ≤ coordMatrixForm B z z :=
    (mul_nonneg hk.le (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (z i)))).trans (hlo z)
  have hcross := real_matrix_cutoff_absorption B hs hn eta W g d
  have hg := mul_le_mul_of_nonneg_left (hlo g) (sq_nonneg eta)
  have hd := mul_le_mul_of_nonneg_left (hhi d) (sq_nonneg W)
  have hp1 := mul_le_mul_of_nonneg_left (real_dot_young_quarter k hk g F) (sq_nonneg eta)
  have hp2 := real_dot_young (fun i ↦ W*d i) (fun i ↦ eta*F i)
  simp only [mul_pow,mul_assoc,← Finset.mul_sum] at hp2
  have hpot := mul_le_mul_of_nonneg_left ((le_abs_self V).trans hV) (mul_nonneg (sq_nonneg eta) (sq_nonneg W))
  have hf := mul_nonneg (sq_nonneg eta) (sq_nonneg (W+f))
  have hg0 : 0 ≤ ∑ i, g i^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hd0 : 0 ≤ ∑ i, d i^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hF0 : 0 ≤ ∑ i, F i^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hdi : 0 ≤ k⁻¹ := inv_nonneg.mpr hk.le
  have hp2' : 2*eta*W*(∑ i, d i*F i) ≤ W^2*(∑ i, d i^2)+eta^2*(∑ i, F i^2) := by
    convert hp2 using 1
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have base : k/2*(eta^2*(∑ i, g i^2)) ≤
      (eta^2*coordMatrixForm B g g+2*eta*W*coordMatrixForm B d g -
        eta^2*W*V*W - (eta^2*(∑ i, g i*F i)+2*eta*W*(∑ i, d i*F i)) +eta^2*W*f) +
      (M+1)*(eta^2*W^2)+(4*L+1)*((∑ i, d i^2)*W^2)+
        eta^2*f^2+(k⁻¹+1)*(eta^2*(∑ i, F i^2)) := by
    nlinarith only [hcross,hg,hd,hp1,hp2',hpot,hf,
      mul_nonneg (sq_nonneg eta) (sq_nonneg W),mul_nonneg (sq_nonneg eta) (sq_nonneg f)]
  have h1 := mul_nonneg (show 0 ≤ 4*L+k⁻¹+2 by positivity) (mul_nonneg (sq_nonneg eta) (sq_nonneg W))
  have h2 := mul_nonneg (show 0 ≤ M+k⁻¹+2 by positivity) (mul_nonneg hd0 (sq_nonneg W))
  have h3 := mul_nonneg (show 0 ≤ M+4*L+k⁻¹+2 by positivity) (mul_nonneg (sq_nonneg eta) (sq_nonneg f))
  have h4 := mul_nonneg (show 0 ≤ M+4*L+2 by positivity) (mul_nonneg (sq_nonneg eta) hF0)
  nlinarith only [base,h1,h2,h3,h4]

end
end Yau.Geometry

end OAI
