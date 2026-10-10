import OAI.Geometry.Relativity.CKS.CovariantHeat
import OAI.Geometry.Relativity.CKS.AreaCuts

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise

 def quadratic3 (g : AmbientMat) (v : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, g i j*v i*v j

lemma quadratic3_eq_dot (g : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 g v=star v ⬝ᵥ (g *ᵥ v) := by
  simp only [quadratic3,dotProduct,mulVec,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic3_sub (g h : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 (g-h) v=quadratic3 g v-quadratic3 h v := by
  simp only [quadratic3,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma quadratic3_smul (c : ℝ) (g : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 (c • g) v=c*quadratic3 g v := by
  simp only [quadratic3,Matrix.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

lemma quadratic3_bound {e : AmbientMat} {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖e‖ ≤ δ) (v : Fin 3 → ℝ) :
    |quadratic3 e v| ≤ 3*δ*(∑ i, (v i)^2) := by
  have hentry (i j : Fin 3) : |e i j| ≤ δ := by
    exact ((norm_le_pi_norm (e i) j).trans (norm_le_pi_norm e i)).trans he
  have hv (i j : Fin 3) : |v i| *|v j| ≤ ((v i)^2+(v j)^2)/2 := by
    nlinarith [sq_nonneg (|v i| -|v j|),sq_abs (v i),sq_abs (v j)]
  calc
    |quadratic3 e v| ≤ ∑ i, ∑ j, |e i j*v i*v j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, δ*((v i)^2+(v j)^2)/2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [abs_mul,abs_mul]
      calc
        |e i j| *|v i| *|v j| ≤ δ*(|v i| *|v j|) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _)) (abs_nonneg _)
        _ ≤ δ*((v i)^2+(v j)^2)/2 := by nlinarith [mul_le_mul_of_nonneg_left (hv i j) hδ]
    _ = 3*δ*(∑ i, (v i)^2) := by simp [Fin.sum_univ_three]; ring

lemma quadratic3_error {g h : AmbientMat} {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖g-h‖ ≤ δ)
    (v : Fin 3 → ℝ) : |quadratic3 g v-quadratic3 h v| ≤ 3*δ*(∑ i, (v i)^2) := by
  rw [← quadratic3_sub]
  exact quadratic3_bound hδ he v

lemma round_background_lower {κ l : ℝ} (hκ : κ ≤ 1) (hl : κ ≤ l) (v : Fin 3 → ℝ) :
    κ*(∑ i, (v i)^2) ≤ quadratic3 (metricBlock 1 0 (l • (1:Mat))) v := by
  simp [quadratic3,metricBlock,Matrix.of_apply,Fin.sum_univ_three]
  nlinarith [mul_nonneg (sub_nonneg.mpr hκ) (sq_nonneg (v 0)),
    mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (v 1)),
    mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (v 2))]

theorem metric_lower_from_coefficients {G H : AmbientMat} {δ κ : ℝ}
    (hκ : 0<κ) (hδ : 0 ≤ δ) (hclose : ‖G-H‖ ≤ δ)
    (hbackground : ∀ v, κ*(∑ i : Fin 3, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, (1-3*δ/κ)*quadratic3 H v ≤ quadratic3 G v := by
  intro v
  have hlow := (abs_le.mp (quadratic3_error hδ hclose v)).1
  have hbg := hbackground v
  have hd : κ*(3*δ/κ)=3*δ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hbg (show 0 ≤ 3*δ/κ by positivity)
  have he : (3*δ/κ)*(κ*(∑ i : Fin 3, (v i)^2)) = 3*δ*(∑ i : Fin 3, (v i)^2) := by
    field_simp
  rw [he] at hh
  nlinarith

lemma metric_upper_from_coefficients {g H : AmbientMat} {δ κ : ℝ}
    (hκ : 0<κ) (hδ : 0 ≤ δ) (hclose : ‖g-H‖ ≤ δ)
    (hbackground : ∀ v, κ*(∑ i : Fin 3, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, quadratic3 g v ≤ (1+3*δ/κ)*quadratic3 H v := by
  intro v
  have hupper := (abs_le.mp (quadratic3_error hδ hclose v)).2
  have hbg := hbackground v
  have hd : κ*(3*δ/κ)=3*δ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hbg (show 0 ≤ 3*δ/κ by positivity)
  have he : (3*δ/κ)*(κ*(∑ i : Fin 3, (v i)^2)) = 3*δ*(∑ i : Fin 3, (v i)^2) := by
    field_simp
  rw [he] at hh
  nlinarith

theorem metric_comparison_from_background {G g H : AmbientMat} {δ ε κ : ℝ}
    (hκ : 0<κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hsmall : 3*δ ≤ κ)
    (hGclose : ‖G-H‖ ≤ δ) (hgclose : ‖g-H‖ ≤ ε)
    (hbackground : ∀ v, κ*(∑ i : Fin 3, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, ((1-3*δ/κ)/(1+3*ε/κ))*quadratic3 g v ≤ quadratic3 G v := by
  intro v
  have hlow := metric_lower_from_coefficients hκ hδ hGclose hbackground v
  have hupp := metric_upper_from_coefficients hκ hε hgclose hbackground v
  have hn : 0 ≤ 1-3*δ/κ := sub_nonneg.mpr ((div_le_one hκ).mpr hsmall)
  have hd : 0 < 1+3*ε/κ := by positivity
  have hh := mul_le_mul_of_nonneg_left hupp (div_nonneg hn hd.le)
  have he : (1-3*δ/κ)/(1+3*ε/κ)*((1+3*ε/κ)*quadratic3 H v)=
      (1-3*δ/κ)*quadratic3 H v := by field_simp
  rw [he] at hh
  exact hh.trans hlow

lemma comparison_posSemidef {G g : AmbientMat} {c : ℝ}
    (hG : G.IsHermitian) (hg : g.IsHermitian)
    (h : ∀ v, c*quadratic3 g v ≤ quadratic3 G v) : (G-c • g).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hG.sub (hg.smul (isSelfAdjoint_iff.mpr (star_trivial c))))
  intro v
  rw [← quadratic3_eq_dot,quadratic3_sub,quadratic3_smul]
  exact sub_nonneg.mpr (h v)

end
end CKSAngularGeometry

end

end OAI
