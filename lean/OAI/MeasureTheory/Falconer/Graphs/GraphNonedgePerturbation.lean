import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalPhase
import OAI.MeasureTheory.Falconer.Graphs.GraphChartVariation

namespace OAI

namespace PlanarFalconer
open Set

theorem graphA_norm_bound (z : ℝ) (v : Plane) :
    ‖graphA z v‖ ≤ (1+|z|)/2*‖v‖ := by
  calc
    _ = (1/2:ℝ)*‖v-z • quarterTurn v‖ := by simp [graphA,norm_smul]
    _ ≤ (1/2:ℝ)*(‖v‖+‖z • quarterTurn v‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = _ := by rw [norm_smul,Real.norm_eq_abs,graph_quarterTurn_norm]; ring

theorem graphB_norm_bound (z : ℝ) (v : Plane) :
    ‖graphB z v‖ ≤ (1+|z|)/2*‖v‖ := by
  simpa only [graphA,graphB,neg_smul,sub_neg_eq_add,abs_neg] using graphA_norm_bound (-z) v

theorem graphA_perturbation_identity (z z₀ : ℝ) (v v₀ : Plane) :
    graphA z v-graphA z₀ v₀ = graphA z (v-v₀) + ((z₀-z)/2) • quarterTurn v₀ := by
  ext i
  fin_cases i <;> simp [graphA,quarterTurn] <;> ring

theorem graphB_perturbation_identity (z z₀ : ℝ) (v v₀ : Plane) :
    graphB z v-graphB z₀ v₀ = graphB z (v-v₀) + ((z-z₀)/2) • quarterTurn v₀ := by
  ext i
  fin_cases i <;> simp [graphB,quarterTurn] <;> ring

theorem graphA_perturbation_bound (z z₀ : ℝ) (v v₀ : Plane) :
    ‖graphA z v-graphA z₀ v₀‖ ≤
      (1+|z|)/2*‖v-v₀‖+|z-z₀|/2*‖v₀‖ := by
  rw [graphA_perturbation_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (graphA_norm_bound _ _) (le_of_eq _)
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_sub_comm,abs_of_pos (by norm_num : (0:ℝ)<2),graph_quarterTurn_norm]

theorem graphB_perturbation_bound (z z₀ : ℝ) (v v₀ : Plane) :
    ‖graphB z v-graphB z₀ v₀‖ ≤
      (1+|z|)/2*‖v-v₀‖+|z-z₀|/2*‖v₀‖ := by
  rw [graphB_perturbation_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (graphB_norm_bound _ _) (le_of_eq _)
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),graph_quarterTurn_norm]

theorem graph_vector_perturbation (s z z₀ : ℝ) (v w v₀ w₀ : Plane) (hs : |s| = 1)
    {δ θ ℓ : ℝ} (_hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (_hℓ : 0 ≤ ℓ)
    (hz : |z| ≤ 4) (hmove : |z-z₀| ≤ θ)
    (hv : ‖v-v₀‖ ≤ 4*δ) (hw : ‖w-w₀‖ ≤ 4*δ)
    (hv₀ : ‖v₀‖ ≤ ℓ) (hw₀ : ‖w₀‖ ≤ ℓ) :
    ‖(graphA z v+s • graphB z w)-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤ 20*δ+θ*ℓ := by
  have he : (graphA z v+s • graphB z w)-(graphA z₀ v₀+s • graphB z₀ w₀) =
      (graphA z v-graphA z₀ v₀)+s • (graphB z w-graphB z₀ w₀) := by rw [smul_sub]; abel
  rw [he]
  have htri := norm_add_le (graphA z v-graphA z₀ v₀) (s • (graphB z w-graphB z₀ w₀))
  rw [norm_smul,Real.norm_eq_abs,hs,one_mul] at htri
  apply htri.trans
  have hA := graphA_perturbation_bound z z₀ v v₀
  have hB := graphB_perturbation_bound z z₀ w w₀
  have hcoeff : (1+|z|)/2 ≤ 5/2 := by linarith
  have h1 := mul_le_mul hcoeff hv (norm_nonneg _) (by norm_num : (0:ℝ)≤5/2)
  have h2 := mul_le_mul hcoeff hw (norm_nonneg _) (by norm_num : (0:ℝ)≤5/2)
  have h3 := mul_le_mul (div_le_div_of_nonneg_right hmove (by norm_num : (0:ℝ)≤2)) hv₀
    (norm_nonneg _) (by positivity : 0 ≤ θ/2)
  have h4 := mul_le_mul (div_le_div_of_nonneg_right hmove (by norm_num : (0:ℝ)≤2)) hw₀
    (norm_nonneg _) (by positivity : 0 ≤ θ/2)
  nlinarith

theorem graphDerivative_norm_bound (s : ℝ) (v w : Plane) (hs : |s| = 1) :
    ‖graphDerivative s v w‖ ≤ (‖v‖+‖w‖)/2 := by
  calc
    _ = (1/2:ℝ)*‖-quarterTurn v+s • quarterTurn w‖ := by rw [graphDerivative,norm_smul]; norm_num
    _ ≤ (1/2:ℝ)*(‖-quarterTurn v‖+‖s • quarterTurn w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [norm_neg,norm_smul,Real.norm_eq_abs,hs,one_mul,graph_quarterTurn_norm,graph_quarterTurn_norm]; ring

theorem graphDerivative_sub (s : ℝ) (v w v₀ w₀ : Plane) :
    graphDerivative s v w-graphDerivative s v₀ w₀ = graphDerivative s (v-v₀) (w-w₀) := by
  ext i
  fin_cases i <;> simp [graphDerivative,quarterTurn] <;> ring

theorem graph_scalar_perturbation (s : ℝ) (v w v₀ w₀ e e₀ : Plane) (hs : |s| = 1)
    {δ θ ℓ : ℝ} (_hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (_hℓ : 0 ≤ ℓ)
    (he : ‖e‖ = 1) (hmove : ‖e-e₀‖ ≤ θ)
    (hv : ‖v-v₀‖ ≤ 4*δ) (hw : ‖w-w₀‖ ≤ 4*δ)
    (hv₀ : ‖v₀‖ ≤ ℓ) (hw₀ : ‖w₀‖ ≤ ℓ) :
    |inner ℝ e (graphDerivative s v w)-inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ 4*δ+θ*ℓ := by
  have hid : inner ℝ e (graphDerivative s v w)-inner ℝ e₀ (graphDerivative s v₀ w₀) =
      inner ℝ e (graphDerivative s v w-graphDerivative s v₀ w₀) +
        inner ℝ (e-e₀) (graphDerivative s v₀ w₀) := by rw [inner_sub_right,inner_sub_left]; ring
  have hder : ‖graphDerivative s v w-graphDerivative s v₀ w₀‖ ≤ 4*δ := by
    rw [graphDerivative_sub]
    exact (graphDerivative_norm_bound s _ _ hs).trans (by linarith)
  have hder₀ : ‖graphDerivative s v₀ w₀‖ ≤ ℓ :=
    (graphDerivative_norm_bound s v₀ w₀ hs).trans (by linarith)
  rw [hid]
  calc
    _ ≤ |inner ℝ e (graphDerivative s v w-graphDerivative s v₀ w₀)| +
        |inner ℝ (e-e₀) (graphDerivative s v₀ w₀)| := abs_add_le _ _
    _ ≤ ‖e‖*‖graphDerivative s v w-graphDerivative s v₀ w₀‖ +
        ‖e-e₀‖*‖graphDerivative s v₀ w₀‖ := add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ 4*δ+θ*ℓ := by
      rw [he,one_mul]
      exact add_le_add hder (mul_le_mul hmove hder₀ (norm_nonneg _) hθ)

end PlanarFalconer

end OAI
