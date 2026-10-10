import OAI.Probability.ContinuumTransition.OccupationProducts

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def tetraRaw (i : Fin 4) : Space :=
  WithLp.toLp 2 (![![0,0,0],![1,1,0],![1,0,1],![0,1,1]] i)

lemma tetraRaw_zero : tetraRaw 0 = 0 := by ext k; fin_cases k <;> simp [tetraRaw]

lemma tetraRaw_dist {i j : Fin 4} (hij : i ≠ j) : ‖tetraRaw i-tetraRaw j‖ = Real.sqrt 2 := by
  have he : ‖tetraRaw i-tetraRaw j‖^2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    fin_cases i <;> fin_cases j <;> norm_num [tetraRaw, Fin.sum_univ_succ] at *
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := norm_nonneg (tetraRaw i-tetraRaw j)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith only [he,hs,hn,hp]

noncomputable def tetraVertex (i : Fin 4) : Space :=
  ((1+shellDelta/2)/Real.sqrt 2) • tetraRaw i

lemma tetraVertex_zero : tetraVertex 0 = 0 := by rw [tetraVertex, tetraRaw_zero, smul_zero]

lemma tetraVertex_dist {i j : Fin 4} (hij : i ≠ j) :
    ‖tetraVertex i-tetraVertex j‖ = 1+shellDelta/2 := by
  rw [tetraVertex, tetraVertex, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by unfold shellDelta; positivity), tetraRaw_dist hij]
  exact div_mul_cancel₀ _ (Real.sqrt_pos.2 (by norm_num)).ne'

lemma tetraVertex_norm (i : Fin 4) : ‖tetraVertex i‖ ≤ 1+shellDelta/2 := by
  by_cases hi : i=0
  · rw [hi,tetraVertex_zero,norm_zero]
    unfold shellDelta
    norm_num
  · simpa only [tetraVertex_zero,sub_zero] using (tetraVertex_dist hi).le

noncomputable def clusterRadius (t : ℝ) : ℝ := shellDelta/8*Real.exp (-t)

lemma clusterRadius_pos (t : ℝ) : 0 < clusterRadius t := by unfold clusterRadius shellDelta; positivity

def TetraCluster (t : ℝ) (x : Fin 4 → Space) : Prop :=
  ∀ i, ‖(x i-x 0)-Real.exp (-t) • tetraVertex i‖ ≤ clusterRadius t

lemma tetraCluster_free {t : ℝ} {x : Fin 4 → Space} (hx : TetraCluster t x) : FreeConfig t x := by
  intro i j hij _
  let a := x i-x j
  let b := Real.exp (-t) • (tetraVertex i-tetraVertex j)
  have he : a-b = ((x i-x 0)-Real.exp (-t) • tetraVertex i)-
      ((x j-x 0)-Real.exp (-t) • tetraVertex j) := by dsimp only [a,b]; module
  have hd : ‖a-b‖ ≤ 2*clusterRadius t := by
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith only [hx i,hx j])
  have hb : ‖b‖ = Real.exp (-t)*(1+shellDelta/2) := by
    dsimp only [b]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),tetraVertex_dist hij]
  have hnorm := abs_norm_sub_norm_le a b
  have hlo := (abs_le.mp (hnorm.trans hd)).1
  have hup := (abs_le.mp (hnorm.trans hd)).2
  rw [hb] at hlo hup
  change Real.exp (-t) ≤ ‖a‖ ∧ ‖a‖ ≤ (1+shellDelta)*Real.exp (-t)
  dsimp only [clusterRadius] at hlo hup
  have hδ : 0 ≤ shellDelta*Real.exp (-t) := by unfold shellDelta; positivity
  constructor <;> linarith

lemma tetraCluster_norm_le {t : ℝ} {x : Fin 4 → Space} (hx : TetraCluster t x) (i : Fin 4) :
    ‖x i-x 0‖ ≤ 2*Real.exp (-t) := by
  have hh := norm_le_norm_add_norm_sub (Real.exp (-t) • tetraVertex i) (x i-x 0)
  rw [norm_sub_rev (Real.exp (-t) • tetraVertex i),norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hh
  have hmul := mul_le_mul_of_nonneg_left (tetraVertex_norm i) (Real.exp_pos (-t)).le
  have hd := hx i
  dsimp only [clusterRadius] at hd
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  unfold shellDelta at hmul hd
  linarith

end ContinuumTemperature
end

end OAI
