import Mathlib
import OAI.Geometry.WeakMTW.Variations.LineTaylor

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem tendsto_clm_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {g : α → E}
    {L : E →L[ℝ] F} {v : E} (hf : Tendsto f l (𝓝 L)) (hg : Tendsto g l (𝓝 v)) :
    Tendsto (fun a => f a (g a)) l (𝓝 (L v)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.continuousAt.tendsto.comp (hf.prodMk_nhds hg)

 theorem segment_norm_bound (_ : E) (v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖t•v‖ ≤ ‖v‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

 theorem moving_segment_tendsto {x v : ℕ → E} {a : E}
    (hx : Tendsto x atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 0))
    {t : ℕ → ℝ} (ht : ∀ᶠ j in atTop, t j ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun j => x j+t j•v j) atTop (𝓝 a) := by
  have hzero : Tendsto (fun j => t j•v j) atTop (𝓝 (0 : E)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (ht.mono (fun j hj => segment_norm_bound (x j) (v j) hj))
    simpa using hv.norm
  simpa using hx.add hzero

 theorem moving_segment_smooth {f : E → ℝ} {a : E} (hf : ContDiffAt ℝ ∞ f a)
    {x v : ℕ → E} (hx : Tendsto x atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x j+t•v j) := by
  have hnear : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ 2 f z :=
    (hf.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall : ∀ᶠ j in atTop, ‖x j-a‖+‖v j‖ < ε := by
    apply (tendsto_order.mp ((hx.sub tendsto_const_nhds).norm.add hv.norm)).2 ε
    simpa using hε
  filter_upwards [hsmall] with j hj t ht
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  change ‖x j+t•v j-a‖ < ε
  calc
    _ = ‖(x j-a)+t•v j‖ := by congr 1; abel
    _ ≤ ‖x j-a‖+‖t•v j‖ := norm_add_le _ _
    _ ≤ ‖x j-a‖+‖v j‖ := add_le_add (le_refl _) (segment_norm_bound (x j) (v j) ht)
    _ < ε := hj

 theorem second_limit {f : E → ℝ} {a e : E} (hf : ContDiffAt ℝ ∞ f a)
    {x d : ℕ → E} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j)-f (x j)-fderiv ℝ f (x j) (l j•d j))/(l j)^2)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) a e e / 2)) := by
  classical
  have hv : Tendsto (fun j => l j•d j) atTop (𝓝 (0 : E)) := by simpa using hl.smul hd
  have hsm := moving_segment_smooth hf hx hv
  let P (j : ℕ) (t : ℝ) : Prop := t ∈ Ioo (0 : ℝ) 1 ∧
    f (x j+l j•d j)-f (x j)-fderiv ℝ f (x j) (l j•d j) =
      fderiv ℝ (fderiv ℝ f) (x j+t•(l j•d j)) (l j•d j) (l j•d j) / 2
  have hex : ∀ᶠ j in atTop, ∃ t, P j t := hsm.mono (fun j hj => second_segment (x j) (l j•d j) hj)
  let t (j : ℕ) : ℝ := if H : ∃ t, P j t then Classical.choose H else 0
  have ht : ∀ᶠ j in atTop, P j (t j) := hex.mono (fun j hj => by
    dsimp only [t]
    rw [dite_eq_left hj]
    exact Classical.choose_spec hj)
  have hpoint := moving_segment_tendsto hx hv (ht.mono (fun j hj => ⟨hj.1.1.le,hj.1.2.le⟩))
  have hH : ContinuousAt (fderiv ℝ (fderiv ℝ f)) a :=
    ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuousAt
  have hlim := (tendsto_clm_apply (tendsto_clm_apply (hH.tendsto.comp hpoint) hd) hd).div_const 2
  apply hlim.congr'
  filter_upwards [ht,hlne] with j hj hlj
  rw [hj.2]
  simp only [map_smul,smul_apply,smul_eq_mul,Function.comp_def]
  field_simp [hlj]

 theorem first_limit {f : E → ℝ} {a e : E} (hf : ContDiffAt ℝ ∞ f a)
    {x d : ℕ → E} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j)-f (x j))/l j)
      atTop (𝓝 (fderiv ℝ f a e)) := by
  have h2 := second_limit hf hx hd hl hlne
  have hD := tendsto_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).continuousAt.tendsto.comp hx) hd
  have hh := (h2.mul hl).add hD
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [hlne] with j hj
  simp only [map_smul,smul_eq_mul,Function.comp_def]
  field_simp [hj]
  ring

end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
