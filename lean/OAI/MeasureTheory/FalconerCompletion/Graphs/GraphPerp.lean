import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
namespace CurrentFalconer
open Set Metric
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def graphPerpND (v x : V) : V := x-inner ℝ x v • v

lemma graphPerpND_sub (v x y : V) :
    graphPerpND v (x-y) = graphPerpND v x-graphPerpND v y := by
  simp only [graphPerpND,inner_sub_left,sub_smul]; abel

lemma graphPerpND_add (v x y : V) :
    graphPerpND v (x+y) = graphPerpND v x+graphPerpND v y := by
  simp only [graphPerpND,inner_add_left,add_smul]; abel

lemma graphPerpND_norm_le (v x : V) (hv : ‖v‖=1) : ‖graphPerpND v x‖ ≤ ‖x‖ := by
  have he : ‖graphPerpND v x‖^2=‖x‖^2-(inner ℝ x v)^2 := by
    rw [graphPerpND,norm_sub_sq_real,norm_smul,inner_smul_right,hv,Real.norm_eq_abs]
    rw [mul_one,sq_abs]
    ring
  nlinarith [norm_nonneg (graphPerpND v x),norm_nonneg x,sq_nonneg (inner ℝ x v)]

lemma graphPerpND_change_direction (v w x : V) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    ‖graphPerpND w x-graphPerpND v x‖ ≤ 2*‖x‖*dist v w := by
  have he : graphPerpND w x-graphPerpND v x =
      inner ℝ x v • (v-w)+inner ℝ x (v-w) • w := by
    simp only [graphPerpND,inner_sub_right,smul_sub,sub_smul]; abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ x v • (v-w)‖+‖inner ℝ x (v-w) • w‖ := norm_add_le _ _
    _ = |inner ℝ x v| *‖v-w‖+|inner ℝ x (v-w)| := by
      simp [norm_smul,Real.norm_eq_abs,hw]
    _ ≤ (‖x‖*‖v‖)*‖v-w‖+‖x‖*‖v-w‖ := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = _ := by rw [hv,dist_eq_norm]; ring

theorem graph_witness_tubeND (v w a x y : V) (hv : ‖v‖=1) (hw : ‖w‖=1)
    {τ δ D : ℝ} (_hδ : 0 ≤ δ) (hxy : dist x y ≤ D) (hvw : dist v w ≤ δ)
    (hx : ‖graphPerpND v (x-a)‖ ≤ τ) (hy : ‖graphPerpND v (y-a)‖ ≤ τ) :
    ‖graphPerpND w (x-y)‖ ≤ 2*τ+2*D*δ := by
  have hD : 0 ≤ D := dist_nonneg.trans hxy
  have hp : ‖graphPerpND v (x-y)‖ ≤ 2*τ := by
    have he : x-y=(x-a)-(y-a) := by abel
    rw [he,graphPerpND_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖graphPerpND w (x-y)-graphPerpND v (x-y)‖+‖graphPerpND v (x-y)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 2*‖x-y‖*dist v w+2*τ := add_le_add (graphPerpND_change_direction v w (x-y) hv hw) hp
    _ ≤ 2*D*δ+2*τ := by gcongr; simpa [dist_eq_norm] using hxy
    _ = _ := by ring

theorem graph_scalar_perp_ballND (v a x : V) (hv : ‖v‖=1) {t τ : ℝ}
    (hp : ‖graphPerpND v (x-a)‖ ≤ τ)
    (hs : |t+inner ℝ (x-a) v| ≤ τ) :
    dist x (a-t • v) ≤ 2*τ := by
  have he : x-(a-t • v)=graphPerpND v (x-a)+(t+inner ℝ (x-a) v) • v := by
    simp only [graphPerpND,add_smul]; abel
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖graphPerpND v (x-a)‖+‖(t+inner ℝ (x-a) v) • v‖ := norm_add_le _ _
    _ ≤ τ+τ := by simpa [norm_smul,Real.norm_eq_abs,hv] using add_le_add hp hs
    _ = _ := by ring

lemma graph_phase_changeND (v w d Δ : V) (hw : ‖w‖=1) :
    |inner ℝ w Δ-inner ℝ v d| ≤ dist w v*‖d‖+‖Δ-d‖ := by
  have he : inner ℝ w Δ-inner ℝ v d=inner ℝ (w-v) d+inner ℝ w (Δ-d) := by
    simp only [inner_sub_left,inner_sub_right]; ring
  rw [he]
  calc
    _ ≤ |inner ℝ (w-v) d|+|inner ℝ w (Δ-d)| := abs_add_le _ _
    _ ≤ ‖w-v‖*‖d‖+‖w‖*‖Δ-d‖ := add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = _ := by rw [hw,one_mul,dist_eq_norm]

lemma graph_perp_center_changeND (v d Δ : V) (hv : ‖v‖=1) :
    ‖graphPerpND v d‖ ≤ ‖graphPerpND v Δ‖+‖Δ-d‖ := by
  calc
    _ = ‖graphPerpND v Δ+graphPerpND v (d-Δ)‖ := by rw [← graphPerpND_add]; congr 2; abel
    _ ≤ ‖graphPerpND v Δ‖+‖graphPerpND v (d-Δ)‖ := norm_add_le _ _
    _ ≤ ‖graphPerpND v Δ‖+‖d-Δ‖ := add_le_add le_rfl (graphPerpND_norm_le v (d-Δ) hv)
    _ = _ := by rw [norm_sub_rev]

def graphAffineLineND (v c : V) : Set V := {z | ∃ t : ℝ, z=c+t • v}

lemma graphAffineLineND_nonempty (v c : V) : (graphAffineLineND v c).Nonempty := by
  exact ⟨c,0,by simp⟩

lemma graphPerpND_sub_smul (v x : V) (hv : ‖v‖=1) (t : ℝ) :
    graphPerpND v (x-t • v)=graphPerpND v x := by
  simp only [graphPerpND,inner_sub_left,inner_smul_left,real_inner_self_eq_norm_sq,hv,one_pow,mul_one,sub_smul,starRingEnd_apply,star_trivial]
  abel

lemma infDist_graphAffineLineND (v c x : V) (hv : ‖v‖=1) :
    infDist x (graphAffineLineND v c)=‖graphPerpND v (x-c)‖ := by
  apply le_antisymm
  · have hy : c+inner ℝ (x-c) v • v ∈ graphAffineLineND v c :=
      ⟨inner ℝ (x-c) v,rfl⟩
    calc
      _ ≤ dist x (c+inner ℝ (x-c) v • v) := infDist_le_dist_of_mem hy
      _ = _ := by rw [dist_eq_norm,graphPerpND]; congr 1; abel
  · apply (le_infDist (graphAffineLineND_nonempty v c)).mpr
    rintro y ⟨t,rfl⟩
    have he : x-(c+t • v)=(x-c)-t • v := by abel
    rw [dist_eq_norm,he]
    rw [← graphPerpND_sub_smul v (x-c) hv t]
    exact graphPerpND_norm_le v ((x-c)-t • v) hv

end CurrentFalconer
end
end

end OAI
