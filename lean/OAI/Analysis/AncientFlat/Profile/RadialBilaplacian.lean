import OAI.Analysis.AncientFlat.Profile.RadialLaplacian

namespace OAI
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
open InnerProductSpace
namespace FlatRadial
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def T (f : ℝ → ℝ) (y : ℝ) : ℝ := y*deriv (deriv f) y+12*deriv f y
lemma L_eq_T (f : ℝ → ℝ) : L 24 f=fun y => 4*T f y := by
  funext y
  simp only [L,T]
  norm_num
  ring
lemma T_const_mul (c : ℝ) (f : ℝ → ℝ) : T (fun y => c*f y)=fun y => c*T f y := by
  funext y
  simp only [T,deriv_const_mul_field',deriv_const_mul_field]
  ring
lemma L_L_T (f : ℝ → ℝ) : L 24 (L 24 f)=fun y => 16*T (T f) y := by
  rw [L_eq_T,L_eq_T,T_const_mul]
  funext y
  dsimp
  ring
lemma contDiffAt_L (m : ℕ) (f : ℝ → ℝ) {y : ℝ} (hf : ContDiffAt ℝ 4 f y) :
    ContDiffAt ℝ 2 (L m f) y := by
  have hd : ContDiffAt ℝ 3 (deriv f) y := hf.derivWithin (by norm_num)
  have hdd : ContDiffAt ℝ 2 (deriv (deriv f)) y := hd.derivWithin (by norm_num)
  exact ((contDiffAt_const.mul contDiffAt_id).mul hdd).add (contDiffAt_const.mul (hd.of_le (by norm_num)))
lemma bilaplacian_lift (f : ℝ → ℝ) (x : V) (hf : ContDiffAt ℝ 4 f (‖x‖^2)) :
    Δ (Δ (lift (V := V) f)) x=L (Module.finrank ℝ V) (L (Module.finrank ℝ V) f) (‖x‖^2) := by
  have he : Δ (lift (V := V) f)=ᶠ[𝓝 x] lift (L (Module.finrank ℝ V) f) := by
    have hn := (contDiff_norm_sq ℝ (n:=4)).continuous.continuousAt.eventually
      (hf.eventually (by norm_num : (4:ℕ∞ω)≠∞))
    filter_upwards [hn] with z hz
    exact laplacian_lift f z (hz.of_le (by norm_num))
  have he2 := (laplacian_congr_nhds he).self_of_nhds
  rw [he2,laplacian_lift _ x (contDiffAt_L _ f hf)]
lemma bilaplacian_lift_24 (hm : Module.finrank ℝ V=24) (f : ℝ → ℝ) (x : V)
    (hf : ContDiffAt ℝ 4 f (‖x‖^2)) :
    Δ (Δ (lift (V := V) f)) x/16=T (T f) (‖x‖^2) := by
  rw [bilaplacian_lift f x hf,hm,L_L_T]
  dsimp
  ring
end FlatRadial

end

end OAI
