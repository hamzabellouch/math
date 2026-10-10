import OAI.MathematicalPhysics.Transonic.Phase.Timelike

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology BigOperators

def GlobalProfile.radialC (P : GlobalProfile) (z : ℝ) : ℝ :=
  P.b*P.radialH z*P.radialIntegrand z
def GlobalProfile.radialA (P : GlobalProfile) (z : ℝ) : ℝ := P.b*P.radialH z+z*P.radialC z
def GlobalProfile.radialM (P : GlobalProfile) (z : ℝ) : ℝ := P.radialA z^2-z*P.radialC z^2
def GlobalProfile.radialF (P : GlobalProfile) (z : ℝ) : ℝ := P.radialM z^((1:ℝ)/3)*P.radialA z
def GlobalProfile.radialJ (P : GlobalProfile) (z : ℝ) : ℝ := P.radialM z^((1:ℝ)/3)*P.radialC z

lemma GlobalProfile.radialC_sq (P : GlobalProfile) (y : ℝ) :
    P.radialC (y^2)=P.A y*P.g (y^2) := by
  rw [GlobalProfile.radialC,GlobalProfile.radialIntegrand,← P.H_radial,P.A_eq,GlobalProfile.velocity]
  have he : y*(y*P.g (y^2))=y^2*P.g (y^2) := by ring
  rw [he]
  ring
lemma GlobalProfile.B_radial (P : GlobalProfile) (y : ℝ) : P.B y=y*P.radialC (y^2) := by
  rw [P.radialC_sq,P.B_eq,GlobalProfile.velocity]
  ring
lemma GlobalProfile.radialA_sq (P : GlobalProfile) (y : ℝ) : P.radialA (y^2)=P.A y := by
  have hB := P.B_radial y
  unfold GlobalProfile.B at hB
  rw [GlobalProfile.radialA,← P.H_radial,GlobalProfile.A,hB]
  ring
lemma GlobalProfile.radialM_sq (P : GlobalProfile) (y : ℝ) : P.radialM (y^2)=P.M0 y := by
  rw [GlobalProfile.radialM,P.radialA_sq,GlobalProfile.M0,P.B_radial]
  ring
lemma GlobalProfile.radialM_pos (P : GlobalProfile) {z : ℝ} (hz : 0≤z) : 0<P.radialM z := by
  rw [← Real.sq_sqrt hz,P.radialM_sq]
  exact P.M0_pos _
lemma GlobalProfile.radialC_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialC (Ici 0) :=
  (contDiffOn_const.mul P.radialH_smooth).mul P.radialIntegrand_smooth
lemma GlobalProfile.radialA_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialA (Ici 0) :=
  (contDiffOn_const.mul P.radialH_smooth).add (contDiffOn_id.mul P.radialC_smooth)
lemma GlobalProfile.radialM_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialM (Ici 0) :=
  (P.radialA_smooth.pow 2).sub (contDiffOn_id.mul (P.radialC_smooth.pow 2))
lemma GlobalProfile.radialF_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialF (Ici 0) :=
  (P.radialM_smooth.rpow_const_of_ne (fun _ hz => ne_of_gt (P.radialM_pos hz))).mul P.radialA_smooth
lemma GlobalProfile.radialJ_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialJ (Ici 0) :=
  (P.radialM_smooth.rpow_const_of_ne (fun _ hz => ne_of_gt (P.radialM_pos hz))).mul P.radialC_smooth
lemma GlobalProfile.F_radial (P : GlobalProfile) (y : ℝ) : P.F y=P.radialF (y^2) := by
  rw [GlobalProfile.radialF,P.radialM_sq,P.radialA_sq,GlobalProfile.F]
lemma GlobalProfile.G_radial (P : GlobalProfile) (y : ℝ) : P.G y=y*P.radialJ (y^2) := by
  rw [GlobalProfile.radialJ,P.radialM_sq,GlobalProfile.G,P.B_radial]
  ring

lemma smooth_square_chain {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ici 0)) (y : ℝ) :
    HasDerivAt (fun q => f (q^2)) (2*y*derivWithin f (Ici 0) (y^2)) y := by
  have hd := (hf.differentiableOn (by simp) (y^2) (sq_nonneg y)).hasDerivWithinAt
  have hc := hd.comp_hasDerivAt (h:=fun q : ℝ => q^2) y ((hasDerivAt_id y).pow 2)
    (Filter.Eventually.of_forall (fun q => sq_nonneg q))
  convert hc using 1 <;> try rfl
  norm_num only [Nat.cast_ofNat,pow_one,one_mul,id_eq]
  ring

lemma GlobalProfile.F_derivative_radial (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.F (2*y*derivWithin P.radialF (Ici 0) (y^2)) y := by
  rw [show P.F=(fun q => P.radialF (q^2)) from funext P.F_radial]
  exact smooth_square_chain P.radialF_smooth y
lemma GlobalProfile.G_derivative_radial (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.G (P.radialJ (y^2)+2*y^2*derivWithin P.radialJ (Ici 0) (y^2)) y := by
  have hd := (hasDerivAt_id y).mul (smooth_square_chain P.radialJ_smooth y)
  rw [show P.G=(fun q => q*P.radialJ (q^2)) from funext P.G_radial]
  convert hd using 1 <;> try rfl
  simp only [id_eq]
  ring

lemma GlobalProfile.g_zero (P : GlobalProfile) : P.g 0=P.beta*ell/4 := by
  have hg : ContDiff ℝ ∞ (fun y : ℝ => P.g (y^2)) :=
    P.smooth.comp_contDiff (contDiff_id.pow 2) (fun y => sq_nonneg y)
  have hd := (hasDerivAt_id (0:ℝ)).mul ((hg.differentiable (by simp) 0).hasDerivAt)
  have he : HasDerivAt P.velocity (P.g 0) 0 := by
    convert hd using 1 <;> first | rfl | simp
  rw [← he.deriv]
  exact source_axis_slope P.smooth P.equation

lemma GlobalProfile.radial_transport_sq (P : GlobalProfile) {z : ℝ} (hz : 0≤z) :
    ell*P.beta*P.radialF z+2*z*derivWithin P.radialF (Ici 0) z-
      4*P.radialJ z-2*z*derivWithin P.radialJ (Ici 0) z=0 := by
  rcases eq_or_lt_of_le hz with hz|hz
  · subst z
    simp only [mul_zero,zero_mul,sub_zero,add_zero]
    dsimp only [GlobalProfile.radialF,GlobalProfile.radialJ,GlobalProfile.radialA,
      GlobalProfile.radialC,GlobalProfile.radialIntegrand]
    rw [P.g_zero]
    ring
  · have hy : 0<Real.sqrt z := Real.sqrt_pos.mpr hz
    have he := P.radial_transport hy
    rw [P.F_radial,(P.F_derivative_radial _).deriv,(P.G_derivative_radial _).deriv,
      P.G_radial,Real.sq_sqrt hz.le] at he
    have hs := Real.sq_sqrt hz.le
    field_simp [ne_of_gt hy] at he
    rw [hs] at he
    linarith only [he]

end SepticProfile

end
end

end OAI
