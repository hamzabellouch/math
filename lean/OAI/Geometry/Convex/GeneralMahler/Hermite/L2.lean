import OAI.Geometry.Convex.GeneralMahler.Hermite.Dense

namespace OAI
/-! Scalar coefficient calculus. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
abbrev G2 (m:ℕ) := Lp ℝ 2 (normal m)
def ModL (a:MI m) : G2 m :=
  MemLp.toLp (MM a) (lp_poly (M_poly a) (M_cont a).aestronglyMeasurable)
omit [NeZero m] in
lemma ModL_ae (a:MI m) : ModL a=ᵐ[normal m] MM a := MemLp.coeFn_toLp ..
def qcf (f:Rn m→ℝ) (a:MI m) := ∫ x,f x*MM a x ∂normal m

omit [NeZero m] in
lemma qcf_ip (f:G2 m) (a) : qcf f a = ⟪ModL a,f⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ModL_ae a] with x hx
  rw [hx]; rfl
omit [NeZero m] in
lemma qcf_ip' (f:G2 m) (a) : qcf f a=⟪f,ModL a⟫ := (qcf_ip ..).trans (real_inner_comm ..)

omit [NeZero m] in
lemma qcf_congr {f g:Rn m→ℝ} (h:f=ᵐ[normal m]g) (a:MI m) :
    qcf f a=qcf g a := by
  apply integral_congr_ae
  filter_upwards [h] with x hx; rw [hx]

omit [NeZero m] in
lemma Mod_o : Orthonormal ℝ (@ModL m) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [← qcf_ip,qcf_congr (ModL_ae _)]
  simpa [qcf,eq_comm] using M_inner b a

def HB (m:ℕ) [NeZero m] : HilbertBasis (MI m) ℝ (G2 m) :=
  HilbertBasis.mkOfOrthogonalEqBot Mod_o (by
    rw [eq_bot_iff]
    intro f hf
    have hz (a:MI m) : qcf f a=0 := by
      rw [qcf_ip]; exact hf (ModL a) (Submodule.subset_span ⟨a,rfl⟩)
    have hh := ae_zero (Lp.memLp f) hz
    change f=0
    apply Lp.ext
    filter_upwards [hh,Lp.coeFn_zero ℝ 2 (normal m)] with x hx he
    rw [hx,he]; rfl)
@[simp] lemma HB_eq (a:MI m) : HB m a=ModL a := by simp [HB]

lemma repr_eq (a:MI m) (f:G2 m) : (HB m).repr f a=qcf f a := by
  rw [qcf_ip,HilbertBasis.repr_apply_apply,HB_eq]

lemma qcf_sum {f g:Rn m→ℝ} (hf:MemLp f 2 (normal m)) (hg:MemLp g 2 (normal m)) :
    HasSum (fun a=> qcf f a*qcf g a) (∫ x,f x*g x ∂normal m) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hF : F=ᵐ[normal m] f := MemLp.coeFn_toLp ..
  have hG : G=ᵐ[normal m] g := MemLp.coeFn_toLp ..
  have hi (a) := qcf_congr hF a
  have hh (a) := qcf_congr hG a
  have hv := (HB m).hasSum_inner_mul_inner F G
  simp_rw [HB_eq,← qcf_ip', ← qcf_ip,hi,hh] at hv
  have he : ⟪F,G⟫ = ∫ x,f x*g x ∂normal m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF,hG] with x hx hy
    rw [hx,hy]
    exact mul_comm ..
  rwa [he] at hv
end GeneralMahler.HMode

end

end OAI
