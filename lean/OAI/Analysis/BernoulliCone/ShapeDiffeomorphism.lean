import OAI.Analysis.BernoulliCone.RankOnePerturbation

namespace OAI

universe uE

section
noncomputable section
open Set Filter Metric
open scoped NNReal Topology
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def deform (φ : E → ℝ) (e : E) (t : ℝ) (x : E) : E := x + (t*φ x) • e

lemma displacement_lipschitz {φ : E → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (e : E) (t : ℝ) : LipschitzWith (‖t‖₊ * C * ‖e‖₊) (fun x => (t*φ x) • e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hφ.dist_le_mul x y
  simp only [dist_eq_norm] at hh ⊢
  rw [← sub_smul,← mul_sub,norm_smul,norm_mul]
  exact (by simpa only [NNReal.coe_mul,coe_nnnorm,mul_assoc,mul_left_comm,mul_comm] using
    mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg t) (norm_nonneg e)))

lemma hasFDerivAt_deform {φ : E → ℝ} {a : E →L[ℝ] ℝ} {x : E}
    (hφ : HasFDerivAt φ a x) (e : E) (t : ℝ) :
    HasFDerivAt (deform φ e t) (rankOneMap a e t) x := by
  have h := (hasFDerivAt_id x).add ((hφ.const_smul t).smul_const e)
  convert h using 1
  · rfl
  · ext y
    simp [rankOneMap,smul_smul]

lemma inverse_hasFDerivAt_deform {φ : E → ℝ} {a : E →L[ℝ] ℝ} {x : E}
    (hφ : HasFDerivAt φ a x) (e : E) (t : ℝ) (h : 1+t*a e ≠ 0)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) :
    HasFDerivAt g.symm (rankOneInverse a e t) (g x) := by
  have hf : HasFDerivAt g (rankOneMap a e t) x := by
    convert hasFDerivAt_deform hφ e t using 1
    exact funext hg
  have hs := HasFDerivAt.of_local_left_inverse (g.symm.continuous.continuousAt (x:=g x))
    (f':=rankOneEquiv a e t h) (by simpa using hf)
    (Eventually.of_forall g.apply_symm_apply)
  simpa using hs

omit [NormedSpace ℝ E] in
lemma image_eq_of_fixed_compl (g : E ≃ₜ E) (s : Set E)
    (hg : ∀ x ∉ s, g x=x) : g '' s=s := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    by_contra hx
    have h := hg (g y) hx
    have hh := g.injective h
    rw [hh] at hx
    exact hx hy
  · intro hx
    refine ⟨g.symm x,?_,g.apply_symm_apply x⟩
    by_contra hy
    have h := hg (g.symm x) hy
    rw [g.apply_symm_apply] at h
    exact hy (h ▸ hx)

omit [NormedSpace ℝ E] in
lemma inv_fixed_of_fixed (g : E ≃ₜ E) {x : E} (hx : g x=x) : g.symm x=x := by
  apply g.injective
  simpa using hx.symm

lemma pullback_diff_support {φ u : E → ℝ} (e : E) (t : ℝ)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) :
    tsupport (fun x => u (g.symm x)-u x) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_tsupport
  intro hφ
  have hfixed : g x=x := by rw [hg]; simp [deform,hφ]
  have hh := inv_fixed_of_fixed g hfixed
  exact hx (by simp [hh])
end Bernoulli.Shape

end
end

end OAI
