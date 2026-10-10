import OAI.Geometry.Relativity.CKS.ScalarThreeJets
import OAI.Geometry.Relativity.CKS.MixedJetCalculus

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev ScalarThreeJet := ScalarJet × (I → ScalarJet)
def actualThreeJet (f : Point → ℝ) (x : Point) : ScalarThreeJet :=
  (actualScalarJet f x,fun a => actualScalarJet (D (basis a) f) x)
def constantThreeJet (c : ℝ) : ScalarThreeJet := (constantJet c,0)
def productThreeJet (f g : ScalarThreeJet) : ScalarThreeJet :=
  (productJet f.1 g.1,fun a => productJet f.1 (g.2 a)+productJet g.1 (f.2 a))
def reciprocalThreeJet (f : ScalarThreeJet) : ScalarThreeJet :=
  (reciprocalJet f.1,fun a => -productJet (productJet (reciprocalJet f.1) (reciprocalJet f.1)) (f.2 a))

lemma actualThreeJet_const (c : ℝ) (x : Point) :
    actualThreeJet (fun _ => c) x = constantThreeJet c := by
  apply Prod.ext
  · exact actualScalarJet_const c x
  · funext a
    change actualScalarJet (D (basis a) (fun _ : Point => c)) x = 0
    have hz : D (basis a) (fun _ : Point => c) = (fun _ => 0) := by
      funext y
      exact D_const _ _ _
    rw [hz]
    exact actualScalarJet_const 0 x

lemma actualThreeJet_zero (x : Point) : actualThreeJet (fun _ => 0) x = 0 := by
  exact actualThreeJet_const 0 x

lemma actualThreeJet_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => c*f y+d*g y) x = c • actualThreeJet f x+d • actualThreeJet g x := by
  apply Prod.ext
  · exact actualScalarJet_linear c d (hf.of_le (by norm_num)) (hg.of_le (by norm_num))
  · funext a
    exact actualScalarJet_D_linear c d hf hg a

lemma actualThreeJet_smul (c : ℝ) {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    actualThreeJet (fun y => c*f y) x = c • actualThreeJet f x := by
  simpa using actualThreeJet_linear c 0 hf (contDiffAt_const (c := (0:ℝ)))

lemma actualThreeJet_add {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => f y+g y) x = actualThreeJet f x+actualThreeJet g x := by
  simpa using actualThreeJet_linear 1 1 hf hg

lemma actualThreeJet_neg {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    actualThreeJet (fun y => -f y) x = -actualThreeJet f x := by
  simpa using actualThreeJet_smul (-1) hf

lemma actualThreeJet_sub {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => f y-g y) x = actualThreeJet f x-actualThreeJet g x := by
  simpa [sub_eq_add_neg] using actualThreeJet_linear 1 (-1) hf hg

theorem actualThreeJet_mul {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => f y*g y) x = productThreeJet (actualThreeJet f x) (actualThreeJet g x) := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hg2 : ContDiffAt ℝ 2 g x := hg.of_le (by norm_num)
  apply Prod.ext
  · exact actualScalarJet_mul hf2 hg2
  · funext a
    have heq : D (basis a) (fun y => f y*g y) =ᶠ[𝓝 x]
        (fun y => f y*D (basis a) g y+g y*D (basis a) f y) := by
      filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
      exact D_mul _ (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
    change actualScalarJet (D (basis a) (fun y => f y*g y)) x = _
    rw [actualScalarJet_congr heq]
    have hfd : ContDiffAt ℝ 2 (D (basis a) f) x := contDiffAt_D hf (by norm_num) _
    have hgd : ContDiffAt ℝ 2 (D (basis a) g) x := contDiffAt_D hg (by norm_num) _
    rw [actualScalarJet_add (hf2.mul hgd) (hg2.mul hfd),
      actualScalarJet_mul hf2 hgd,actualScalarJet_mul hg2 hfd]
    rfl

theorem actualThreeJet_reciprocal {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (h0 : f x ≠ 0) :
    actualThreeJet (fun y => 1/f y) x = reciprocalThreeJet (actualThreeJet f x) := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hi : ContDiffAt ℝ 2 (fun y => 1/f y) x := contDiffAt_const.div hf2 h0
  apply Prod.ext
  · exact actual_reciprocal hf2 h0
  · funext a
    have heq : D (basis a) (fun y => 1/f y) =ᶠ[𝓝 x]
        (fun y => -((1/f y)*(1/f y)*D (basis a) f y)) := by
      filter_upwards [hf.eventually (by norm_num),hf.continuousAt.eventually_ne h0] with y hyf hy0
      rw [D_inv_inv _ (hyf.differentiableAt (by norm_num)) hy0]
      field_simp
    change actualScalarJet (D (basis a) (fun y => 1/f y)) x = _
    rw [actualScalarJet_congr heq]
    have hfd : ContDiffAt ℝ 2 (D (basis a) f) x := contDiffAt_D hf (by norm_num) _
    rw [actualScalarJet_neg ((hi.mul hi).mul hfd),actualScalarJet_mul (hi.mul hi) hfd,
      actualScalarJet_mul hi hi,actual_reciprocal hf2 h0]
    rfl

lemma productThreeJet_smooth : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => productThreeJet j.1 j.2) := by
  unfold productThreeJet
  apply ContDiff.prodMk
  · exact productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => (j.1.1,j.2.1)))
  apply contDiff_pi.mpr
  intro a
  exact (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => (j.1.1,j.2.2 a)))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => (j.2.1,j.1.2 a))))

lemma reciprocalThreeJet_smooth {f : ScalarThreeJet} (h0 : f.1.1 ≠ 0) :
    ContDiffAt ℝ ∞ reciprocalThreeJet f := by
  have hi : ContDiffAt ℝ ∞ (fun j : ScalarThreeJet => reciprocalJet j.1) f :=
    (reciprocalJet_smooth h0).comp f (by fun_prop)
  have hp : ContDiffAt ℝ ∞ (fun j : ScalarThreeJet => productJet (reciprocalJet j.1) (reciprocalJet j.1)) f :=
    productJet_smooth.contDiffAt.comp f (hi.prodMk hi)
  apply ContDiffAt.prodMk hi
  apply contDiffAt_pi.mpr
  intro a
  exact (productJet_smooth.contDiffAt.comp f
    (hp.prodMk (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarThreeJet => j.2 a) f))).neg

end
end CKSMixedGeometry

end

end OAI
