import OAI.Geometry.Relativity.CKS.AngularCurvature

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def constantJet (c : ℝ) : ScalarJet := (c,0,0)

def productJet (f g : ScalarJet) : ScalarJet :=
  (f.1*g.1, (fun a => f.1*g.2.1 a+g.1*f.2.1 a), fun a b =>
    f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)

def sqrtJet (f : ScalarJet) : ScalarJet :=
  (Real.sqrt f.1, (fun a => f.2.1 a/(2*Real.sqrt f.1)), fun a b =>
    f.2.2 a b/(2*Real.sqrt f.1)-f.2.1 a*f.2.1 b/(4*Real.sqrt f.1^3))

lemma actualScalarJet_const (c : ℝ) (x : Point) : actualScalarJet (fun _ => c) x = constantJet c := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a; exact D_const _ _ _
  · ext a b; exact D_D_const _ _ _ _

lemma actualScalarJet_add {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y+g y) x = actualScalarJet f x+actualScalarJet g x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_add _ (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))
  · ext a b
    have heq : D (basis b) (fun y => f y+g y) =ᶠ[𝓝 x]
        (fun y => D (basis b) f y+D (basis b) g y) := by
      filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
      exact D_add _ (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
    change D (basis a) (D (basis b) (fun y => f y+g y)) x = _
    rw [D_congr heq]
    exact D_add _ ((contDiffAt_D hf (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))
      ((contDiffAt_D hg (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))

lemma actualScalarJet_smul (c : ℝ) {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    actualScalarJet (fun y => c*f y) x = c • actualScalarJet f x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_const_mul _ c (hf.differentiableAt (by norm_num))
  · ext a b
    have heq : D (basis b) (fun y => c*f y) =ᶠ[𝓝 x]
        (fun y => c*D (basis b) f y) := by
      filter_upwards [hf.eventually (by norm_num)] with y hyf
      exact D_const_mul _ c (hyf.differentiableAt (by norm_num))
    change D (basis a) (D (basis b) (fun y => c*f y)) x = _
    rw [D_congr heq]
    exact D_const_mul _ c ((contDiffAt_D hf (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))

lemma actualScalarJet_sub {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y-g y) x = actualScalarJet f x-actualScalarJet g x := by
  have hh : (fun y => f y-g y) = (fun y => f y+(-1)*g y) := by funext y; ring
  have hn : ContDiffAt ℝ 2 (fun y => (-1:ℝ)*g y) x := hg.const_smul (-1:ℝ)
  rw [hh,actualScalarJet_add hf hn,actualScalarJet_smul (-1) hg]
  simp [sub_eq_add_neg]

lemma actualScalarJet_mul {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y*g y) x = productJet (actualScalarJet f x) (actualScalarJet g x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_mul _ (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))
  · ext a b
    exact D_D_mul (basis b) (basis a) hf hg

lemma actualScalarJet_sqrt {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (h0 : 0 < f x) :
    actualScalarJet (fun y => Real.sqrt (f y)) x = sqrtJet (actualScalarJet f x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_sqrt _ (hf.differentiableAt (by norm_num)) h0
  · ext a b
    dsimp [actualScalarJet,sqrtJet]
    rw [D_D_sqrt (basis b) (basis a) hf h0]
    ring

lemma productJet_smooth : ContDiff ℝ ∞ (fun j : ScalarJet × ScalarJet => productJet j.1 j.2) := by
  unfold productJet
  fun_prop

lemma reciprocalJet_smooth {j : ScalarJet} (h0 : j.1 ≠ 0) : ContDiffAt ℝ ∞ reciprocalJet j := by
  unfold reciprocalJet
  apply ContDiffAt.prodMk
  · exact contDiffAt_const.div (by fun_prop) h0
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => -j.2.1 a) j).div
      (by fun_prop) (pow_ne_zero 2 h0)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => 2*j.2.1 a*j.2.1 b) j).div
      (by fun_prop) (pow_ne_zero 3 h0)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (by fun_prop) (pow_ne_zero 2 h0))

lemma sqrtJet_smooth {j : ScalarJet} (h0 : 0 < j.1) : ContDiffAt ℝ ∞ sqrtJet j := by
  have hs : ContDiffAt ℝ ∞ (fun j : ScalarJet => Real.sqrt j.1) j :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.1) j).sqrt h0.ne'
  unfold sqrtJet
  apply ContDiffAt.prodMk hs
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a) j).div (hs.const_smul (2:ℝ)) (by positivity)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (hs.const_smul (2:ℝ)) (by positivity)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a*j.2.1 b) j).div ((hs.pow 3).const_smul (4:ℝ)) (by positivity))

end
end CKSAngularGeometry

end

end OAI
