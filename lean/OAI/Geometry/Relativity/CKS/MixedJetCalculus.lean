import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CollarExpansionRealization
import OAI.Geometry.Relativity.CKS.NonroundFrame

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev Mat := Matrix A A ℝ
abbrev ScalarJet := ℝ × (I → ℝ) × (I → I → ℝ)
def actualScalarJet (f : Point → ℝ) (x : Point) : ScalarJet :=
  (f x,fun a => D (basis a) f x,fun a b => D (basis a) (D (basis b) f) x)

def constantJet (c : ℝ) : ScalarJet := (c,0,0)

def productJet (f g : ScalarJet) : ScalarJet :=
  (f.1*g.1, (fun a => f.1*g.2.1 a+g.1*f.2.1 a), fun a b =>
    f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)

def reciprocalJet (z : ScalarJet) : ScalarJet :=
  (1/z.1, (fun a => -z.2.1 a/z.1^2), fun a b =>
    2*z.2.1 a*z.2.1 b/z.1^3-z.2.2 a b/z.1^2)

lemma actual_reciprocal {z : Point → ℝ} {x : Point} (hz : ContDiffAt ℝ 2 z x) (h0 : z x ≠ 0) :
    actualScalarJet (fun y => 1/z y) x = reciprocalJet (actualScalarJet z x) := by
  dsimp only [actualScalarJet, reciprocalJet]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a
    exact D_inv_inv (basis a) (hz.differentiableAt (by norm_num)) h0
  · ext a b
    dsimp [actualScalarJet,reciprocalJet]
    rw [D_D_inv (basis b) (basis a) hz h0]
    ring

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

lemma actualScalarJet_congr {f g : Point → ℝ} {x : Point} (h : f =ᶠ[𝓝 x] g) :
    actualScalarJet f x = actualScalarJet g x := by
  apply Prod.ext
  · exact h.eq_of_nhds
  apply Prod.ext
  · ext a
    exact D_congr h (basis a)
  · ext a b
    have hd : D (basis b) f =ᶠ[𝓝 x] D (basis b) g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : Point →L[ℝ] ℝ => L (basis b)) hy
    exact D_congr hd (basis a)

lemma actualScalarJet_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => c*f y+d*g y) x = c • actualScalarJet f x+d • actualScalarJet g x := by
  have hcf : ContDiffAt ℝ 2 (fun y => c*f y) x := by simpa only [smul_eq_mul] using hf.const_smul c
  have hdg : ContDiffAt ℝ 2 (fun y => d*g y) x := by simpa only [smul_eq_mul] using hg.const_smul d
  rw [actualScalarJet_add hcf hdg,
    actualScalarJet_smul c hf,actualScalarJet_smul d hg]

lemma actualScalarJet_D_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) (a : I) :
    actualScalarJet (D (basis a) (fun y => c*f y+d*g y)) x =
      c • actualScalarJet (D (basis a) f) x+d • actualScalarJet (D (basis a) g) x := by
  have heq : D (basis a) (fun y => c*f y+d*g y) =ᶠ[𝓝 x]
      (fun y => c*D (basis a) f y+d*D (basis a) g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    have hfd := hyf.differentiableAt (by norm_num)
    have hgd := hyg.differentiableAt (by norm_num)
    rw [D_add _ (hfd.const_mul c) (hgd.const_mul d),D_const_mul _ c hfd,D_const_mul _ d hgd]
  rw [actualScalarJet_congr heq]
  exact actualScalarJet_linear c d (contDiffAt_D hf (by norm_num) (basis a))
    (contDiffAt_D hg (by norm_num) (basis a))

lemma actualScalarJet_neg {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    actualScalarJet (fun y => -(f y)) x = -actualScalarJet f x := by
  simpa using actualScalarJet_smul (-1) hf

lemma actualScalarJet_sum {α : Type*} (s : Finset α) {f : α → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    actualScalarJet (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, actualScalarJet (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change actualScalarJet (fun _ => 0) x = constantJet 0
    exact actualScalarJet_const 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [actualScalarJet_add (hf a (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end
end CKSMixedGeometry

end

end OAI
