import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Convex.Combination

namespace OAI

/-! Bounded analytic tubes preserve a common bound under finite convex
combinations of their real parameters. This is the scalar interpolation
step used for the finitely many shift parameters in manuscript §11. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*}

def phaseTubePoint (a eta : ι → ℝ) : ι → ℂ :=
  fun i => (a i:ℂ)+(eta i:ℂ)*Complex.I

def phaseTubeLine (a b eta : ι → ℝ) (z : ℂ) : ι → ℂ :=
  fun i => (1-z)*(a i:ℂ)+z*(b i:ℂ)+(eta i:ℂ)*Complex.I

def phaseTubeBound (F : (ι → ℂ) → ℂ) (C : ℝ) (a : ι → ℝ) : Prop :=
  ∀ eta, ‖F (phaseTubePoint a eta)‖ ≤ C

theorem phaseTubeLine_re_im (a b eta : ι → ℝ) (z : ℂ) :
    phaseTubeLine a b eta z = phaseTubePoint ((1-z.re) • a+z.re • b)
      (fun i => eta i+z.im*(b i-a i)) := by
  funext i
  apply Complex.ext
  · simp [phaseTubeLine,phaseTubePoint,Complex.mul_re,Complex.mul_im]
  · simp [phaseTubeLine,phaseTubePoint,Complex.mul_re,Complex.mul_im]
    ring

theorem convex_phaseTubeBound (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (C : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, phaseTubeBound F M a) :
    Convex ℝ {a | a ∈ D ∧ phaseTubeBound F C a} := by
  intro a ha b hb r s hr hs hrs
  refine ⟨hD ha.1 hb.1 hr hs hrs,?_⟩
  intro eta
  let f := fun z => F (phaseTubeLine a b eta z)
  obtain ⟨M,hM⟩ := hbounded
  have hfB : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨M,?_⟩
    rintro y ⟨z,hz,rfl⟩
    change ‖F (phaseTubeLine a b eta z)‖ ≤ M
    rw [phaseTubeLine_re_im]
    exact hM _ (hD ha.1 hb.1 (sub_nonneg.mpr hz.2) hz.1 (by ring)) _
  have hf0 : ∀ z ∈ Complex.re ⁻¹' {0}, ‖f z‖ ≤ C := by
    intro z hz
    change z.re = 0 at hz
    dsimp only [f]
    rw [phaseTubeLine_re_im]
    simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using
      ha.2 (fun i => eta i+z.im*(b i-a i))
  have hf1 : ∀ z ∈ Complex.re ⁻¹' {1}, ‖f z‖ ≤ C := by
    intro z hz
    change z.re = 1 at hz
    dsimp only [f]
    rw [phaseTubeLine_re_im]
    simpa only [hz,sub_self,zero_smul,one_smul,zero_add] using
      hb.2 (fun i => eta i+z.im*(b i-a i))
  have hs1 : s ≤ 1 := by linarith
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    f (z := (s:ℂ)) ⟨hs,hs1⟩ (hentire a ha.1 b hb.1 eta).diffContOnCl hfB hf0 hf1
  have hpower : C^(1-s)*C^s = C := by
    rw [← Real.rpow_add hC,sub_add_cancel,Real.rpow_one]
  have hr' : r = 1-s := by linarith
  simpa only [f,phaseTubeLine_re_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    add_zero,hpower,hr'] using h

theorem phaseTubeBound_finite_convex_combination (F : (ι → ℂ) → ℂ)
    (D : Set (ι → ℝ)) (hD : Convex ℝ D) (C : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, phaseTubeBound F M a)
    (S : Finset κ) (w : κ → ℝ) (v : κ → ι → ℝ)
    (hw : ∀ k ∈ S, 0 ≤ w k) (hsum : ∑ k ∈ S, w k = 1)
    (hv : ∀ k ∈ S, v k ∈ D) (hvertex : ∀ k ∈ S, phaseTubeBound F C (v k)) :
    phaseTubeBound F C (∑ k ∈ S, w k • v k) := by
  have hc := convex_phaseTubeBound F D hD C hC hentire hbounded
  exact (hc.sum_mem hw hsum (fun k hk => ⟨hv k hk,hvertex k hk⟩)).2

end LipschitzHilbert

end

end OAI
