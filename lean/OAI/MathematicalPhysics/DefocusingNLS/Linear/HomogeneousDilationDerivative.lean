import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDilationContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDifferentiation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalC2

namespace OAI

/-! # Right differentiation of the physical similarity dilation -/

open Filter Set Topology

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousSimilarityDilation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (s : ℝ) :
    HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  homogeneousDilation a k (Real.exp (max s 0 / 2)) ha ha1 hk
    (Real.one_le_exp_iff.mpr (by positivity))

attribute [local irreducible] homogeneousDilation homogeneousSimilarityDilation

theorem continuous_homogeneousSimilarityDilation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (fun p : ℝ × HomogeneousY a k =>
      homogeneousSimilarityDilation a k ha ha1 hk p.1 p.2) := by
  let R : ℝ × HomogeneousY a k → {R : ℝ // 1 ≤ R} := fun p =>
    ⟨Real.exp (max p.1 0 / 2), Real.one_le_exp_iff.mpr (by positivity)⟩
  have hR : Continuous R := Continuous.subtype_mk (by fun_prop) _
  simpa only [Function.comp_def, R, homogeneousSimilarityDilation] using
    (continuous_homogeneousDilation_uncurry a k ha ha1 hk).comp
      (hR.prodMk continuous_snd)

theorem homogeneousSimilarityDilation_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (s : ℝ) (q : HomogeneousY a k) (x : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousSimilarityDilation a k ha ha1 hk s q) x =
      (Real.exp (-a * max s 0) : ℝ) *
        homogeneousPhysicalCLM a k ha ha1 hk q (Real.exp (-max s 0 / 2) • x) := by
  rw [homogeneousSimilarityDilation, homogeneousDilation_physical, ← Real.exp_mul,
    ← Real.exp_neg]
  rw [show max s 0 / 2 * (-2 * a) = -a * max s 0 by ring,
    show -(max s 0 / 2) = -max s 0 / 2 by ring]

@[simp] theorem homogeneousSimilarityDilation_zero (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (q : HomogeneousY a k) :
    homogeneousSimilarityDilation a k ha ha1 hk 0 q = q := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  ext x
  rw [homogeneousSimilarityDilation_physical]
  simp

theorem hasDerivWithinAt_homogeneousSimilarityDilation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (q g : HomogeneousY a k)
    (hg : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk g x =
      -(a : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk q x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) x x) :
    HasDerivWithinAt (fun s => homogeneousSimilarityDilation a k ha ha1 hk s q)
      g (Ici 0) 0 := by
  let Q := fun x : E => homogeneousPhysicalCLM a k ha ha1 hk q x
  have hQ : Differentiable ℝ Q :=
    (contDiff_homogeneousPhysical a k ha ha1 hk q).differentiable (by norm_num)
  have hc (u : HomogeneousY a k) :
      Continuous (fun s => homogeneousSimilarityDilation a k ha ha1 hk s u) :=
    (continuous_homogeneousSimilarityDilation a k ha ha1 hk).comp
      (continuous_id.prodMk continuous_const)
  have hd : ∀ t : ℝ, 0 < t → ∀ x : E, HasDerivAt
      (fun s => homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousSimilarityDilation a k ha ha1 hk s q) x)
      (homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousSimilarityDilation a k ha ha1 hk t g) x) t := by
    intro t ht x
    have hscale := (((hasDerivAt_id t).neg.div_const 2).exp).smul_const x
    have hcomp := (hQ (Real.exp (-t / 2) • x)).hasFDerivAt.comp_hasDerivAt t hscale
    have hamp := (((hasDerivAt_id t).const_mul (-a)).exp).ofReal_comp
    have h := hamp.mul hcomp
    have he : (fun s => homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousSimilarityDilation a k ha ha1 hk s q) x) =ᶠ[𝓝 t]
        (fun s => (Real.exp (-a * s) : ℂ) * Q (Real.exp (-s / 2) • x)) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      rw [homogeneousSimilarityDilation_physical, max_eq_left hs.le]
    apply HasDerivAt.congr_of_eventuallyEq _ he
    convert h using 1
    · funext s
      rfl
    · rw [homogeneousSimilarityDilation_physical, max_eq_left ht.le, hg]
      dsimp only [Q, Function.comp_apply]
      simp only [Pi.neg_apply, id_eq, neg_div, neg_mul, one_div,
        ContinuousLinearMap.map_smul, Complex.real_smul, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_one]
      push_cast
      ring
  have h := hasDerivWithinAt_homogeneous_of_physical_Ici a k ha ha1 hk
    (fun s => homogeneousSimilarityDilation a k ha ha1 hk s q)
    (fun s => homogeneousSimilarityDilation a k ha ha1 hk s g)
    (hc q).continuousOn (hc g) hd 0 le_rfl
  simpa only [homogeneousSimilarityDilation_zero] using h

end DefocusingNLS

end OAI
