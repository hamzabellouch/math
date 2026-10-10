import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDilationDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchrodingerDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StrongOperatorDerivative

namespace OAI

/-! # Classical Laplacian and dilation data give a strong free generator -/

open Filter Set Topology
open scoped Laplacian

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousFreeOperator homogeneousSimilarityDilation
  homogeneousSchrodingerOperator

@[simp] theorem homogeneousSchrodingerOperator_zero (a k : ℝ) (q : HomogeneousY a k) :
    homogeneousSchrodingerOperator a k 0 q = q := by
  unfold homogeneousSchrodingerOperator
  apply MeasureTheory.Lp.ext
  filter_upwards [homogeneousSchrodingerVector_ae a k 0 q] with ξ hξ
  change homogeneousSchrodingerVector a k 0 q ξ = q ξ
  simpa only [homogeneousSchrodingerPhase, neg_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, one_mul] using hξ

theorem homogeneousFreeOperator_factor (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hs : 0 ≤ s) (q : HomogeneousY a k) :
    homogeneousFreeOperator a b k s ha ha1 hk q =
      Complex.exp (Complex.I * (b : ℂ) * (s : ℂ)) •
        homogeneousSimilarityDilation a k ha ha1 hk s
          (homogeneousSchrodingerOperator a k (1 - Real.exp (-s)) q) := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  ext x
  rw [homogeneousFreeOperator_physical,
    (homogeneousPhysicalCLM a k ha ha1 hk).map_smul]
  change _ = Complex.exp (Complex.I * (b : ℂ) * (s : ℂ)) *
    homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousSimilarityDilation a k ha ha1 hk s
        (homogeneousSchrodingerOperator a k (1 - Real.exp (-s)) q)) x
  rw [homogeneousSimilarityDilation_physical, max_eq_left hs]
  have hA : homogeneousPhysicalAmplitude a b s =
      Complex.exp (Complex.I * (b : ℂ) * (s : ℂ)) * (Real.exp (-a * s) : ℂ) := by
    rw [homogeneousPhysicalAmplitude, Complex.exp_add, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hA]
  ring

theorem homogeneousFree_hasDerivWithinAt_of_classical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (q qL g : HomogeneousY a k)
    (hL : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk qL x =
      Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) x)
    (hg : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk g x =
      -(a : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk q x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) x x) :
    HasDerivWithinAt (fun s => homogeneousFreeOperator a b k s ha ha1 hk q)
      (g + Complex.I • qL + (Complex.I * (b : ℂ)) • q) (Ici 0) 0 := by
  let v := fun s => homogeneousSchrodingerOperator a k (1 - Real.exp (-s)) q
  have hv : HasDerivAt v (Complex.I • qL) 0 := by
    have ht : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) 1 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1) using 1 <;> norm_num
    have h := (hasDerivAt_homogeneousSchrodinger a k ha ha1 hk q qL hL (1 - Real.exp (-0))).scomp 0 ht
    simpa only [Function.comp_def, v, neg_zero, Real.exp_zero, sub_self, homogeneousSchrodingerOperator_zero, one_smul] using h
  have hv0 : v 0 = q := by simp [v]
  have hg' := hasDerivWithinAt_homogeneousSimilarityDilation a k ha ha1 hk q g hg
  rw [← hv0] at hg'
  have hD := hasDerivWithinAt_strong_apply
    (fun s => (homogeneousSimilarityDilation a k ha ha1 hk s).restrictScalars ℝ)
    v (Complex.I • qL) g (continuous_homogeneousSimilarityDilation a k ha ha1 hk)
    hv.hasDerivWithinAt hg'
  change HasDerivWithinAt
    (fun s => homogeneousSimilarityDilation a k ha ha1 hk s (v s))
    (g + homogeneousSimilarityDilation a k ha ha1 hk 0 (Complex.I • qL)) (Ici 0) 0 at hD
  rw [homogeneousSimilarityDilation_zero] at hD
  have he : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (b : ℂ) * (s : ℂ)))
      (Complex.I * (b : ℂ)) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (Complex.I * (b : ℂ))).cexp
    simpa only [id_eq, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
      Complex.ofReal_one, mul_one] using h
  have h := he.hasDerivWithinAt.smul hD
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul,
    homogeneousSimilarityDilation_zero, hv0] at h
  apply h.congr_of_mem _ (by simp only [mem_Ici]; exact le_rfl)
  intro s hs
  exact homogeneousFreeOperator_factor a b k s ha ha1 hk hs q

end DefocusingNLS

end OAI
