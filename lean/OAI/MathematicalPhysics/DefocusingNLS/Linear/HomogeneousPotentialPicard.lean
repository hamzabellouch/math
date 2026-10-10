import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeightedDuhamel
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # Whole-space mild evolution for a bounded real-linear potential

The construction acts on the faithful homogeneous Fourier completion and
takes a bounded real operator as input. Identifying the manuscript profile
potential with such an operator is a separate spatial estimate.
-/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

variable {a k : ℝ}

noncomputable def homogeneousPotentialHistory (T : ℝ) (hT : 0 ≤ T)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) : ℝ → HomogeneousY a k :=
  fun t => B (u (projIcc 0 T hT t))

theorem continuous_homogeneousPotentialHistory (T : ℝ) (hT : 0 ≤ T)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) :
    Continuous (homogeneousPotentialHistory T hT B u) :=
  B.continuous.comp (u.continuous.comp continuous_projIcc)

noncomputable def homogeneousTimeWeight (T η : ℝ)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) : C(Icc (0 : ℝ) T, HomogeneousY a k) where
  toFun t := Real.exp (η * t) • u t
  continuous_toFun :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul u.continuous

@[simp] theorem homogeneousTimeWeight_cancel (T η : ℝ)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) :
    homogeneousTimeWeight T η (homogeneousTimeWeight T (-η) u) = u := by
  apply ContinuousMap.ext
  intro t
  change Real.exp (η * t) • (Real.exp (-η * t) • u t) = u t
  rw [smul_smul, ← Real.exp_add, show η * (t : ℝ) + -η * t = 0 by ring,
    Real.exp_zero, one_smul]

noncomputable def homogeneousPotentialPicard (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k) (u₀ : HomogeneousY a k)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) : C(Icc (0 : ℝ) T, HomogeneousY a k) where
  toFun t := homogeneousFreeOperator a b k t ha ha1 hk u₀ +
    homogeneousDuhamel a b k ha ha1 hk t (homogeneousPotentialHistory T hT B u)
  continuous_toFun :=
    ((continuous_homogeneousFreeOperator a b k ha ha1 hk u₀).comp continuous_subtype_val).add
      ((continuous_homogeneousDuhamel a b k ha ha1 hk _
        (continuous_homogeneousPotentialHistory T hT B u)).comp continuous_subtype_val)

noncomputable def homogeneousPotentialBielecki (a b k T η : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k) (u₀ : HomogeneousY a k)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) : C(Icc (0 : ℝ) T, HomogeneousY a k) :=
  homogeneousTimeWeight T (-η)
    (homogeneousPotentialPicard a b k T ha ha1 hk hT B u₀ (homogeneousTimeWeight T η u))

/-- The contraction constant is independent of the finite slab length. -/
theorem homogeneousPotentialBielecki_dist_le (a b k T η : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T) (hη : 0 < η)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k) (u₀ : HomogeneousY a k)
    (u v : C(Icc (0 : ℝ) T, HomogeneousY a k)) :
    dist (homogeneousPotentialBielecki a b k T η ha ha1 hk hT B u₀ u)
      (homogeneousPotentialBielecki a b k T η ha ha1 hk hT B u₀ v) ≤ ‖B‖ / η * dist u v := by
  apply (ContinuousMap.dist_le (mul_nonneg (div_nonneg (norm_nonneg _) hη.le) dist_nonneg)).2
  intro t
  let ru := homogeneousPotentialHistory T hT B (homogeneousTimeWeight T η u)
  let rv := homogeneousPotentialHistory T hT B (homogeneousTimeWeight T η v)
  have hru : Continuous ru := continuous_homogeneousPotentialHistory T hT B _
  have hrv : Continuous rv := continuous_homogeneousPotentialHistory T hT B _
  have hbound : ∀ τ ∈ Icc (0 : ℝ) t, ‖ru τ - rv τ‖ ≤ (‖B‖ * dist u v) * Real.exp (η * τ) := by
    intro τ hτ
    let τ' : Icc (0 : ℝ) T := ⟨τ, hτ.1, hτ.2.trans t.2.2⟩
    have hτT : τ ∈ Icc 0 T := τ'.2
    change ‖B (homogeneousTimeWeight T η u (projIcc 0 T hT τ)) -
      B (homogeneousTimeWeight T η v (projIcc 0 T hT τ))‖ ≤ _
    rw [← map_sub, projIcc_of_mem _ hτT]
    apply (B.le_opNorm _).trans
    change ‖B‖ * ‖Real.exp (η * τ) • u τ' - Real.exp (η * τ) • v τ'‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hdist : ‖u τ' - v τ'‖ ≤ dist u v := by
      simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := u) (g := v) τ')
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist
      (Real.exp_pos _).le) (norm_nonneg B)).trans_eq (by ring)
  have hb := homogeneousDuhamel_weighted_norm_le a b k η t (‖B‖ * dist u v)
    ha ha1 hk hη t.2.1 (mul_nonneg (norm_nonneg _) dist_nonneg) (fun τ => ru τ - rv τ) hbound
  change dist
    (Real.exp (-η * t) • (homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t ru))
    (Real.exp (-η * t) • (homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t rv)) ≤ _
  rw [dist_eq_norm, ← smul_sub, add_sub_add_left_eq_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← homogeneousDuhamel_sub a b k ha ha1 hk t t.2.1
      ru rv hru.continuousOn hrv.continuousOn]
  exact hb.trans_eq (by ring)

/-- A bounded real-linear perturbation has one mild trajectory on every finite forward slab. -/
theorem existsUnique_homogeneousPotential_finiteSlab (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k) (u₀ : HomogeneousY a k) :
    ∃! u : C(Icc (0 : ℝ) T, HomogeneousY a k), ∀ t : Icc (0 : ℝ) T,
      u t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
        homogeneousDuhamel a b k ha ha1 hk t (homogeneousPotentialHistory T hT B u) := by
  let η := ‖B‖ + 1
  have hη : 0 < η := by dsimp [η]; positivity
  have hKl : 0 ≤ ‖B‖ / η := div_nonneg (norm_nonneg _) hη.le
  have hKl' : ‖B‖ / η < 1 := (div_lt_one hη).2 (by dsimp [η]; linarith)
  let P := homogeneousPotentialBielecki a b k T η ha ha1 hk hT B u₀
  have hP : ContractingWith ⟨‖B‖ / η, hKl⟩ P :=
    ⟨hKl', LipschitzWith.of_dist_le_mul
      (homogeneousPotentialBielecki_dist_le a b k T η ha ha1 hk hT hη B u₀)⟩
  let v := hP.fixedPoint P
  have hv : P v = v := hP.fixedPoint_isFixedPt
  let u := homogeneousTimeWeight T η v
  refine ⟨u, ?_, ?_⟩
  · intro t
    have he := congrArg (fun f : C(Icc (0 : ℝ) T, HomogeneousY a k) =>
      homogeneousTimeWeight T η f t) hv
    change u t = homogeneousPotentialPicard a b k T ha ha1 hk hT B u₀ u t
    simpa only [P, homogeneousPotentialBielecki, homogeneousTimeWeight_cancel, u] using he.symm
  · intro w hw
    let z := homogeneousTimeWeight T (-η) w
    have hz : Function.IsFixedPt P z := by
      apply ContinuousMap.ext
      intro t
      change Real.exp (-η * t) •
        (homogeneousFreeOperator a b k t ha ha1 hk u₀ +
          homogeneousDuhamel a b k ha ha1 hk t
            (homogeneousPotentialHistory T hT B (homogeneousTimeWeight T η z))) = z t
      rw [show homogeneousTimeWeight T η z = w from homogeneousTimeWeight_cancel T η w]
      rw [← hw t]
      rfl
    have he : z = v := hP.fixedPoint_unique hz
    have h := congrArg (homogeneousTimeWeight T η) he
    simpa only [z, homogeneousTimeWeight_cancel, u] using h

end DefocusingNLS

end OAI
