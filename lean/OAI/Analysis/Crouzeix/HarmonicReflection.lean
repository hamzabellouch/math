import Mathlib
import OAI.Analysis.Crouzeix.HarmonicMaximum

namespace OAI

/-! Harmonic Reflection. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

def upperHalfBall (R : ℝ) : Set ℂ := ball 0 R ∩ {z | 0 < z.im}

def closedUpperHalfBall (R : ℝ) : Set ℂ := closedBall 0 R ∩ {z | 0 ≤ z.im}

theorem isOpen_upperHalfBall (R : ℝ) : IsOpen (upperHalfBall R) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem convex_upperHalfBall (R : ℝ) : Convex ℝ (upperHalfBall R) :=
  (convex_ball _ _).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)

theorem closure_upperHalfBall_subset (R : ℝ) :
    closure (upperHalfBall R) ⊆ closedUpperHalfBall R := by
  apply closure_minimal
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, show 0 ≤ z.im from le_of_lt (show 0 < z.im from hz.2)⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

def oddReflection (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then u z else -u (conj z)

theorem oddReflection_conj {R : ℝ} {u : ℂ → ℝ}
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : oddReflection u (conj z) = -oddReflection u z := by
  by_cases hi : z.im = 0
  · have hz' : conj z = z := Complex.ext (by simp) (by simp [hi])
    simp [oddReflection, hi, hz', hzero z hz hi]
  · rcases lt_or_gt_of_ne hi with hneg | hpos
    · simp [oddReflection, not_le.mpr hneg, (neg_pos.mpr hneg).le]
    · simp [oddReflection, hpos.le, not_le.mpr (neg_neg_of_pos hpos)]

theorem continuousOn_oddReflection {R : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedUpperHalfBall R))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0) :
    ContinuousOn (oddReflection u) (sphere 0 R) := by
  let S : Set ℂ := {z | 0 ≤ z.im}
  have hS : IsClosed S := isClosed_le continuous_const Complex.continuous_im
  have hfront : ∀ z ∈ frontier S, z.im = 0 := by
    intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ici (0 : ℝ)) hz
    simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hf
  have hlow : closure Sᶜ ⊆ {z : ℂ | z.im ≤ 0} := by
    apply closure_minimal
    · intro z hz
      exact (not_le.mp (show ¬ 0 ≤ z.im from hz)).le
    · exact isClosed_le Complex.continuous_im continuous_const
  change ContinuousOn (S.piecewise u (fun z => -u (conj z))) (sphere 0 R)
  apply ContinuousOn.piecewise
  · intro z hz
    have hi := hfront z hz.2
    have he : conj z = z := Complex.ext (by simp) (by simp [hi])
    rw [he, hzero z (sphere_subset_closedBall hz.1) hi, neg_zero]
  · rw [hS.closure_eq]
    exact hu.mono (fun z hz => ⟨sphere_subset_closedBall hz.1, hz.2⟩)
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [mem_closedBall_zero_iff, Complex.norm_conj] using
        (sphere_subset_closedBall hz.1)
    · change 0 ≤ -z.im
      exact neg_nonneg.mpr (show z.im ≤ 0 from hlow hz.2)

theorem harmonic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (upperHalfBall R))
    (huc : ContinuousOn u (closedUpperHalfBall R))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0) :
    HarmonicOnNhd (poissonExtension R (oddReflection u)) (ball 0 R) ∧
    EqOn (poissonExtension R (oddReflection u)) u (upperHalfBall R) ∧
    (∀ z ∈ ball (0 : ℂ) R, z.im = 0 → poissonExtension R (oddReflection u) z = 0) := by
  have hboundary := continuousOn_oddReflection huc hzero
  have hodd : ∀ z ∈ sphere (0 : ℂ) R,
      oddReflection u (conj z) = -oddReflection u z :=
    fun z hz => oddReflection_conj hzero (sphere_subset_closedBall hz)
  have hreal : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 →
      dirichletExtension R (oddReflection u) z = 0 := by
    intro z hz hi
    by_cases hb : z ∈ ball (0 : ℂ) R
    · rw [(dirichletExtension_eventuallyEq hb).eq_of_nhds]
      have he : conj z = z := Complex.ext (by simp) (by simp [hi])
      have ho := poissonExtension_conj hR.le hodd z
      rw [he] at ho
      linarith
    · have he : conj z = z := Complex.ext (by simp) (by simp [hi])
      simp only [dirichletExtension, piecewise_eq_of_notMem _ _ _ hb,
        oddReflection, hi, le_refl, ite_true, hzero z hz hi]
  have hd := harmonicContOnCl_dirichletExtension hR hboundary
  have heq := harmonic_eqOn_of_boundary_eq (isOpen_upperHalfBall R)
    (convex_upperHalfBall R).isPreconnected
    (isBounded_ball.subset inter_subset_left)
    (show HarmonicContOnCl (dirichletExtension R (oddReflection u)) (upperHalfBall R)
      from hd.mono inter_subset_left)
    (show HarmonicContOnCl u (upperHalfBall R) from
      ⟨hu, huc.mono (closure_upperHalfBall_subset R)⟩) (by
        intro z hz
        have hzc := closure_upperHalfBall_subset R (frontier_subset_closure hz)
        have hzn : z ∉ upperHalfBall R := by
          have hn := hz.2
          simpa only [(isOpen_upperHalfBall R).interior_eq] using hn
        by_cases hi : z.im = 0
        · rw [hreal z hzc.1 hi, hzero z hzc.1 hi]
        · have hpos : 0 < z.im := lt_of_le_of_ne hzc.2 (Ne.symm hi)
          have hs : z ∈ sphere (0 : ℂ) R := mem_sphere.mpr
            (le_antisymm (mem_closedBall.mp hzc.1)
              (le_of_not_gt (fun he => hzn ⟨he, hpos⟩)))
          rw [dirichletExtension_eq_on_sphere hs, oddReflection, ite_eq_left hpos.le])
  refine ⟨harmonicOnNhd_poissonExtension hR.le hboundary, ?_, ?_⟩
  · intro z hz
    rw [← (dirichletExtension_eventuallyEq hz.1).eq_of_nhds]
    exact heq (subset_closure hz)
  · intro z hz hi
    rw [← (dirichletExtension_eventuallyEq hz).eq_of_nhds]
    exact hreal z (ball_subset_closedBall hz) hi

end CrouzeixHilbert.Conformal

end

end OAI
