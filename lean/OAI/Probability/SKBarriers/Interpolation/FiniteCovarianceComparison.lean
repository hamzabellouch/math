import Mathlib
import OAI.Probability.SKBarriers.Interpolation.FiniteCovarianceInterpolation

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section
variable {S : Type} [Fintype S] [Nonempty S]

def interpolationCoefficient (n : ℕ) (I : Fin n → Bool) (t : ℝ) (i : Fin n) : ℝ :=
  if I i then Real.sqrt t else Real.sqrt (1-t)

def interpolationRate (n : ℕ) (I : Fin n → Bool) (i : Fin n) : ℝ :=
  if I i then 1/2 else -(1/2)

omit [Fintype S] [Nonempty S] in
theorem interpolationCoefficient_continuous (n : ℕ) (I : Fin n → Bool) :
    Continuous (interpolationCoefficient n I) := by
  apply continuous_pi
  intro i
  simp only [interpolationCoefficient]
  split_ifs
  · exact Real.continuous_sqrt
  · exact Real.continuous_sqrt.comp (continuous_const.sub continuous_id)

omit [Fintype S] [Nonempty S] in
theorem interpolationCoefficient_hasDerivAt (n : ℕ) (I : Fin n → Bool)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    ∃ a' : Fin n → ℝ, HasDerivAt (interpolationCoefficient n I) a' t ∧
      ∀ i, a' i*interpolationCoefficient n I t i=interpolationRate n I i := by
  let a' : Fin n → ℝ := fun i => if I i then 1/(2*Real.sqrt t) else -(1/(2*Real.sqrt (1-t)))
  refine ⟨a',?_,?_⟩
  · apply hasDerivAt_pi.mpr
    intro i
    dsimp only [a',interpolationCoefficient]
    split_ifs
    · exact Real.hasDerivAt_sqrt ht.1.ne'
    · simpa only [id_eq,Pi.sub_apply,zero_sub,neg_div] using
        (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).sqrt (by linarith [ht.2] : 1-t≠0))
  · intro i
    dsimp only [a',interpolationCoefficient,interpolationRate]
    split_ifs
    · have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht.1).ne'
      field_simp
    · have hs : Real.sqrt (1-t)≠0 := (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
      field_simp

theorem observablePressure_covariance_comparison (n : ℕ) (O : Fin n → S → ℝ)
    (c : S → ℝ) (m : Fin n → ℝ) (I : Fin n → Bool)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (D : ℝ) (C : Fin (n+1) → ℝ)
    (hdiag : ∀ s, (∑ i, interpolationRate n I i*(O i s)^2) ≤ D)
    (hkernel : ∀ j, hierarchyAtom n m 1 j≠0 → ∀ s t, -C j ≤ partialObservableCovariance n O (interpolationRate n I) j s t) :
    hierarchyPressure n m (affineLogPartition c (observableExponent n O (interpolationCoefficient n I 1))) 0 ≤
      hierarchyPressure n m (affineLogPartition c (observableExponent n O (interpolationCoefficient n I 0))) 0+
      D+∑ j : Fin (n+1), hierarchyAtom n m 1 j*C j := by
  let f : ℝ → ℝ := fun t =>
    hierarchyPressure n m (affineLogPartition c (observableExponent n O (interpolationCoefficient n I t))) 0
  let K := D+∑ j : Fin (n+1), hierarchyAtom n m 1 j*C j
  let d : ℝ → ℝ := fun t =>
    weightedHierarchyTerminalMean n m c (observableExponent n O (interpolationCoefficient n I t))
      (fun s => ∑ i, interpolationRate n I i*(O i s)^2)-
      ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c (observableExponent n O (interpolationCoefficient n I t)) j
          (partialObservableCovariance n O (interpolationRate n I) j)
  have hc : Continuous f := by
    have H := parameter_contDiff_at_field
      (hierarchyPressure_paramRegular n m _ (observableTerminal_paramRegular n O c)).1 (0:ℝ)
    exact H.continuous.comp (interpolationCoefficient_continuous n I)
  have hd (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) : HasDerivAt f (d t) t := by
    obtain ⟨a',ha,he⟩ := interpolationCoefficient_hasDerivAt n I ht
    simpa only [he] using observablePressure_hasDerivAt_covariance n O c m (interpolationCoefficient n I) ha
  have hB (t : ℝ) : d t≤K := weightedCovariance_bound n m c _ O (interpolationRate n I)
    hm hmono D C hdiag hkernel
  have H : f 1-K≤f 0 := by
    have HM : AntitoneOn (fun t => f t-K*t) (Icc (0:ℝ) 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) 1)
        (hc.sub (continuous_const.mul continuous_id)).continuousOn
        (fun t ht => ((hd t (by simpa only [interior_Icc] using ht)).sub
          ((hasDerivAt_id t).const_mul K)).hasDerivWithinAt)
        (fun t _ => by simpa only [mul_one] using sub_nonpos.mpr (hB t))
    simpa using HM (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤1)
  change f 1 ≤ f 0+D+_
  dsimp only [K] at H
  linarith

end
end SK.Analytic

end
end

end OAI
