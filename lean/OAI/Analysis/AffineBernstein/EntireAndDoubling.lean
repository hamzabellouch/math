import Mathlib
import OAI.Analysis.AffineBernstein.MaximalModelExclusion

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireAndDoubling
/-- The global geometric part of the exact main theorem: the nonempty open
convex base is all of Euclidean space, and one section-balance constant works at
all centers and heights. This is not the quadratic-rigidity conclusion. -/
theorem affineMaximal_entire_and_balance {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    Ω = univ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ SectionBalance univ u ρ := by
  obtain ⟨ρ,hρ,hρ1,hbal⟩ := affineMaximal_section_balance hn hn9 hΩ hne hcv hu hp hm hc
  have hU := eq_univ_of_sectionBalance hΩ hne hcv hu hp hc hρ hbal
  exact ⟨hU,ρ,hρ,hρ1,hU ▸ hbal⟩

/-- Uniform tangent-gap doubling is also produced, with the manuscript's exact
constants and no global growth assumption. -/
theorem affineMaximal_entire_gap_doubling {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    Ω = univ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ a x : Space n,
      tangentHeight u a (a+(1+ρ/2) • (x-a)) ≤
        ((2+ρ)*(1+ρ)/ρ) * tangentHeight u a x := by
  obtain ⟨hU,ρ,hρ,hρ1,hbal⟩ := affineMaximal_entire_and_balance hn hn9 hΩ hne hcv hu hp hm hc
  refine ⟨hU,ρ,hρ,hρ1,?_⟩
  subst Ω
  intro a x
  exact (gap_doubling_of_sectionBalance isOpen_univ convex_univ hu hp hc hρ hbal
    (mem_univ a) (mem_univ x)).2
end EntireAndDoubling

open Filter
open scoped Topology

/-- The logarithm is taken only on the positive Hessian determinant at points
where the estimates are asserted. Outside the domain this is just a total function. -/
def logHessianDet {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.log (hessian u x).det

/-- The actual inverse-Hessian linearized operator, without the harmless
positive determinant factor in the frozen original PDE. -/
def inverseHessianTrace {n : ℕ} (u f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian f x i j

def inverseHessianPair {n : ℕ} (u f g : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (hessian u x)⁻¹ i j *
    dirDeriv (coordinateVector n i) f x * dirDeriv (coordinateVector n j) g x

lemma contDiffAt_logHessianDet {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (logHessianDet u) x :=
  (contDiffAt_det_hessian hu).log (ne_of_gt hp.det_pos)

lemma contDiffOn_logHessianDet {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) : ContDiffOn ℝ ∞ (logHessianDet u) Ω := by
  intro x hx
  exact (contDiffAt_logHessianDet (hu.contDiffAt (hΩ.mem_nhds hx)) (hp x hx)).contDiffWithinAt

lemma affineMaximal_inverseHessianTrace_zero {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hm : AffineMaximalOn Ω u)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (affineWeight u) x = 0 := by
  have hh := hm x hx
  have he : (∑ i, ∑ j, cofactorHessian u x i j * hessian (affineWeight u) x i j) =
      (hessian u x).det * inverseHessianTrace u (affineWeight u) x := by
    simp only [cofactorHessian, Matrix.smul_apply, smul_eq_mul, inverseHessianTrace,
      Finset.mul_sum, mul_assoc]
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hp.det_pos)

lemma affineWeight_eq_exp_logHessianDet {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) :
    affineWeight u x = Real.exp (-(((n : ℝ)+1)/((n : ℝ)+2)) * logHessianDet u x) := by
  rw [affineWeight, Real.rpow_eq_pow, Real.rpow_def_of_pos hp.det_pos]
  simp only [logHessianDet, mul_comm]

/-- The exact logarithmic form of the original affine maximal equation.
It is derived from the frozen determinant exponent, not a replacement PDE. -/
theorem affineMaximal_logHessianDet_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {x : Space n} (hx : x ∈ Ω) :
    inverseHessianTrace u (logHessianDet u) x =
      (((n : ℝ)+1)/((n : ℝ)+2)) *
        inverseHessianPair u (logHessianDet u) (logHessianDet u) x := by
  let a : ℝ := ((n : ℝ)+1)/((n : ℝ)+2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hφ := contDiffOn_logHessianDet hΩ hu hp
  have he : affineWeight u =ᶠ[𝓝 x] (fun y => Real.exp (-a * logHessianDet u y)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact affineWeight_eq_exp_logHessianDet (hp y hy)
  have hentry (i j : Fin n) : hessian (affineWeight u) x i j =
      Real.exp (-a * logHessianDet u x) *
        (-a * hessian (logHessianDet u) x i j + a^2 *
          dirDeriv (coordinateVector n i) (logHessianDet u) x *
          dirDeriv (coordinateVector n j) (logHessianDet u) x) := by
    change dirDeriv _ (dirDeriv _ (affineWeight u)) x = _
    rw [second_dirDeriv_congr he, second_dirDeriv_expMul hΩ hφ hx]
    simp only [neg_sq]
    rfl
  have htrace : inverseHessianTrace u (affineWeight u) x =
      Real.exp (-a * logHessianDet u x) *
        (-a * inverseHessianTrace u (logHessianDet u) x + a^2 *
          inverseHessianPair u (logHessianDet u) (logHessianDet u) x) := by
    simp only [inverseHessianTrace, inverseHessianPair, hentry,
      Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
      apply Finset.sum_congr rfl <;> intro j hj <;> ring
  rw [affineMaximal_inverseHessianTrace_zero hm hx (hp x hx)] at htrace
  have hz := (mul_eq_zero.mp htrace.symm).resolve_left (Real.exp_ne_zero _)
  change inverseHessianTrace u (logHessianDet u) x = a * _
  nlinarith

/-- The differential of the log determinant is the literal inverse-Hessian
contraction of the differentiated Hessian. -/
lemma dirDeriv_logHessianDet {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (v : Space n) :
    dirDeriv v (logHessianDet u) x =
      ∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv v (fun y => hessian u y i j) x := by
  have hd := ((contDiffAt_det_hessian hu).differentiableAt (by simp)).hasFDerivAt
  have hr := hd.log (ne_of_gt hp.det_pos)
  have he : dirDeriv v (logHessianDet u) x =
      (hessian u x).det⁻¹ * dirDeriv v (fun y => (hessian u y).det) x := by
    unfold dirDeriv logHessianDet
    rw [hr.fderiv]
    simp only [smul_apply, smul_eq_mul]
  rw [he, dirDeriv_det (hessian u)
    (fun i j => (contDiffAt_hessian_entry hu i j).differentiableAt (by simp))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hc : (hessian u x).adjugate j i = (hessian u x).det * (hessian u x)⁻¹ i j := by
    rw [← cofactorHessian_eq_adjugate u x (ne_of_gt hp.det_pos)]
    rw [(cofactorHessian_isSymm u x hp).apply i j]
    rfl
  rw [hc]
  field_simp [ne_of_gt hp.det_pos]

lemma inverseHessianTrace_dirDeriv {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) (k : Fin n) :
    inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x =
      dirDeriv (coordinateVector n k) (logHessianDet u) x := by
  rw [dirDeriv_logHessianDet (hu.contDiffAt (hΩ.mem_nhds hx)) hp]
  simp only [inverseHessianTrace, hessian_dirDeriv hΩ hu hx]

end AffineBernstein

end

end OAI
