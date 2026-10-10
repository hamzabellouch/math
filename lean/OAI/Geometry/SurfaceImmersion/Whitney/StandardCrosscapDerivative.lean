import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapFactorization

namespace OAI

/-! The standard umbrella has one singular point and a transverse double ray. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance standardBaseNormed : NormedAddCommGroup Base := inferInstance
local instance standardBaseSpace : NormedSpace ℝ Base := inferInstance
local instance standardTripleNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance standardTripleSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

def standardCrosscapDerivative (x : Base) : Base →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.pi ![
    x 1 • ContinuousLinearMap.proj (0 : Fin 2) + x 0 • ContinuousLinearMap.proj (1 : Fin 2),
    (2*x 1) • ContinuousLinearMap.proj (1 : Fin 2)]).prod (ContinuousLinearMap.proj (0 : Fin 2))

lemma standardCrosscap_hasFDerivAt (x : Base) :
    HasFDerivAt standardCrosscap (standardCrosscapDerivative x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have h := (((h0.mul h1).smul_const ((![1,0],0) : Base × ℝ)).add
    ((h1.pow 2).smul_const ((![0,1],0) : Base × ℝ))).add
      (h0.smul_const ((0,1) : Base × ℝ))
  have he : (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
      (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) =
      standardCrosscap := by
    funext y
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  change HasFDerivAt (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
    (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) _ x at h
  rw [he] at h
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [standardCrosscapDerivative]
    ring
  · simp [standardCrosscapDerivative]

lemma standardCrosscap_immersion_iff (x : Base) :
    Function.Injective (fderiv ℝ standardCrosscap x) ↔ x ≠ 0 := by
  rw [(standardCrosscap_hasFDerivAt x).fderiv]
  constructor
  · intro h hx
    have he : standardCrosscapDerivative x (![0,1] : Base) = standardCrosscapDerivative x 0 := by
      subst x
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [standardCrosscapDerivative]
      · rfl
    have hh := congrFun (h he) 1
    norm_num at hh
  · intro hx u v he
    have h0 : u 0 = v 0 := congrArg Prod.snd he
    have h1 : x 1 * u 0 + x 0 * u 1 = x 1 * v 0 + x 0 * v 1 := congrFun (congrArg Prod.fst he) 0
    have h2 : (2*x 1)*u 1 = (2*x 1)*v 1 := congrFun (congrArg Prod.fst he) 1
    have huv : u 1 = v 1 := by
      by_cases hx0 : x 0 = 0
      · have hx1 : x 1 ≠ 0 := by
          intro hz
          apply hx
          ext i
          fin_cases i
          · exact hx0
          · exact hz
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hx1) h2
      · rw [h0] at h1
        exact mul_left_cancel₀ hx0 (add_left_cancel h1)
    ext i
    fin_cases i
    · exact h0
    · exact huv

lemma standardCrosscap_double_iff {x y : Base} (hne : x ≠ y) :
    standardCrosscap x = standardCrosscap y ↔
      x 0 = 0 ∧ y 0 = 0 ∧ x 1 = -y 1 ∧ x 1 ≠ 0 := by
  constructor
  · intro he
    have h0 : x 0 = y 0 := congrArg Prod.snd he
    have h1 : x 0*x 1 = y 0*y 1 := congrFun (congrArg Prod.fst he) 0
    have h2 : (x 1)^2 = (y 1)^2 := congrFun (congrArg Prod.fst he) 1
    have hxy1 : x 1 ≠ y 1 := by
      intro h
      apply hne
      ext i
      fin_cases i
      · exact h0
      · exact h
    have hx0 : x 0 = 0 := by
      by_contra h
      apply hxy1
      rw [← h0] at h1
      exact mul_left_cancel₀ h h1
    have hneg : x 1 = -y 1 := (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left hxy1
    refine ⟨hx0,h0 ▸ hx0,hneg,?_⟩
    intro hx1
    apply hxy1
    linarith
  · rintro ⟨hx,hy,hneg,_⟩
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap,hx,hy,hneg]
    · exact hx.trans hy.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
