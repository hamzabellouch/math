import OAI.Combinatorics.SparsestCut.Smoothing

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CoordinateSplit
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def splitLinear : E ≃ₗ[ℝ] ℝ × Z where
  toFun x := (x 0, WithLp.toLp 2 (fun j => x j.succ))
  invFun p := WithLp.toLp 2 (Fin.cons p.1 (fun j => p.2 j))
  left_inv x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' t x := by ext <;> simp

def split : E ≃L[ℝ] ℝ × Z := splitLinear.toContinuousLinearEquiv
@[simp] lemma split_apply (x : E) : split x=(x 0,WithLp.toLp 2 (fun j => x j.succ)) := rfl
@[simp] lemma split_symm_apply (p : ℝ × Z) : split.symm p=WithLp.toLp 2 (Fin.cons p.1 (fun j => p.2 j)) := rfl

def splitMeasurable : E ≃ᵐ ℝ × Z := split.toHomeomorph.toMeasurableEquiv

lemma preserving : MeasurePreserving (split (m := m)) volume volume := by
  have h₁ := MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ))
    (PiLp.volume_preserving_toLp (Fin (m+1)))
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
  have h₃ : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2 : (Fin m → ℝ) → Z)) volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin m))
  have heq : (split (m := m) : E → ℝ × Z) = Prod.map (id : ℝ → ℝ) (WithLp.toLp 2) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0) ∘
      (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).symm := by
    ext x <;>
    simp [split,splitLinear,MeasurableEquiv.piFinSuccAbove_apply,Fin.tail]
  rw [heq]
  exact h₃.comp (h₂.comp h₁)

lemma integral_split (f : ℝ × Z → ℝ) : (∫ x : E, f (split x))=∫ p, f p :=
  preserving.integral_comp splitMeasurable.measurableEmbedding f

lemma convolution_split (φ : E → ℝ) (f : (ℝ × Z) → ℝ)
    (θ : E) :
    convolution φ (f ∘ split) (ContinuousLinearMap.mul ℝ ℝ) volume θ =
    convolution (φ ∘ split.symm) f (ContinuousLinearMap.mul ℝ ℝ) volume (split θ) := by
  change (∫ x : E, φ x*f (split (θ-x))) =
    ∫ p : ℝ × Z, φ (split.symm p)*f (split θ-p)
  rw [← integral_split]
  congr 1
  ext x
  simp only [ContinuousLinearEquiv.symm_apply_apply,map_sub]

lemma derivative_transport (h : (ℝ × Z) → ℝ) (D : (ℝ × Z) →L[ℝ] ℝ)
    (θ : E) (hd : HasFDerivAt h D (split θ)) :
    HasFDerivAt (h ∘ split) (D.comp split.toContinuousLinearMap) θ :=
  hd.comp θ split.hasFDerivAt

def rest (u : E) : Z →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ E u).comp
    (split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ Z))
def slope (u : E) : Z →L[ℝ] ℝ := -(u 0)⁻¹ • rest u
lemma rest_apply (u : E) (z : Z) : rest u z=∑ j, u j.succ*z j := by
  simp [rest,PiLp.inner_apply,Fin.sum_univ_succ,mul_comm]
lemma inner_formula (u x : E) : inner ℝ u x=u 0*(split x).1+rest u (split x).2 := by
  simp [rest_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro j _; ring
lemma normalized_form (u : E) (hu : u 0≠0) (x : E) :
    inner ℝ u x/(u 0)=(split x).1-slope u (split x).2 := by
  rw [inner_formula]
  simp only [slope,_root_.smul_apply,smul_eq_mul]
  field_simp
  ring
lemma slope_injective {I : Type u1} (u : I → E) (hu : ∀ i, u i 0≠0)
    (hn : ∀ i j, i≠j → ∀ t : ℝ, u i≠t • u j) : Function.Injective (fun i => slope (u i)) := by
  intro i j he
  by_contra hij
  apply hn i j hij (u i 0/u j 0)
  apply (InnerProductSpace.toDual ℝ E).injective
  ext x
  have hh := congrArg (fun L : Z →L[ℝ] ℝ => L (split x).2) he
  simp only [slope,_root_.smul_apply,smul_eq_mul] at hh
  change inner ℝ (u i) x=inner ℝ ((u i 0/u j 0) • u j) x
  rw [real_inner_smul_left]
  rw [inner_formula (u i),inner_formula (u j)]
  field_simp [hu i,hu j] at hh ⊢
  nlinarith
end UniformSparsestCut.CoordinateSplit

end

end OAI
