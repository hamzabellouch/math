import OAI.Analysis.Nuclearity.CompletedSpatialSum

namespace OAI

/-! Extension from the dense algebraic tensor product, with a nonunital
target. An auxiliary unital structure gives extensions to concrete
represented subalgebras. -/

noncomputable section
open scoped TensorProduct

namespace WeakPureInfiniteness

section Dense

variable {R E F : Type*} [Ring R] [StarAddMonoid R] [Algebra ℂ R]
  [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]

def nonUnitalStarLinearMap (f : R →⋆ₙₐ[ℂ] E) : R →ₗ[ℂ] E where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smul f

def denseNonUnitalStarCompletion (f : R →⋆ₙₐ[ℂ] E) (g : R →⋆ₙₐ[ℂ] F)
    (hf : DenseRange f) (hn : ∀ x, ‖g x‖ ≤ ‖f x‖) : E →⋆ₙₐ[ℂ] F := by
  let L : E →L[ℂ] F :=
    (nonUnitalStarLinearMap g).extendOfNorm (nonUnitalStarLinearMap f)
  have heq (x : R) : L (f x) = g x :=
    LinearMap.extendOfNorm_eq hf ⟨1, fun x => by
      change ‖g x‖ ≤ 1 * ‖f x‖
      simpa only [one_mul] using hn x⟩ x
  exact {
    toFun := L
    map_zero' := L.map_zero
    map_add' := L.map_add
    map_smul' := L.map_smul
    map_mul' := by
      refine hf.induction_on₂ ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_mul)
          ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
      · intro x y
        rw [← map_mul, heq, heq, heq, map_mul]
    map_star' := by
      intro x
      refine hf.induction_on x ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
      · intro y
        rw [← map_star, heq, heq, map_star] }

lemma denseNonUnitalStarCompletion_apply (f : R →⋆ₙₐ[ℂ] E) (g : R →⋆ₙₐ[ℂ] F)
    (hf : DenseRange f) (hn : ∀ x, ‖g x‖ ≤ ‖f x‖) (x : R) :
    denseNonUnitalStarCompletion f g hf hn (f x) = g x :=
  LinearMap.extendOfNorm_eq hf ⟨1, fun x => by
    change ‖g x‖ ≤ 1 * ‖f x‖
    simpa only [one_mul] using hn x⟩ x

end Dense

section DenseLinear

variable {R E F : Type*} [AddCommGroup R] [Module ℂ R] [Mul R] [Star R]
  [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]

def denseLinearStarCompletion (f : R →ₗ[ℂ] E) (g : R →ₗ[ℂ] F)
    (hf : DenseRange f) (hfm : ∀ x y, f (x * y) = f x * f y)
    (hgm : ∀ x y, g (x * y) = g x * g y)
    (hfs : ∀ x, f (star x) = star (f x)) (hgs : ∀ x, g (star x) = star (g x))
    (hn : ∀ x, ‖g x‖ ≤ ‖f x‖) : E →⋆ₙₐ[ℂ] F := by
  let L := g.extendOfNorm f
  have heq (x : R) : L (f x) = g x :=
    LinearMap.extendOfNorm_eq hf ⟨1, fun x => by simpa only [one_mul] using hn x⟩ x
  exact {
    toFun := L
    map_zero' := L.map_zero
    map_add' := L.map_add
    map_smul' := L.map_smul
    map_mul' := by
      refine hf.induction_on₂ ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_mul)
          ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
      · intro x y
        rw [← hfm, heq, heq, heq, hgm]
    map_star' := by
      intro x
      refine hf.induction_on x ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
      · intro y
        rw [← hfs, heq, heq, hgs] }

lemma denseLinearStarCompletion_apply (f : R →ₗ[ℂ] E) (g : R →ₗ[ℂ] F)
    (hf : DenseRange f) (hfm : ∀ x y, f (x * y) = f x * f y)
    (hgm : ∀ x y, g (x * y) = g x * g y)
    (hfs : ∀ x, f (star x) = star (f x)) (hgs : ∀ x, g (star x) = star (g x))
    (hn : ∀ x, ‖g x‖ ≤ ‖f x‖) (x : R) :
    denseLinearStarCompletion f g hf hfm hgm hfs hgs hn (f x) = g x :=
  LinearMap.extendOfNorm_eq hf ⟨1, fun x => by simpa only [one_mul] using hn x⟩ x

end DenseLinear

section Bilinear

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def minimalTensorBilinear : A →ₗ[ℂ] B →ₗ[ℂ] MinimalTensor A B where
  toFun := minimalElementaryRightLinear
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact map_add (minimalElementaryLeftLinear c) a b
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    exact map_smul (minimalElementaryLeftLinear b) r a

def minimalAlgebraicLinear : A ⊗[ℂ] B →ₗ[ℂ] MinimalTensor A B :=
  TensorProduct.lift minimalTensorBilinear

@[simp] lemma minimalAlgebraicLinear_tmul (a : A) (b : B) :
    minimalAlgebraicLinear (a ⊗ₜ[ℂ] b) = minimalElementary a b := rfl

lemma minimalAlgebraicLinear_dense :
    DenseRange (minimalAlgebraicLinear (A := A) (B := B)) := by
  let S := (minimalAlgebraicLinear (A := A) (B := B)).range
  have hs : S.topologicalClosure = ⊤ := by
    apply minimal_elementary_span_dense _ S.isClosed_topologicalClosure
    intro a b
    apply S.le_topologicalClosure
    exact ⟨a ⊗ₜ[ℂ] b, rfl⟩
  intro x
  change x ∈ S.topologicalClosure
  rw [hs]
  trivial

lemma algebraic_linear_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : A ⊗[ℂ] B →ₗ[ℂ] F)
    (h : ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B),
      ‖g (∑ i, a i ⊗ₜ[ℂ] b i)‖ ≤
        ‖(∑ i, minimalElementary (a i) (b i) : MinimalTensor A B)‖)
    (z : A ⊗[ℂ] B) : ‖g z‖ ≤ ‖minimalAlgebraicLinear z‖ := by
  obtain ⟨n, a, b, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  rw [hz]
  simpa only [map_sum, minimalAlgebraicLinear_tmul] using h n a b

end Bilinear

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

@[irreducible] def minimalAlgebraicMap : A ⊗[ℂ] B →⋆ₙₐ[ℂ] MinimalTensor A B where
  toFun := minimalAlgebraicLinear
  map_zero' := map_zero minimalAlgebraicLinear
  map_add' := map_add minimalAlgebraicLinear
  map_smul' := map_smul minimalAlgebraicLinear
  map_mul' z w := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      induction w using TensorProduct.inductionOn with
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, minimalAlgebraicLinear_tmul,
          minimalElementary_mul]
      | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  map_star' z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.star_tmul, minimalAlgebraicLinear_tmul, minimalElementary_star]
    | add x y hx hy => simp only [star_add, map_add, hx, hy]

@[simp] lemma minimalAlgebraicMap_tmul (a : A) (b : B) :
    minimalAlgebraicMap (a ⊗ₜ[ℂ] b) = minimalElementary a b := by
  unfold minimalAlgebraicMap
  exact minimalAlgebraicLinear_tmul a b

lemma minimalAlgebraicMap_dense : DenseRange (minimalAlgebraicMap (A := A) (B := B)) := by
  unfold minimalAlgebraicMap
  exact minimalAlgebraicLinear_dense

lemma minimalAlgebraicMap_apply (z : A ⊗[ℂ] B) :
    minimalAlgebraicMap z = minimalAlgebraicLinear z := by
  unfold minimalAlgebraicMap
  rfl

lemma minimalAlgebraicLinear_mul (z w : A ⊗[ℂ] B) :
    minimalAlgebraicLinear (z * w) = minimalAlgebraicLinear z * minimalAlgebraicLinear w := by
  simpa only [minimalAlgebraicMap_apply] using map_mul (minimalAlgebraicMap (A := A) (B := B)) z w

lemma minimalAlgebraicLinear_star (z : A ⊗[ℂ] B) :
    minimalAlgebraicLinear (star z) = star (minimalAlgebraicLinear z) := by
  simpa only [minimalAlgebraicMap_apply] using map_star (minimalAlgebraicMap (A := A) (B := B)) z

@[irreducible] def minimalTensorExtend (g : A ⊗[ℂ] B →⋆ₐ[ℂ] C)
    (hg : ∀ z, ‖g z‖ ≤ ‖minimalAlgebraicLinear z‖) :
    MinimalTensor A B →⋆ₙₐ[ℂ] C :=
  denseNonUnitalStarCompletion minimalAlgebraicMap g.toNonUnitalStarAlgHom
    minimalAlgebraicMap_dense (fun z => by rw [minimalAlgebraicMap_apply]; exact hg z)

lemma minimalTensorExtend_apply (g : A ⊗[ℂ] B →⋆ₐ[ℂ] C)
    (hg : ∀ z, ‖g z‖ ≤ ‖minimalAlgebraicLinear z‖) (z : A ⊗[ℂ] B) :
    minimalTensorExtend g hg (minimalAlgebraicMap z) = g z := by
  unfold minimalTensorExtend
  exact denseNonUnitalStarCompletion_apply _ _ _ _ z

@[simp] lemma minimalTensorExtend_elementary (g : A ⊗[ℂ] B →⋆ₐ[ℂ] C)
    (hg : ∀ z, ‖g z‖ ≤ ‖minimalAlgebraicLinear z‖) (a : A) (b : B) :
    minimalTensorExtend g hg (minimalElementary a b) = g (a ⊗ₜ[ℂ] b) := by
  rw [← minimalAlgebraicMap_tmul]
  exact minimalTensorExtend_apply g hg _

end WeakPureInfiniteness

end

end OAI
