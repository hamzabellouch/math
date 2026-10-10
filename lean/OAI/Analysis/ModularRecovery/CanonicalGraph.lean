import OAI.Analysis.ModularRecovery.Recovery

namespace OAI

/-! The closed graph and block operators of a cyclic separating vector. -/

universe u uE

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure CyclicSeparatingData (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  M : VonNeumannAlgebra H
  xi : H
  norm_xi : ‖xi‖ = 1
  cyclic : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  separating : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0

namespace CyclicSeparatingData

local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

def coreMap (S : CyclicSeparatingData H) : S.M.toStarSubalgebra →ₗ[ℝ] HilbertPair H where
  toFun a := HilbertPair.pair ((a:H →L[ℂ] H) S.xi) ((star (a:H →L[ℂ] H)) S.xi)
  map_add' a b := by
    change HilbertPair.pair (((a:H →L[ℂ] H)+(b:H →L[ℂ] H)) S.xi)
      ((star ((a:H →L[ℂ] H)+(b:H →L[ℂ] H))) S.xi) = _
    simp only [star_add,add_apply]
    rfl
  map_smul' r a := by
    change HilbertPair.pair ((r • (a:H →L[ℂ] H)) S.xi)
      ((star (r • (a:H →L[ℂ] H))) S.xi) = _
    simp only [star_smul,star_trivial,smul_apply]
    rfl

def graph (S : CyclicSeparatingData H) : Submodule ℝ (HilbertPair H) :=
  S.coreMap.range.topologicalClosure

lemma core_mem_graph (S : CyclicSeparatingData H) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    HilbertPair.pair (a S.xi) ((star a) S.xi) ∈ S.graph :=
  Submodule.le_topologicalClosure _ ⟨⟨a,ha⟩,rfl⟩

lemma graph_isClosed (S : CyclicSeparatingData H) : IsClosed (S.graph : Set (HilbertPair H)) :=
  Submodule.isClosed_topologicalClosure _

lemma graph_inner_commutant (S : CyclicSeparatingData H) {x y : H}
    (hxy : HilbertPair.pair x y ∈ S.graph) (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    inner ℂ (b S.xi) y = inner ℂ x ((star b) S.xi) := by
  have he : (S.graph : Set (HilbertPair H)) ⊆
      {p | inner ℂ (b S.xi) (WithLp.sndL 2 ℂ H H p) =
        inner ℂ (WithLp.fstL 2 ℂ H H p) ((star b) S.xi)} := by
    apply closure_minimal
    · rintro p ⟨a,rfl⟩
      change inner ℂ (b S.xi) ((star (a:H →L[ℂ] H)) S.xi) =
        inner ℂ ((a:H →L[ℂ] H) S.xi) ((star b) S.xi)
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      exact congrArg (fun c : H →L[ℂ] H => inner ℂ (c S.xi) S.xi)
        (VonNeumannAlgebra.mem_commutant_iff.mp hb a a.property)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  exact he hxy

lemma graph_vertical (S : CyclicSeparatingData H) {y : H}
    (hy : HilbertPair.pair 0 y ∈ S.graph) : y = 0 := by
  apply ext_inner_left ℂ
  intro z
  refine (commutant_cyclic S.M S.xi S.separating).induction ?_ ?_ z
  · rintro v ⟨b,hb,rfl⟩
    simpa only [inner_zero_left,inner_zero_right] using S.graph_inner_commutant hy b hb
  · exact isClosed_eq (by fun_prop) (by fun_prop)

lemma graph_swap (S : CyclicSeparatingData H) {x y : H}
    (hxy : HilbertPair.pair x y ∈ S.graph) : HilbertPair.pair y x ∈ S.graph := by
  have he : (S.graph : Set (HilbertPair H)) ⊆
      {p | HilbertPair.pair (WithLp.sndL 2 ℂ H H p) (WithLp.fstL 2 ℂ H H p) ∈ S.graph} := by
    apply closure_minimal
    · rintro p ⟨a,rfl⟩
      change HilbertPair.pair ((star (a:H →L[ℂ] H)) S.xi) ((a:H →L[ℂ] H) S.xi) ∈ S.graph
      simpa only [star_star] using S.core_mem_graph (star (a:H →L[ℂ] H)) (star_mem a.property)
    · apply S.graph_isClosed.preimage
      exact (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.continuous.comp
        ((WithLp.sndL 2 ℂ H H).continuous.prodMk (WithLp.fstL 2 ℂ H H).continuous)
  exact he hxy

lemma graph_horizontal (S : CyclicSeparatingData H) {x : H}
    (hx : HilbertPair.pair x 0 ∈ S.graph) : x = 0 := S.graph_vertical (S.graph_swap hx)

lemma graph_twist (S : CyclicSeparatingData H) {x y : H}
    (hxy : HilbertPair.pair x y ∈ S.graph) :
    HilbertPair.pair (Complex.I • x) (-Complex.I • y) ∈ S.graph := by
  have he : (S.graph : Set (HilbertPair H)) ⊆
      {p | HilbertPair.pair (Complex.I • WithLp.fstL 2 ℂ H H p)
        (-Complex.I • WithLp.sndL 2 ℂ H H p) ∈ S.graph} := by
    apply closure_minimal
    · rintro p ⟨a,rfl⟩
      change HilbertPair.pair (Complex.I • (a:H →L[ℂ] H) S.xi)
        (-Complex.I • (star (a:H →L[ℂ] H)) S.xi) ∈ S.graph
      simpa only [star_smul,Complex.star_def,Complex.conj_I,smul_apply] using
        S.core_mem_graph (Complex.I • (a:H →L[ℂ] H))
          (S.M.toStarSubalgebra.smul_mem a.property Complex.I)
    · apply S.graph_isClosed.preimage
      exact (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.continuous.comp
        (((WithLp.fstL 2 ℂ H H).continuous.const_smul Complex.I).prodMk
          ((WithLp.sndL 2 ℂ H H).continuous.const_smul (-Complex.I)))
  exact he hxy

end CyclicSeparatingData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

lemma projection_commute_real {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (a : E →L[ℝ] E)
    (ha : G ∈ Module.End.invtSubmodule a)
    (hast : G ∈ Module.End.invtSubmodule (star a : E →L[ℝ] E)) : Commute G.starProjection a := by
  have h := G.isIdempotentElem_starProjection
  have hp := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff h).mp
    (by simpa only [Submodule.range_starProjection] using ha)
  have hpst := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff h).mp
    (by simpa only [Submodule.range_starProjection] using hast)
  change G.starProjection * a * G.starProjection = a * G.starProjection at hp
  change G.starProjection * star a * G.starProjection = star a * G.starProjection at hpst
  have hh := congrArg star hpst
  simp only [star_mul, star_star, (isSelfAdjoint_starProjection G).star_eq] at hh
  exact (hp.symm.trans ((mul_assoc _ _ _).trans hh)).symm

namespace HilbertPair

def swapR : HilbertPair H →L[ℝ] HilbertPair H where
  toFun p := pair (WithLp.sndL 2 ℝ H H p) (WithLp.fstL 2 ℝ H H p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.continuous.comp
    ((WithLp.sndL 2 ℝ H H).continuous.prodMk (WithLp.fstL 2 ℝ H H).continuous)

omit [CompleteSpace H] in
@[simp] lemma swapR_pair (x y : H) : swapR (pair x y) = pair y x := rfl

lemma star_swapR : star (swapR : HilbertPair H →L[ℝ] HilbertPair H) = swapR := by
  ext x
  apply ext_inner_left ℝ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (pair y₂ y₁) (pair x₁ x₂) = inner ℝ (pair y₁ y₂) (pair x₂ x₁)
  change inner ℝ y₂ x₁ + inner ℝ y₁ x₂ = inner ℝ y₁ x₂ + inner ℝ y₂ x₁
  exact add_comm _ _

def twistR : HilbertPair H →L[ℝ] HilbertPair H where
  toFun p := pair (Complex.I • WithLp.fstL 2 ℝ H H p) (-Complex.I • WithLp.sndL 2 ℝ H H p)
  map_add' _ _ := by simp only [map_add,smul_add]; rfl
  map_smul' r p := by
    simp only [map_smul, RingHom.id_apply,smul_comm Complex.I r,smul_comm (-Complex.I) r]
    rfl
  cont := (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.continuous.comp
    (((WithLp.fstL 2 ℝ H H).continuous.const_smul Complex.I).prodMk
      ((WithLp.sndL 2 ℝ H H).continuous.const_smul (-Complex.I)))

omit [CompleteSpace H] in
@[simp] lemma twistR_pair (x y : H) : twistR (pair x y) = pair (Complex.I • x) (-Complex.I • y) := rfl

lemma star_twistR : star (twistR : HilbertPair H →L[ℝ] HilbertPair H) = -twistR := by
  ext x
  apply ext_inner_left ℝ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (pair (Complex.I • y₁) (-Complex.I • y₂)) (pair x₁ x₂) =
    inner ℝ (pair y₁ y₂) (-pair (Complex.I • x₁) (-Complex.I • x₂))
  rw [inner_neg_right]
  simp only [WithLp.prod_inner_apply]
  change (inner ℂ (Complex.I • y₁) x₁).re + (inner ℂ (-Complex.I • y₂) x₂).re =
    -((inner ℂ y₁ (Complex.I • x₁)).re+(inner ℂ y₂ (-Complex.I • x₂)).re)
  simp [inner_smul_left,inner_smul_right]
  ring

end HilbertPair
namespace CyclicSeparatingData

instance graph_hasProjection (S : CyclicSeparatingData H) : S.graph.HasOrthogonalProjection := by
  unfold graph
  infer_instance

lemma projection_swap (S : CyclicSeparatingData H) : Commute S.graph.starProjection HilbertPair.swapR := by
  apply projection_commute_real
  · rintro ⟨x,y⟩ hxy
    exact S.graph_swap hxy
  · rw [HilbertPair.star_swapR]
    rintro ⟨x,y⟩ hxy
    exact S.graph_swap hxy

lemma projection_twist (S : CyclicSeparatingData H) : Commute S.graph.starProjection HilbertPair.twistR := by
  apply projection_commute_real
  · rintro ⟨x,y⟩ hxy
    exact S.graph_twist hxy
  · rw [HilbertPair.star_twistR]
    rintro ⟨x,y⟩ hxy
    exact S.graph.neg_mem (S.graph_twist hxy)

def diagonalBlock (S : CyclicSeparatingData H) : H →L[ℝ] H :=
  (WithLp.fstL 2 ℝ H H).comp (S.graph.starProjection.comp (HilbertPair.inl.restrictScalars ℝ))

def offDiagonalBlock (S : CyclicSeparatingData H) : H →L[ℝ] H :=
  (WithLp.sndL 2 ℝ H H).comp (S.graph.starProjection.comp (HilbertPair.inl.restrictScalars ℝ))

lemma projection_inl (S : CyclicSeparatingData H) (x : H) :
    S.graph.starProjection (HilbertPair.pair x 0) =
      HilbertPair.pair (S.diagonalBlock x) (S.offDiagonalBlock x) := rfl

lemma projection_inr (S : CyclicSeparatingData H) (y : H) :
    S.graph.starProjection (HilbertPair.pair 0 y) =
      HilbertPair.pair (S.offDiagonalBlock y) (S.diagonalBlock y) := by
  exact congrArg (fun f : HilbertPair H →L[ℝ] HilbertPair H => f (HilbertPair.pair y 0)) S.projection_swap.eq

lemma projection_pair (S : CyclicSeparatingData H) (x y : H) :
    S.graph.starProjection (HilbertPair.pair x y) =
      HilbertPair.pair (S.diagonalBlock x+S.offDiagonalBlock y)
        (S.offDiagonalBlock x+S.diagonalBlock y) := by
  rw [HilbertPair.pair_eq_inl_add_inr,map_add,HilbertPair.inl_apply,HilbertPair.inr_apply,
    S.projection_inl,S.projection_inr,← HilbertPair.pair_add]

lemma blocks_I (S : CyclicSeparatingData H) (x : H) :
    S.diagonalBlock (Complex.I • x) = Complex.I • S.diagonalBlock x ∧
    S.offDiagonalBlock (Complex.I • x) = -Complex.I • S.offDiagonalBlock x := by
  have he := congrArg (fun f : HilbertPair H →L[ℝ] HilbertPair H => f (HilbertPair.pair x 0)) S.projection_twist.eq
  change S.graph.starProjection (HilbertPair.pair (Complex.I • x) (-Complex.I • (0:H))) =
    HilbertPair.twistR (S.graph.starProjection (HilbertPair.pair x 0)) at he
  rw [smul_zero,S.projection_inl,S.projection_inl,HilbertPair.twistR_pair] at he
  exact ⟨congrArg (WithLp.fstL 2 ℝ H H) he,congrArg (WithLp.sndL 2 ℝ H H) he⟩

end CyclicSeparatingData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

omit [CompleteSpace H] in
lemma realLinear_smul_complex (a : H →L[ℝ] H)
    (ha : ∀ x, a (Complex.I • x) = Complex.I • a x) (c : ℂ) (x : H) :
    a (c • x) = c • a x := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul,mul_smul,map_add,Complex.coe_smul,Complex.coe_smul,map_smul,map_smul,ha]
  conv_rhs => rw [← Complex.re_add_im c]
  rw [add_smul,mul_smul,Complex.coe_smul,Complex.coe_smul]

omit [CompleteSpace H] in
lemma realLinear_smul_conj (a : H →L[ℝ] H)
    (ha : ∀ x, a (Complex.I • x) = -Complex.I • a x) (c : ℂ) (x : H) :
    a (c • x) = (starRingEnd ℂ c) • a x := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul,mul_smul,map_add,Complex.coe_smul,Complex.coe_smul,map_smul,map_smul,ha]
  have hc : starRingEnd ℂ c = (c.re:ℂ) + (c.im:ℂ) * (-Complex.I) := by
    rw [← Complex.re_add_im c,map_add,map_mul]
    simp
  rw [hc,add_smul,mul_smul,Complex.coe_smul,Complex.coe_smul]

namespace CyclicSeparatingData

def A (S : CyclicSeparatingData H) : H →L[ℂ] H where
  toFun := S.diagonalBlock
  map_add' := S.diagonalBlock.map_add
  map_smul' := realLinear_smul_complex S.diagonalBlock (fun x => (S.blocks_I x).1)
  cont := S.diagonalBlock.continuous

def B (S : CyclicSeparatingData H) : H →L[ℝ] H := S.offDiagonalBlock

@[simp] lemma A_apply (S : CyclicSeparatingData H) (x : H) : S.A x = S.diagonalBlock x := rfl
@[simp] lemma B_apply (S : CyclicSeparatingData H) (x : H) : S.B x = S.offDiagonalBlock x := rfl

lemma A_symmetric_real (S : CyclicSeparatingData H) (x y : H) :
    inner ℝ (S.A x) y = inner ℝ x (S.A y) := by
  change inner ℝ (S.diagonalBlock x) y = inner ℝ x (S.diagonalBlock y)
  have he := S.graph.inner_starProjection_left_eq_right (HilbertPair.pair x 0) (HilbertPair.pair y 0)
  rw [S.projection_inl,S.projection_inl] at he
  simpa only [WithLp.prod_inner_apply,HilbertPair.pair,WithLp.ofLp_toLp,inner_zero_left,
    inner_zero_right,add_zero] using he

lemma B_symmetric_real (S : CyclicSeparatingData H) (x y : H) :
    inner ℝ (S.B x) y = inner ℝ x (S.B y) := by
  change inner ℝ (S.offDiagonalBlock x) y = inner ℝ x (S.offDiagonalBlock y)
  have he := S.graph.inner_starProjection_left_eq_right (HilbertPair.pair x 0) (HilbertPair.pair 0 y)
  rw [S.projection_inl,S.projection_inr] at he
  simpa only [WithLp.prod_inner_apply,HilbertPair.pair,WithLp.ofLp_toLp,inner_zero_left,
    inner_zero_right,add_zero,zero_add] using he

lemma A_selfAdjoint (S : CyclicSeparatingData H) : IsSelfAdjoint S.A := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  apply Complex.ext
  · exact S.A_symmetric_real x y
  · have he := S.A_symmetric_real x (Complex.I • y)
    change (inner ℂ (S.A x) (Complex.I • y)).re = (inner ℂ x (S.A (Complex.I • y))).re at he
    simpa [inner_smul_right] using he

lemma B_selfAdjoint (S : CyclicSeparatingData H) : IsSelfAdjoint S.B :=
  LinearMap.IsSymmetric.isSelfAdjoint (S.B_symmetric_real)

lemma A_positive (S : CyclicSeparatingData H) : 0 ≤ S.A := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨S.A_selfAdjoint,fun x => ?_⟩
  change 0 ≤ inner ℝ (S.diagonalBlock x) x
  have he := S.graph.re_inner_starProjection_nonneg (HilbertPair.pair x 0)
  rw [S.projection_inl] at he
  change 0 ≤ inner ℝ (S.diagonalBlock x) x + inner ℝ (S.offDiagonalBlock x) 0 at he
  simpa only [inner_zero_right,add_zero] using he

lemma A_norm_le (S : CyclicSeparatingData H) : ‖S.A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have he := S.graph.norm_starProjection_apply_le (HilbertPair.pair x 0)
  rw [S.projection_inl] at he
  have hf := WithLp.norm_fst_le (p := (2:ENNReal)) H (HilbertPair.pair (S.diagonalBlock x) (S.offDiagonalBlock x))
  change ‖S.diagonalBlock x‖ ≤ ‖HilbertPair.pair (S.diagonalBlock x) (S.offDiagonalBlock x)‖ at hf
  simpa only [one_mul,A_apply] using hf.trans (by simpa [HilbertPair.pair] using he)

lemma A_le_one (S : CyclicSeparatingData H) : S.A ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg S.A S.A_positive).mp S.A_norm_le

lemma blocks_idempotent (S : CyclicSeparatingData H) (x : H) :
    S.A (S.A x)+S.B (S.B x)=S.A x ∧ S.B (S.A x)+S.A (S.B x)=S.B x := by
  have he := congrArg (fun f : HilbertPair H →L[ℝ] HilbertPair H => f (HilbertPair.pair x 0))
    S.graph.isIdempotentElem_starProjection.eq
  change S.graph.starProjection (S.graph.starProjection (HilbertPair.pair x 0)) = _ at he
  rw [S.projection_inl,S.projection_pair] at he
  exact ⟨congrArg (WithLp.fstL 2 ℝ H H) he,congrArg (WithLp.sndL 2 ℝ H H) he⟩

lemma A_injective (S : CyclicSeparatingData H) : Function.Injective S.A := by
  apply (S.A.toLinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change S.A x = 0 at hx
  have hmem : HilbertPair.pair (S.A x) (S.B x) ∈ S.graph :=
    Submodule.starProjection_apply_mem _ _
  have hb : S.B x = 0 := S.graph_vertical (hx ▸ hmem)
  have hp : S.graph.starProjection (HilbertPair.pair x 0)=0 := by
    rw [S.projection_inl]
    change HilbertPair.pair (S.A x) (S.B x)=0
    rw [hx,hb]
    rfl
  have ho := S.graph.starProjection_apply_eq_zero_iff.mp hp
  have hz : ∀ z : H, inner ℝ z x = 0 := by
    intro z
    refine S.cyclic.induction ?_ ?_ z
    · rintro _ ⟨a,ha,rfl⟩
      have hh := ho _ (S.core_mem_graph a ha)
      simpa only [WithLp.prod_inner_apply,HilbertPair.pair,WithLp.ofLp_toLp,inner_zero_right,add_zero] using hh
    · exact isClosed_eq (by fun_prop) continuous_const
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hz x)

lemma B_injective (S : CyclicSeparatingData H) : Function.Injective S.B := by
  apply (S.B.toLinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change S.B x = 0 at hx
  have hmem : HilbertPair.pair (S.A x) (S.B x) ∈ S.graph :=
    Submodule.starProjection_apply_mem _ _
  have ha : S.A x = 0 := S.graph_horizontal (hx ▸ hmem)
  exact S.A_injective (ha.trans S.A.map_zero.symm)

end CyclicSeparatingData
end BoundedRecovery

end
end
end

end OAI
