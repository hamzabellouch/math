import Mathlib
import OAI.Analysis.Commutator.ScalarUltralimit

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Pre (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] where
  seq : ℕ →ᵇ H

def equiv : Pre ω H ≃ (ℕ →ᵇ H) where
  toFun := Pre.seq
  invFun := Pre.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : AddCommGroup (Pre ω H) := (equiv ω H).addCommGroup

instance : Module ℂ (Pre ω H) := (equiv ω H).addEquiv.module ℂ

omit [InnerProductSpace ℂ H] in
@[simp] lemma seq_add (x y : Pre ω H) (i : ℕ) : (x+y).seq i=x.seq i+y.seq i := rfl

@[simp] lemma seq_smul (r : ℂ) (x : Pre ω H) (i : ℕ) : (r • x).seq i=r • x.seq i := rfl

omit [InnerProductSpace ℂ H] in
@[simp] lemma seq_zero (i : ℕ) : (0 : Pre ω H).seq i=0 := rfl

lemma inner_bounded (x y : Pre ω H) : ∃ C : ℝ, ∀ i,
    ‖inner ℂ (x.seq i) (y.seq i)‖≤C := by
  refine ⟨‖x.seq‖*‖y.seq‖,fun i => ?_⟩
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (x.seq.norm_coe_le_norm i)
    (y.seq.norm_coe_le_norm i) (norm_nonneg _) (norm_nonneg _))

def form (x y : Pre ω H) : ℂ :=
  ScalarUltralimit.limit ω (fun i => inner ℂ (x.seq i) (y.seq i)) (inner_bounded ω H x y)

lemma tendsto_form (x y : Pre ω H) :
    Tendsto (fun i => inner ℂ (x.seq i) (y.seq i)) (ω : Filter ℕ) (𝓝 (form ω H x y)) :=
  ScalarUltralimit.tendsto_limit ω _ _

instance core : PreInnerProductSpace.Core ℂ (Pre ω H) where
  inner := form ω H
  conj_inner_symm x y := by
    apply tendsto_nhds_unique _ (tendsto_form ω H x y)
    simpa only [RCLike.star_def,inner_conj_symm] using (tendsto_form ω H y x).star
  re_inner_nonneg x := by
    apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (tendsto_form ω H x x))
    exact Filter.Eventually.of_forall (fun i => (inner_self_nonneg (𝕜 := ℂ) (x := x.seq i)))
  add_left x y z := by
    apply tendsto_nhds_unique (tendsto_form ω H (x+y) z)
    simpa only [seq_add,inner_add_left] using (tendsto_form ω H x z).add (tendsto_form ω H y z)
  smul_left x y r := by
    apply tendsto_nhds_unique (tendsto_form ω H (r • x) y)
    simpa only [seq_smul,inner_smul_left] using tendsto_const_nhds.mul (tendsto_form ω H x y)

instance : SeminormedAddCommGroup (Pre ω H) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core ω H)

instance : InnerProductSpace ℂ (Pre ω H) := InnerProductSpace.ofCore (core ω H)

@[simp] lemma pre_inner (x y : Pre ω H) : inner ℂ x y=form ω H x y := rfl

lemma tendsto_inner (x y : Pre ω H) :
    Tendsto (fun i => inner ℂ (x.seq i) (y.seq i)) (ω : Filter ℕ) (𝓝 (inner ℂ x y)) :=
  tendsto_form ω H x y

lemma tendsto_norm (x : Pre ω H) :
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 ‖x‖) := by
  have h := (Complex.continuous_re.tendsto _ |>.comp (tendsto_inner ω H x x)).sqrt
  simpa only [Function.comp_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)] using h

abbrev Space := Completion (Pre ω H)

lemma norm_coe_tendsto (x : Pre ω H) :
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 ‖(x : Space ω H)‖) := by
  rw [Completion.norm_coe]
  exact tendsto_norm ω H x

lemma coe_eq_zero_iff (x : Pre ω H) : (x : Space ω H)=0 ↔
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 0) := by
  constructor
  · intro hx
    simpa only [hx,norm_zero] using norm_coe_tendsto ω H x
  · intro hx
    apply norm_eq_zero.mp
    exact tendsto_nhds_unique (norm_coe_tendsto ω H x) hx

def constantPre (x : H) : Pre ω H := ⟨BoundedContinuousFunction.const ℕ x⟩

lemma norm_constantPre (x : H) : ‖constantPre ω H x‖=‖x‖ :=
  tendsto_nhds_unique (tendsto_norm ω H _) tendsto_const_nhds

def constantPreMap : H →ₗᵢ[ℂ] Pre ω H where
  toFun := constantPre ω H
  map_add' := by
    intro x y
    apply (equiv ω H).injective
    apply BoundedContinuousFunction.ext
    intro i
    rfl
  map_smul' := by
    intro r x
    apply (equiv ω H).injective
    apply BoundedContinuousFunction.ext
    intro i
    rfl
  norm_map' := norm_constantPre ω H

def constant : H →ₗᵢ[ℂ] Space ω H :=
  (toComplₗᵢ : Pre ω H →ₗᵢ[ℂ] Space ω H).comp (constantPreMap ω H)

@[simp] lemma constant_apply (x : H) : constant ω H x=(constantPre ω H x : Space ω H) := rfl

end Kadison.HilbertSequence

end

end
end

end OAI
