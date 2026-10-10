import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Homogeneous
import OAI.Analysis.TracialCohomology.RepresentationLimits

namespace OAI

/-! Mixed words for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev Letter (C B : Type*) := C ⊕ B

def letterValue (a : C → M) (γ : B → G) (v : Rep G M) : Letter C B → M :=
  Sum.elim a (fun b => v (γ b))
def letterDegree (γ : B → G) : Letter C B → G := Sum.elim (fun _ => 1) γ

def evaluate (a : C → M) (γ : B → G) (v : Rep G M) (l : List (Letter C B)) : M :=
  (l.map (letterValue a γ v)).prod
def degree (γ : B → G) (l : List (Letter C B)) : G := (l.map (letterDegree γ)).prod

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma evaluate_nil (a : C → M) (γ : B → G) (v : Rep G M) : evaluate a γ v []=1 := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma evaluate_cons (a : C → M) (γ : B → G) (v : Rep G M) (x) (l) :
    evaluate a γ v (x::l)=letterValue a γ v x*evaluate a γ v l := rfl
@[simp] lemma degree_nil (γ : B → G) : degree (C:=C) γ []=1 := rfl
@[simp] lemma degree_cons (γ : B → G) (x : Letter C B) (l) :
    degree γ (x::l)=letterDegree γ x*degree γ l := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma letter_norm_le (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (v : Rep G M) (x) :
    ‖letterValue a γ v x‖≤1 := by
  cases x with
  | inl c => exact ha c
  | inr b => exact v.norm_le (γ b)

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_norm_le (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (v : Rep G M) (l) :
    ‖evaluate a γ v l‖≤1 := by
  induction l with
  | nil => exact (IsStarProjection.one M).norm_le
  | cons x l ih =>
    calc
      ‖evaluate a γ v (x::l)‖ ≤ ‖letterValue a γ v x‖ * ‖evaluate a γ v l‖ := norm_mul_le _ _
      _ ≤ 1 * ‖evaluate a γ v l‖ :=
        mul_le_mul_of_nonneg_right (letter_norm_le a ha γ v x) (norm_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using ih

lemma degree_append (γ : B → G) (l k : List (Letter C B)) : degree γ (l++k)=degree γ l*degree γ k := by
  simp only [degree,List.map_append,List.prod_append]
omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_append (a : C → M) (γ : B → G) (v : Rep G M) (l k) :
    evaluate a γ v (l++k)=evaluate a γ v l*evaluate a γ v k := by
  simp only [evaluate,List.map_append,List.prod_append]

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_zero_of_degree_ne_one (a : C → M) (γ : B → G) (l : List (Letter C B))
    (hl : degree γ l ≠ 1) : evaluate a γ Rep.zero l=0 := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons x l ih =>
    cases x with
    | inl c =>
      have hh : degree γ l ≠ 1 := by simpa only [degree_cons,letterDegree,Sum.elim_inl,one_mul] using hl
      change a c*evaluate a γ Rep.zero l=0
      rw [ih hh,mul_zero]
    | inr b => exact zero_mul _

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include htr in
lemma evaluate_tendsto (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G)
    {v : ℕ → Rep G M} {w : Rep G M}
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) (l) :
    GNSTendsto τ (fun n => evaluate a γ (v n) l) atTop (evaluate a γ w l) := by
  induction l with
  | nil => exact GNSTendsto.const τ 1 atTop
  | cons x l ih =>
    have hx : GNSTendsto τ (fun n => letterValue a γ (v n) x) atTop (letterValue a γ w x) := by
      cases x with
      | inl c => exact GNSTendsto.const τ (a c) atTop
      | inr b => exact ht (γ b)
    exact hx.mul τ htr ih 1 (fun n => letter_norm_le a ha γ (v n) x)

def Good (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) (v : Rep G M) : Prop :=
  ∀ l : List (Letter C B), l.length ≤ L → degree γ l ≠ 1 →
    ‖τ (evaluate a γ v l)‖ ≤ ε l.length*Rep.rank τ v

omit [StarOrderedRing M] in
lemma good_zero (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) : Good τ a γ L ε Rep.zero := by
  intro l hl hd
  rw [evaluate_zero_of_degree_ne_one a γ l hd,map_zero,norm_zero]
  simp only [Rep.rank,Rep.support,Rep.zero,map_zero,Complex.zero_re,mul_zero,le_refl]

include e hτ htr hfaith in
lemma good_closed (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ)
    (v : ℕ → Rep G M) (w : Rep G M) (hv : ∀ n, Good τ a γ L ε (v n))
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) : Good τ a γ L ε w := by
  intro l hl hd
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hrt := Rep.rank_tendsto e τ hτ hfaith ht
  have hvt := trace_predual_tendsto e τ hτ
    (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
      (fun n => evaluate_norm_le a ha γ (v n) l) (evaluate_tendsto τ htr a ha γ ht l))
  exact le_of_tendsto_of_tendsto hvt.norm (tendsto_const_nhds.mul hrt)
    (Filter.Eventually.of_forall (fun n => hv n l hl hd))

include e hτ htr hfaith in
lemma maximal_good (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) :
    ∃ v : Rep G M, Good τ a γ L ε v ∧ ∀ w, Good τ a γ L ε w → v ≤ w → w ≤ v :=
  Rep.exists_maximal_closed e τ hτ htr hfaith (Good τ a γ L ε)
    (good_zero τ a γ L ε) (good_closed e τ hτ htr hfaith a ha γ L ε)
end Dual
end PopaPatching

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def Good (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) (v : PopaPatching.Rep G M) : Prop :=
  Homogeneous e τ hτ htr hfaith v.support ∧
  ∀ l : List (Letter C B), l.length ≤ L → degree γ l ≠ 1 →
    ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖ ≤ ε l.length*Rep.rank τ v

include h1 in
lemma good_zero (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) :
    Good e τ hτ htr hfaith a γ L ε Rep.zero := by
  refine ⟨homogeneous_zero e τ hτ htr hfaith h1,fun l hl hd => ?_⟩
  rw [evaluate_zero_of_degree_ne_one a γ l hd]
  change ‖τ.toPreGNS (expectation e τ hτ htr hfaith h1 0)‖≤_
  rw [map_zero,map_zero,norm_zero]
  simp only [Rep.rank,Rep.support,Rep.zero,map_zero,Complex.zero_re,mul_zero,le_refl]

include h1 in
lemma good_closed (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ)
    (v : ℕ → Rep G M) (w : Rep G M) (hv : ∀ n, Good e τ hτ htr hfaith a γ L ε (v n))
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) : Good e τ hτ htr hfaith a γ L ε w := by
  refine ⟨homogeneous_limit e τ hτ htr hfaith h1 (fun n => (hv n).1) (ht 1) 1
    (fun n => (v n).norm_le 1),fun l hl hd => ?_⟩
  have hrt := Rep.rank_tendsto e τ hτ hfaith ht
  have hvt := average_gns_tendsto e τ hτ htr hfaith h1 (evaluate_tendsto τ htr a ha γ ht l)
  have htn : Tendsto (fun n => τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ (v n) l)))
      atTop (𝓝 (τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ w l)))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [GNSTendsto,←map_sub] using hvt
  exact le_of_tendsto_of_tendsto htn.norm (tendsto_const_nhds.mul hrt)
    (Filter.Eventually.of_forall (fun n => (hv n).2 l hl hd))

include h1 in
lemma maximal_good (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) :
    ∃ v : Rep G M, Good e τ hτ htr hfaith a γ L ε v ∧
      ∀ w, Good e τ hτ htr hfaith a γ L ε w → v ≤ w → w ≤ v :=
  Rep.exists_maximal_closed e τ hτ htr hfaith (Good e τ hτ htr hfaith a γ L ε)
    (good_zero e τ hτ htr hfaith h1 a γ L ε) (good_closed e τ hτ htr hfaith h1 a ha γ L ε)
end PopaCenter

end

end OAI
