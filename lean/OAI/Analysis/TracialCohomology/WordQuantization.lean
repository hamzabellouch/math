import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.MixedWords
import OAI.Analysis.TracialCohomology.PatchTraces

namespace OAI

/-! Word quantization for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
universe u v
variable {A : Type u} [Fintype A]

def shortWords (A : Type u) [Fintype A] : ℕ → Finset (List A)
  | 0 => {[]}
  | n+1 => by
    classical
    exact insert [] (Finset.univ.biUnion (fun a => (shortWords A n).image (List.cons a)))

@[simp] theorem mem_shortWords (l : List A) (n : ℕ) : l ∈ shortWords A n ↔ l.length ≤ n := by
  classical
  induction n generalizing l with
  | zero => simp [shortWords]
  | succ n ih =>
    cases l with
    | nil => simp [shortWords]
    | cons a l => simp [shortWords,ih]

variable {C B : Type u} [Fintype C] [Fintype B]
variable {G : Type u} [Group G]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem quantize_words (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (a : C → M) (γ : B → G) (v : Rep G M) (L : ℕ)
    (θ d : ℝ) (hθ : 0<θ) (hd : 0<d) :
    ∃ q : M, ∃ hq : IsStarProjection q, q ≠ 0 ∧ q ≤ p ∧ (τ q).re < d*(τ p).re ∧
      ∀ l : List (Letter C B), l.length ≤ L →
        ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
          (PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v l))) • 1)‖≤θ := by
  classical
  let W := {l : List (Letter C B) // l ∈ shortWords (Letter C B) L}
  let E := Fintype.equivFin W
  let F : Fin (Fintype.card W) → M := fun i => evaluate a γ v (E.symm i).val
  obtain ⟨q,hq,hq0,hqp,hqd,hqe⟩ := PopaCorner.local_quantization e τ hτ htr hfaith h1 hfactor
    hdiff hp hp0 F (θ^2) d (sq_pos_of_pos hθ) hd
  refine ⟨q,hq,hq0,hqp,hqd,fun l hl => ?_⟩
  let j : Fin (Fintype.card W) := E ⟨l,(mem_shortWords l L).mpr hl⟩
  have hj : F j=evaluate a γ v l := by simp [F,j]
  have hb : ‖τ.toPreGNS (q*evaluate a γ v l*q-
      (PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v l))) • q)‖^2 < θ^2*(τ q).re := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖τ.toPreGNS (q*F i*q-
        (PopaCorner.trace hp τ (PopaCorner.compress hp (F i))) • q)‖) (Finset.mem_univ j)
    have hhh := hh.trans_lt hqe
    simpa only [hj] using hhh
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  let z : PopaCorner.algebra hq := PopaCorner.compress hq (evaluate a γ v l)-
      (PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v l))) • 1
  have hz := PopaCorner.norm_sq_trace_corner τ hq z
  have hzb : ((τ q).re)*‖(PopaCorner.trace hq τ).toPreGNS z‖^2 < (τ q).re*θ^2 := by
    rw [hz,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_comm]
    exact hb
  have hh : ‖(PopaCorner.trace hq τ).toPreGNS z‖^2 < θ^2 := by nlinarith
  nlinarith [norm_nonneg ((PopaCorner.trace hq τ).toPreGNS z)]
end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B : Type u} [Fintype C] [Fintype B]
variable {G : Type u} [Group G]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in

theorem quantize_words (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hEp : Homogeneous e τ hτ htr hfaith p)
    (a : C → M) (γ : B → G) (v : Rep G M) (L : ℕ)
    (θ d : ℝ) (hθ : 0<θ) (hd : 0<d) :
    ∃ q : M, ∃ hq : IsStarProjection q, q ≠ 0 ∧ q ≤ p ∧ (τ q).re < d*(τ p).re ∧ Homogeneous e τ hτ htr hfaith q ∧
      ∀ l : List (Letter C B), l.length ≤ L →
        ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
          PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ := by
  classical
  let W := {l : List (Letter C B) // l ∈ shortWords (Letter C B) L}
  let E := Fintype.equivFin W
  let F : Fin (Fintype.card W) → M := fun i => evaluate a γ v (E.symm i).val
  obtain ⟨q,hq,hq0,hqp,hqd,hEq,hqe⟩ := local_quantization_corner e τ hτ htr hfaith h1
    hII hp hp0 hEp F (θ^2) d (sq_pos_of_pos hθ) hd
  refine ⟨q,hq,hq0,hqp,hqd,hEq,fun l hl => ?_⟩
  let j : Fin (Fintype.card W) := E ⟨l,(mem_shortWords l L).mpr hl⟩
  have hj : F j=evaluate a γ v l := by simp [F,j]
  have hb : ‖τ.toPreGNS (q*evaluate a γ v l*q-
      cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)*q)‖^2 < θ^2*(τ q).re := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖τ.toPreGNS (q*F i*q-
        cornerCoefficient e τ hτ htr hfaith hp (F i)*q)‖) (Finset.mem_univ j)
    have hhh := hh.trans_lt hqe
    simpa only [hj] using hhh
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  let z : PopaCorner.algebra hq := PopaCorner.compress hq (evaluate a γ v l)-
      PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l))
  have hz := PopaCorner.norm_sq_trace_corner τ hq z
  have hzb : ((τ q).re)*‖(PopaCorner.trace hq τ).toPreGNS z‖^2 < (τ q).re*θ^2 := by
    rw [hz,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_comm]
    change ‖τ.toPreGNS (q*evaluate a γ v l*q-
      ((PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l))):M))‖^2 < _
    rw [compress_central hq (cornerCoefficient_central e τ hτ htr hfaith hp (evaluate a γ v l))]
    exact hb
  have hh : ‖(PopaCorner.trace hq τ).toPreGNS z‖^2 < θ^2 := by nlinarith
  nlinarith [norm_nonneg ((PopaCorner.trace hq τ).toPreGNS z)]
end PopaCenter

end

end OAI
