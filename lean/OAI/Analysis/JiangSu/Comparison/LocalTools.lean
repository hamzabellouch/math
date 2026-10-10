import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ExactLocalSupply

namespace OAI

noncomputable section
namespace DirectPacking
open Pureness CurrentMain DirectComparison Filter
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

def CoefficientSupply : Prop :=
  ∀ (q : D), IsStarProjection q → ∀ s : ℝ, s ∈ Set.Icc 0 1 →
    ∀ F : Finset D, ∀ ε : ℝ, 0 < ε →
      ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ b ∈ F, ∀ τ : RestrictedTracialState D,
        ‖τ.functional (e*b)-(s:ℂ)*τ.functional (q*b)‖ < ε

def InsertionSupply : Prop :=
  ∀ (z y : D), IsStarProjection z → IsStarProjection y →
    ∃ t : D, IsStarProjection t ∧ t ≤ 1-z ∧ ∀ τ : RestrictedTracialState D,
      ((τ.functional y).re-3*(τ.functional (y*z)).re ≤ (τ.functional t).re ∧
        (τ.functional t).re ≤ (τ.functional y).re) ∧
      traceTwoNorm τ (t-y)^2 ≤ 5*(τ.functional (y*z)).re ∧
      ∀ x : D, ‖x‖ ≤ 1 → ‖τ.functional ((t-y)*x)‖ ≤
        2*Real.sqrt (τ.functional y).re*traceTwoNorm τ (t-y)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ)
local notation "D₀" => FamilyUltrapower (fun τ : TracialState A => τ) U

@[instance_reducible] def limitTraceFamily : TraceFamily D₀ where
  carrier := Set.range (familyLimitTrace (fun τ : TracialState A => τ) U)

lemma limitTraceFamily_nonempty :
    let := limitTraceFamily (A := A) U
    Nonempty (RestrictedTracialState D₀) := by
  let := limitTraceFamily (A := A) U
  let s : ℕ → TracialState A := fun _ => Classical.ofNonempty
  exact ⟨⟨familyLimitTrace (fun τ : TracialState A => τ) U s,⟨s,rfl⟩⟩⟩

lemma source_tools (hfree : (U : Filter ℕ) ≤ atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A) (hcmp : StrictComparison A) :
    let := limitTraceFamily (A := A) U
    SpectralProjectionSupply (fun τ : RestrictedTracialState D₀ => (τ : TracialState D₀)) ∧
      CoefficientSupply (D := D₀) ∧ InsertionSupply (D := D₀) := by
  let := limitTraceFamily (A := A) U
  constructor
  · intro h hh hhn α hα hα1
    obtain ⟨p,hp,hl,hr,htr⟩ := projection_supply U hfree hsimple hinf hcmp h hh hhn α hα hα1
    refine ⟨p,hp,hl,hr,?_⟩
    rintro ⟨τ,⟨s,rfl⟩⟩
    exact htr s
  constructor
  · intro q hq s hs F ε hε
    obtain ⟨e,he,heq,ht⟩ := coefficient_split U hfree hsimple hinf hcmp hq hs F hε
    refine ⟨e,he,heq,?_⟩
    intro b hb
    rintro ⟨τ,⟨t,rfl⟩⟩
    exact ht b hb t
  · intro z y hz hy
    obtain ⟨t,ht,htz,htr⟩ := DirectComparison.orthogonal_insertion U hfree hsimple hinf hcmp hz hy
    refine ⟨t,ht,htz,?_⟩
    rintro ⟨τ,⟨s,rfl⟩⟩
    exact htr s

end DirectPacking

namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder

variable {D I : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TraceFamily D] [Fintype I] {q : D} (U : ProjectionRow I q)

theorem sample_mass_overlap (hcoef : CoefficientSupply (D := D))
    (z : D) {c ε : ℝ} (hc : c ∈ Set.Icc 0 1) (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ τ : RestrictedTracialState D,
      ‖τ.functional (U.sample e) - (c : ℂ) * τ.functional (U.sample q)‖ < ε ∧
      ‖τ.functional (z * U.sample e) - (c : ℂ) * τ.functional (z * U.sample q)‖ < ε := by
  classical
  let k : ℝ := Fintype.card I
  let δ := ε / (k + 1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (k + 1) = ε := div_mul_cancel₀ _ (ne_of_gt (by positivity))
  have hkδ : k * δ < ε := calc
    k * δ < (k + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one k) hδ
    _ = ε := (mul_comm _ _).trans hδeq
  have hδε : δ ≤ ε := div_le_self hε.le (le_add_of_nonneg_left hk)
  obtain ⟨e, he, heq, htest⟩ := hcoef q U.projection c hc {1, U.overlapTest z} δ hδ
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  refine ⟨e, he, heq, ?_⟩
  intro τ
  constructor
  · have hmass := htest 1 (Finset.mem_insert_self _ _) τ
    simp only [mul_one] at hmass
    rw [U.trace_sample τ e heq', U.trace_sample τ q U.projection.isIdempotentElem]
    rw [show (Fintype.card I : ℂ) * τ.functional e -
      (c : ℂ) * ((Fintype.card I : ℂ) * τ.functional q) =
      (Fintype.card I : ℂ) * (τ.functional e - (c : ℂ) * τ.functional q) by ring,
      norm_mul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hmass.le hk).trans_lt hkδ
  · rw [U.trace_overlap_sample, U.trace_overlap_sample]
    exact (htest _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) τ).trans_le hδε

end DirectPacking
end

end OAI
