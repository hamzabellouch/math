import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PointStrength
import OAI.Combinatorics.RamseyFive.Probability.AbsScoreTerm

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

def ownQuery (x : ℙ K V) (S O : Finset (ℙ K V)) (y : S) : Prop :=
  y.val∈O ∨ x=y.val

noncomputable def outsideEquiv (x : ℙ K V) (S O : Finset (ℙ K V)) :
    {y : S // ¬ownQuery x S O y} ≃ outsideAt x S O where
  toFun y := ⟨⟨y.val.val,(not_or.mp y.property).2⟩,
    Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨y.val.property,(not_or.mp y.property).1⟩)⟩
  invFun y := ⟨⟨y.val.val,(Finset.mem_sdiff.mp (Finset.mem_subtype.mp y.property)).1⟩,
    not_or.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_subtype.mp y.property)).2,y.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def ownBitsMinus (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ}
    (u : Fin R→{y : S // ownQuery x S O y}→ℕ) (H : F) (r : Fin R) : Bool :=
  decide (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → u r ⟨y,Or.inl hy⟩=0)

noncomputable def modifiedPointScore (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) : ℝ :=
  typicalScore Finset.univ
    (fun H : F => Finset.univ.filter fun y : outsideAt x S O => Incident y.val.val H.val)
    b (ownBitsMinus x S O F (fun r i => ω r i))
    (fun r d => ω r ((outsideEquiv x S O).symm d).val)

variable [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_original_validation {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (L : ℝ≥0) (hL : 1≤(L:ℝ)) (R : ℕ) (hR : 2≤R) :
    (∫ ω,(modifiedPointScore x S (C a∪C b) F
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω)^2
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R) ≤
      (F.card:ℝ)*(2*Real.exp (-(L:ℝ)*(3/4)))^R+
      (2*(L:ℝ)^2*Real.exp (-(L:ℝ)*(3/4)))^R*
        ((40*scale (K:=K) d S.card*Real.exp ξ)^2+
          ∑ H : F,∑ H'∈Finset.univ.erase H,
            (mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
              (pencilLines x F H∩pencilLines x F H'))^R) := by
  have hbase : Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have hb0 : 0≤1-ownFraction S (C a) (C b) := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) hb0
  apply original_uniform_score_moment (ownQuery x S (C a∪C b))
    (outsideEquiv x S (C a∪C b)) (L*pointStrength S) Finset.univ _ hbase
    (ownBitsMinus x S (C a∪C b) F) 2
  intro u
  exact actual_validation_second x hdim hd S C hS a b c ha hb hc F hF hf hn hξ hx L hL R hR _

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

noncomputable def pointScore (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) : ℝ :=
  ∑ H : F, ∏ r, (if (∀ y : S,y.val∈O → Incident y.val H.val → ω r y=0) then 1 else 0)*
    ((if (∀ y : S,y.val∉O → Incident y.val H.val → ω r y=0) then 1 else 0)-b)

def Unsampled (x : ℙ K V) (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) : Prop :=
  ∀r y,x=y.val → ω r y=0

omit [Finite K] [FiniteDimensional K V] in
theorem modifiedPointScore_eq (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ)
    (hω : Unsampled x S ω) : modifiedPointScore x S O F b ω=pointScore S O F b ω := by
  unfold modifiedPointScore typicalScore pointScore
  apply Finset.sum_congr rfl
  intro H hH
  unfold scoreTerm
  apply Finset.prod_congr rfl
  intro r hr
  have ho : (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → ω r y=0) ↔
      (∀ y : S,y.val∈O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI
      by_cases hx : x=y.val
      · exact hω r y hx
      · exact h y hy hx hI
    · intro h y hy _ hI
      exact h y hy hI
  have he : (fun d : outsideAt x S O => ω r ((outsideEquiv x S O).symm d).val) ∈
      emptyEvent (Finset.univ.filter fun y : outsideAt x S O => Incident y.val.val H.val) ↔
      (∀ y : S,y.val∉O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI
      by_cases hx : x=y.val
      · exact hω r y hx
      · let z : {y : S // ¬ownQuery x S O y} := ⟨y,not_or.mpr ⟨hy,hx⟩⟩
        have hz : (outsideEquiv x S O z)∈Finset.univ.filter
            (fun y : outsideAt x S O => Incident y.val.val H.val) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI⟩
        have hh := h (outsideEquiv x S O z) hz
        simpa only [Equiv.symm_apply_apply,Set.mem_singleton_iff] using hh
    · intro h y hy
      apply h ((outsideEquiv x S O).symm y).val
      · exact (not_or.mp ((outsideEquiv x S O).symm y).property).1
      · exact (Finset.mem_filter.mp hy).2
  change (if decide (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → ω r y=0)
    then _ else 0)=_
  simp only [ho,decide_eq_true_eq,centeredFactor,emptyIndicator,Set.indicator_apply,he]
  split_ifs <;> ring

end SharpRamseyFive.ScoreGeometry

end OAI
