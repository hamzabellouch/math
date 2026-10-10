import OAI.Analysis.CStarAlgebra.PureInfiniteness.Ultrafilter

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
open Filter
open scoped Topology
universe u v
variable {ι : Type*} {A : Type u} [CStarAlgebra A]
local instance avoidanceLimitPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance avoidanceLimitStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance avoidanceLimitOperatorPartialOrder (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance avoidanceLimitOperatorStarOrderedRing (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _
variable {H : ι → Type v} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

theorem four_limit_impossible (ω : Ultrafilter ι)
    (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hV : ∀ᶠ i in (ω : Filter ι), (1/8 : ℝ) ≤ ‖π i (firstV X) (ξ i)‖)
    (hD₁ : ∀ i, π i (B 0) * star (π i (B 0)) ≤ (1/2 : ℝ) • 1)
    (hm₁ : ∀ i, π i (B 1 * star (B 1)) = π i (B 0 * star (B 0)))
    (hc₁ : ∀ i, π i (B 0 * star (B 1)) = 0)
    (hs₀ : ∀ i, π i (firstH X * star (B 0)) = π i (star (B 0)))
    (hs₁ : ∀ i, π i (firstH X * star (B 1)) = π i (star (B 1)))
    (hU : ∀ w : A, Tendsto (fun i => ‖π i (firstU X (B 0) * w * firstV X)‖)
      (ω : Filter ι) (𝓝 0))
    (hD₃ : ∀ i, π i (B 2) * star (π i (B 2)) ≤ (1/2 : ℝ) • 1)
    (hc₃ : ∀ i, π i (star (B 2) * B 3) = 0)
    (hm₃ : ∀ i, π i (star (B 2) * B 2) = π i (star (B 3) * B 3))
    (hR : Tendsto (fun i => ‖π i (lastR X (B 0) (B 2))‖) (ω : Filter ι) (𝓝 0))
    (hs₃ : ∀ i, π i (ramp (prospectiveDefect X (B 0)) 0 (1/2) * B 3) = π i (B 3)) : False := by
  let ρ := limitRep ω π ξ hξ
  let Ψ := rangeRestriction ρ (firstV X)
  have hkill : ∀ a : A, Tendsto (fun i => ‖π i a‖) (ω : Filter ι) (𝓝 0) → Ψ a = 0 := by
    intro a ha
    have hz : ρ a = 0 := limitRep_annihilates ω π ξ hξ a ha
    ext x
    change (ρ a x : LimitHilbert ω π ξ hξ) = 0
    rw [hz, zero_apply]
  have hzero : ∀ a : A, (∀ i, π i a = 0) → Ψ a = 0 := by
    intro a ha
    apply hkill a
    simp only [ha, norm_zero]
    exact tendsto_const_nhds
  have heq : ∀ a b : A, (∀ i, π i a = π i b) → Ψ a = Ψ b := by
    intro a b hab
    have hz := hzero (a-b) (fun i => by rw [map_sub, hab i, sub_self])
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  have hbound (j : Fin 4) (hj : ∀ i, π i (B j) * star (π i (B j)) ≤ (1/2 : ℝ) • 1) := by
    have hz := hzero (cut (B j * star (B j)) (1/2)) (fun i => by
      rw [map_cut_sa (π i) (.mul_star_self _) (by norm_num), map_mul, map_star]
      exact cut_zero_of_le (mul_star_self_nonneg _) (by norm_num) (hj i))
    rw [map_cut_sa (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (IsSelfAdjoint.mul_star_self (B j)) (by norm_num : (0:ℝ) ≤ 1/2), map_mul, map_star] at hz
    exact le_of_cut_zero (mul_star_self_nonneg _) (by norm_num) hz
  have hψV : firstV (Ψ X) ≠ 0 := by
    rw [← map_firstV (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)]
    exact rangeRestriction_nonzero ρ (firstV X) (.of_nonneg (cut_nonneg X _))
      (limitRep_nonzero ω π ξ hξ (firstV X) (by norm_num : (0:ℝ) < 1/8) hV)
  have hψU : firstU (Ψ X) (Ψ (B 0)) = 0 := by
    rw [← map_firstU (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)]
    apply rangeRestriction_kills ρ (firstV X) (firstU X (B 0))
    intro w
    simpa only [map_mul] using limitRep_annihilates ω π ξ hξ _ (hU w)
  apply four_fixed_impossible (map_nonneg Ψ hX) (fun i => Ψ (B i)) hψV
    (hbound 0 hD₁) ?_ ?_ ?_ ?_ hψU (hbound 2 hD₃) ?_ ?_ ?_ ?_
  · simpa only [map_mul, map_star] using heq _ _ hm₁
  · simpa only [map_mul, map_star] using hzero _ hc₁
  · simpa only [map_mul, map_star, map_firstH (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using heq _ _ hs₀
  · simpa only [map_mul, map_star, map_firstH (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using heq _ _ hs₁
  · simpa only [map_mul, map_star] using hzero _ hc₃
  · simpa only [map_mul, map_star] using heq _ _ hm₃
  · simpa only [map_lastR (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using hkill _ hR
  · have hp : IsSelfAdjoint (prospectiveDefect X (B 0)) :=
      .of_nonneg (prospectiveDefect_nonneg X _)
    simpa only [map_mul, map_ramp_sa (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ hp le_rfl, map_prospectiveDefect (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using
      heq _ _ hs₃

end MainGap

namespace MainGap
universe u v
open Filter
open scoped Topology
variable (A : Type u) [CStarAlgebra A]

structure HilbertRep where
  H : Type v
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  hom : A →⋆ₐ[ℂ] (H →L[ℂ] H)

attribute [instance] HilbertRep.normed HilbertRep.inner HilbertRep.complete

variable {A}
local instance avoidancePartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance avoidanceStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance avoidanceOperatorPartialOrder (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance avoidanceOperatorStarOrderedRing (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _

theorem four_avoidance_unital {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z) :
    ∃ T : Fin 4 → A, (∀ j, ‖T j‖ ≤ 1) ∧ (∀ j, T j ∈ fourHer X) ∧
      ∀ R : HilbertRep.{u,v} A, (1/4 : ℝ) < ‖R.hom X‖ →
        ¬ ∀ j, R.hom (T j) = R.hom (B j) := by
  classical
  by_contra! hbad
  let F : ∀ i : FourIndex A, FourChoice.{v,u} X B i.2 (fourEta A i) :=
    fun i => Classical.choice (fourChoice_nonempty hX B hp i.2 (fourEta_pos A i))
  have hbad' : ∀ i : FourIndex A, ∃ R : HilbertRep.{u,v} A,
      (1/4 : ℝ) < ‖R.hom X‖ ∧ ∀ j, R.hom ((F i).T j) = R.hom (B j) :=
    fun i => hbad (F i).T (F i).contractive (F i).mem
  choose R hRX hmatch using hbad'
  let π := fun i => (R i).hom
  change ∀ i j, π i ((F i).T j) = π i (B j) at hmatch
  have hVbig : ∀ i, (1/8 : ℝ) < ‖π i (firstV X)‖ := by
    intro i
    have hn : ‖π i X - π i (firstV X)‖ ≤ (1/8 : ℝ) := by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (π i) _).trans
        (norm_sub_cut_le hX (by norm_num))
    have hm := norm_sub_norm_le (π i X) (π i (firstV X))
    have hi := hRX i
    change (1/4 : ℝ) < ‖π i X‖ at hi
    linarith
  choose ξ hξ hξV using fun i => (π i (firstV X)).exists_lt_apply_of_lt_opNorm (hVbig i)
  have hnξ : ∀ i, ‖ξ i‖ ≤ 1 := fun i => (hξ i).le
  have hEt := fourEta_ultra A
  apply four_limit_impossible (fourUltra A) π ξ hnξ hX B
    (Filter.Eventually.of_forall (fun i => (hξV i).le))
    (fun i => (F i).first_bound (π i) hX (fourEta_pos A i) (hmatch i)) ?_ ?_ ?_ ?_ ?_
    (fun i => (F i).last_bound (π i) hX (fourEta_pos A i) (hmatch i)) ?_ ?_ ?_ ?_
  · intro i
    have hm := congrArg (π i) (F i).first_equal
    simpa only [map_mul, map_star, hmatch i] using hm
  · intro i
    have hm := congrArg (π i) (F i).first_cross
    simpa only [map_mul, map_star, hmatch i, map_zero] using hm
  · intro i
    have hm := congrArg (π i) ((F i).first_support₀ hX)
    simpa only [map_mul, map_star, hmatch i] using hm
  · intro i
    have hm := congrArg (π i) ((F i).first_support₁ hX)
    simpa only [map_mul, map_star, hmatch i] using hm
  · intro w
    have hg : Tendsto (fun i : FourIndex A =>
        Real.sqrt (2 * fourEta A i) * ‖CFC.sqrt (firstV X)‖ +
          fourEta A i * ‖w‖ * ‖firstV X‖) (fourUltra A : Filter (FourIndex A)) (𝓝 0) := by
      convert ((hEt.const_mul 2).sqrt.mul_const ‖CFC.sqrt (firstV X)‖).add
        ((hEt.mul_const ‖w‖).mul_const ‖firstV X‖) using 1; norm_num
    apply squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _)) ?_ hg
    filter_upwards [fourUltra_le A (fourIndex_eventually_mem A w)] with i hi
    exact represented_mixed_estimate (π i) (firstU_nonneg _ _) (cut_nonneg X _)
      (fourEta_pos A i) hi ((F i).first_norm (π i) hX (fourEta_pos A i) (hmatch i)).le
  · intro i
    have hm := congrArg (π i) (F i).last_cross
    simpa only [map_mul, map_star, hmatch i, map_zero] using hm
  · intro i
    have hm := congrArg (π i) (F i).last_equal
    simpa only [map_mul, map_star, hmatch i] using hm
  · have ht : Tendsto (fun i : FourIndex A => 4 * fourEta A i)
        (fourUltra A : Filter (FourIndex A)) (𝓝 0) := by
      simpa using hEt.const_mul 4
    exact squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _))
      (Filter.Eventually.of_forall (fun i =>
        ((F i).last_norm_lt (π i) hX (fourEta_pos A i) (hmatch i)).le)) ht
  · intro i
    have hm := congrArg (π i) (F i).last_support
    simpa only [map_mul, hmatch i] using hm

end MainGap

end

end OAI
