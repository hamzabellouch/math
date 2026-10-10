import OAI.Analysis.TreePotential.FiniteHeads

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section AsymptoticModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed finite-codimensional subspaces for asymptotic moduli. -/

structure ClosedFiniteCodim where
  space : Submodule ℝ E
  closed : IsClosed (space : Set E)
  finiteCodim : Module.Finite ℝ (E ⧸ space)

/-- We take these infima and suprema in the extended reals, so their definitions
    are meaningful without tacit boundedness side conditions. On infinite
    dimensional normed spaces their values at positive radii are finite. -/
def averagedModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1 ≤ ‖y‖},
      (((‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1 : ℝ) : EReal)

def oneSidedModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖ = 1},
      ((‖x.val + t • y.val‖ - 1 : ℝ) : EReal)

def IsAUC : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulus E t

end AsymptoticModuli

lemma ereal_le_of_forall_pos_sub_le (a : ℝ) (b : EReal)
    (h : ∀ ε : ℝ, 0 < ε → ((a - ε : ℝ) : EReal) ≤ b) : (a : EReal) ≤ b := by
  cases b using EReal.rec with
  | bot => exact ((EReal.bot_lt_coe (a - 1)).not_ge (h 1 zero_lt_one)).elim
  | coe b => exact EReal.coe_le_coe_iff.mpr (le_of_forall_pos_sub_le (fun ε hε =>
      EReal.coe_le_coe_iff.mp (h ε hε)))
  | top => exact le_top

lemma averagedModulus_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t b : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ F : ClosedFiniteCodim E,
      ∀ y : E, y ∈ F.space → 1 ≤ ‖y‖ →
        b - ε ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1) :
    (b : EReal) ≤ averagedModulus E t := by
  apply le_iInf
  intro x
  apply ereal_le_of_forall_pos_sub_le
  intro ε hε
  obtain ⟨F, hF⟩ := h x.val x.property ε hε
  apply le_iSup_of_le F
  apply le_iInf
  intro y
  exact EReal.coe_le_coe_iff.mpr (hF y.val y.property.1 y.property.2)

lemma midpoint_center_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x z y : E) (t : ℝ) :
    (‖z + t • y‖ + ‖z - t • y‖) / 2 ≤
      (‖x + t • y‖ + ‖x - t • y‖) / 2 + ‖z - x‖ := by
  have h1 := norm_sub_norm_le (z + t • y) (x + t • y)
  have h2 := norm_sub_norm_le (z - t • y) (x - t • y)
  have he1 : (z + t • y) - (x + t • y) = z - x := by abel
  have he2 : (z - t • y) - (x - t • y) = z - x := by abel
  rw [he1] at h1
  rw [he2] at h2
  linarith

lemma optimal_pair_parameters {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ a θ : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧ a^2 + θ^2 ≤ 1 ∧
      a + t * θ / 2 = Real.sqrt (1 + t^2/4) := by
  let d := Real.sqrt (4 + t^2)
  have hd : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hd2 : d^2 = 4 + t^2 := Real.sq_sqrt (by positivity)
  have hdle : 2 ≤ d := by nlinarith
  refine ⟨2 / d, t / d, by positivity, (div_le_one hd).mpr hdle,
    by positivity, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · have he : (2 / d)^2 + (t / d)^2 = 1 := by
      field_simp
      nlinarith
    exact he.le
  · have he : 2 / d + t * (t / d) / 2 = d / 2 := by
      field_simp
      nlinarith
    rw [he]
    have hs : (d / 2)^2 = 1 + t^2 / 4 := by nlinarith
    rw [← hs, Real.sqrt_sq (by positivity)]

section TestSeparable
open scoped Classical
variable {I : Type*}

def testVectorBasis (K : TestFamily I) : Module.Basis I ℝ (TestVector K) :=
  Finsupp.basisSingleOne.map (testVectorEquiv K).symm

instance testVector_separable (K : TestFamily I) [Countable I] :
    TopologicalSpace.SeparableSpace (TestVector K) := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have h := (Set.countable_range (testVectorBasis K)).isSeparable.span (R := ℝ)
  simpa only [(testVectorBasis K).span_eq, Submodule.top_coe] using h

lemma coordinates_linearlyIndependent (K : TestFamily I) :
    LinearIndependent ℝ (coordinateVector K) := by
  have h := (testVectorBasis K).linearIndependent.map'
    (UniformSpace.Completion.toComplL : TestVector K →L[ℝ] TestCompletion K).toLinearMap
    (LinearMap.ker_eq_bot.mpr (UniformSpace.Completion.coe_injective (TestVector K)))
  exact h

lemma testCompletion_infiniteDimensional (K : TestFamily I) [Infinite I] :
    ¬ Module.Finite ℝ (TestCompletion K) := by
  intro h
  have := h
  have := (coordinates_linearlyIndependent K).finite
  exact not_finite I

end TestSeparable

namespace TreeCalculus
open scoped Classical

instance treeCoordinate_infinite (r : Bool) : Infinite (TreeCoordinate r) :=
  Infinite.of_injective (fun n : ℕ => (⟨[n], Or.inr (by simp)⟩ : TreeCoordinate r))
    (fun _ _ h => by simpa using congrArg Subtype.val h)

/-- Uniform quantitative tail estimate at every unit center, including centers
    in the completion. The finite codimensional space may depend on ε. -/
theorem four_completed_tail_bound {r : Bool} {k : QuadraticKind}
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x : TestCompletion (treeTestFamily r k)) (hx : ‖x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim (TestCompletion (treeTestFamily r k)),
      ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1 + t^2/4) - 1 - ε ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 := by
  let K := treeTestFamily r k
  obtain ⟨a, θ, ha, ha1, hθ, hθ1, hsquare, he⟩ := optimal_pair_parameters ht ht1
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (show 0 < ε / 3 by positivity)
  have hw' : ‖(w : TestCompletion K) - x‖ < ε / 3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hw
  let D := initialHull (testVectorEquiv K w)
  let B := coordinateHead r D
  refine ⟨⟨coordinateTail K B, coordinateTail_closed K B, inferInstance⟩, ?_⟩
  intro y hy hy1
  have hp := paired_completed_inequality (initialHull_initial _) (root_mem_initialHull _)
    w y (support_mem_initialHull _) hy ha ha1 hθ hθ1 ht.le hsquare
  have hnw : 1 - ε / 3 ≤ ‖w‖ := by
    have hn := norm_sub_norm_le x (w : TestCompletion K)
    rw [hx, UniformSpace.Completion.norm_coe, norm_sub_rev] at hn
    linarith
  have haw : a - ε / 3 ≤ a * ‖w‖ := by
    have hmul := mul_le_mul_of_nonneg_left hnw ha
    have hc : a * (ε / 3) ≤ ε / 3 := mul_le_of_le_one_left (by positivity) ha1
    nlinarith
  have hby : t * θ / 2 ≤ (t * θ / 2) * ‖y‖ := le_mul_of_one_le_right (by positivity) hy1
  have hperturb := midpoint_center_perturbation x (w : TestCompletion K) y t
  linarith

/-- The common lower bound, with each root convention and quadratic budget kept distinct. -/
theorem four_averaged_modulus (r : Bool) (k : QuadraticKind)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ((Real.sqrt (1 + t^2/4) - 1 : ℝ) : EReal) ≤
      averagedModulus (TestCompletion (treeTestFamily r k)) t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact four_completed_tail_bound ht ht1 x hx hε

end TreeCalculus


end BoundedTreePotentials

end

end OAI
