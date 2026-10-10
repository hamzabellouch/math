import OAI.Geometry.PinnedDistances.UnboundedContradiction

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded

/-- Simultaneous selection from a normalized weighted family. In particular,
there is no required lower bound on a nonzero archimedean-place weight. -/
lemma weighted_select {J : Type u1} [Fintype J] (w T V : J → ℝ) (C ε : ℝ)
    (hw : ∀ j, 0 < w j) (hW : ∑ j, w j = 1)
    (hT : ∀ j, 0 ≤ T j) (hV : ∀ j, 0 ≤ V j)
    (hC : 0 ≤ C) (hε : 0 < ε)
    (hTC : ∑ j, w j * T j ≤ C) (hVE : ∑ j, w j * V j ≤ ε) :
    ∃ j, T j ≤ 2*C+1 ∧ V j ≤ 2*ε := by
  have hne : (Finset.univ : Finset J).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hW
    norm_num at hW
  have hs : ∑ j, w j*(T j+(C+1)/ε*V j) ≤ ∑ j, w j*(2*C+1) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hW, one_mul]
    have hv := mul_le_mul_of_nonneg_left hVE (show 0≤(C+1)/ε by positivity)
    have he : (∑ j, w j*((C+1)/ε*V j)) = (C+1)/ε*(∑ j,w j*V j) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [he]
    have he' : (C+1)/ε*ε=C+1 := by field_simp
    rw [he'] at hv
    linarith
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hne hs
  have hj' : T j+(C+1)/ε*V j ≤ 2*C+1 := (mul_le_mul_iff_right₀ (hw j)).mp hj
  refine ⟨j, (le_add_of_nonneg_right (mul_nonneg (by positivity) (hV j))).trans hj', ?_⟩
  have hv' : (C+1)/ε*V j ≤ 2*C+1 := by linarith [hT j]
  have he : (C+1)/ε*(2*ε) = 2*(C+1) := by field_simp
  by_contra h
  have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) (show 0 < (C+1)/ε by positivity)
  rw [he] at hh
  linarith

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
lemma massEval_nonneg (q : Finset P → ℝ) (hq : ∀ C, 0≤q C) (d d' : Depth P) :
    0 ≤ massEval q d d' := by
  exact add_nonneg (Finset.sum_nonneg (fun C _ => mul_nonneg (d.mass_nonneg C) (hq C)))
    (Finset.sum_nonneg (fun C _ => mul_nonneg (d'.mass_nonneg C) (hq C)))

omit Z₁ Z₂ h₁ h₂ in
def scaleEval (d d' : Depth P) : ℝ :=
  massEval (pairCell Finset.univ) d d' + potentialEval (prob Finset.univ) d d'

omit Z₁ Z₂ h₁ h₂ in
lemma scaleEval_nonneg (d d' : Depth P) : 0 ≤ scaleEval d d' := by
  apply add_nonneg (massEval_nonneg _ (fun C => pairCell_nonneg _ _) _ _)
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (add_nonneg (d.potential_nonneg x) (d'.potential_nonneg x))
  simp only [prob,Finset.mem_univ,ite_true]; positivity

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_scaleEval (hn : 2≤Fintype.card P) :
    AverageIntegrable Z₁ Z₂ (scaleEval (P:=P)) := by
  intro v
  exact (integrable_massEval Z₁ Z₂ h₁ h₂ hn _ v).add
    (integrable_potentialEval Z₁ Z₂ h₁ h₂ hn _ v)

lemma average_scaleEval (hn : 2≤Fintype.card P) :
    average Z₁ Z₂ h₁ h₂ scaleEval = overlapScale Z₁ Z₂ h₁ h₂ + potentialScale Z₁ Z₂ h₁ h₂ := by
  unfold scaleEval
  rw [average_add Z₁ Z₂ h₁ h₂
    (integrable_massEval Z₁ Z₂ h₁ h₂ hn _) (integrable_potentialEval Z₁ Z₂ h₁ h₂ hn _),
    average_massEval Z₁ Z₂ h₁ h₂ hn,average_potentialEval Z₁ Z₂ h₁ h₂ hn]
  rfl

def archMean (f : Depth P → Depth P → ℝ) (v : InfinitePlace K) : ℝ :=
  ∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂ Grid.fullLaw

omit [Fintype P] [NumberField K] in
lemma archMean_nonneg (f : Depth P → Depth P → ℝ) (hf : ∀ d d', 0≤f d d')
    (v : InfinitePlace K) : 0≤archMean Z₁ Z₂ f v := integral_nonneg (fun _ => hf _ _)

lemma archMean_le_average (f : Depth P → Depth P → ℝ) (hf : ∀ d d', 0≤f d d') :
    (∑ v, Arithmetic.archWeight v * archMean Z₁ Z₂ f v) ≤ average Z₁ Z₂ h₁ h₂ f := by
  apply le_add_of_nonneg_right
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => hf _ _))

omit Z₁ Z₂ h₁ h₂ in
lemma archWeight_pos (v : InfinitePlace K) : 0<Arithmetic.archWeight v := by
  unfold Arithmetic.archWeight
  apply div_pos
  · exact_mod_cast (InfinitePlace.mult_pos (w := v))
  · exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)

/-- Both the local scale and any nonnegative sum of variance cells are
controlled at one genuine complex embedding. -/
lemma select_arch (hn : 2≤Fintype.card P) (q : Finset P → ℝ) (hq : ∀ C, 0≤q C)
    (C ε : ℝ) (hC : 0≤C) (hε : 0<ε)
    (hscale : overlapScale Z₁ Z₂ h₁ h₂ + potentialScale Z₁ Z₂ h₁ h₂ ≤ C)
    (hvar : weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q ≤ ε) :
    ∃ v : InfinitePlace K,
      archMean Z₁ Z₂ scaleEval v ≤ 2*C+1 ∧ archMean Z₁ Z₂ (massEval q) v ≤ 2*ε := by
  apply weighted_select Arithmetic.archWeight _ _ C ε archWeight_pos Arithmetic.sum_archWeight
    (archMean_nonneg Z₁ Z₂ _ scaleEval_nonneg)
    (archMean_nonneg Z₁ Z₂ _ (massEval_nonneg q hq)) hC hε
  · exact (archMean_le_average Z₁ Z₂ h₁ h₂ _ scaleEval_nonneg).trans
      (by rw [average_scaleEval Z₁ Z₂ h₁ h₂ hn]; exact hscale)
  · exact (archMean_le_average Z₁ Z₂ h₁ h₂ _ (massEval_nonneg q hq)).trans
      (by rw [average_massEval Z₁ Z₂ h₁ h₂ hn]; exact hvar)

end WeakPinned.Bounded

end
end

end OAI
