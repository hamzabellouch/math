import Mathlib
import OAI.Probability.Ballisticity.Estimates.ConfinementTemplates

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def StripExcursion {d : ℕ} (ℓ : Vector d) (H R : ℝ) : Set (Path d) :=
  {X | ∃ n, X ∈ BoundedHeightPrefix ℓ H n ∧ ∃ u : Direction d, R < signedCoordinate u (X n)}

lemma measurableSet_stripExcursion {d : ℕ} (ℓ : Vector d) (H R : ℝ) :
    MeasurableSet (StripExcursion ℓ H R) := by
  simp only [StripExcursion, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  refine (measurableSet_boundedHeightPrefix ℓ H n).inter (MeasurableSet.iUnion fun u => ?_)
  exact measurableSet_lt measurable_const ((measurable_of_countable (signedCoordinate u)).comp (measurable_pi_apply n))

lemma stripExcursion_subset_ratio {d : ℕ} (ℓ : Vector d) (X : Path d)
    (h0 : X 0 = 0) (hNN : ∀ n, ∃ e : Direction d, X (n+1) = X n+step e)
    (b a D : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (N : ℕ) :
    X ∈ StripExcursion ℓ N (a*(2*b+2+D)*(N+1)^2) →
    X ∈ ⋃ u : Direction d, RatioHit ℓ u b a N (1+N*(2*b+1+D)) := by
  rintro ⟨n,hn,u,hu⟩
  refine Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨n,⟨⟨h0,fun j _ => hNN j⟩,hn⟩,?_⟩⟩
  have hm := runningHeight_le ℓ X n N (Nat.cast_nonneg _) (fun j hj => (hn j hj).2)
  have hm0 := runningHeight_nonneg ℓ X n
  have ht : 0 ≤ 1+(N:ℝ)*(2*b+1+D) := by positivity
  have hfactor : 1+(N:ℝ)*(2*b+1+D) ≤ (2*b+2+D)*(N+1) := by nlinarith
  have hbnd : (1+(N:ℝ)*(2*b+1+D))*(a*(1+runningHeight ℓ X n)) ≤
      a*(2*b+2+D)*(N+1)^2 := by
    calc
      _ ≤ (1+(N:ℝ)*(2*b+1+D))*(a*(1+N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) ht
      _ ≤ ((2*b+2+D)*(N+1))*(a*(1+N)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring
  change _ < tiltedCoordinate ℓ u b a (X n)/(a*(1+runningHeight ℓ X n))
  apply (lt_div_iff₀ (mul_pos (by linarith) (by linarith))).mpr
  have hz := mul_nonneg (mul_nonneg hb (show 0 ≤ a by linarith)) (hn n le_rfl).1
  dsimp only [tiltedCoordinate]
  linarith

theorem spatial_confinement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ε ≤ 1 ∧ ∀ N : ℕ,
      (annealedLaw ν).real (StripExcursion (realPosition (step e)) N (C*(N+1)^2)) ≤
        (2*d : ℕ)*(1-ε)^N := by
  obtain ⟨b,a,D,ε,hb,ha,hD,hε,hε1,hA⟩ := strip_templates ν hue e htrans
  refine ⟨a*(2*b+2+D),ε,mul_pos (by linarith) (by linarith),hε,hε1,?_⟩
  intro N
  obtain ⟨A,hAm,hAp,hAc⟩ := hA N
  apply le_trans ?_ (ratio_hit_union_bound ν (realPosition (step e))
    (unit_direction_coordinate_bound _ (signed_direction_unit e)) b a D N ε hb ha hD hε.le hε1 A hAm hAp hAc N)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [annealed_initial ν,annealed_nearest_neighbor ν] with X h0 hNN
  exact stripExcursion_subset_ratio _ X h0 hNN b a D hb ha hD N

end DirectionalTransience

end

end OAI
