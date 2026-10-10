import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledObservable
import OAI.Analysis.HardSphere.PathBounds.VisitPacking

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

lemma pathVisitedSites_card_measurable {S : Type*} {n : ℕ} (L : Length)
    (v : S → Torus L) (A : Finset S) (i : Fin n) :
    Measurable (fun ω : ConfigurationPath n L ↦ (pathVisitedSites L v A i ω).card) := by
  classical
  simp only [pathVisitedSites,Finset.card_filter]
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (pathVisitsBall_isClosed L 12 (v a) i).measurableSet
    measurable_const measurable_const

def visitCount {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t : ℝ) (X : Configuration n L) (w : CoordinatePaths n) : ℕ :=
  (pathVisitedSites L (siteCenter L) A i (freeTrajectory n L t w X)).card

lemma visitCount_measurable {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t : ℝ) (X : Configuration n L) : Measurable (visitCount L A i t X) :=
  (pathVisitedSites_card_measurable L (siteCenter L) A i).comp
    ((freeTrajectory_continuous n L t).comp (continuous_id.prodMk continuous_const)).measurable

lemma one_segment_visit_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ} (ht : 0<t) (X : Configuration n L) :
    coordinateWiener n {w | 29^3<visitCount L A i t X w} ≤
      3*M*ENNReal.ofReal (Real.exp (-c/(2*t))) := by
  let R : ℝ := (Real.sqrt (2*t))⁻¹
  have hs : 0<Real.sqrt (2*t) := Real.sqrt_pos.mpr (by positivity)
  have hR : 0≤R := inv_nonneg.mpr hs.le
  have hsub : {w | 29^3<visitCount L A i t X w} ⊆
      ⋃ j : Fin 3, {w | R≤‖w (i,j)‖} := by
    intro w hw
    by_contra hnot
    have hn : ∀ j, ‖w (i,j)‖<R := by simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hnot
    have hb := free_visited_card_le_of_norm L hL A i t w X (fun j ↦ ?_)
    · exact (not_lt_of_ge hb) hw
    · calc
        Real.sqrt (2*t)*‖w (i,j)‖ ≤ Real.sqrt (2*t)*R := mul_le_mul_of_nonneg_left (hn j).le hs.le
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hs)
  have he (j : Fin 3) : coordinateWiener n {w | R≤‖w (i,j)‖} = wiener {w | R≤‖w‖} := by
    exact (measurePreserving_eval (fun _ : Direction n ↦ wiener) (i,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener n (⋃ j : Fin 3, {w | R≤‖w (i,j)‖}) := measure_mono hsub
    _ ≤ ∑' j : Fin 3, coordinateWiener n {w | R≤‖w (i,j)‖} := measure_iUnion_le _
    _ = 3 * wiener {w | R≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*R^2))) := mul_le_mul_right (htail R hR) _
    _ = _ := by
      dsimp [R]
      rw [inv_pow,Real.sq_sqrt (by positivity : 0≤2*t)]
      simp only [div_eq_mul_inv,mul_assoc]

lemma visit_count_split {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {s t : ℝ} (hs : 0<s) (ht : 0<t) (w : CoordinatePaths n) (X : Configuration n L) :
    visitCount L A i (s+t) X w ≤
      visitCount L A i s X (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) +
      visitCount L A i t
        (freeTrajectory n L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X 1)
        (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) := by
  have hle := visited_card_split_le L (siteCenter L) A i (freeTrajectory n L (s+t) w X)
    (splitTime s t hs ht) (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)
  have hp := congrArg Prod.fst (split_fixedTrajectory n L s t hs ht w X)
  have hq := congrArg Prod.snd (split_fixedTrajectory n L s t hs ht w X)
  dsimp only [Prod.fst,Prod.snd] at hp hq
  rw [hp,hq] at hle
  exact hle

attribute [local irreducible] freeTrajectory pathVisitedSites

lemma visit_tail_add {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {s t : ℝ} (hs : 0<s) (ht : 0<t) (a b : ℕ) (p q : ℝ≥0∞)
    (hsbound : ∀ X, coordinateWiener n {w | a<visitCount L A i s X w}≤p)
    (htbound : ∀ X, coordinateWiener n {w | b<visitCount L A i t X w}≤q)
    (X : Configuration n L) :
    coordinateWiener n {w | a+b<visitCount L A i (s+t) X w}≤p+q := by
  let u := splitTime s t hs ht
  let split : CoordinatePaths n → CoordinatePaths n × CoordinatePaths n := fun w ↦
    (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p))
  let E₁ : Set (CoordinatePaths n × CoordinatePaths n) :=
    {p | a<visitCount L A i s X p.1}
  let E₂ : Set (CoordinatePaths n × CoordinatePaths n) :=
    {p | b<visitCount L A i t (freeTrajectory n L s p.1 X 1) p.2}
  have hE₁ : MeasurableSet E₁ := measurableSet_lt measurable_const
    ((visitCount_measurable L A i s X).comp measurable_fst)
  have hE₂ : MeasurableSet E₂ := by
    apply measurableSet_lt measurable_const
    exact (pathVisitedSites_card_measurable L (siteCenter L) A i).comp
      (measurable_snd.comp (split_fixedTrajectory_measurable n L s t X))
  have hsub : {w | a+b<visitCount L A i (s+t) X w} ⊆ split ⁻¹' (E₁∪E₂) := by
    intro w hw
    have hle := visit_count_split L A i hs ht w X
    change a<visitCount L A i s X (split w).1 ∨
      b<visitCount L A i t (freeTrajectory n L s (split w).1 X 1) (split w).2
    change a+b<visitCount L A i (s+t) X w at hw
    change visitCount L A i (s+t) X w ≤ visitCount L A i s X (split w).1 +
      visitCount L A i t (freeTrajectory n L s (split w).1 X 1) (split w).2 at hle
    omega
  have hp₁ : ((coordinateWiener n).prod (coordinateWiener n)) E₁≤p := by
    have he : E₁={w | a<visitCount L A i s X w} ×ˢ Set.univ := by ext v; simp [E₁]
    rw [he,Measure.prod_prod,measure_univ,mul_one]
    exact hsbound X
  have hp₂ : ((coordinateWiener n).prod (coordinateWiener n)) E₂≤q := by
    rw [Measure.prod_apply hE₂]
    calc
      _ ≤ ∫⁻ _w : CoordinatePaths n, q ∂coordinateWiener n := by
        apply lintegral_mono
        intro w
        exact htbound (freeTrajectory n L s w X 1)
      _ = q := by simp
  calc
    _ ≤ coordinateWiener n (split ⁻¹' (E₁∪E₂)) := measure_mono hsub
    _ = ((coordinateWiener n).prod (coordinateWiener n)) (E₁∪E₂) :=
      (coordinateSplit_preserving n u (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)).measure_preimage
        (hE₁.union hE₂).nullMeasurableSet
    _ ≤ ((coordinateWiener n).prod (coordinateWiener n)) E₁ +
        ((coordinateWiener n).prod (coordinateWiener n)) E₂ := measure_union_le _ _
    _ ≤ p+q := add_le_add hp₁ hp₂

lemma n_segment_visit_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ} (ht : 0<t) :
    ∀ k : ℕ, 0<k → ∀ X : Configuration n L,
      coordinateWiener n {w | 29^3*k<visitCount L A i ((k:ℝ)*t) X w} ≤
        (k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c/(2*t)))) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro X
    simpa only [Nat.succ_eq_add_one,Nat.zero_add,Nat.cast_one,one_mul,mul_one] using one_segment_visit_tail htail L hL A i ht X
  | succ k hk ih =>
    intro X
    have hkt : 0<(k:ℝ)*t := mul_pos (by exact_mod_cast hk) ht
    have h := visit_tail_add L A i hkt ht (29^3*k) (29^3)
      ((k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c/(2*t)))))
      (3*M*ENNReal.ofReal (Real.exp (-c/(2*t)))) ih
      (fun X ↦ one_segment_visit_tail htail L hL A i ht X) X
    convert h using 1 <;> push_cast <;> ring_nf

lemma whole_time_visit_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ} (ht : 0<t)
    (k : ℕ) (hk : 0<k) (X : Configuration n L) :
    coordinateWiener n {w | 29^3*k<visitCount L A i t X w} ≤
      (k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(k:ℝ)/(2*t)))) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have h := n_segment_visit_tail htail L hL A i (div_pos ht hk') k hk X
  have he : (k:ℝ)*(t/k)=t := mul_div_cancel₀ t (ne_of_gt hk')
  rw [he] at h
  convert h using 1
  congr 3
  field_simp

end HardSphere.FreeVisits

end
end

end

end OAI
