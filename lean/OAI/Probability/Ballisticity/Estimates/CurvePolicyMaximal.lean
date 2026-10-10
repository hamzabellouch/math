import Mathlib
import OAI.Probability.Ballisticity.Walk.CurvePolicyKernel
import OAI.Probability.Ballisticity.Estimates.AeMaximalSquare

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma curvePolicy_average_lateral_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    ∀ᵐ u ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure,
      |signedCoordinate f u-b H| ≤ B := by
  rw [curvePolicy_average_toMeasure,ae_iff,Measure.bind_apply (Set.to_countable _ |>.measurableSet)
    ((curvePolicy_rows _ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Eventually.of_forall (fun ω => ae_iff.mp (curvePolicy_lateral_bound e f 0 b hB hH E δ α dummy hd ω))

local instance CurvePolicyMaximalMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance CurvePolicyMaximalSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_event_iid {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy = H) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) (S : Set (List (Lattice d))) :
    (∫⁻ ω, (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure S ∂environmentLaw ν) =
      (iidListPMF (curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy) n).toMeasure S := by
  have he (ω : Environment d) :
      finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n =
      finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x n := by
    ext w
    exact curvePolicy_alignment e f b B H E hδ hα dummy hd ω i x hx n w
  simp_rw [he]
  apply finitePolicyPMF_annealed_event ν _ (blockRows e H) (blockRows_pairwise e H)
    (alignedCurvePolicy_rows e f b B hH E hδ hα dummy)
  intro j y u
  exact curvePolicyPMF_average ν (realPosition (step e)) f _ b B hH E hδ hα dummy u

lemma curvePolicy_maximal_tail {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy = H)
    (hdb : signedCoordinate f dummy = b H) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    let p := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
    let c := ∫ u, signedCoordinate f u ∂p.toMeasure
    (∫⁻ ω, (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure {w | r ≤ listCenteredMax (signedCoordinate f) c w} ∂environmentLaw ν).toReal ≤
      (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂p.toMeasure))/r^2 := by
  dsimp only
  rw [curvePolicy_event_iid ν e f b B hH E hδ hα dummy hd i x hx n]
  exact iidList_max_tail _ _ (b H) hB
    (curvePolicy_average_lateral_bound ν e f b hB hH E hδ hα dummy hdb) n hr

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma policySafe_iff {G : Type*} [AddMonoid G] (Good : G → Prop) (x : G) (w : List G) :
    policySafe Good x w ↔ ∀ j < w.length, Good (x+(w.take j).sum) := by
  induction w generalizing x with
  | nil => simp [policySafe]
  | cons u w ih =>
    rw [policySafe,ih]
    constructor
    · rintro ⟨hx,hw⟩ j hj
      cases j with
      | zero => simpa using hx
      | succ j => simpa only [List.take_succ_cons,List.sum_cons,← add_assoc] using (hw j (by simpa using hj))
    · intro h
      refine ⟨by simpa using h 0 (by simp),?_⟩
      intro j hj
      simpa only [List.take_succ_cons,List.sum_cons,← add_assoc] using h (j+1) (by simpa using hj)

lemma curvePolicy_word_height {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (hd : signedHeight e dummy = H) (ω : Environment d) (i : ℕ) (x : Lattice d)
    (n : ℕ) (w : List (Lattice d))
    (hw : finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n w ≠ 0) : ∀ u ∈ w, signedHeight e u=H := by
  induction n generalizing i x w with
  | zero =>
    have he : w=[] := by
      by_contra he
      exact hw (finitePolicyPMF_length _ ω i x 0 w (by simpa using he))
    simp [he]
  | succ n ih =>
    cases w with
    | nil => simp
    | cons u w =>
      rw [finitePolicyPMF_cons] at hw
      have hu := (mul_ne_zero_iff.mp hw).1
      have ht := ih (i+1) (x+u) w (mul_ne_zero_iff.mp hw).2
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · by_contra hh
        exact hu (curvePolicyPMF_zero e f x b B H E hδ hα dummy hd ω v hh)
      · exact ht v hv

lemma signedHeight_sum_of_constant {d : ℕ} (e : Direction d) (H : ℤ) (w : List (Lattice d))
    (hw : ∀ u ∈ w, signedHeight e u=H) : signedHeight e w.sum=(w.length:ℤ)*H := by
  induction w with
  | nil => simp [signedHeight]
  | cons u w ih =>
    rw [List.sum_cons,signedHeight_add,hw u (by simp),ih (fun v hv => hw v (by simp [hv]))]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finitePolicyPMF_take {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (m n : ℕ) :
    (finitePolicyPMF Q ω i x (m+n)).map (List.take m) = finitePolicyPMF Q ω i x m := by
  induction m generalizing i x with
  | zero =>
    rw [Nat.zero_add]
    have he : List.take 0 = Function.const (List G) [] := by funext w; simp
    rw [he,PMF.map_const]
    rfl
  | succ m ih =>
    rw [show m+1+n = (m+n)+1 by omega]
    rw [finitePolicyPMF,PMF.map_bind,finitePolicyPMF]
    congr 1
    funext u
    rw [PMF.map_comp]
    have he : List.take (m+1) ∘ List.cons u = List.cons u ∘ List.take m := by
      funext w; simp
    rw [he,← PMF.map_comp,ih]

def priorRows {d : ℕ} (S : ℕ → Set (Lattice d)) (t : ℕ) : Set (Lattice d) :=
  ⋃ j ∈ Set.Iio t, S j

lemma finitePolicyPMF_prior_local {d : ℕ} {G : Type*} [Add G]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (i : ℕ) (x : G) (n t : ℕ) (hnt : i+n ≤ t) (w : List G) :
    @Measurable _ _ (rowSigma (priorRows S t)) _ (fun ω => finitePolicyPMF Q ω i x n w) := by
  induction n generalizing i x w with
  | zero => exact measurable_const
  | succ n ih =>
    cases w with
    | nil => simp only [finitePolicyPMF_nil_succ]; exact measurable_const
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      have hs : S i ⊆ priorRows S t := by
        intro y hy
        exact Set.mem_iUnion₂.mpr ⟨i,(show i<t by omega),hy⟩
      exact ((hQ i x u).mono (rowSigma_mono hs) le_rfl).mul
        (ih (i+1) (x+u) (by omega) w)

lemma disjoint_prior_rows {d : ℕ} (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (t : ℕ) :
    Disjoint (priorRows S t) (S t) := by
  simp only [priorRows,Set.disjoint_iUnion_left]
  intro j hj
  exact hS (ne_of_lt hj)

lemma finitePolicyPMF_fresh_test {d : ℕ} {G : Type*} [AddMonoid G] [Countable G]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (B : Environment d → G → ℝ≥0∞) (i n : ℕ) (x : G)
    (hB : ∀ y, @Measurable _ _ (rowSigma (S (i+n))) _ (fun ω => B ω y))
    (b : ℝ≥0∞) (havg : ∀ y, (∫⁻ ω, B ω y ∂environmentLaw ν) = b) :
    (∫⁻ ω, ∑' w : List G, finitePolicyPMF Q ω i x n w * B ω (x+w.sum) ∂environmentLaw ν) = b := by
  have hp (w : List G) := finitePolicyPMF_prior_local Q S hQ i x n (i+n) le_rfl w
  rw [lintegral_tsum]
  · have he (w : List G) :
        (∫⁻ ω, finitePolicyPMF Q ω i x n w * B ω (x+w.sum) ∂environmentLaw ν) =
          (∫⁻ ω, finitePolicyPMF Q ω i x n w ∂environmentLaw ν)*b := by
      have hind := indepFun_of_disjoint_rows ν (disjoint_prior_rows S hS (i+n))
        (fun ω => finitePolicyPMF Q ω i x n w) (fun ω => B ω (x+w.sum)) (hp w) (hB _)
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        ((hp w).mono (rowSigma_le _) le_rfl).aemeasurable
        ((hB _).mono (rowSigma_le _) le_rfl).aemeasurable hind,havg]
    simp_rw [he]
    rw [ENNReal.tsum_mul_right,← lintegral_tsum]
    · simp only [PMF.tsum_coe,lintegral_one,measure_univ,one_mul]
    · intro w; exact ((hp w).mono (rowSigma_le _) le_rfl).aemeasurable
  · intro w
    exact (((hp w).mono (rowSigma_le _) le_rfl).mul
      ((hB _).mono (rowSigma_le _) le_rfl)).aemeasurable

end DirectionalTransience

end

end

end OAI
