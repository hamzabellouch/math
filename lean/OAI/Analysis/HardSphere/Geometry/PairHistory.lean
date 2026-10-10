import Mathlib
import OAI.Analysis.HardSphere.Geometry.Sigma

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

def pairHistory (m u : ℕ) (w : PairNoise m) : PairHistory u :=
  (positionHistory m u w.1, positionHistory m u w.2)

def fourHistory (m u : ℕ) (w : FourNoise m) : FourHistory u :=
  (pairHistory m u w.1, pairHistory m u w.2)

def pairDifference (m t : ℕ) (w : PairNoise m) : ℤ := walk m w.1 t - walk m w.2 t

def differenceAt (m t : ℕ) (w : FourNoise m) : ℤ × ℤ :=
  (pairDifference m t w.1, pairDifference m t w.2)

def atomCoefficient (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((6:ℝ)^sigma * (k:ℝ)^(-sigma))

def pairJoint (m u k : ℕ) : PMF (PairHistory u × ℤ) :=
  (pairLaw m).map fun w ↦ (pairHistory m u w, pairDifference m (u+k) w)

lemma pairJoint_eq (m u k : ℕ) :
    pairJoint m u k =
      (independentPair
        ((PMF.uniformOfFintype (TreeNoise m)).map
          (fun w ↦ (positionHistory m u w, walk m w (u+k))))
        ((PMF.uniformOfFintype (TreeNoise m)).map
          (fun w ↦ (positionHistory m u w, walk m w (u+k))))).map
        (fun v ↦ ((v.1.1,v.2.1),v.1.2-v.2.2)) := by
  rw [← independentPair_map, PMF.map_comp]
  rfl

lemma pairJoint_bound (m u k : ℕ) (hk : 0 < k) (ht : u+k ≤ 3^m)
    (H : PairHistory u) (z : ℤ) :
    pairJoint m u k (H,z) ≤ atomCoefficient k * ((pairJoint m u k).map Prod.fst) H := by
  let p := (PMF.uniformOfFintype (TreeNoise m)).map
    (fun w ↦ (positionHistory m u w, walk m w (u+k)))
  have hp : ∀ h x, p (h,x) ≤ atomCoefficient k * (p.map Prod.fst) h := by
    intro h x
    simpa only [p, PMF.map_comp, Function.comp_def, atomCoefficient] using
      position_prediction m u k hk ht h x
  have he : ((pairJoint m u k).map Prod.fst) H =
      (p.map Prod.fst) H.1 * (p.map Prod.fst) H.2 := by
    rw [pairJoint_eq, PMF.map_comp]
    change ((independentPair p p).map
      (fun v ↦ (Prod.fst v.1, Prod.fst v.2))) H = _
    rw [independentPair_map]
    exact independentPair_apply _ _ H.1 H.2
  rw [he, pairJoint_eq]
  exact independent_difference_bound p p (atomCoefficient k) hp H.1 H.2 z

lemma fourJoint_eq (m u k : ℕ) :
    (fourLaw m).map (fun w ↦ (fourHistory m u w, differenceAt m (u+k) w)) =
      independentJoint (pairJoint m u k) (pairJoint m u k) := by
  rw [independentJoint, pairJoint, ← independentPair_map, PMF.map_comp]
  rfl

theorem difference_point_prediction (m u k : ℕ) (hk : 0 < k) (ht : u+k ≤ 3^m)
    (H : FourHistory u) (z : ℤ × ℤ) :
    ((fourLaw m).map (fun w ↦ (fourHistory m u w, differenceAt m (u+k) w))) (H,z) ≤
      (atomCoefficient k)^2 * ((fourLaw m).map (fourHistory m u)) H := by
  have h := independentJoint_bound (pairJoint m u k) (pairJoint m u k)
    (atomCoefficient k) (atomCoefficient k) (pairJoint_bound m u k hk ht)
      (pairJoint_bound m u k hk ht) H.1 H.2 z.1 z.2
  rw [← fourJoint_eq, PMF.map_comp] at h
  simpa only [pow_two, Function.comp_def] using h

def square (l : ℕ) : Finset (ℤ × ℤ) := (Finset.Icc (-(l:ℤ)) l) ×ˢ (Finset.Icc (-(l:ℤ)) l)

lemma square_card (l : ℕ) : (square l).card = (2*l+1)^2 := by
  simp only [square, Finset.card_product, Int.card_Icc]
  have he : ((l:ℤ)+1- -(l:ℤ)).toNat = 2*l+1 := by omega
  rw [he, pow_two]

lemma mem_square (l : ℕ) (z : ℤ × ℤ) : z ∈ square l ↔ |z.1| ≤ l ∧ |z.2| ≤ l := by
  simp only [square, Finset.mem_product, Finset.mem_Icc, abs_le]

theorem difference_square_prediction (m u k : ℕ) (hk : 0 < k) (ht : u+k ≤ 3^m)
    (E : Set (FourHistory u)) (l : ℕ) :
    (fourLaw m).toOuterMeasure
      {w | fourHistory m u w ∈ E ∧ differenceAt m (u+k) w ∈ square l} ≤
      ((2*l+1 : ℕ) : ℝ≥0∞)^2 * (atomCoefficient k)^2 *
        ((fourLaw m).map (fourHistory m u)).toOuterMeasure E := by
  let p := (fourLaw m).map (fun w ↦ (fourHistory m u w, differenceAt m (u+k) w))
  have hp : ∀ H z, p (H,z) ≤ (atomCoefficient k)^2 * (p.map Prod.fst) H := by
    intro H z
    simpa only [p, PMF.map_comp, Function.comp_def] using
      difference_point_prediction m u k hk ht H z
  have h := joint_region_bound p _ hp E (square l)
  simpa only [p, PMF.toOuterMeasure_map_apply, PMF.map_comp, Function.comp_def,
    Set.preimage_ofPred_eq, square_card, Nat.cast_pow] using h

def gapKernel (k : ℕ) : ℝ≥0∞ := if k = 0 then 1 else (atomCoefficient k)^2

def radiusFactor (l : ℕ) : ℝ≥0∞ := ((2*l+1 : ℕ) : ℝ≥0∞)^2

lemma radiusFactor_one_le (l : ℕ) : 1 ≤ radiusFactor l := by
  have h : (1 : ℝ≥0∞) ≤ (2*l+1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2*l+1)
  exact one_le_pow₀ h

def encounterEvent (m : ℕ) {n : ℕ} (t l : Fin n → ℕ) : Set (FourNoise m) :=
  {w | ∀ i, differenceAt m (t i) w ∈ square (l i)}

def encounterMass (m : ℕ) {n : ℕ} (t l : Fin n → ℕ) : ℝ≥0∞ :=
  (fourLaw m).toOuterMeasure (encounterEvent m t l)

lemma pmf_outer_le_one {A : Type*} (p : PMF A) (S : Set A) : p.toOuterMeasure S ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum fun _ ↦ Set.indicator_apply_le fun _ ↦ le_rfl

lemma pmf_outer_univ {A : Type*} (p : PMF A) : p.toOuterMeasure Set.univ = 1 := by
  simp [PMF.toOuterMeasure_apply]

def historyDifference {u : ℕ} (H : FourHistory u) (s : Fin (u+1)) : ℤ × ℤ :=
  (H.1.1 s-H.1.2 s, H.2.1 s-H.2.2 s)

lemma historyDifference_actual (m u : ℕ) (w : FourNoise m) (s : Fin (u+1)) :
    historyDifference (fourHistory m u w) s = differenceAt m s.val w := rfl

lemma encounter_append_bound (m u s : ℕ) (hus : u < s) (hs : s ≤ 3^m)
    {n : ℕ} (t l : Fin n → ℕ) (ht : ∀ i, t i ≤ u) (r : ℕ) :
    encounterMass m (Fin.snoc t s) (Fin.snoc l r) ≤
      radiusFactor r * gapKernel (s-u) * encounterMass m t l := by
  let E : Set (FourHistory u) := {H | ∀ i, historyDifference H ⟨t i, by have := ht i; omega⟩
    ∈ square (l i)}
  have h := difference_square_prediction m u (s-u) (by omega) (by omega) E r
  have hpre : (fourHistory m u) ⁻¹' E = encounterEvent m t l := rfl
  have he : {w | fourHistory m u w ∈ E ∧ differenceAt m (u+(s-u)) w ∈ square r} =
      encounterEvent m (Fin.snoc t s) (Fin.snoc l r) := by
    ext w
    change (∀ i, differenceAt m (t i) w ∈ square (l i)) ∧
      differenceAt m (u+(s-u)) w ∈ square r ↔ _
    rw [Nat.add_sub_of_le hus.le]
    constructor
    · rintro ⟨h,h'⟩ i
      exact Fin.lastCases (by simpa using h') (fun j ↦ by simpa using h j) i
    · intro h
      exact ⟨fun i ↦ by simpa using h i.castSucc, by simpa using h (Fin.last n)⟩
  rw [PMF.toOuterMeasure_map_apply, hpre, he] at h
  simpa only [encounterMass, radiusFactor, gapKernel, ite_eq_right (by omega : s-u ≠ 0)] using h

lemma encounter_singleton_bound (m s r : ℕ) (hs : s ≤ 3^m) :
    encounterMass m (fun _ : Fin 1 ↦ s) (fun _ ↦ r) ≤ radiusFactor r * gapKernel s := by
  by_cases h0 : s = 0
  · subst s
    calc
      _ ≤ 1 := pmf_outer_le_one _ _
      _ ≤ _ := by simpa [gapKernel] using radiusFactor_one_le r
  · have h := difference_square_prediction m 0 s (by omega) (by simpa using hs)
      Set.univ r
    rw [pmf_outer_univ] at h
    simpa [encounterMass, encounterEvent, radiusFactor, gapKernel, h0] using h

theorem encounterMass_le_gap_prod (m n : ℕ) (t l : Fin n → ℕ)
    (ht : StrictMono t) (hT : ∀ i, t i ≤ 3^m) :
    encounterMass m t l ≤ ∏ i, radiusFactor (l i) * gapKernel (timeGaps t i) := by
  induction n with
  | zero =>
    calc
      encounterMass m t l = 1 := by
        rw [encounterMass, show encounterEvent m t l = Set.univ by ext w; simp [encounterEvent],
          pmf_outer_univ]
      _ ≤ ∏ i, radiusFactor (l i) * gapKernel (timeGaps t i) := by rw [Fin.prod_univ_zero]
  | succ n ih =>
    cases n with
    | zero =>
      have h := encounter_singleton_bound m (t 0) (l 0) (hT 0)
      have he : (fun _ : Fin 1 ↦ t 0) = t := by
        funext i; exact congrArg t (Fin.ext (by omega))
      have hl : (fun _ : Fin 1 ↦ l 0) = l := by
        funext i; exact congrArg l (Fin.ext (by omega))
      rw [he, hl] at h
      rw [Fin.prod_univ_one, timeGaps_zero]
      exact h
    | succ n =>
      have hin : StrictMono (Fin.init t) := ht.comp (Fin.strictMono_castSucc)
      have hb := ih (Fin.init t) (Fin.init l) hin (fun i ↦ hT i.castSucc)
      have hlt : t (Fin.last n).castSucc < t (Fin.last (n+1)) :=
        ht (by simp)
      have ha := encounter_append_bound m (t (Fin.last n).castSucc) (t (Fin.last (n+1)))
        hlt (hT _) (Fin.init t) (Fin.init l)
        (fun i ↦ ht.monotone (by exact_mod_cast Fin.le_last i)) (l (Fin.last (n+1)))
      rw [Fin.snoc_init_self, Fin.snoc_init_self] at ha
      refine ha.trans ?_
      rw [Fin.prod_univ_castSucc]
      calc
        _ ≤ radiusFactor (l (Fin.last (n+1))) *
            gapKernel (t (Fin.last (n+1))-t (Fin.last n).castSucc) *
            ∏ i, radiusFactor (Fin.init l i) * gapKernel (timeGaps (Fin.init t) i) :=
          mul_le_mul' le_rfl hb
        _ = _ := by
          simp_rw [timeGaps_castSucc]
          change _ = _ * (radiusFactor (l (Fin.last (n+1))) *
            gapKernel (t (Fin.last (n+1))-t (Fin.last n).castSucc))
          exact mul_comm _ _

lemma atomCoefficient_sq (k : ℕ) :
    (atomCoefficient k)^2 = ENNReal.ofReal
      (((6:ℝ)^sigma)^2 * (k:ℝ)^(-2*sigma)) := by
  rw [atomCoefficient, ← ENNReal.ofReal_pow (by positivity), mul_pow]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
  congr 1
  ring

lemma gapKernel_sum_ne_top : (∑' k, gapKernel k) ≠ ∞ := by
  have hs : Summable (fun k : ℕ ↦ ((6:ℝ)^sigma)^2 * (k:ℝ)^(-2*sigma)) :=
    (Real.summable_nat_rpow.mpr (by linarith [sigma_gt_half])).mul_left _
  have he : (∑' k, (atomCoefficient k)^2) =
      ENNReal.ofReal (∑' k : ℕ, ((6:ℝ)^sigma)^2 * (k:ℝ)^(-2*sigma)) := by
    simp_rw [atomCoefficient_sq]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs).symm
  have hb : (∑' k, gapKernel k) ≤ 1 + ∑' k, (atomCoefficient k)^2 := by
    calc
      _ ≤ (∑' k : ℕ, ((if k = 0 then 1 else 0) + (atomCoefficient k)^2)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases h : k = 0 <;> simp [gapKernel, h]
      _ = _ := by rw [ENNReal.tsum_add]; simp
  rw [he] at hb
  exact ne_top_of_le_ne_top (by finiteness) hb

lemma gapKernel_sum_one_le : (1 : ℝ≥0∞) ≤ ∑' k, gapKernel k := by
  simpa only [gapKernel, ↓reduceIte] using ENNReal.le_tsum (f := gapKernel) 0

def orderedEncounterConstant : ℝ := (4 * ∑' k, gapKernel k).toReal

lemma orderedEncounterConstant_pos : 0 < orderedEncounterConstant := by
  apply ENNReal.toReal_pos
  · exact mul_ne_zero (by norm_num) (ne_of_gt (lt_of_lt_of_le (by norm_num) gapKernel_sum_one_le))
  · exact ENNReal.mul_ne_top (by norm_num) gapKernel_sum_ne_top

lemma orderedEncounterConstant_cast : ENNReal.ofReal orderedEncounterConstant =
    4 * ∑' k, gapKernel k :=
  ENNReal.ofReal_toReal (ENNReal.mul_ne_top (by norm_num) gapKernel_sum_ne_top)

lemma radiusFactor_le (l : ℕ) : radiusFactor l ≤ 4 * ((1+l : ℕ) : ℝ≥0∞)^2 := by
  unfold radiusFactor
  have h : (2*l+1)^2 ≤ 4*(1+l)^2 := by
    calc
      (2*l+1)^2 ≤ (2*(1+l))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  exact_mod_cast h

theorem ordered_encounter_sum (m T n : ℕ) (hT : T ≤ 3^m) (l : Fin n → ℕ) :
    (∑' t : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}, encounterMass m t.val l) ≤
      ∏ i, ENNReal.ofReal orderedEncounterConstant * ((1+l i : ℕ) : ℝ≥0∞)^2 := by
  calc
    _ ≤ ∑' t : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T},
        ∏ i, radiusFactor (l i) * gapKernel (timeGaps t.val i) := by
      exact ENNReal.tsum_le_tsum fun t ↦ encounterMass_le_gap_prod m n t.val l
        t.property.1 (fun i ↦ (t.property.2 i).trans hT)
    _ = (∏ i, radiusFactor (l i)) *
        ∑' t : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T},
          ∏ i, gapKernel (timeGaps t.val i) := by
      simp_rw [Finset.prod_mul_distrib, ENNReal.tsum_mul_left]
    _ ≤ (∏ i, radiusFactor (l i)) * (∑' k, gapKernel k)^n :=
      mul_le_mul' le_rfl (ordered_gap_sum_bound T n gapKernel)
    _ = ∏ i, radiusFactor (l i) * (∑' k, gapKernel k) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ i, ENNReal.ofReal orderedEncounterConstant * ((1+l i : ℕ) : ℝ≥0∞)^2 := by
      apply Finset.prod_le_prod fun i _ ↦ ?_
      rw [orderedEncounterConstant_cast]
      exact (mul_le_mul' (radiusFactor_le (l i)) le_rfl).trans_eq (by ring)

def radiusEnvelope (a : ℕ → ℝ≥0∞) (z : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' l, if z ∈ square l then a l else 0

lemma prod_ite_all {n : ℕ} (P : Fin n → Prop) (v : Fin n → ℝ≥0∞) :
    (∏ i, if P i then v i else 0) = if ∀ i, P i then ∏ i, v i else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma radiusEnvelope_prod (m : ℕ) {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (w : FourNoise m) :
    (∏ i, radiusEnvelope a (differenceAt m (t i) w)) =
      ∑' l : Fin n → ℕ, if w ∈ encounterEvent m t l then ∏ i, a (l i) else 0 := by
  unfold radiusEnvelope
  rw [← tsum_vector_prod]
  apply tsum_congr
  intro l
  by_cases h : w ∈ encounterEvent m t l
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    exact ite_eq_left (h i)
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, differenceAt m (t i) w ∈ square (l i) := h
    obtain ⟨i,hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def weightedEncounterMass (m : ℕ) {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' w, fourLaw m w * ∏ i, radiusEnvelope a (differenceAt m (t i) w)

lemma weightedEncounterMass_eq (m : ℕ) {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞) :
    weightedEncounterMass m t a =
      ∑' l : Fin n → ℕ, (∏ i, a (l i)) * encounterMass m t l := by
  unfold weightedEncounterMass
  calc
    _ = ∑' w, ∑' l : Fin n → ℕ, fourLaw m w *
        (if w ∈ encounterEvent m t l then ∏ i, a (l i) else 0) := by
      apply tsum_congr
      intro w
      rw [radiusEnvelope_prod, ENNReal.tsum_mul_left]
    _ = ∑' l : Fin n → ℕ, ∑' w, fourLaw m w *
        (if w ∈ encounterEvent m t l then ∏ i, a (l i) else 0) := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro l
      rw [encounterMass, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro w
      by_cases h : w ∈ encounterEvent m t l <;> simp [Set.indicator, h, mul_comm]

def radiusActivity (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal orderedEncounterConstant * ∑' l, a l * ((1+l : ℕ) : ℝ≥0∞)^2

lemma weighted_ordered_sum_bound (m T n : ℕ) (hT : T ≤ 3^m) (a : ℕ → ℝ≥0∞) :
    (∑' t : BoundedTimes T n, weightedEncounterMass m t.val a) ≤ (radiusActivity a)^n := by
  simp_rw [weightedEncounterMass_eq]
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' l : Fin n → ℕ, (∏ i, a (l i)) *
        ∑' t : BoundedTimes T n, encounterMass m t.val l := by
      apply tsum_congr
      intro l
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' l : Fin n → ℕ, (∏ i, a (l i)) *
        ∏ i, ENNReal.ofReal orderedEncounterConstant * ((1+l i : ℕ) : ℝ≥0∞)^2 := by
      exact ENNReal.tsum_le_tsum fun l ↦ mul_le_mul' le_rfl (ordered_encounter_sum m T n hT l)
    _ = ∑' l : Fin n → ℕ, ∏ i,
        ENNReal.ofReal orderedEncounterConstant * (a (l i) * ((1+l i : ℕ) : ℝ≥0∞)^2) := by
      apply tsum_congr
      intro l
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [tsum_vector_prod (fun (_ : Fin n) k ↦
        ENNReal.ofReal orderedEncounterConstant * (a k * ((1+k : ℕ) : ℝ≥0∞)^2))]
      simp only [ENNReal.tsum_mul_left, radiusActivity, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

lemma ordered_product_bound_envelope (m T : ℕ) (hT : T ≤ 3^m) (a : ℕ → ℝ≥0∞) :
    (∑' w, fourLaw m w * ∏ u ∈ Finset.range (T+1),
        (1+radiusEnvelope a (differenceAt m u w))) ≤ (1-radiusActivity a)⁻¹ := by
  calc
    _ ≤ ∑' w, fourLaw m w * ∑' n, ∑' t : BoundedTimes T n,
        ∏ i, radiusEnvelope a (differenceAt m (t.val i) w) := by
      exact ENNReal.tsum_le_tsum fun w ↦ mul_le_mul' le_rfl
        (prod_one_add_le_ordered_series T (fun u ↦ radiusEnvelope a (differenceAt m u w)))
    _ = ∑' n, ∑' t : BoundedTimes T n, weightedEncounterMass m t.val a := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro n
      rw [ENNReal.tsum_comm]
      rfl
    _ ≤ ∑' n, (radiusActivity a)^n :=
      ENNReal.tsum_le_tsum fun n ↦ weighted_ordered_sum_bound m T n hT a
    _ = _ := ENNReal.tsum_geometric _

theorem ordered_product_bound (m T : ℕ) (hT : T ≤ 3^m) (a : ℕ → ℝ≥0∞)
    (f : ℤ × ℤ → ℝ≥0∞) (hf : ∀ z, f z ≤ radiusEnvelope a z)
    (ha : radiusActivity a < 1) :
    (∑' w, fourLaw m w * ∏ u ∈ Finset.range (T+1), (1+f (differenceAt m u w))) ≤
        (1-radiusActivity a)⁻¹ ∧ (1-radiusActivity a)⁻¹ < ∞ := by
  constructor
  · refine (ENNReal.tsum_le_tsum fun w ↦ mul_le_mul' le_rfl ?_).trans
      (ordered_product_bound_envelope m T hT a)
    exact Finset.prod_le_prod fun u _ ↦ add_le_add_right (hf _) 1
  · exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr ha)

lemma exp_sub_one_le_slope {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) :
    Real.exp x - 1 ≤ Real.exp B * x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have he : Real.exp x ≤ Real.exp B := Real.exp_le_exp.mpr hB
  nlinarith [mul_le_mul_of_nonneg_right he hx]

lemma radiusEnvelope_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (z : ℤ × ℤ) :
    radiusEnvelope (fun l ↦ c*a l) z = c*radiusEnvelope a z := by
  unfold radiusEnvelope
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  by_cases h : z ∈ square l <;> simp [h]

end HardSphere.Lattice
end

end OAI
