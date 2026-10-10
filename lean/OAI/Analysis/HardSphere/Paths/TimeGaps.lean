import Mathlib
import OAI.Analysis.HardSphere.Paths.Index

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma weighted_gap_concentration (t k : ℕ) (hk : 0 < k)
    (y : Fin 2 → ℝ) (R : ℝ) (hR : 0 ≤ R) (H : Noise → ℝ≥0∞)
    (hH : Measurable H) (hinv : PastInvariant t H) :
    (∫⁻ ω, H ω * nearTest (t+k) y R ω ∂law) ≤
      ENNReal.ofReal ((16*R^2/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) *
        ∫⁻ ω, H ω ∂law := by
  obtain ⟨ℓ,b,ht,hf,hkℓ⟩ := exists_fresh_block t k hk
  refine (fresh_weighted_pair ℓ b (t+k) hf y R H hH
    (fun j ↦ hinv j ℓ b ht)).trans ?_
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_pow (div_nonneg hR (freshScale_pos ℓ).le)]
  exact ENNReal.ofReal_le_ofReal (freshScale_gap_bound k ℓ hk hkℓ R)

def timeGaps : {n : ℕ} → (Fin n → ℕ) → Fin n → ℕ
  | 0, _ => Fin.elim0
  | _+1, t => Fin.cases (t 0) (fun i ↦ t i.succ - t i.castSucc)

@[simp] lemma timeGaps_zero {n : ℕ} (t : Fin (n+1) → ℕ) : timeGaps t 0 = t 0 := rfl
@[simp] lemma timeGaps_succ {n : ℕ} (t : Fin (n+1) → ℕ) (i : Fin n) :
    timeGaps t i.succ = t i.succ - t i.castSucc := rfl

lemma timeGaps_castSucc {n : ℕ} (t : Fin (n+1) → ℕ) (i : Fin n) :
    timeGaps t i.castSucc = timeGaps (Fin.init t) i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact Fin.cases rfl (fun _ ↦ rfl) i

lemma timeGaps_injective {n : ℕ} :
    Function.Injective (fun t : {t : Fin n → ℕ // Monotone t} ↦ timeGaps t.val) := by
  intro t s h
  apply Subtype.ext
  funext i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.induction ?_ (fun j ih ↦ ?_) i
    · exact congrFun h 0
    · have he := congrFun h j.succ
      simp only [timeGaps_succ] at he
      have ht := t.property (Fin.castSucc_le_succ j)
      have hs := s.property (Fin.castSucc_le_succ j)
      omega

def splitVectorEquiv (n : ℕ) (A : Type*) : (Fin (n+1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i ↦ f i.succ)
  invFun v := Fin.cases v.1 v.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv v := rfl

lemma tsum_vector_prod {n : ℕ} (f : Fin n → ℕ → ℝ≥0∞) :
    (∑' g : Fin n → ℕ, ∏ i, f i (g i)) = ∏ i, ∑' k, f i k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (splitVectorEquiv n ℕ).symm.tsum_eq]
    change (∑' v : ℕ × (Fin n → ℕ), ∏ i, f i (Fin.cases v.1 v.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right]

lemma ordered_gap_sum_bound (T n : ℕ) (b : ℕ → ℝ≥0∞) :
    (∑' t : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}, ∏ i, b (timeGaps t.val i)) ≤
      (∑' k, b k)^n := by
  let g : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T} → (Fin n → ℕ) :=
    fun t ↦ timeGaps t.val
  have hg : Function.Injective g := by
    intro t s he
    have hv := timeGaps_injective (a₁ := ⟨t.val,t.property.1.monotone⟩)
      (a₂ := ⟨s.val,s.property.1.monotone⟩) he
    exact Subtype.ext (congrArg (fun q : {f : Fin n → ℕ // Monotone f} ↦ q.val) hv)
  have h := ENNReal.tsum_comp_le_tsum_of_injective hg (fun v : Fin n → ℕ ↦ ∏ i, b (v i))
  simpa only [g, tsum_vector_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

abbrev BoundedTimes (T n : ℕ) := {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}
abbrev TimeSubset (T : ℕ) := {s : Finset ℕ // s ∈ (Finset.range (T+1)).powerset}

def encodeTimeSubset (T : ℕ) (s : TimeSubset T) : Σ n, BoundedTimes T n :=
  ⟨s.val.card, ⟨s.val.orderEmbOfFin rfl, (s.val.orderEmbOfFin rfl).strictMono,
    fun i ↦ by
      have h := (Finset.mem_powerset.mp s.property) (s.val.orderEmbOfFin_mem rfl i)
      exact Nat.le_of_lt_succ (Finset.mem_range.mp h)⟩⟩

def decodeTimes {T : ℕ} (v : Σ n, BoundedTimes T n) : Finset ℕ :=
  Finset.univ.image v.2.val

lemma decode_encode (T : ℕ) (s : TimeSubset T) : decodeTimes (encodeTimeSubset T s) = s.val := by
  exact s.val.image_orderEmbOfFin_univ rfl

lemma encodeTimeSubset_injective (T : ℕ) : Function.Injective (encodeTimeSubset T) := by
  intro s t h
  apply Subtype.ext
  simpa only [decode_encode] using congrArg decodeTimes h

lemma prod_encode (T : ℕ) (s : TimeSubset T) (f : ℕ → ℝ≥0∞) :
    (∏ i, f ((encodeTimeSubset T s).2.val i)) = ∏ u ∈ s.val, f u := by
  change (∏ i, f (s.val.orderEmbOfFin rfl i)) = _
  conv_rhs => rw [← s.val.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

lemma prod_one_add_le_ordered_series (T : ℕ) (f : ℕ → ℝ≥0∞) :
    (∏ u ∈ Finset.range (T+1), (1+f u)) ≤
      ∑' n, ∑' t : BoundedTimes T n, ∏ i, f (t.val i) := by
  rw [Finset.prod_one_add]
  calc
    _ = ∑' s : TimeSubset T, ∏ u ∈ s.val, f u := by
      rw [tsum_fintype]
      exact (Finset.sum_attach _ _).symm
    _ = ∑' s : TimeSubset T, ∏ i, f ((encodeTimeSubset T s).2.val i) := by
      apply tsum_congr
      intro s
      exact (prod_encode T s f).symm
    _ ≤ ∑' v : Σ n, BoundedTimes T n, ∏ i, f (v.2.val i) :=
      ENNReal.tsum_comp_le_tsum_of_injective (encodeTimeSubset_injective T)
        (fun v : Σ n, BoundedTimes T n ↦ ∏ i, f (v.2.val i))
    _ = _ := ENNReal.tsum_sigma' _

def gapKernel (k : ℕ) : ℝ≥0∞ :=
  if k=0 then 1 else ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2))
def radiusFactor (R : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((1+R)^2)

lemma radiusFactor_one_le (R : ℝ) (hR : 0 ≤ R) : 1 ≤ radiusFactor R := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

lemma weighted_gap_radius (t k : ℕ) (hk : 0 < k)
    (y : Fin 2 → ℝ) (R : ℝ) (hR : 0 ≤ R) (H : Noise → ℝ≥0∞)
    (hH : Measurable H) (hinv : PastInvariant t H) :
    (∫⁻ ω, H ω * nearTest (t+k) y R ω ∂law) ≤
      radiusFactor R * gapKernel k * ∫⁻ ω, H ω ∂law := by
  refine (weighted_gap_concentration t k hk y R hR H hH hinv).trans ?_
  apply mul_le_mul_left
  rw [gapKernel,ite_eq_right (ne_of_gt hk),radiusFactor,
    ← ENNReal.ofReal_mul (sq_nonneg (1+R))]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ (16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2) := by positivity
  calc
    _ = R^2 * ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) hp

def encounterMass {n : ℕ} (t : Fin n → ℕ) (r : Fin n → ℝ)
    (y : ℕ → Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∏ i, nearTest (t i) (y (t i)) (r i) ω ∂law

lemma encounter_append_bound (u s : ℕ) (hus : u < s)
    {n : ℕ} (t : Fin n → ℕ) (r : Fin n → ℝ) (y : ℕ → Fin 2 → ℝ)
    (ht : ∀ i, t i ≤ u) (R : ℝ) (hR : 0 ≤ R) :
    encounterMass (Fin.snoc t s) (Fin.snoc r R) y ≤
      radiusFactor R * gapKernel (s-u) * encounterMass t r y := by
  have h := weighted_gap_radius u (s-u) (by omega) (y s) R hR
    (fun ω ↦ ∏ i, nearTest (t i) (y (t i)) (r i) ω) (by fun_prop) (by
      intro j ℓ b hb ω x
      apply Finset.prod_congr rfl
      intro i _
      exact nearTest_pastInvariant (t i) u (ht i) (y (t i)) (r i) j ℓ b hb ω x)
  rw [Nat.add_sub_of_le hus.le] at h
  simpa only [encounterMass,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last] using h

lemma encounter_singleton_bound (s : ℕ) (R : ℝ) (hR : 0 ≤ R) (y : ℕ → Fin 2 → ℝ) :
    encounterMass (fun _ : Fin 1 ↦ s) (fun _ ↦ R) y ≤ radiusFactor R * gapKernel s := by
  by_cases h0 : s=0
  · subst s
    refine le_trans ?_ (by simpa [gapKernel] using radiusFactor_one_le R hR)
    calc
      _ ≤ ∫⁻ _ : Noise, 1 ∂law := by
        apply lintegral_mono
        intro ω
        simpa only [Fin.prod_univ_one] using nearTest_le_one 0 (y 0) R ω
      _ = 1 := by simp
  · have h := weighted_gap_radius 0 s (by omega) (y s) R hR
      (fun _ ↦ 1) measurable_const (by intro j ℓ b hb ω x; rfl)
    simpa [encounterMass,Fin.prod_univ_one] using h

lemma encounterMass_le_gap_prod (n : ℕ) (t : Fin n → ℕ) (r : Fin n → ℝ)
    (y : ℕ → Fin 2 → ℝ) (ht : StrictMono t) (hr : ∀ i, 0 ≤ r i) :
    encounterMass t r y ≤ ∏ i, radiusFactor (r i) * gapKernel (timeGaps t i) := by
  induction n with
  | zero => simp [encounterMass]
  | succ n ih =>
    cases n with
    | zero =>
      have h := encounter_singleton_bound (t 0) (r 0) (hr 0) y
      have he : (fun _ : Fin 1 ↦ t 0) = t := by
        funext i; exact congrArg t (Fin.ext (by omega))
      have hl : (fun _ : Fin 1 ↦ r 0) = r := by
        funext i; exact congrArg r (Fin.ext (by omega))
      rw [he, hl] at h
      rw [Fin.prod_univ_one, timeGaps_zero]
      exact h
    | succ n =>
      have hin : StrictMono (Fin.init t) := ht.comp (Fin.strictMono_castSucc)
      have hb := ih (Fin.init t) (Fin.init r) hin (fun i ↦ hr i.castSucc)
      have hlt : t (Fin.last n).castSucc < t (Fin.last (n+1)) := ht (by simp)
      have ha := encounter_append_bound (t (Fin.last n).castSucc) (t (Fin.last (n+1)))
        hlt (Fin.init t) (Fin.init r) y
        (fun i ↦ ht.monotone (by exact_mod_cast Fin.le_last i))
        (r (Fin.last (n+1))) (hr _)
      rw [Fin.snoc_init_self, Fin.snoc_init_self] at ha
      refine ha.trans ?_
      rw [Fin.prod_univ_castSucc]
      calc
        _ ≤ radiusFactor (r (Fin.last (n+1))) *
            gapKernel (t (Fin.last (n+1))-t (Fin.last n).castSucc) *
            ∏ i, radiusFactor (Fin.init r i) * gapKernel (timeGaps (Fin.init t) i) :=
          mul_le_mul' le_rfl hb
        _ = _ := by
          simp_rw [timeGaps_castSucc]
          change _ = _ * (radiusFactor (r (Fin.last (n+1))) *
            gapKernel (t (Fin.last (n+1))-t (Fin.last n).castSucc))
          exact mul_comm _ _

lemma gapKernel_sum_ne_top : (∑' k, gapKernel k) ≠ ∞ := by
  have hs : Summable (fun k : ℕ ↦ (16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  have he : (∑' k : ℕ, ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2))) =
      ENNReal.ofReal (∑' k : ℕ, (16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs).symm
  have hb : (∑' k, gapKernel k) ≤
      1 + ∑' k : ℕ, ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) := by
    calc
      _ ≤ (∑' k : ℕ, ((if k=0 then 1 else 0) +
          ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)))) := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases h : k=0 <;> simp [gapKernel,h]
      _ = _ := by rw [ENNReal.tsum_add]; simp
  rw [he] at hb
  exact ne_top_of_le_ne_top (by finiteness) hb

lemma gapKernel_sum_one_le : (1 : ℝ≥0∞) ≤ ∑' k, gapKernel k := by
  simpa only [gapKernel,↓reduceIte] using ENNReal.le_tsum (f := gapKernel) 0

def orderedEncounterConstant : ℝ := (∑' k, gapKernel k).toReal
lemma orderedEncounterConstant_pos : 0 < orderedEncounterConstant := by
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (by norm_num) gapKernel_sum_one_le))
    gapKernel_sum_ne_top
lemma orderedEncounterConstant_cast : ENNReal.ofReal orderedEncounterConstant = ∑' k, gapKernel k :=
  ENNReal.ofReal_toReal gapKernel_sum_ne_top

lemma ordered_encounter_sum (T n : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (y : ℕ → Fin 2 → ℝ) :
    (∑' t : BoundedTimes T n, encounterMass t.val r y) ≤
      ∏ i, ENNReal.ofReal orderedEncounterConstant * radiusFactor (r i) := by
  calc
    _ ≤ ∑' t : BoundedTimes T n, ∏ i, radiusFactor (r i) * gapKernel (timeGaps t.val i) :=
      ENNReal.tsum_le_tsum fun t ↦ encounterMass_le_gap_prod n t.val r y t.property.1 hr
    _ = (∏ i, radiusFactor (r i)) *
        ∑' t : BoundedTimes T n, ∏ i, gapKernel (timeGaps t.val i) := by
      simp_rw [Finset.prod_mul_distrib,ENNReal.tsum_mul_left]
    _ ≤ (∏ i, radiusFactor (r i)) * (∑' k, gapKernel k)^n :=
      mul_le_mul' le_rfl (ordered_gap_sum_bound T n gapKernel)
    _ = _ := by
      rw [Finset.prod_mul_distrib,orderedEncounterConstant_cast]
      simp [mul_comm]

def radiusEnvelope (a : ℕ → ℝ≥0∞) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) : ℝ≥0∞ :=
  ∑' l : ℕ, a l * nearTest n y (l:ℝ) ω

@[fun_prop] lemma measurable_radiusEnvelope (a : ℕ → ℝ≥0∞) (n : ℕ) (y : Fin 2 → ℝ) :
    Measurable (radiusEnvelope a n y) := by
  unfold radiusEnvelope
  exact Measurable.tsum (fun l ↦ (measurable_nearTest n y (l:ℝ)).const_mul _)

lemma radiusEnvelope_prod {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) (ω : Noise) :
    (∏ i, radiusEnvelope a (t i) (y (t i)) ω) =
      ∑' l : Fin n → ℕ, (∏ i, a (l i)) * ∏ i, nearTest (t i) (y (t i)) (l i : ℝ) ω := by
  unfold radiusEnvelope
  rw [← tsum_vector_prod]
  apply tsum_congr
  intro l
  exact Finset.prod_mul_distrib

def weightedEncounterMass {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∏ i, radiusEnvelope a (t i) (y (t i)) ω ∂law

lemma weightedEncounterMass_eq {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) :
    weightedEncounterMass t a y =
      ∑' l : Fin n → ℕ, (∏ i, a (l i)) * encounterMass t (fun i ↦ (l i : ℝ)) y := by
  unfold weightedEncounterMass
  simp_rw [radiusEnvelope_prod]
  rw [lintegral_tsum (fun l ↦ by fun_prop)]
  apply tsum_congr
  intro l
  exact lintegral_const_mul _ (by fun_prop)

def radiusActivity (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal orderedEncounterConstant * ∑' l : ℕ, a l * radiusFactor (l:ℝ)

lemma weighted_ordered_sum_bound (T n : ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) :
    (∑' t : BoundedTimes T n, weightedEncounterMass t.val a y) ≤ (radiusActivity a)^n := by
  simp_rw [weightedEncounterMass_eq]
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' l : Fin n → ℕ, (∏ i, a (l i)) *
        ∑' t : BoundedTimes T n, encounterMass t.val (fun i ↦ (l i : ℝ)) y := by
      apply tsum_congr
      intro l
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' l : Fin n → ℕ, (∏ i, a (l i)) *
        ∏ i, ENNReal.ofReal orderedEncounterConstant * radiusFactor (l i : ℝ) :=
      ENNReal.tsum_le_tsum fun l ↦ mul_le_mul' le_rfl
        (ordered_encounter_sum T n (fun i ↦ (l i : ℝ)) (fun i ↦ Nat.cast_nonneg _) y)
    _ = ∑' l : Fin n → ℕ, ∏ i,
        ENNReal.ofReal orderedEncounterConstant * (a (l i) * radiusFactor (l i : ℝ)) := by
      apply tsum_congr
      intro l
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [tsum_vector_prod (fun (_ : Fin n) k ↦
        ENNReal.ofReal orderedEncounterConstant * (a k * radiusFactor (k:ℝ)))]
      simp only [ENNReal.tsum_mul_left,radiusActivity,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin]

lemma ordered_product_bound_envelope (T : ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) :
    (∫⁻ ω, ∏ u ∈ Finset.range (T+1), (1+radiusEnvelope a u (y u) ω) ∂law) ≤
      (1-radiusActivity a)⁻¹ := by
  calc
    _ ≤ ∫⁻ ω, ∑' n, ∑' t : BoundedTimes T n,
        ∏ i, radiusEnvelope a (t.val i) (y (t.val i)) ω ∂law :=
      lintegral_mono fun ω ↦ prod_one_add_le_ordered_series T
        (fun u ↦ radiusEnvelope a u (y u) ω)
    _ = ∑' n, ∑' t : BoundedTimes T n, weightedEncounterMass t.val a y := by
      rw [lintegral_tsum (fun n ↦ (Measurable.tsum (fun t ↦ by fun_prop)).aemeasurable)]
      apply tsum_congr
      intro n
      rw [lintegral_tsum (fun t ↦ by fun_prop)]
      rfl
    _ ≤ ∑' n, (radiusActivity a)^n :=
      ENNReal.tsum_le_tsum (fun n ↦ weighted_ordered_sum_bound T n a y)
    _ = _ := ENNReal.tsum_geometric _

lemma ordered_product_bound (T : ℕ) (a : ℕ → ℝ≥0∞) (y : ℕ → Fin 2 → ℝ)
    (f : ℕ → Noise → ℝ≥0∞) (hf : ∀ n ω, f n ω ≤ radiusEnvelope a n (y n) ω) :
    (∫⁻ ω, ∏ u ∈ Finset.range (T+1), (1+f u ω) ∂law) ≤ (1-radiusActivity a)⁻¹ := by
  refine le_trans (lintegral_mono (fun ω ↦ ?_)) (ordered_product_bound_envelope T a y)
  exact Finset.prod_le_prod (fun u _ ↦ add_le_add_right (hf u ω) 1)

lemma exp_sub_one_le_slope {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) :
    Real.exp x - 1 ≤ Real.exp B * x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have he : Real.exp x ≤ Real.exp B := Real.exp_le_exp.mpr hB
  nlinarith [mul_le_mul_of_nonneg_right he hx]

lemma radiusEnvelope_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (n : ℕ)
    (y : Fin 2 → ℝ) (ω : Noise) :
    radiusEnvelope (fun l ↦ c*a l) n y ω = c*radiusEnvelope a n y ω := by
  unfold radiusEnvelope
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  ring

lemma radiusActivity_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    radiusActivity (fun l ↦ c*a l) = c*radiusActivity a := by
  unfold radiusActivity
  simp only [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  ac_rfl

lemma ofReal_exp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (Real.exp (∑ i ∈ s, f i)) = ∏ i ∈ s, ENNReal.ofReal (Real.exp (f i)) := by
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (Real.exp_pos _).le

lemma radius_exponential_bound (T : ℕ) (a : ℕ → ℝ≥0∞) (y : ℕ → Fin 2 → ℝ)
    (U : ℕ → Noise → ℝ) (hU0 : ∀ n ω, 0 ≤ U n ω) (hU1 : ∀ n ω, U n ω ≤ 1)
    (hUa : ∀ n ω, ENNReal.ofReal (U n ω) ≤ radiusEnvelope a n (y n) ω)
    (ha : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (2 * ∑ u ∈ Finset.range (T+1), U u ω)) ∂law) ≤ 2 := by
  let c := ENNReal.ofReal (2*Real.exp 2)
  let b := fun l ↦ c*a l
  let f := fun n ω ↦ ENNReal.ofReal (Real.exp (2*U n ω)-1)
  have hba : radiusActivity b ≤ (1/2:ℝ≥0∞) := by
    simpa only [b,radiusActivity_smul,c] using ha
  have hbf : ∀ n ω, f n ω ≤ radiusEnvelope b n (y n) ω := by
    intro n ω
    calc
      f n ω ≤ ENNReal.ofReal (2*Real.exp 2 * U n ω) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc,mul_left_comm,mul_comm] using
          exp_sub_one_le_slope (by linarith [hU0 n ω] : 0 ≤ 2*U n ω)
            (by linarith [hU1 n ω] : 2*U n ω ≤ 2)
      _ = c * ENNReal.ofReal (U n ω) := by rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ c * radiusEnvelope a n (y n) ω := mul_le_mul' le_rfl (hUa n ω)
      _ = radiusEnvelope b n (y n) ω := (radiusEnvelope_smul c a n (y n) ω).symm
  have he (n : ℕ) (ω : Noise) : 1+f n ω = ENNReal.ofReal (Real.exp (2*U n ω)) := by
    have hx : 0 ≤ Real.exp (2*U n ω)-1 := by
      have := Real.one_le_exp_iff.mpr (by linarith [hU0 n ω] : 0 ≤ 2*U n ω)
      linarith
    change 1+ENNReal.ofReal (Real.exp (2*U n ω)-1) = _
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) hx]
    congr 1
    ring
  have h := ordered_product_bound T b y f hbf
  have hh : (∫⁻ ω, ENNReal.ofReal
      (Real.exp (2 * ∑ u ∈ Finset.range (T+1), U u ω)) ∂law) =
      ∫⁻ ω, ∏ u ∈ Finset.range (T+1), (1+f u ω) ∂law := by
    apply lintegral_congr
    intro ω
    rw [Finset.mul_sum,ofReal_exp_finset_sum]
    exact Finset.prod_congr rfl (fun u _ ↦ (he _ _).symm)
  rw [hh]
  refine h.trans ?_
  have hd : (1/2:ℝ≥0∞) ≤ 1-radiusActivity b := by
    simpa using tsub_le_tsub_left hba (1:ℝ≥0∞)
  exact (ENNReal.inv_le_inv.mpr hd).trans_eq (by norm_num)

end HardSphere.DyadicSkeleton
end
end

end OAI
