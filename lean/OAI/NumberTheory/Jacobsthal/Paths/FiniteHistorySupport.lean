import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Probability.TransitionKernels

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

inductive Side | even | odd deriving DecidableEq

def Side.flip : Side → Side | .even => .odd | .odd => .even

noncomputable def weight : Side → ℝ → ℝ | .even => phiEven | .odd => phiOdd

def Valid : Side → ℝ → Prop
  | .even, s => 198 / 100 ≤ s
  | .odd, s => 95 / 100 ≤ s

noncomputable def minRatio : Side → ℝ → ℝ
  | .even, s => s - 1
  | .odd, s => max 2 (s - 1)

noncomputable def transitionDensity (i : Side) (s : ℝ) : ℝ → ℝ :=
  tailDensity (minRatio i s) (weight i s) (fun t => W t * weight i.flip t)

def Admissible : Side → ℝ → List ℝ → Prop
  | _, _, [] => True
  | i, s, t :: ts => minRatio i s ≤ t ∧ Admissible i.flip t ts

noncomputable def nextExponent (r t : ℝ) : ℝ := r / (t + 1)
noncomputable def nextGap (r t : ℝ) : ℝ := r * t / (t + 1)
noncomputable def cost (t : ℝ) : ℝ := Real.log (1 + 1 / t)

noncomputable def finalGap : ℝ → List ℝ → ℝ
  | r, [] => r
  | r, t :: ts => finalGap (nextGap r t) ts

def finalRatio : ℝ → List ℝ → ℝ
  | s, [] => s
  | _, t :: ts => finalRatio t ts

def finalSide : Side → List ℝ → Side
  | i, [] => i
  | i, _ :: ts => finalSide i.flip ts

noncomputable def pathCost : List ℝ → ℝ
  | [] => 0
  | t :: ts => cost t + pathCost ts

noncomputable def harmonicDensity : List ℝ → ℝ
  | [] => 1
  | t :: ts => (1 / (t + 1)) * harmonicDensity ts

noncomputable def tiltedDensity : Side → ℝ → List ℝ → ℝ
  | _, _, [] => 1
  | i, s, t :: ts => transitionDensity i s t * tiltedDensity i.flip t ts

def AllExponentsAbove (ell : ℝ) : ℝ → List ℝ → Prop
  | _, [] => True
  | r, t :: ts => ell < nextExponent r t ∧ AllExponentsAbove ell (nextGap r t) ts

theorem valid_pos {i : Side} {s : ℝ} (hs : Valid i s) : 0 < s := by
  cases i <;> dsimp [Valid] at hs <;> linarith

theorem weight_pos {i : Side} {s : ℝ} (hs : Valid i s) : 0 < weight i s := by
  cases i with
  | even => exact phiEven_pos (by dsimp [Valid] at hs; linarith)
  | odd => exact phiOdd_pos s

theorem valid_next {i : Side} {s t : ℝ} (hs : Valid i s) (ht : minRatio i s ≤ t) :
    Valid i.flip t := by
  cases i with
  | even => dsimp [Valid, minRatio, Side.flip] at *; linarith
  | odd =>
    change 198 / 100 ≤ t
    change max 2 (s - 1) ≤ t at ht
    linarith [le_max_left (2 : ℝ) (s - 1)]

theorem minRatio_ge_sub_one (i : Side) (s : ℝ) : s - 1 ≤ minRatio i s := by
  cases i with
  | even => exact le_rfl
  | odd => exact le_max_right _ _

theorem transitionDensity_even (s : EvenState) : transitionDensity .even s = evenDensity s := rfl
theorem transitionDensity_odd (s : OddState) : transitionDensity .odd s = oddDensity s := rfl

theorem nextGap_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 0 < nextGap r t := by
  unfold nextGap
  positivity

theorem nextExponent_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 0 < nextExponent r t := by
  unfold nextExponent
  positivity

theorem gap_exponent_conservation {r t : ℝ} (ht : 0 < t) :
    nextGap r t + nextExponent r t = r := by
  unfold nextGap nextExponent
  field_simp

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem nextRatio_identity {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    nextGap r t / nextExponent r t = t := by
  unfold nextGap nextExponent
  field_simp

theorem exponent_le_cutoff {i : Side} {s t r : ℝ}
    (hs : Valid i s) (ht : minRatio i s ≤ t) (hr : 0 < r) : nextExponent r t ≤ r / s := by
  have hs0 := valid_pos hs
  have ht0 := valid_pos (valid_next hs ht)
  have hst : s ≤ t + 1 := by linarith [minRatio_ge_sub_one i s]
  exact div_le_div_of_nonneg_left hr.le hs0 hst

theorem upper_standard_admission {s t r : ℝ} (ht : minRatio .odd s ≤ t) (hr : 0 < r) :
    2 * nextExponent r t ≤ nextGap r t := by
  have ht2 : 2 ≤ t := le_trans (le_max_left _ _) ht
  unfold nextExponent nextGap
  have h := mul_le_mul_of_nonneg_left ht2 hr.le
  have ht1 : 0 < t + 1 := by linarith
  apply (le_div_iff₀ ht1).mpr
  field_simp
  nlinarith

theorem step_weight_identity {i : Side} {s t r : ℝ}
    (hs : Valid i s) (ht : minRatio i s ≤ t) (hr : 0 < r) :
    1 / (t + 1) = transitionDensity i s t * (nextGap r t / r) ^ 2 *
      (weight i s / weight i.flip t) := by
  have hv := valid_next hs ht
  have ht0 := valid_pos hv
  have hw := weight_pos hs
  have hw' := weight_pos hv
  unfold transitionDensity tailDensity
  rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
  unfold W nextGap
  field_simp

theorem valid_final {i : Side} {s : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) : Valid (finalSide i ts) (finalRatio s ts) := by
  induction ts generalizing i s with
  | nil => exact hs
  | cons t ts ih => exact ih (valid_next hs ht.1) ht.2

theorem finalGap_pos {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) (hr : 0 < r) : 0 < finalGap r ts := by
  induction ts generalizing i s r with
  | nil => exact hr
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    exact ih hv ht.2 (nextGap_pos hr (valid_pos hv))

theorem telescoping_path_weight {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) (hr : 0 < r) :
    harmonicDensity ts = tiltedDensity i s ts * (finalGap r ts / r) ^ 2 *
      (weight i s / weight (finalSide i ts) (finalRatio s ts)) := by
  induction ts generalizing i s r with
  | nil =>
    have hw := weight_pos hs
    simp only [harmonicDensity, tiltedDensity, finalGap, finalSide, finalRatio]
    field_simp
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    have ht0 := valid_pos hv
    have hn := nextGap_pos hr ht0
    have hw := weight_pos hs
    have hw' := weight_pos hv
    have hew := weight_pos (valid_final hv ht.2)
    simp only [harmonicDensity, tiltedDensity, finalGap, finalSide, finalRatio]
    rw [step_weight_identity hs ht.1 hr, ih hv ht.2 hn]
    field_simp

theorem cost_pos {t : ℝ} (ht : 0 < t) : 0 < cost t := by
  unfold cost
  exact Real.log_pos (by have h : 0 < 1 / t := one_div_pos.mpr ht; linarith)

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

theorem finalGap_eq_cost {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) :
    finalGap r ts = r * Real.exp (-pathCost ts) := by
  induction ts generalizing i s r with
  | nil => simp [finalGap, pathCost]
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    rw [finalGap, ih hv ht.2, nextGap_eq_cost (valid_pos hv), pathCost,
      neg_add, Real.exp_add]
    ring

theorem final_gap_ratio_le_cutoff {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) (hr : 0 < r) :
    finalGap r ts / finalRatio s ts ≤ r / s := by
  induction ts generalizing i s r with
  | nil => exact le_rfl
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    have ht0 := valid_pos hv
    have h := ih hv ht.2 (nextGap_pos hr ht0)
    rw [nextGap_div_ratio ht0] at h
    exact le_trans h (exponent_le_cutoff hs ht.1 hr)

theorem all_exponents_iff_final {i : Side} {s r ell : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) (hr : 0 < r) (hne : ts ≠ []) :
    AllExponentsAbove ell r ts ↔ ell < finalGap r ts / finalRatio s ts := by
  induction ts generalizing i s r with
  | nil => exact (hne rfl).elim
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    have ht0 := valid_pos hv
    have hn := nextGap_pos hr ht0
    cases ts with
    | nil =>
      simp only [AllExponentsAbove, finalGap, finalRatio, and_true]
      rw [nextGap_div_ratio ht0]
    | cons u us =>
      have hb := final_gap_ratio_le_cutoff hv ht.2 hn
      rw [nextGap_div_ratio ht0] at hb
      change (ell < nextExponent r t ∧ AllExponentsAbove ell (nextGap r t) (u :: us)) ↔
        ell < finalGap (nextGap r t) (u :: us) / finalRatio t (u :: us)
      rw [ih hv ht.2 hn (by simp)]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h hb, h⟩⟩

theorem arrival_cutoff {i : Side} {s r ell : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) (hr : 0 < r)
    (hell : 0 < ell) (hne : ts ≠ []) :
    AllExponentsAbove ell r ts ↔ finalRatio s ts < finalGap r ts / ell := by
  rw [all_exponents_iff_final hs ht hr hne]
  have hratio := valid_pos (valid_final hs ht)
  rw [lt_div_iff₀ hratio, lt_div_iff₀ hell, mul_comm]

end NumberTheoryLean.FinitePathGeometry



namespace NumberTheoryLean.FinitePathMeasures

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry

abbrev State := EvenState ⊕ OddState
abbrev CostState := State × ℝ

noncomputable def evenToOdd : Kernel EvenState OddState :=
  evenKernel.comapRight (MeasurableEmbedding.subtype_coe measurableSet_Ici)

noncomputable def oddToEven : Kernel OddState EvenState :=
  oddKernel.comapRight (MeasurableEmbedding.subtype_coe measurableSet_Ici)

instance evenToOdd_isMarkovKernel : IsMarkovKernel evenToOdd := by
  apply Kernel.IsMarkovKernel.comapRight
  intro s
  have h := (ae_mem_iff_measure_eq (μ := evenKernel s)
    (s := Ici (95 / 100 : ℝ)) measurableSet_Ici.nullMeasurableSet).mp (evenKernel_ae_odd_domain s)
  rw [measure_univ] at h
  convert! h using 1
  congr 1
  ext t
  simp
  rfl

instance oddToEven_isMarkovKernel : IsMarkovKernel oddToEven := by
  apply Kernel.IsMarkovKernel.comapRight
  intro s
  have h := (ae_mem_iff_measure_eq (μ := oddKernel s)
    (s := Ici (198 / 100 : ℝ)) measurableSet_Ici.nullMeasurableSet).mp (oddKernel_ae_even_domain s)
  rw [measure_univ] at h
  convert! h using 1
  congr 1
  ext t
  simp
  rfl

noncomputable def evenBranch : Kernel EvenState State := evenToOdd.map Sum.inr
noncomputable def oddBranch : Kernel OddState State := oddToEven.map Sum.inl

instance evenBranch_isMarkovKernel : IsMarkovKernel evenBranch :=
  Kernel.IsMarkovKernel.map _ measurable_inr

instance oddBranch_isMarkovKernel : IsMarkovKernel oddBranch :=
  Kernel.IsMarkovKernel.map _ measurable_inl

noncomputable def stateKernel : Kernel State State where
  toFun := Sum.elim evenBranch oddBranch
  measurable' := evenBranch.measurable.sumElim oddBranch.measurable

instance stateKernel_isMarkovKernel : IsMarkovKernel stateKernel := by
  constructor
  intro s
  cases s with
  | inl s => change IsProbabilityMeasure (evenBranch s); infer_instance
  | inr s => change IsProbabilityMeasure (oddBranch s); infer_instance

def stateRatio : State → ℝ := Sum.elim Subtype.val Subtype.val
def stateSide : State → Side := Sum.elim (fun _ => .even) (fun _ => .odd)

theorem stateRatio_valid (s : State) : Valid (stateSide s) (stateRatio s) := by
  cases s with
  | inl s => exact s.2
  | inr s => exact s.2

theorem stateRatio_measurable : Measurable stateRatio :=
  measurable_subtype_coe.sumElim measurable_subtype_coe

theorem cost_measurable : Measurable cost := by
  unfold cost
  exact Real.measurable_log.comp (measurable_const.add (measurable_const.div measurable_id))

noncomputable def addCost (z : CostState × State) : CostState :=
  (z.2, z.1.2 + cost (stateRatio z.2))

theorem addCost_measurable : Measurable addCost :=
  measurable_snd.prodMk ((measurable_snd.comp measurable_fst).add
    (cost_measurable.comp (stateRatio_measurable.comp measurable_snd)))

noncomputable def costKernel : Kernel CostState CostState :=
  (Kernel.id ×ₖ stateKernel.prodMkRight ℝ).map addCost

instance costKernel_isMarkovKernel : IsMarkovKernel costKernel :=
  Kernel.IsMarkovKernel.map _ addCost_measurable

theorem costKernel_apply (z : CostState) {B : Set CostState} (hB : MeasurableSet B) :
    costKernel z B = stateKernel z.1 {s | (s, z.2 + cost (stateRatio s)) ∈ B} := by
  rw [costKernel, Kernel.map_apply' _ addCost_measurable _ hB,
    Kernel.prod_apply' _ _ _ (addCost_measurable hB), Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (addCost_measurable hB)

noncomputable def historyKernel (n : ℕ) :
    Kernel (∀ _ : Finset.Iic n, CostState) CostState :=
  costKernel.comap (fun h => h ⟨n, by simp⟩) (measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n))

instance historyKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (historyKernel n) := by
  unfold historyKernel
  infer_instance

noncomputable def finitePathKernel (n : ℕ) :
    Kernel (∀ _ : Finset.Iic (0 : ℕ), CostState) (∀ _ : Finset.Iic n, CostState) :=
  Kernel.partialTraj (X := fun _ => CostState) historyKernel 0 n

instance finitePathKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (finitePathKernel n) := by
  unfold finitePathKernel
  infer_instance

noncomputable def finitePathMeasure (s : State) (n : ℕ) : Measure (∀ _ : Finset.Iic n, CostState) :=
  finitePathKernel n (fun _ => (s, 0))

instance finitePathMeasure_isProbabilityMeasure (s : State) (n : ℕ) :
    IsProbabilityMeasure (finitePathMeasure s n) := by
  unfold finitePathMeasure
  infer_instance

theorem finite_history_factorization {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Kernel.partialTraj (X := fun _ => CostState) historyKernel b c ∘ₖ Kernel.partialTraj (X := fun _ => CostState) historyKernel a b =
      Kernel.partialTraj (X := fun _ => CostState) historyKernel a c :=
  Kernel.partialTraj_comp_partialTraj hab hbc

end NumberTheoryLean.FinitePathMeasures



namespace NumberTheoryLean.ReciprocalGapExposure
open FinitePathGeometry
attribute [local instance] Classical.propDecidable

noncomputable def potential (a r : ℝ) : ℝ := min (1/r) (1/a)

theorem potential_step_mono {a r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    potential a r ≤ potential a (nextGap r t) := by
  have hn := nextGap_pos hr ht
  have hle : nextGap r t ≤ r := by linarith [gap_exponent_conservation (r := r) ht,nextExponent_pos hr ht]
  exact min_le_min_right _ (one_div_le_one_div_of_le hn hle)

theorem selected_step_exposure {a L r t : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hr : 0 < r) (ht : 0 < t) :
    (if a ≤ nextGap r t ∧ t ≤ L then 1/nextGap r t else 0) ≤
      (L+1)*(potential a (nextGap r t)-potential a r) := by
  have hn := nextGap_pos hr ht
  have hmono := potential_step_mono (a := a) hr ht
  split_ifs with hs
  · have hnr : nextGap r t ≤ r := by linarith [gap_exponent_conservation (r := r) ht,nextExponent_pos hr ht]
    have hpnext : potential a (nextGap r t)=1/nextGap r t :=
      min_eq_left (one_div_le_one_div_of_le ha hs.1)
    have hpr : potential a r=1/r := min_eq_left (one_div_le_one_div_of_le ha (hs.1.trans hnr))
    rw [hpnext,hpr] at hmono ⊢
    have he : (t+1)*(1/nextGap r t-1/r)=1/nextGap r t := by
      unfold nextGap
      field_simp [hr.ne',ht.ne',show t+1 ≠ 0 by positivity]
      ring
    have hm := mul_le_mul_of_nonneg_right (show t+1 ≤ L+1 by linarith) (sub_nonneg.mpr hmono)
    rw [he] at hm
    exact hm
  · exact mul_nonneg (by linarith) (sub_nonneg.mpr hmono)

noncomputable def exposure (a L : ℝ) : ℝ → List ℝ → ℝ
  | _,[] => 0
  | r,t::ts => (if a ≤ nextGap r t ∧ t ≤ L then 1/nextGap r t else 0)+exposure a L (nextGap r t) ts

theorem exposure_potential {a L r : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hr : 0 < r)
    (ts : List ℝ) (ht : ∀ t ∈ ts,0 < t) :
    exposure a L r ts ≤ (L+1)*(potential a (finalGap r ts)-potential a r) := by
  induction ts generalizing r with
  | nil => simp [exposure,finalGap]
  | cons t ts ih =>
    have hp := ht t (by simp)
    have hs := selected_step_exposure ha hL hr hp
    have hh := ih (nextGap_pos hr hp) (fun u hu => ht u (by simp [hu]))
    change _+exposure a L (nextGap r t) ts ≤ _
    change _ ≤ (L+1)*(potential a (finalGap (nextGap r t) ts)-potential a r)
    linarith

theorem exposure_bound {a L r : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hr : 0 < r)
    (ts : List ℝ) (ht : ∀ t ∈ ts,0 < t) : exposure a L r ts ≤ (L+1)/a := by
  have hh := exposure_potential ha hL hr ts ht
  have hn : 0 ≤ potential a r := le_min (by positivity) (by positivity)
  have hu : potential a (finalGap r ts) ≤ 1/a := min_le_right _ _
  have hm := mul_le_mul_of_nonneg_left (show potential a (finalGap r ts)-potential a r ≤ 1/a by linarith)
    (show 0 ≤ L+1 by linarith)
  exact hh.trans (by simpa only [mul_one_div] using hm)

theorem admissible_exposure_bound {a L r s : ℝ} {i : Side}
    (ha : 0 < a) (hL : 0 ≤ L) (hr : 0 < r) (hs : Valid i s)
    (ts : List ℝ) (had : Admissible i s ts) : exposure a L r ts ≤ (L+1)/a := by
  apply exposure_bound ha hL hr ts
  induction ts generalizing i s with
  | nil => simp
  | cons t ts ih =>
    have hnext := valid_next hs had.1
    intro u hu
    rcases List.mem_cons.mp hu with he | hu
    · subst u
      exact valid_pos hnext
    · exact ih hnext had.2 u hu
end NumberTheoryLean.ReciprocalGapExposure



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory MeasurableEquiv
open scoped ENNReal

abbrev Hist (X : Type*) (n : ℕ) := ∀ _ : Finset.Iic n, X

def last {X : Type*} (n : ℕ) (h : Hist X n) : X := h ⟨n, by simp⟩

def mapHist {X Y : Type*} (f : X → Y) (n : ℕ) (h : Hist X n) : Hist Y n :=
  fun k => f (h k)

noncomputable def extend {X : Type*} [MeasurableSpace X] (n : ℕ)
    (h : Hist X n) (x : X) : Hist X (n+1) :=
  _root_.IicProdIoc (X := fun _ => X) n (n+1) (h, piSingleton (X := fun _ => X) n x)

theorem mapHist_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) (n : ℕ) : Measurable (mapHist f n) := by
  exact Measurable.of_eval (fun k => hf.comp (measurable_pi_apply k))

theorem extend_measurable {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (fun p : Hist X n × X => extend n p.1 p.2) := by
  exact (measurable_IicProdIoc (X := fun _ => X) (m := n) (n := n+1)).comp
    (measurable_fst.prodMk ((piSingleton (X := fun _ => X) n).measurable.comp measurable_snd))

theorem mapHist_extend {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (n : ℕ) (h : Hist X n) (x : X) :
    mapHist f (n+1) (extend n h x) = extend n (mapHist f n h) (f x) := by
  ext k
  simp only [mapHist, extend, IicProdIoc_def, piSingleton,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  split_ifs <;> simp

private theorem last_measurable_for_comap {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (last (X := X) n) := measurable_pi_apply _

noncomputable def pastKernel {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) (n : ℕ) : Kernel (Hist X n) X :=
  K.comap (last n) (last_measurable_for_comap n)

instance pastKernel_sfinite {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (pastKernel K n) := by
  unfold pastKernel
  infer_instance

noncomputable def pathKernel {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) (n : ℕ) : Kernel (Hist X 0) (Hist X n) :=
  Kernel.partialTraj (X := fun _ => X) (pastKernel K) 0 n

instance pathKernel_sfinite {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (pathKernel K n) := by
  unfold pathKernel
  infer_instance

theorem lintegral_pathKernel_succ {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) (h₀ : Hist X 0)
    {F : Hist X (n+1) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂pathKernel K (n+1) h₀ =
      ∫⁻ h, ∫⁻ x, F (extend n h x) ∂K (last n h) ∂pathKernel K n h₀ := by
  rw [pathKernel, Kernel.partialTraj_succ_of_le (Nat.zero_le n),
    Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => X) (m := n) (n := n+1)) _ hF,
    Kernel.lintegral_comp _ _ _ (by exact hF.comp measurable_IicProdIoc)]
  congr 1
  funext h
  rw [Kernel.lintegral_id_prod (by exact hF.comp measurable_IicProdIoc),
    Kernel.lintegral_map _ (piSingleton (X := fun _ => X) n).measurable _
      (by exact (hF.comp measurable_IicProdIoc).comp measurable_prodMk_left)]
  rw [pastKernel, Kernel.comap_apply]
  rfl

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteGapExposure
open FinitePathGeometry ReciprocalGapExposure
attribute [local instance] Classical.propDecidable

theorem finite_potential_telescope (N : ℕ) (f : Fin (N+1) → ℝ) :
    (∑ j : Fin N,(f j.succ-f j.castSucc))=f (Fin.last N)-f 0 := by
  have h₁ := Fin.sum_univ_succ f
  have h₂ := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

theorem finite_arrival_exposure {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (N : ℕ) (r : Fin (N+1) → ℝ) (t : Fin N → ℝ)
    (hr : ∀ j,0 < r j) (ht : ∀ j,0 < t j)
    (hflow : ∀ j,r j.succ=nextGap (r j.castSucc) (t j)) :
    (∑ j : Fin N,if a ≤ r j.succ ∧ t j ≤ L then 1/r j.succ else 0) ≤ (L+1)/a := by
  have hsum : (∑ j : Fin N,if a ≤ r j.succ ∧ t j ≤ L then 1/r j.succ else 0) ≤
      ∑ j : Fin N,(L+1)*(potential a (r j.succ)-potential a (r j.castSucc)) := by
    apply Finset.sum_le_sum
    intro j _
    rw [hflow j]
    exact selected_step_exposure ha hL (hr j.castSucc) (ht j)
  rw [← Finset.mul_sum,finite_potential_telescope N (fun j => potential a (r j))] at hsum
  have hn : 0 ≤ potential a (r 0) := le_min (one_div_nonneg.mpr (hr 0).le) (by positivity)
  have hu : potential a (r (Fin.last N)) ≤ 1/a := min_le_right _ _
  have hm := mul_le_mul_of_nonneg_left (show potential a (r (Fin.last N))-potential a (r 0) ≤ 1/a by linarith)
    (show 0 ≤ L+1 by linarith)
  exact hsum.trans (by simpa only [mul_one_div] using hm)

theorem finite_all_exposure {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (N : ℕ) (r s : Fin (N+1) → ℝ)
    (hr : ∀ j,0 < r j) (hs : ∀ j,0 < s j)
    (hflow : ∀ j : Fin N,r j.succ=nextGap (r j.castSucc) (s j.succ)) :
    (∑ j : Fin (N+1),if a ≤ r j ∧ s j ≤ L then 1/r j else 0) ≤ (L+2)/a := by
  have hh := finite_arrival_exposure ha hL N r (fun j => s j.succ) hr (fun j => hs j.succ) hflow
  rw [Fin.sum_univ_succ]
  have hinit : (if a ≤ r 0 ∧ s 0 ≤ L then 1/r 0 else 0) ≤ 1/a := by
    split_ifs with h
    · exact one_div_le_one_div_of_le ha h.1
    · positivity
  have he : (L+2)/a=1/a+(L+1)/a := by ring
  rw [he]
  exact add_le_add hinit hh
end NumberTheoryLean.FiniteGapExposure



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (K : Kernel X X) (L : Kernel Y Y) [IsSFiniteKernel K] [IsSFiniteKernel L]
variable {f : X → Y} (hf : Measurable f)
variable (hstep : ∀ x, (K x).map f = L (f x))

include hf hstep

theorem lintegral_mapHist (n : ℕ) (h₀ : Hist X 0)
    {F : Hist Y n → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (mapHist f n h) ∂pathKernel K n h₀ =
      ∫⁻ h, F h ∂pathKernel L n (mapHist f 0 h₀) := by
  induction n with
  | zero =>
    simp only [pathKernel, Kernel.partialTraj_self, Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (mapHist_measurable hf 0)), lintegral_dirac' _ hF]
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (mapHist_measurable hf (n+1))),
      lintegral_pathKernel_succ L n (mapHist f 0 h₀) hF]
    have hG : Measurable (fun h : Hist Y n =>
        ∫⁻ y, F (extend n h y) ∂L (last n h)) := by
      have hm : Measurable (Function.uncurry (fun h : Hist Y n => fun y : Y =>
          F (extend n h y))) := hF.comp (extend_measurable n)
      simpa only [pastKernel, Kernel.comap_apply] using
        (hm.lintegral_kernel_prod_right (κ := pastKernel L n))
    calc
      _ = ∫⁻ h, ∫⁻ y, F (extend n (mapHist f n h) y)
          ∂L (last n (mapHist f n h)) ∂pathKernel K n h₀ := by
        apply lintegral_congr
        intro h
        simp only [mapHist_extend]
        change (∫⁻ x, F (extend n (mapHist f n h) (f x)) ∂K (last n h)) =
          ∫⁻ y, F (extend n (mapHist f n h) y) ∂L (f (last n h))
        rw [← hstep (last n h), lintegral_map]
        · exact hF.comp ((extend_measurable n).comp measurable_prodMk_left)
        · exact hf
      _ = _ := ih hG

theorem pathKernel_mapHist (n : ℕ) :
    (pathKernel K n).map (mapHist f n) =
      (pathKernel L n).comap (mapHist f 0) (mapHist_measurable hf 0) := by
  apply Kernel.ext_fun
  intro h₀ F hF
  rw [Kernel.lintegral_map _ (mapHist_measurable hf n) _ hF, Kernel.comap_apply]
  exact lintegral_mapHist K L hf hstep n h₀ hF

theorem pathMeasure_mapHist (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (mapHist f n) =
      pathKernel L n (mapHist f 0 h₀) := by
  rw [← Kernel.map_apply _ (mapHist_measurable hf n), pathKernel_mapHist K L hf hstep,
    Kernel.comap_apply]

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem extend_last (n : ℕ) (h : Hist X n) (x : X) : last (n+1) (extend n h x) = x := by
  simp [last, extend, IicProdIoc_def, MeasurableEquiv.piSingleton]

instance pastKernel_markov (K : Kernel X X) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (pastKernel K n) := by
  unfold pastKernel
  infer_instance

instance pathKernel_markov (K : Kernel X X) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (pathKernel K n) := by
  unfold pathKernel
  infer_instance

theorem last_measurable (n : ℕ) : Measurable (last (X := X) n) :=
  measurable_pi_apply _

variable (K : Kernel X X) [IsSFiniteKernel K]

theorem lintegral_endpoint (n : ℕ) (h₀ : Hist X 0) {F : X → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (last n h) ∂pathKernel K n h₀ = ∫⁻ x, F x ∂(K^n) (last 0 h₀) := by
  induction n generalizing F with
  | zero =>
    change (∫⁻ h, F (last 0 h) ∂Kernel.id h₀) = ∫⁻ x, F x ∂Kernel.id (last 0 h₀)
    simp only [Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (measurable_pi_apply _)), lintegral_dirac' _ hF]
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (measurable_pi_apply _))]
    simp only [extend_last]
    have hp : K^(n+1) = K ∘ₖ (K^n) := by
      simpa only [Nat.add_comm, pow_one] using Kernel.pow_add K 1 n
    rw [hp, Kernel.lintegral_comp _ _ _ hF]
    exact ih (hF.lintegral_kernel (κ := K))

theorem pathKernel_endpoint (n : ℕ) :
    (pathKernel K n).map (last n) = (K^n).comap (last 0) (last_measurable 0) := by
  apply Kernel.ext_fun
  intro h₀ F hF
  rw [Kernel.lintegral_map _ (last_measurable n) _ hF, Kernel.comap_apply]
  exact lintegral_endpoint K n h₀ hF

theorem pathMeasure_endpoint (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (last n) = (K^n) (last 0 h₀) := by
  rw [← Kernel.map_apply _ (last_measurable n), pathKernel_endpoint, Kernel.comap_apply]

theorem pathMeasure_coordinate [IsMarkovKernel K] (n k : ℕ) (hk : k ≤ n) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (fun h => h ⟨k, by simpa using hk⟩) =
      (K^k) (last 0 h₀) := by
  have hrestriction : (pathKernel K n h₀).map (frestrictLe₂ (π := fun _ => X) hk) = pathKernel K k h₀ :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => X) (κ := pastKernel K) h₀ hk
  calc
    _ = ((pathKernel K n h₀).map (frestrictLe₂ (π := fun _ => X) hk)).map (last k) := by
      rw [Measure.map_map (last_measurable k) (measurable_frestrictLe₂ hk)]
      rfl
    _ = _ := by rw [hrestriction, pathMeasure_endpoint]

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryOccurrence
open Set MeasureTheory ProbabilityTheory FiniteHistoryTransport
variable {X : Type*} [MeasurableSpace X]

def atIndex (N : ℕ) (h : Hist X N) (j : Fin (N+1)) : X :=
  h ⟨j.1,Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.isLt)⟩

noncomputable def arrivalOccurrence (E : Set X) (N : ℕ) : Set (Hist X N) :=
  ⋃ j : Fin N,{h | atIndex N h j.succ ∈ E}

theorem arrivalOccurrence_measurable {E : Set X} (hE : MeasurableSet E) (N : ℕ) :
    MeasurableSet (arrivalOccurrence E N) := by
  apply MeasurableSet.iUnion
  intro j
  exact (measurable_pi_apply _) hE

theorem atIndex_law (K : Kernel X X) [IsMarkovKernel K] (N : ℕ) (h₀ : Hist X 0) (j : Fin (N+1)) :
    (pathKernel K N h₀).map (fun h => atIndex N h j)=(K^j.1) (last 0 h₀) :=
  pathMeasure_coordinate K N j.1 (Nat.le_of_lt_succ j.isLt) h₀

theorem probability_integrable (K : Kernel X X) [IsMarkovKernel K]
    {E : Set X} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) (j : Fin (N+1)) :
    Integrable (fun h => (K (atIndex N h j) E).toReal) (pathKernel K N h₀) := by
  have hc : Measurable (fun h : Hist X N => atIndex N h j) := measurable_pi_apply _
  have hm := (K.measurable_coe hE).ennreal_toReal.comp hc
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun h => by
    change ‖(K (atIndex N h j) E).toReal‖ ≤ 1
    have hb : (K (atIndex N h j) E).toReal ≤ 1 := measureReal_le_one
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb)

theorem next_probability_identity (K : Kernel X X) [IsMarkovKernel K]
    {E : Set X} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) (j : Fin N) :
    (pathKernel K N h₀).real {h | atIndex N h j.succ ∈ E}=
      ∫ h,(K (atIndex N h j.castSucc) E).toReal ∂pathKernel K N h₀ := by
  have hn := atIndex_law K N h₀ j.succ
  have hp := atIndex_law K N h₀ j.castSucc
  simp only [Fin.val_succ] at hn
  simp only [Fin.val_castSucc] at hp
  have hcn : Measurable (fun h : Hist X N => atIndex N h j.succ) := measurable_pi_apply _
  have hcp : Measurable (fun h : Hist X N => atIndex N h j.castSucc) := measurable_pi_apply _
  have he : (K^(j.1+1)) (last 0 h₀) E = ∫⁻ x,K x E ∂(K^j.1) (last 0 h₀) := by
    have hh := Kernel.pow_add_apply_eq_lintegral K j.1 1 (last 0 h₀) hE
    simpa only [pow_one] using hh
  calc
    _ = ((K^(j.1+1)) (last 0 h₀) E).toReal := by
      rw [← hn,Measure.map_apply hcn hE]
      rfl
    _ = (∫⁻ x,K x E ∂(K^j.1) (last 0 h₀)).toReal := congrArg ENNReal.toReal he
    _ = ∫ x,(K x E).toReal ∂(K^j.1) (last 0 h₀) :=
      (integral_toReal (K.measurable_coe hE).aemeasurable
        (Filter.Eventually.of_forall (fun x => measure_lt_top (K x) E))).symm
    _ = _ := by
      rw [← hp,integral_map_of_stronglyMeasurable hcp
        (K.measurable_coe hE).ennreal_toReal.stronglyMeasurable]

theorem occurrence_le_integrated_hazards (K : Kernel X X) [IsMarkovKernel K]
    {E : Set X} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) :
    (pathKernel K N h₀).real (arrivalOccurrence E N) ≤
      ∫ h,∑ j : Fin N,(K (atIndex N h j.castSucc) E).toReal ∂pathKernel K N h₀ := by
  apply (measureReal_iUnion_fintype_le (fun j : Fin N => {h | atIndex N h j.succ ∈ E})).trans_eq
  simp_rw [next_probability_identity K hE N h₀]
  symm
  apply integral_finsetSum
  intro j _
  exact probability_integrable K hE N h₀ j.castSucc
end NumberTheoryLean.FiniteHistoryOccurrence



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem ae_pathKernel_succ (K : Kernel X X) [IsSFiniteKernel K]
    (n : ℕ) (h₀ : Hist X 0) {P : Hist X (n+1) → Prop}
    (hP : MeasurableSet {h | P h})
    (hstep : ∀ᵐ h ∂pathKernel K n h₀, ∀ᵐ x ∂K (last n h), P (extend n h x)) :
    ∀ᵐ h ∂pathKernel K (n+1) h₀, P h := by
  classical
  rw [ae_iff]
  change pathKernel K (n+1) h₀ ({h | P h}ᶜ) = 0
  rw [← lintegral_indicator_one hP.compl,
    lintegral_pathKernel_succ K n h₀ (by exact measurable_const.indicator hP.compl)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hstep] with h hh
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hh] with x hx
  simp [hx]

noncomputable def pathSum (F : X → ℝ) (n : ℕ) (h : Hist X n) : ℝ :=
  ∑ j : Fin n, F (h ⟨j,by exact Finset.mem_Iic.mpr j.isLt.le⟩)

theorem pathSum_measurable {F : X → ℝ} (hF : Measurable F) (n : ℕ) :
    Measurable (pathSum F n) := by
  unfold pathSum
  fun_prop

theorem extend_previous (n : ℕ) (h : Hist X n) (x : X) (k : Finset.Iic n) :
    extend n h x ⟨k,by exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp k.2).trans n.le_succ)⟩ = h k := by
  simp [extend,IicProdIoc_def,show (k:ℕ) ≤ n from Finset.mem_Iic.mp k.2]

theorem pathSum_extend (F : X → ℝ) (n : ℕ) (h : Hist X n) (x : X) :
    pathSum F (n+1) (extend n h x) = pathSum F n h + F (last n h) := by
  rw [pathSum,Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact extend_previous n h x ⟨j,by exact Finset.mem_Iic.mpr j.isLt.le⟩
  · congr 1
    exact extend_previous n h x ⟨n,by simp⟩

end NumberTheoryLean.FiniteHistoryTransport


end Erdos970

end OAI
