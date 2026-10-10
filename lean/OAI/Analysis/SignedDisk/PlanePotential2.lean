import OAI.Analysis.SignedDisk.VectorRefinement1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SignedDisk

namespace PlanePotential

theorem kernel_column_lp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α × β → ℝ≥0∞} (hK : Measurable K) {C : ℝ≥0∞}
    (hC : ∀ᵐ y ∂ν, (∫⁻ x, (K (x,y))^(3/2:ℝ) ∂μ) ≤ C) :
    (∫⁻ x, (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ∂μ) ≤ C*(ν univ)^(3/2:ℝ) := by
  have hpq : Real.HolderConjugate (3/2) 3 := by rw [Real.holderConjugate_iff]; norm_num
  have hpoint (x : α) : (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ≤
      (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => K (x,y)) (g := fun _ => 1)
      ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (aemeasurable_const (b := (1:ℝ≥0∞)))
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 3/2)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),← ENNReal.rpow_mul,
      show (1/(3/2:ℝ))*(3/2)=1 by norm_num,
      show (1/(3:ℝ))*(3/2)=1/2 by norm_num,ENNReal.rpow_one,one_mul] using h'
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ∫⁻ x, K (x,y)^(3/2:ℝ) ∂μ ∂ν)*(ν univ)^(1/2:ℝ) := by
      rw [lintegral_mul_const _ (hK.pow_const _).lintegral_prod_right,
        lintegral_lintegral_swap (hK.pow_const _).aemeasurable]
    _ ≤ (C*ν univ)*(ν univ)^(1/2:ℝ) :=
      mul_le_mul_left ((lintegral_mono_ae hC).trans_eq (lintegral_const _)) _
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (ν univ)^(1:ℝ)*(ν univ)^(1/2:ℝ) := by rw [ENNReal.rpow_one]
        _ = (ν univ)^((1:ℝ)+1/2) :=
          (ENNReal.rpow_add_of_nonneg 1 (1/2) (by norm_num) (by norm_num)).symm
        _ = _ := by norm_num

/-- No pointwise integrability assertion for the singular kernel is needed
in this domination: the Bochner integral is bounded by the nonnegative integral. -/
lemma potential_domination {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    ENNReal.ofReal |∫ y, ⟪L y,b y⟫| ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  calc
    _ = ‖∫ y, ⟪L y,b y⟫‖ₑ := by rw [← ofReal_norm,Real.norm_eq_abs]
    _ ≤ ∫⁻ y, ‖⟪L y,b y⟫‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only [Pi.mul_apply]
      rw [← ofReal_norm]
      change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

theorem cancelled_potential_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪cancelledGreen ψ z a x y,β y⟫|)^(3/2:ℝ)) ≤
    (ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a)))) * (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := cancelledGreen_measurable hψm z a
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ)*(2*Real.pi/(2*a))))
    (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_piece_column hψm hψs hψB hψL hM hB hL ha z y
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

lemma zero_mass_kernel_shift {L : ℂ → ℂ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (c : ℂ) :
    (∫ y, ⟪L y,β y⟫) = ∫ y, ⟪L y-c,β y⟫ := by
  have hc : Integrable (fun y => ⟪c,β y⟫) := hβ.const_inner c
  have hci : (∫ y, ⟪c,β y⟫) = 0 := by rw [integral_inner hβ,hzero,inner_zero_right]
  simp only [inner_sub_left]
  by_cases hi : Integrable (fun y => ⟪L y,β y⟫)
  · rw [integral_sub hi hc,hci,sub_zero]
  · rw [integral_undef hi,integral_undef]
    intro hs
    have hh := hs.add hc
    change Integrable (fun y => (⟪L y,β y⟫-⟪c,β y⟫)+⟪c,β y⟫) at hh
    simp only [sub_add_cancel] at hh
    exact hi hh

lemma cancelled_potential_eq {ψ : ℂ → ℝ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (z : ℂ) (a : ℝ) (x : ℂ) :
    (∫ y, ⟪green ψ x y,β y⟫) = ∫ y, ⟪cancelledGreen ψ z a x y,β y⟫ := by
  by_cases hx : ‖x-z‖ ≤ 2*a
  · simp only [cancelledGreen,ite_eq_left hx]
  · simp only [cancelledGreen,ite_eq_right hx]
    exact zero_mass_kernel_shift hβ hzero _

/-- Uniform scaling of the exact p-th power column constant: in dimension two
and at p=3/2 its radius dependence is precisely a^(1/2). -/
lemma column_scaling {K D a : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    K^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ)) +
      (D*a)^(3/2:ℝ)*(2*Real.pi/(2*a)) =
      (8*Real.pi*K^(3/2:ℝ)+Real.pi*D^(3/2:ℝ))*a^(1/2:ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) ha.le,Real.mul_rpow hD ha.le]
  have hfour : (4:ℝ)^(1/2:ℝ) = 2 := by norm_num [← Real.sqrt_eq_rpow]
  have hpow : a^(3/2:ℝ)/a = a^(1/2:ℝ) := by
    rw [← Real.rpow_sub_one ha.ne']
    norm_num
  rw [hfour]
  calc
    _ = 8*Real.pi*K^(3/2:ℝ)*a^(1/2:ℝ)+Real.pi*D^(3/2:ℝ)*(a^(3/2:ℝ)/a) := by ring
    _ = _ := by rw [hpow]; ring

theorem green_zero_piece_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  simp_rw [cancelled_potential_eq hβ hzero z a]
  have h := cancelled_potential_lp hψm hψs hψB hψL hM hB hL ha z hβ hβs
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    column_scaling (by positivity) ha] at h
  exact h

end PlanePotential

open scoped RealInnerProductSpace

namespace IntrinsicMarks

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def direction (e v : E) : E := by
  classical
  exact if v = 0 then e else ‖v‖⁻¹ • v

lemma norm_direction {e : E} (he : ‖e‖ = 1) (v : E) : ‖direction e v‖ = 1 := by
  by_cases hv : v = 0
  · simp [direction,hv,he]
  · rw [direction,ite_eq_right hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

lemma mass_direction (e v : E) : ‖v‖ • direction e v = v := by
  by_cases hv : v = 0
  · simp [hv]
  · simp [direction,hv,smul_smul,norm_ne_zero_iff.mpr hv]

lemma debt_identity {e n : E} (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (v : E) :
    2*(‖v‖-⟪v,n⟫) = ‖v‖*‖direction e v-n‖^2 := by
  have hi : ‖v‖*⟪direction e v,n⟫ = ⟪v,n⟫ := by
    rw [← real_inner_smul_left,mass_direction]
  rw [norm_sub_sq_real,norm_direction he,hn]
  nlinarith

lemma marked_mass_le {e n : E} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (v : E) {δ : ℝ} (hδ : 0 < δ) (hmark : δ < ‖direction e v-n‖) :
    ‖v‖ ≤ (2/δ^2)*(‖v‖-⟪v,n⟫) := by
  have hs : δ^2 ≤ ‖direction e v-n‖^2 :=
    (sq_le_sq₀ hδ.le (norm_nonneg _)).mpr hmark.le
  have hm := mul_le_mul_of_nonneg_left hs (norm_nonneg v)
  have hid := debt_identity he hn v
  have hd : 0 < δ^2 := sq_pos_of_pos hδ
  rw [div_mul_eq_mul_div,le_div_iff₀ hd]
  nlinarith

/-- Finite uniform branching includes each finite positive-refinement path forest
by padding absent children with zero vectors. No triangle defect is assumed. -/
inductive Tree (ι : Type*) (E : Type*) where
  | leaf : E → Tree ι E
  | branch : (ι → Tree ι E) → Tree ι E

variable {ι : Type*} [Fintype ι]

def vector : Tree ι E → E
  | .leaf v => v
  | .branch t => ∑ i, vector (t i)

def terminalMass : Tree ι E → ℝ
  | .leaf v => ‖v‖
  | .branch t => ∑ i, terminalMass (t i)

omit [InnerProductSpace ℝ E] in
lemma norm_vector_le_terminalMass (t : Tree ι E) : ‖vector t‖ ≤ terminalMass t := by
  induction t with
  | leaf v => exact le_rfl
  | branch t ih =>
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ih i)

/-- Only the first crossing from the most recent marked direction is counted;
a crossing resets the anchor before descending further. -/
def markedCost (e : E) (δ : ℝ) : Tree ι E → E → ℝ
  | .leaf v, n => if δ < ‖direction e v-n‖ then ‖v‖ else 0
  | .branch t, n =>
      let v := ∑ i, vector (t i)
      if δ < ‖direction e v-n‖ then
        ‖v‖ + ∑ i, markedCost e δ (t i) (direction e v)
      else ∑ i, markedCost e δ (t i) n

theorem markedCost_le {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) {n : E} (hn : ‖n‖ = 1) :
    markedCost e δ t n ≤ (2/δ^2)*(terminalMass t-⟪vector t,n⟫) := by
  induction t generalizing n with
  | leaf v =>
    dsimp [markedCost,terminalMass,vector]
    split_ifs with hm
    · exact marked_mass_le he hn v hδ hm
    · have hi : ⟪v,n⟫ ≤ ‖v‖ := by simpa only [hn,mul_one] using real_inner_le_norm v n
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hi)
  | branch t ih =>
    let v := ∑ i, vector (t i)
    have hs (u : E) (hu : ‖u‖ = 1) :
        (∑ i, markedCost e δ (t i) u) ≤
          (2/δ^2)*((∑ i, terminalMass (t i))-⟪v,u⟫) := by
      calc
        _ ≤ ∑ i, (2/δ^2)*(terminalMass (t i)-⟪vector (t i),u⟫) :=
          Finset.sum_le_sum (fun i _ => ih i hu)
        _ = _ := by simp only [Finset.mul_sum,Finset.sum_sub_distrib,sum_inner,v,mul_sub]
    have hv := norm_direction he v
    change (if δ < ‖direction e v-n‖ then
      ‖v‖ + ∑ i, markedCost e δ (t i) (direction e v)
      else ∑ i, markedCost e δ (t i) n) ≤ _
    split_ifs with hm
    · have hms := marked_mass_le he hn v hδ hm
      have hss := hs (direction e v) hv
      have hinner : ⟪v,direction e v⟫ = ‖v‖ := by
        calc
          _ = ⟪‖v‖ • direction e v,direction e v⟫ := congrArg (fun w => ⟪w,direction e v⟫) (mass_direction e v).symm
          _ = _ := by rw [real_inner_smul_left,real_inner_self_eq_norm_sq,hv]; ring
      rw [hinner] at hss
      change _ ≤ (2/δ^2)*((∑ i, terminalMass (t i))-⟪v,n⟫)
      nlinarith
    · exact hs n hn

def costWithRoot (e : E) (δ : ℝ) : Tree ι E → ℝ
  | .leaf v => ‖v‖
  | .branch t =>
      let v := ∑ i, vector (t i)
      ‖v‖+∑ i, markedCost e δ (t i) (direction e v)

theorem costWithRoot_le {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) : costWithRoot e δ t ≤ (1+2/δ^2)*terminalMass t := by
  cases t with
  | leaf v =>
    change ‖v‖ ≤ (1+2/δ^2)*‖v‖
    nlinarith [mul_nonneg (show 0 ≤ 2/δ^2 by positivity) (norm_nonneg v)]
  | branch t =>
    let v := ∑ i, vector (t i)
    have hv := norm_direction he v
    have hinner : ⟪v,direction e v⟫ = ‖v‖ := by
      calc
        _ = ⟪‖v‖ • direction e v,direction e v⟫ := congrArg (fun w => ⟪w,direction e v⟫) (mass_direction e v).symm
        _ = _ := by rw [real_inner_smul_left,real_inner_self_eq_norm_sq,hv]; ring
    have hs : (∑ i, markedCost e δ (t i) (direction e v)) ≤
        (2/δ^2)*((∑ i, terminalMass (t i))-‖v‖) := by
      calc
        _ ≤ ∑ i, (2/δ^2)*(terminalMass (t i)-⟪vector (t i),direction e v⟫) :=
          Finset.sum_le_sum (fun i _ => markedCost_le he hδ (t i) hv)
        _ = _ := by rw [← Finset.mul_sum,Finset.sum_sub_distrib,← sum_inner,hinner]
    have hn : ‖v‖ ≤ ∑ i, terminalMass (t i) := norm_vector_le_terminalMass (.branch t)
    change ‖v‖+∑ i, markedCost e δ (t i) (direction e v) ≤
      (1+2/δ^2)*(∑ i, terminalMass (t i))
    nlinarith [mul_nonneg (show 0 ≤ 2/δ^2 by positivity) (norm_nonneg v)]

end

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The fraction of the child capacity occupied by particles already alive. -/
def survival (t : ι → Tree ι E) : ℝ :=
  ‖∑ i, vector (t i)‖ / ∑ i, ‖vector (t i)‖

lemma survival_nonneg (t : ι → Tree ι E) : 0 ≤ survival t := by
  unfold survival
  positivity

lemma survival_le_one (t : ι → Tree ι E) : survival t ≤ 1 := by
  unfold survival
  exact div_le_one_of_le₀ (norm_sum_le _ _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

lemma survival_capacity (t : ι → Tree ι E) :
    survival t * (∑ i, ‖vector (t i)‖) = ‖∑ i, vector (t i)‖ := by
  unfold survival
  by_cases h : (∑ i, ‖vector (t i)‖) = 0
  · have hn : ‖∑ i, vector (t i)‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      simpa only [h] using norm_sum_le Finset.univ (fun i => vector (t i))
    simp [h,hn]
  · exact div_mul_cancel₀ _ h

/-- Explicit finite weighted evaluation on terminal paths, for the population
born at the current root. Every branching has its true capacity ratio. -/
def rootEval : Tree ι E → (List ι → ℝ) → ℝ
  | .leaf v, F => ‖v‖ * F []
  | .branch t, F => survival t * ∑ i, rootEval (t i) (fun p => F (i::p))

/-- Explicit finite evaluation of populations born strictly below this root.
The complete prefix is retained, including the part before birth. -/
def lateEval : Tree ι E → (List ι → ℕ → ℝ) → ℝ
  | .leaf _, _ => 0
  | .branch t, F =>
      (1-survival t) * (∑ i, rootEval (t i) (fun p => F (i::p) 1)) +
        ∑ i, lateEval (t i) (fun p b => F (i::p) (b+1))

def particleEval (t : Tree ι E) (F : List ι → ℕ → ℝ) : ℝ :=
  rootEval t (fun p => F p 0) + lateEval t F

lemma rootEval_nonneg (t : Tree ι E) {F : List ι → ℝ} (hF : ∀ p, 0 ≤ F p) :
    0 ≤ rootEval t F := by
  induction t generalizing F with
  | leaf v => exact mul_nonneg (norm_nonneg _) (hF _)
  | branch t ih =>
    exact mul_nonneg (survival_nonneg t) (Finset.sum_nonneg fun i _ => ih i (fun p => hF (i::p)))

lemma lateEval_nonneg (t : Tree ι E) {F : List ι → ℕ → ℝ} (hF : ∀ p b, 0 ≤ F p b) :
    0 ≤ lateEval t F := by
  induction t generalizing F with
  | leaf v => exact le_rfl
  | branch t ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (survival_le_one t))
      (Finset.sum_nonneg (fun i _ => rootEval_nonneg (t i) (fun p => hF (i::p) 1))))
      (Finset.sum_nonneg (fun i _ => ih i (fun p b => hF (i::p) (b+1))))

lemma particleEval_nonneg (t : Tree ι E) {F : List ι → ℕ → ℝ} (hF : ∀ p b, 0 ≤ F p b) :
    0 ≤ particleEval t F := add_nonneg (rootEval_nonneg t (fun p => hF p 0)) (lateEval_nonneg t hF)

lemma rootEval_const (t : Tree ι E) (c : ℝ) :
    rootEval t (fun _ => c) = ‖vector t‖*c := by
  induction t with
  | leaf _ => rfl
  | branch t ih =>
    change survival t * (∑ i, rootEval (t i) (fun _ => c)) = _
    simp only [ih,← Finset.sum_mul]
    rw [← mul_assoc,survival_capacity]
    rfl

lemma rootEval_add (t : Tree ι E) (F G : List ι → ℝ) :
    rootEval t (fun p => F p+G p) = rootEval t F+rootEval t G := by
  induction t generalizing F G with
  | leaf _ => exact mul_add _ _ _
  | branch t ih => simp only [rootEval,ih,Finset.sum_add_distrib,mul_add]

lemma rootEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℝ) :
    rootEval t (fun p => c*F p) = c*rootEval t F := by
  induction t generalizing F with
  | leaf _ => dsimp [rootEval]; ring
  | branch t ih => simp only [rootEval,ih,← Finset.mul_sum]; ring

lemma lateEval_const (t : Tree ι E) (c : ℝ) :
    lateEval t (fun _ _ => c) = (terminalMass t-‖vector t‖)*c := by
  induction t with
  | leaf _ => simp [lateEval,terminalMass,vector]
  | branch t ih =>
    change (1-survival t)*(∑ i, rootEval (t i) (fun _ => c)) +
      (∑ i, lateEval (t i) (fun _ _ => c)) = _
    simp only [ih,rootEval_const,← Finset.sum_mul,Finset.sum_sub_distrib]
    rw [sub_mul,one_mul,← mul_assoc,survival_capacity]
    simp only [terminalMass,vector]
    ring

lemma particleEval_const (t : Tree ι E) (c : ℝ) :
    particleEval t (fun _ _ => c) = terminalMass t*c := by
  rw [particleEval,rootEval_const,lateEval_const]
  ring

lemma lateEval_add (t : Tree ι E) (F G : List ι → ℕ → ℝ) :
    lateEval t (fun p b => F p b+G p b) = lateEval t F+lateEval t G := by
  induction t generalizing F G with
  | leaf _ => simp [lateEval]
  | branch t ih => simp only [lateEval,rootEval_add,ih,Finset.sum_add_distrib,mul_add]; ring

lemma lateEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℕ → ℝ) :
    lateEval t (fun p b => c*F p b) = c*lateEval t F := by
  induction t generalizing F with
  | leaf _ => simp [lateEval]
  | branch t ih => simp only [lateEval,rootEval_smul,ih,← Finset.mul_sum]; ring

lemma particleEval_add (t : Tree ι E) (F G : List ι → ℕ → ℝ) :
    particleEval t (fun p b => F p b+G p b) = particleEval t F+particleEval t G := by
  simp only [particleEval,rootEval_add,lateEval_add]
  ring

lemma particleEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℕ → ℝ) :
    particleEval t (fun p b => c*F p b) = c*particleEval t F := by
  simp only [particleEval,rootEval_smul,lateEval_smul,mul_add]

lemma particleEval_mono (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (hFG : ∀ p b, F p b ≤ G p b) : particleEval t F ≤ particleEval t G := by
  have hn := particleEval_nonneg t (F := fun p b => G p b-F p b) (fun p b => sub_nonneg.mpr (hFG p b))
  have h := particleEval_add t G (fun p b => -1*F p b)
  simp only [neg_one_mul] at h
  have hn' : particleEval t (fun p b => G p b-F p b) = particleEval t G-particleEval t F := by
    calc
      _ = particleEval t G+particleEval t (fun p b => -1*F p b) := by simpa only [neg_one_mul,sub_eq_add_neg] using h
      _ = _ := by rw [particleEval_smul]; ring
  rw [hn'] at hn
  linarith

/-- Sum a node charge only at and after the particle's birth. -/
def pathCharge (C : List ι → ℝ) : List ι → ℕ → ℝ
  | [], 0 => C []
  | [], _+1 => 0
  | i::p, 0 => C [] + pathCharge (fun q => C (i::q)) p 0
  | i::p, b+1 => pathCharge (fun q => C (i::q)) p b

def nodeCharge : Tree ι E → (List ι → ℝ) → ℝ
  | .leaf v, C => ‖v‖*C []
  | .branch t, C => ‖∑ i, vector (t i)‖*C [] + ∑ i, nodeCharge (t i) (fun p => C (i::p))

/-- Exact occupancy identity for every node charge. This includes all levels,
not only the terminal mass; populations created later are not charged earlier. -/
theorem particle_occupancy (t : Tree ι E) (C : List ι → ℝ) :
    particleEval t (pathCharge C) = nodeCharge t C := by
  induction t generalizing C with
  | leaf v => simp [particleEval,rootEval,lateEval,pathCharge,nodeCharge]
  | branch t ih =>
    simp only [particleEval,rootEval,lateEval,pathCharge,rootEval_add,rootEval_const,
      Finset.sum_add_distrib]
    have hs : (∑ i, particleEval (t i) (pathCharge (fun q => C (i::q)))) =
        ∑ i, nodeCharge (t i) (fun q => C (i::q)) :=
      Finset.sum_congr rfl (fun i _ => ih i _)
    simp only [particleEval,Finset.sum_add_distrib] at hs
    rw [← Finset.sum_mul,mul_add,← mul_assoc,survival_capacity]
    change _ = ‖∑ i, vector (t i)‖*C []+∑ i, nodeCharge (t i) (fun q => C (i::q))
    linarith

end IntrinsicMarks

end SignedDisk

end

end OAI
