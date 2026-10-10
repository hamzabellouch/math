import OAI.Geometry.UnitDistances.HeightTransfer

namespace OAI

namespace PlanarUnitDistances.NormalizedCoordinates
open Finset FiniteLaw FiniteStarCoupling WeightedAbsoluteValues
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma center_height (π : Law (P×Q)) (z : P⊕Q → K) (a : K) :
    avg (right π) (fun q => exactHeight K (z (.inr q)-a)) ≤
      Real.log 2+avg (left π) (fun p => exactHeight K (z (.inl p)-a))+
        avg π (fun pq => exactHeight K (z (.inl pq.1)-z (.inr pq.2))) := by
  have hb:=avg_mono π (fun pq => exactHeight_add_le K (z (.inl pq.1)-a) (-(z (.inl pq.1)-z (.inr pq.2))))
  have he (pq : P×Q) : (z (.inl pq.1)-a)+(-(z (.inl pq.1)-z (.inr pq.2)))=z (.inr pq.2)-a := by ring
  simp only [he,exactHeight_neg,avg_add,avg_const] at hb
  simpa only [left,right,push_avg] using hb

theorem translate (π : Law (P×Q)) {C S : ℝ}
    (hc : LocalHeightTransfer.LabelControl C (fun p q => π.val (p,q)))
    (z w : P⊕Q → K)
    (hz : avg π (fun pq => exactHeight K (z (.inl pq.1)-z (.inr pq.2)))≤S)
    (hw : avg π (fun pq => exactHeight K (w (.inl pq.1)-w (.inr pq.2)))≤S) :
    ∃p₀ : P,
      avg (left π) (fun p => exactHeight K (z (.inl p)-z (.inl p₀))+exactHeight K (w (.inl p)-w (.inl p₀)))+
      avg (right π) (fun q => exactHeight K (z (.inr q)-z (.inl p₀))+exactHeight K (w (.inr q)-w (.inl p₀)))+
      avg π (fun pq => exactHeight K (z (.inl pq.1)-z (.inr pq.2))+exactHeight K (w (.inl pq.1)-w (.inr pq.2))) ≤
        4*((C+1)*(Real.log 2+2))*(S+1)+4*S+2*Real.log 2 := by
  let μ:=left π
  let F : P → ℝ:=fun r => avg μ (fun p => exactHeight K (z (.inl p)-z (.inl r))+exactHeight K (w (.inl p)-w (.inl r)))
  obtain ⟨p₀,hp⟩:=exists_le_average μ F
  have hF : avg μ F=
      avg (pair μ μ) (fun pp => exactHeight K (z (.inl pp.1)-z (.inl pp.2)))+
      avg (pair μ μ) (fun pp => exactHeight K (w (.inl pp.1)-w (.inl pp.2))) := by
    rw [←avg_add,pair_avg]
    simp only [F,avg,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    ring
  rw [hF] at hp
  have hC:=LocalHeightTransfer.control_nonneg (LawExpansion.total π) hc
  have hL : 0≤(C+1)*(Real.log 2+2) := mul_nonneg (by linarith) (by have := Real.log_nonneg (show (1:ℝ)≤2 by norm_num); linarith)
  have hpz:=(ActualHeightTransfer.pair_height K π hc z).trans (mul_le_mul_of_nonneg_left (show _ ≤ S+1 by linarith) hL)
  have hpw:=(ActualHeightTransfer.pair_height K π hc w).trans (mul_le_mul_of_nonneg_left (show _ ≤ S+1 by linarith) hL)
  have hqz:=center_height K π z (z (.inl p₀))
  have hqw:=center_height K π w (w (.inl p₀))
  refine ⟨p₀,?_⟩
  simp only [avg_add] at *
  dsimp only [F,μ] at hp
  simp only [avg_add] at hp
  linarith
end
end PlanarUnitDistances.NormalizedCoordinates

namespace PlanarUnitDistances.StateConsistency
open MeasureTheory Set Real
open PlanarUnitDistances.GridShift
noncomputable section
abbrev Shifts := (ℝ × ℝ) × (ℝ × ℝ)
def shiftLaw : Measure Shifts := squareShift.prod squareShift
instance : IsProbabilityMeasure shiftLaw := by unfold shiftLaw; infer_instance

def consistent (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) : Prop :=
  if s < n then
    gridLabel (exp (-s)) z u.1 = gridLabel (exp (-s)) z' u.1 ∧
    gridLabel (exp s) w u.2 ≠ gridLabel (exp s) w' u.2
  else
    gridLabel (exp (-s)) z u.1 ≠ gridLabel (exp (-s)) z' u.1 ∧
    gridLabel (exp s) w u.2 = gridLabel (exp s) w' u.2

def error (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) : ℝ :=
  by classical exact if consistent n s z z' w w' u then 0 else 1

lemma error_bounds (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) :
    0 ≤ error n s z z' w w' u ∧ error n s z z' w w' u ≤ 1 := by
  unfold error; split <;> norm_num

lemma measurable_consistent (n : ℝ) (z z' w w' : ℂ) :
    MeasurableSet {x : ℝ × Shifts | consistent n x.1 z z' w w' x.2} := by
  have h (a : ℂ) (negate : Bool) (first : Bool) :
      Measurable (fun x : ℝ × Shifts =>
        gridLabel (exp (if negate then -x.1 else x.1)) a (if first then x.2.1 else x.2.2)) := by
    cases negate <;> cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, gridLabel] <;> fun_prop
  unfold consistent
  have hA := measurableSet_eq_fun (h z true true) (h z' true true)
  have hB := measurableSet_eq_fun (h w false false) (h w' false false)
  simp only [Bool.false_eq_true,ite_true,ite_false] at hA hB
  convert MeasurableSet.ite (measurableSet_lt measurable_fst (measurable_const (a := n)))
    (hA.inter hB.compl) (hA.compl.inter hB) using 1
  ext x
  by_cases hs : x.1 < n <;> simp [Set.ite,hs]

lemma measurable_error (n : ℝ) (z z' w w' : ℂ) :
    Measurable (fun x : ℝ × Shifts => error n x.1 z z' w w' x.2) :=
  Measurable.ite (measurable_consistent n z z' w w') measurable_const measurable_const

lemma integrable_error (n s : ℝ) (z z' w w' : ℂ) :
    Integrable (error n s z z' w w') shiftLaw := by
  apply Integrable.of_bound ((measurable_error n z z' w w').comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  filter_upwards [] with u
  change ‖error n s z z' w w' u‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (error_bounds n s z z' w w' u).1]
  exact (error_bounds n s z z' w w' u).2

lemma short_jump_z {n s : ℝ} {z z' : ℂ} (hz : ‖z-z'‖ = exp (-n)) :
    2*‖z-z'‖/exp (-s) = 2*exp (s-n) := by
  calc
    _ = 2*(exp (-n)/exp (-s)) := by rw [hz]; ring
    _ = 2*exp ((-n)-(-s)) := by rw [exp_sub]
    _ = _ := by congr 2; ring

lemma short_jump_w {n s : ℝ} {w w' : ℂ} (hw : ‖w-w'‖ = exp n) :
    2*‖w-w'‖/exp s = 2*exp (n-s) := by
  rw [hw,exp_sub]; ring

lemma long_jump_z {n s : ℝ} {z z' : ℂ} (hz : ‖z-z'‖ = exp (-n))
    (h : log 2 < s-n) (u : ℝ × ℝ) :
    gridLabel (exp (-s)) z u ≠ gridLabel (exp (-s)) z' u := by
  intro he
  have hb := norm_le_of_same_grid (exp_pos (-s)) he
  have hl : 2 < exp (s-n) := by
    simpa only [exp_log (by norm_num : (0:ℝ) < 2)] using exp_lt_exp.mpr h
  have hd := short_jump_z hz (s := s)
  have : 2*‖z-z'‖ / exp (-s) ≤ 4 := by
    rw [div_le_iff₀ (exp_pos (-s))]
    nlinarith
  linarith

lemma long_jump_w {n s : ℝ} {w w' : ℂ} (hw : ‖w-w'‖ = exp n)
    (h : log 2 < n-s) (u : ℝ × ℝ) :
    gridLabel (exp s) w u ≠ gridLabel (exp s) w' u := by
  intro he
  have hb := norm_le_of_same_grid (exp_pos s) he
  have hl : 2 < exp (n-s) := by simpa only [exp_log (by norm_num : (0:ℝ) < 2)] using exp_lt_exp.mpr h
  have hd := short_jump_w hw (s := s)
  have : 2*‖w-w'‖ / exp s ≤ 4 := by
    rw [div_le_iff₀ (exp_pos s)]
    nlinarith
  linarith

lemma pointwise_short {n s : ℝ} {z z' w w' : ℂ}
    (hz : ‖z-z'‖ = exp (-n)) (hw : ‖w-w'‖ = exp n)
    (hfar : log 2 < |s-n|) (u : Shifts) :
    error n s z z' w w' u =
      if s < n then gridMismatch (exp (-s)) z z' u.1
      else gridMismatch (exp s) w w' u.2 := by
  by_cases hs : s < n
  · have hw' := long_jump_w hw (by simpa [abs_of_neg (sub_neg.mpr hs)] using hfar) u.2
    simp [error,consistent,hs,hw',gridMismatch]
  · have hz' := long_jump_z hz (by simpa [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hs))] using hfar) u.1
    simp [error,consistent,hs,hz',gridMismatch]

theorem expected_error_le {n s : ℝ} {z z' w w' : ℂ}
    (hz : ‖z-z'‖ = exp (-n)) (hw : ‖w-w'‖ = exp n) :
    (∫ u, error n s z z' w w' u ∂shiftLaw) ≤
      (if |s-n| ≤ log 2 then (1:ℝ) else 0)+2*exp (-|s-n|) := by
  by_cases h : |s-n| ≤ log 2
  · calc
      _ ≤ ∫ _u : Shifts, (1:ℝ) ∂shiftLaw := integral_mono (integrable_error ..)
        (integrable_const _) (fun u => (error_bounds ..).2)
      _ ≤ _ := by simp only [integral_const,probReal_univ,one_smul,ite_eq_left h]; linarith [exp_pos (-|s-n|)]
  · simp only [ite_eq_right h,zero_add]
    simp_rw [pointwise_short hz hw (lt_of_not_ge h)]
    by_cases hs : s < n
    · simp only [ite_eq_left hs]
      rw [shiftLaw,integral_fun_fst]
      simp only [probReal_univ,one_smul]
      exact (gridMismatch_integral_le (exp_pos (-s)) z z').trans <| by
        rw [short_jump_z hz]
        simp [abs_of_neg (sub_neg.mpr hs)]
    · simp only [ite_eq_right hs]
      rw [shiftLaw,integral_fun_snd]
      simp only [probReal_univ,one_smul]
      exact (gridMismatch_integral_le (exp_pos s) w w').trans <| by
        rw [short_jump_w hw]
        simp [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hs))]

lemma exp_abs_integrable : Integrable (fun s : ℝ => exp (-|s|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ))]
  apply IntegrableOn.union
  · apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
    intro x hx
    simp only [mem_Iic] at hx
    simp [abs_of_nonpos (show x ≤ 0 from hx)]
  · apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (show 0 < x from hx)]

lemma exp_abs_integral : (∫ s : ℝ, exp (-|s|)) = 2 := by
  have h₁ := exp_abs_integrable.integrableOn (s := Iic 0)
  have h₂ := exp_abs_integrable.integrableOn (s := Ioi 0)
  calc
    _ = ∫ s in Iic (0:ℝ) ∪ Ioi 0, exp (-|s|) := by rw [Iic_union_Ioi,Measure.restrict_univ]
    _ = (∫ s in Iic (0:ℝ), exp (-|s|)) + ∫ s in Ioi (0:ℝ), exp (-|s|) :=
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi h₁ h₂
    _ = (∫ s in Iic (0:ℝ), exp s) + ∫ s in Ioi (0:ℝ), exp (-s) := by
      congr 1
      · apply setIntegral_congr_fun measurableSet_Iic
        intro x hx; simp [abs_of_nonpos (show x ≤ 0 from hx)]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx; simp [abs_of_pos (show 0 < x from hx)]
    _ = 2 := by rw [integral_exp_Iic_zero,integral_exp_neg_Ioi_zero]; norm_num

def envelope (n s : ℝ) : ℝ :=
  (Icc (n-log 2) (n+log 2)).indicator (fun _ => (1:ℝ)) s+2*exp (-|s-n|)

lemma envelope_eq (n s : ℝ) : envelope n s =
    (if |s-n| ≤ log 2 then (1:ℝ) else 0)+2*exp (-|s-n|) := by
  have he : |s-n| ≤ log 2 ↔ s ∈ Icc (n-log 2) (n+log 2) := by
    rw [abs_le,mem_Icc]; constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp only [envelope,Set.indicator_apply,he]

lemma envelope_nonneg (n s : ℝ) : 0 ≤ envelope n s := by
  rw [envelope_eq]; split <;> positivity

lemma envelope_integrable (n : ℝ) : Integrable (envelope n) := by
  apply Integrable.add
  · exact ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator measurableSet_Icc
  · exact (exp_abs_integrable.comp_sub_right n).const_mul 2

lemma envelope_integral (n : ℝ) : (∫ s : ℝ, envelope n s) = 2*log 2+4 := by
  have h₁ : Integrable ((Icc (n-log 2) (n+log 2)).indicator (fun _ => (1:ℝ))) :=
    ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator measurableSet_Icc
  simp only [envelope]
  rw [integral_add h₁ ((exp_abs_integrable.comp_sub_right n).const_mul 2),
    integral_indicator_const 1 measurableSet_Icc,integral_const_mul]
  have he : (∫ s : ℝ, exp (-|s-n|)) = 2 := by
    simpa only [sub_eq_add_neg] using (integral_add_right_eq_self (fun s : ℝ => exp (-|s|)) (-n)).trans exp_abs_integral
  rw [he]
  have hp : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
  simp [Real.volume_real_Icc,show n+log 2-(n-log 2) = 2*log 2 by ring,max_eq_left (by positivity : 0 ≤ 2*log 2)]; norm_num

lemma product_error_integrable (n l r : ℝ) (z z' w w' : ℂ) :
    Integrable (fun x : ℝ × Shifts => error n x.1 z z' w w' x.2)
      ((volume.restrict (Icc l r)).prod shiftLaw) := by
  apply Integrable.of_bound (measurable_error n z z' w w').aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (error_bounds ..).1]
  exact (error_bounds ..).2

theorem mean_integrated_error_le {n l r : ℝ} {z z' w w' : ℂ}
    (hz : ‖z-z'‖ = exp (-n)) (hw : ‖w-w'‖ = exp n) :
    (∫ u, ∫ s in Icc l r, error n s z z' w w' u ∂volume ∂shiftLaw) ≤ 2*log 2+4 := by
  rw [← integral_integral_swap (product_error_integrable n l r z z' w w')]
  calc
    _ ≤ ∫ s in Icc l r, envelope n s := integral_mono
      (product_error_integrable n l r z z' w w').integral_prod_left
      (envelope_integrable n).integrableOn (fun s => by rw [envelope_eq]; exact expected_error_le hz hw)
    _ ≤ ∫ s : ℝ, envelope n s := integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (envelope_nonneg n)) (envelope_integrable n)
    _ = _ := envelope_integral n

lemma unit_norms {z z' w w' : ℂ} (h : (z-z')*(w-w')=1) :
    ‖z-z'‖ = exp (-(-log ‖z-z'‖)) ∧ ‖w-w'‖ = exp (-log ‖z-z'‖) := by
  have hz : z-z' ≠ 0 := by intro he; rw [he,zero_mul] at h; exact zero_ne_one h
  have hn : 0 < ‖z-z'‖ := norm_pos_iff.mpr hz
  have hh := congrArg norm h
  rw [norm_mul,norm_one] at hh
  constructor
  · rw [neg_neg,exp_log hn]
  · rw [exp_neg,exp_log hn]
    apply mul_left_cancel₀ (ne_of_gt hn)
    rw [hh,mul_inv_cancel₀ (ne_of_gt hn)]

variable {E : Type*} [Fintype E]

theorem exists_shifts (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e) (hμ₁ : ∑ e, μ e = 1)
    (z z' w w' : E → ℂ) (hu : ∀ e, (z e-z' e)*(w e-w' e)=1) (l r : ℝ) :
    ∃ u : Shifts, (∑ e, μ e * ∫ s in Icc l r,
      error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u) ≤ 2*log 2+4 := by
  let F : Shifts → ℝ := fun u => ∑ e, μ e * ∫ s in Icc l r,
    error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u
  have hi (e : E) : Integrable (fun u => ∫ s in Icc l r,
      error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u) shiftLaw :=
    (product_error_integrable _ _ _ _ _ _ _).integral_prod_right
  have hf : Integrable F shiftLaw :=
    integrable_finsetSum _ (fun e _ => (hi e).const_mul (μ e))
  obtain ⟨u,hu'⟩ := exists_le_integral hf
  refine ⟨u,hu'.trans ?_⟩
  change (∫ u, (∑ e, μ e * (∫ s in Icc l r,
    error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u)) ∂shiftLaw) ≤ _
  rw [integral_finsetSum _ (fun e _ => (hi e).const_mul (μ e))]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ e, μ e*(2*log 2+4) := Finset.sum_le_sum (fun e _ =>
      mul_le_mul_of_nonneg_left (mean_integrated_error_le (unit_norms (hu e)).1 (unit_norms (hu e)).2) (hμ e))
    _ = _ := by rw [← Finset.sum_mul,hμ₁,one_mul]

lemma gridLabel_fract_eq_iff (r : ℝ) (z z' : ℂ) (u : ℝ × ℝ) :
    gridLabel r z (Int.fract u.1, Int.fract u.2) =
      gridLabel r z' (Int.fract u.1, Int.fract u.2) ↔
    gridLabel r z u = gridLabel r z' u := by
  have h (x a : ℝ) : ⌊x+Int.fract a⌋ = ⌊x+a⌋-⌊a⌋ := by
    rw [Int.fract,← add_sub_assoc,Int.floor_sub_intCast]
  simp only [gridLabel,Prod.mk.injEq,h,sub_left_inj]

def fractionalShifts (u : Shifts) : Shifts :=
  ((Int.fract u.1.1,Int.fract u.1.2),(Int.fract u.2.1,Int.fract u.2.2))

lemma error_fractionalShifts (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) :
    error n s z z' w w' (fractionalShifts u) = error n s z z' w w' u := by
  classical
  simp only [error,consistent,fractionalShifts,ne_eq,gridLabel_fract_eq_iff]

def Fractional (u : Shifts) : Prop :=
  u.1.1 ∈ Ico (0:ℝ) 1 ∧ u.1.2 ∈ Ico (0:ℝ) 1 ∧
  u.2.1 ∈ Ico (0:ℝ) 1 ∧ u.2.2 ∈ Ico (0:ℝ) 1

theorem exists_fractionalShifts (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e)
    (hμ₁ : ∑ e, μ e = 1) (z z' w w' : E → ℂ)
    (hu : ∀ e, (z e-z' e)*(w e-w' e)=1) (l r : ℝ) :
    ∃ u : Shifts, Fractional u ∧ (∑ e, μ e * ∫ s in Icc l r,
      error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u) ≤ 2*log 2+4 := by
  obtain ⟨u,hu'⟩ := exists_shifts μ hμ hμ₁ z z' w w' hu l r
  refine ⟨fractionalShifts u,?_,?_⟩
  · exact ⟨⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩⟩
  · simpa only [error_fractionalShifts] using hu'

lemma norm_le_sqrt_two_of_same_grid {r : ℝ} (hr : 0 < r)
    {z w : ℂ} {u : ℝ × ℝ} (h : gridLabel r z u = gridLabel r w u) :
    ‖z-w‖ ≤ Real.sqrt 2*r := by
  have hx := abs_sub_lt_one_of_floor_eq (congrArg Prod.fst h)
  have hy := abs_sub_lt_one_of_floor_eq (congrArg Prod.snd h)
  rw [add_sub_add_right_eq_sub,← sub_div,abs_div,abs_of_pos hr,div_lt_one hr] at hx hy
  have hx₂ : (z.re-w.re)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z.re-w.re)) hr.le).mpr hx.le
  have hy₂ : (z.im-w.im)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z.im-w.im)) hr.le).mpr hy.le
  have hn := Complex.sq_norm (z-w)
  rw [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hn
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hb : 0 ≤ Real.sqrt 2*r := mul_nonneg (Real.sqrt_nonneg _) hr.le
  nlinarith [norm_nonneg (z-w)]

def localSetoid {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) : Setoid K :=
  { r := fun x y => v (x-y) ≤ exp s
    iseqv := ⟨by intro x; simpa using (exp_pos s).le,
      by intro x y h; rwa [v.map_sub],
      by
        intro x y z h₁ h₂
        have he : x-z = (x-y)+(y-z) := by ring
        rw [he]; exact (hv _ _).trans (max_le h₁ h₂)⟩ }

def nonarchConsistent {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (n s : ℝ) (z z' w w' : K) : Prop :=
  if s < n then
    Quotient.mk (localSetoid v hv (-s)) z = Quotient.mk _ z' ∧
    Quotient.mk (localSetoid v hv s) w ≠ Quotient.mk _ w'
  else
    Quotient.mk (localSetoid v hv (-s)) z ≠ Quotient.mk _ z' ∧
    Quotient.mk (localSetoid v hv s) w = Quotient.mk _ w'

lemma nonarch_unit_scales {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {z z' w w' : K} (h : (z-z')*(w-w')=1) :
    v (z-z') = exp (-(-log (v (z-z')))) ∧ v (w-w') = exp (-log (v (z-z'))) := by
  have hz : z-z' ≠ 0 := by intro he; rw [he,zero_mul] at h; exact zero_ne_one h
  have hn : 0 < v (z-z') := v.pos hz
  have hh := congrArg v h
  rw [v.map_mul,v.map_one] at hh
  constructor
  · rw [neg_neg,exp_log hn]
  · rw [exp_neg,exp_log hn]
    apply mul_left_cancel₀ (ne_of_gt hn)
    rw [hh,mul_inv_cancel₀ (ne_of_gt hn)]

theorem nonarch_consistent_off_boundary {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {z z' w w' : K}
    (hu : (z-z')*(w-w')=1) {s : ℝ} (hs : s ≠ -log (v (z-z'))) :
    nonarchConsistent v hv (-log (v (z-z'))) s z z' w w' := by
  obtain ⟨hz,hw⟩ := nonarch_unit_scales v hu
  unfold nonarchConsistent
  split_ifs with hsn
  · constructor
    · rw [Quotient.eq]
      change v (z-z') ≤ exp (-s)
      rw [hz,exp_le_exp]; linarith
    · rw [ne_eq,Quotient.eq]
      change ¬v (w-w') ≤ exp s
      rw [hw,not_le,exp_lt_exp]; exact hsn
  · constructor
    · rw [ne_eq,Quotient.eq]
      change ¬v (z-z') ≤ exp (-s)
      rw [hz,not_le,exp_lt_exp]
      exact neg_lt_neg (lt_of_le_of_ne (le_of_not_gt hsn) (Ne.symm hs))
    · rw [Quotient.eq]
      change v (w-w') ≤ exp s
      rw [hw,exp_le_exp]; exact le_of_not_gt hsn

end
end PlanarUnitDistances.StateConsistency

namespace PlanarUnitDistances.FiniteStates
open MeasureTheory Set Real
open scoped Classical
noncomputable section
variable {V : Type*}

def label (r : Setoid V) (x : V) : V → Bool := fun y => decide (r.r x y)
lemma label_eq_iff (r : Setoid V) (x y : V) : label r x=label r y ↔ r.r x y := by
  constructor
  · intro he
    have hh := congrFun he y
    simpa only [label,r.refl y,decide_true,decide_eq_true_eq] using hh
  · intro h
    funext z
    apply Bool.decide_congr
    exact ⟨fun hx => r.trans (r.symm h) hx,fun hy => r.trans h hy⟩

lemma measurable_label {Ω : Type*} [MeasurableSpace Ω]
    (r : Ω → Setoid V) (hr : ∀x y,MeasurableSet {s | (r s).r x y}) (x : V) :
    Measurable (fun s => label (r s) x) := by
  apply measurable_pi_iff.mpr
  intro y
  show Measurable (fun s => decide ((r s).r x y))
  have he : (fun s => decide ((r s).r x y)) =
      (fun s => if (r s).r x y then true else false) := by
    funext s; split_ifs <;> simp_all
  rw [he]
  exact Measurable.ite (hr x y) measurable_const measurable_const

def archRel (z : V → ℂ) (u : ℝ×ℝ) (s : ℝ) : Setoid V :=
  Setoid.ker (fun v => GridShift.gridLabel (exp s) (z v) u)

def archState (z w : V → ℂ) (u : StateConsistency.Shifts) (s : ℝ) (v : V) :
    (V → Bool)×(V → Bool) := (label (archRel z u.1 (-s)) v,label (archRel w u.2 s) v)

lemma archRel_measurable (z : V → ℂ) (u : ℝ×ℝ) :
    ∀x y,MeasurableSet {s | (archRel z u s).r x y} := by
  intro x y
  have hm (v : V) : Measurable (fun s => GridShift.gridLabel (exp s) (z v) u) := by
    apply Measurable.prodMk
    · exact ((measurable_const.div measurable_exp).add_const _).floor
    · exact ((measurable_const.div measurable_exp).add_const _).floor
  exact measurableSet_eq_fun (hm x) (hm y)
lemma archState_measurable (z w : V → ℂ) (u : StateConsistency.Shifts) (v : V) :
    Measurable (fun s => archState z w u s v) :=
  ((measurable_label _ (archRel_measurable z u.1) v).comp measurable_neg).prodMk
    (measurable_label _ (archRel_measurable w u.2) v)

lemma archState_consistent_iff (z w : V → ℂ) (u : StateConsistency.Shifts) (s n : ℝ) (x y : V) :
    CrossStructure.Consistent (decide (s<n)) (archState z w u s x) (archState z w u s y) ↔
      StateConsistency.consistent n s (z x) (z y) (w x) (w y) u := by
  unfold CrossStructure.Consistent StateConsistency.consistent archState
  simp only [label_eq_iff,archRel,Setoid.ker_def]
  by_cases hs : s<n <;> simp [hs,label_eq_iff,Setoid.ker_def]

def finiteRel {K : Type*} [Field K] (z : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) : Setoid V :=
  Setoid.comap z (StateConsistency.localSetoid v hv s)

def finiteState {K : Type*} [Field K] (z w : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) (x : V) : (V → Bool)×(V → Bool) :=
  (label (finiteRel z v hv (-s)) x,label (finiteRel w v hv s) x)

lemma finiteRel_measurable {K : Type*} [Field K] (z : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) : ∀x y,MeasurableSet {s | (finiteRel z v hv s).r x y} := by
  intro x y
  exact measurableSet_le measurable_const measurable_exp
lemma finiteState_measurable {K : Type*} [Field K] (z w : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : V) : Measurable (fun s => finiteState z w v hv s x) :=
  ((measurable_label _ (finiteRel_measurable z v hv) x).comp measurable_neg).prodMk
    (measurable_label _ (finiteRel_measurable w v hv) x)
lemma finiteState_consistent {K : Type*} [Field K] (z w : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {x y : V} (hu : (z x-z y)*(w x-w y)=1)
    {s : ℝ} (hs : s≠-log (v (z x-z y))) :
    CrossStructure.Consistent (decide (s< -log (v (z x-z y))))
      (finiteState z w v hv s x) (finiteState z w v hv s y) := by
  have hc := StateConsistency.nonarch_consistent_off_boundary v hv hu hs
  unfold CrossStructure.Consistent finiteState
  simp only [label_eq_iff,finiteRel,Setoid.comap_rel,StateConsistency.localSetoid]
  unfold StateConsistency.nonarchConsistent at hc
  split_ifs at hc with h
  · simp only [h,decide_true,↓reduceIte,ne_eq,label_eq_iff]
    exact ⟨Quotient.exact hc.1,fun he => hc.2 (Quotient.sound he)⟩
  · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,ne_eq,label_eq_iff]
    exact ⟨fun he => hc.1 (Quotient.sound he),Quotient.exact hc.2⟩
end
end PlanarUnitDistances.FiniteStates

namespace PlanarUnitDistances.FiniteLevels
open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

def measure (weight : ℝ≥0) (l u : J → ℝ) : Measure (J × ℝ) :=
  ∑ j, weight • Measure.map (fun s : ℝ => (j,s))
    (volume.restrict (Icc (l j) (u j)))

instance measure_finite (weight : ℝ≥0) (l u : J → ℝ) :
    IsFiniteMeasure (measure weight l u) := by
  unfold measure
  infer_instance

omit [MeasurableSingletonClass J] in
lemma integrable (weight : ℝ≥0) (l u : J → ℝ) (f : J × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀x, |f x| ≤ M) :
    Integrable f (measure weight l u) := by
  apply Integrable.mono' (integrable_const M)
    hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x

omit [MeasurableSingletonClass J] in
lemma integral_eq (weight : ℝ≥0) (l u : J → ℝ) (f : J × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀x, |f x| ≤ M) :
    (∫x, f x ∂measure weight l u) =
      (weight : ℝ) * ∑ j, ∫ s in Icc (l j) (u j), f (j,s) := by
  have hm (j : J) : Measurable (fun s : ℝ => (j,s)) :=
    measurable_const.prodMk measurable_id
  have hi (j : J) : Integrable f
      (Measure.map (fun s : ℝ => (j,s)) (volume.restrict (Icc (l j) (u j)))) := by
    apply Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x
  unfold measure
  rw [integral_finsetSum_measure (fun j _ => (hi j).smul_measure_nnreal (c := weight))]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact integral_map (hm j).aemeasurable hf.aestronglyMeasurable

lemma measurable_pieces {Y : Type*} [MeasurableSpace Y] (f : J → ℝ → Y) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x : J × ℝ => f x.1 x.2) := by
  exact measurable_from_prod_countable_right (fun j => hf j)

end
end PlanarUnitDistances.FiniteLevels

namespace PlanarUnitDistances.BudgetPlaces
open Real Finset
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

def threshold (v : AbsoluteValue K ℝ) (d : K) : ℝ := -log (v d)
def alpha (v : AbsoluteValue K ℝ) (d d' : K) : ℝ :=
  threshold v (d-d')-min (threshold v d) (threshold v d')
def differenceProduct (d d' : K) : K := (d-d')*(d⁻¹-d'⁻¹)

lemma differenceProduct_ne_zero {d d' : K} (h : d ≠ d') :
    differenceProduct d d' ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr h) (sub_ne_zero.mpr (inv_injective.ne h))

lemma inv_difference_abs (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) :
    v (d⁻¹-d'⁻¹) = v (d-d')/(v d*v d') := by
  have he : d⁻¹-d'⁻¹ = -(d-d')/(d*d') := by field_simp; ring
  rw [he,map_div₀,v.map_neg,v.map_mul]

theorem place_identity (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    -log (v (differenceProduct d d')) =
      2*alpha v d d'-(max (threshold v d) (threshold v d')-
        min (threshold v d) (threshold v d')) := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have hdv := v.pos hd
  have hdv' := v.pos hd'
  have hI := v.pos (sub_ne_zero.mpr (inv_injective.ne hdd))
  rw [differenceProduct,v.map_mul,log_mul hD.ne' hI.ne',inv_difference_abs v hd hd',
    log_div hD.ne' (mul_ne_zero hdv.ne' hdv'.ne'),log_mul hdv.ne' hdv'.ne']
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

lemma alpha_nonneg_nonarch (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d' := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ max (v d) (v d') := by
    simpa only [sub_eq_add_neg,v.map_neg] using hv d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · rw [max_eq_right hh] at htri
    have hlog := log_le_log (v.pos hd) hh
    rw [min_eq_right (by linarith)]
    linarith [log_le_log hD htri]
  · have hh' := (le_of_not_ge hh)
    rw [max_eq_left hh'] at htri
    have hlog := log_le_log (v.pos hd') hh'
    rw [min_eq_left (by linarith)]
    linarith [log_le_log hD htri]

lemma alpha_add_log_two_nonneg (v : AbsoluteValue K ℝ)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d'+log 2 := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ v d+v d' := by
    simpa only [sub_eq_add_neg,v.map_neg] using v.add_le d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · have hlog := log_le_log (v.pos hd) hh
    have ht : v (d-d') ≤ 2*v d' := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd').ne'] at hLt
    rw [min_eq_right (by linarith)]
    linarith
  · have hh' := (le_of_not_ge hh)
    have hlog := log_le_log (v.pos hd') hh'
    have ht : v (d-d') ≤ 2*v d := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd).ne'] at hLt
    rw [min_eq_left (by linarith)]
    linarith

section Global
open PlanarUnitDistances.WeightedAbsoluteValues
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

theorem score_product_formula {d d' : K} (hd : d ≠ 0)
    (hd' : d' ≠ 0) (hdd : d ≠ d') :
    ((∑ σ : K →ₐ[ℚ] ℂ,
        (2*alpha (infiniteEntry K σ) d d'-
          (max (threshold (infiniteEntry K σ) d) (threshold (infiniteEntry K σ) d')-
           min (threshold (infiniteEntry K σ) d) (threshold (infiniteEntry K σ) d')))) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ),
        (2*alpha (finiteEntry K v.1 v.2) d d'-
          (max (threshold (finiteEntry K v.1 v.2) d) (threshold (finiteEntry K v.1 v.2) d')-
           min (threshold (finiteEntry K v.1 v.2) d) (threshold (finiteEntry K v.1 v.2) d'))))) /
      (Module.finrank ℚ K : ℝ) = 0 := by
  simp_rw [← place_identity _ hd hd' hdd]
  rw [sum_neg_distrib,finsum_neg_distrib,← neg_add,neg_div]
  rw [weighted_log_product_formula K (differenceProduct_ne_zero hdd),neg_zero]

omit [IsGalois ℚ K] in

theorem arch_allowance :
    (∑ _σ : K →ₐ[ℚ] ℂ, 2*log 2)/(Module.finrank ℚ K : ℝ) = 2*log 2 := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  simp only [sum_const,card_univ,nsmul_eq_mul,infiniteEntry_count]
  field_simp

end Global
end
end PlanarUnitDistances.BudgetPlaces

namespace PlanarUnitDistances.PlaceLevels
open Finset Real WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def finiteSupport (S : Finset K) : Finset (Nat.Primes × Gal(K/ℚ)) :=
  S.biUnion fun x => ((rootDenominators K x ∪ rootDenominators K x⁻¹).subtype Nat.Prime) ×ˢ univ

lemma log_off_support {S : Finset K} {x : K} (hx : x∈S)
    {v : Nat.Primes × Gal(K/ℚ)} (hv : v∉finiteSupport K S) :
    log (finiteEntry K v.1 v.2 x)=0 := by
  by_cases h0 : x=0
  · simp [h0]
  have hp : v.1.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹ := by
    intro hh
    apply hv
    exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_subtype.mpr hh,mem_univ _⟩⟩
  rw [finiteEntry_eq_one_off_support K h0 _ _ hp,log_one]

abbrev Place (S : Finset K) := (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S)
instance (S : Finset K) : Fintype (Place K S) := inferInstanceAs (Fintype (_ ⊕ _))
instance (S : Finset K) : MeasurableSpace (Place K S) := ⊤
instance (S : Finset K) : MeasurableSingletonClass (Place K S) := ⟨fun _ => trivial⟩

def av {S : Finset K} : Place K S → AbsoluteValue K ℝ
  | .inl σ => infiniteEntry K σ
  | .inr v => finiteEntry K v.val.1 v.val.2

def radius (S : Finset K) (v : Place K S) : ℝ := ∑x∈S, |log (av K v x)|
lemma radius_nonneg (S : Finset K) (v : Place K S) : 0≤radius K S v :=
  sum_nonneg (fun _ _ => abs_nonneg _)
lemma log_le_radius {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    |log (av K v x)|≤radius K S v := by
  exact single_le_sum (fun y _ => abs_nonneg (log (av K v y))) hx
lemma threshold_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ -log (av K v x) ∧ -log (av K v x) ≤ radius K S v := by
  have h := abs_le.mp (log_le_radius K hx v)
  constructor <;> linarith
lemma log_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ log (av K v x) ∧ log (av K v x) ≤ radius K S v :=
  abs_le.mp (log_le_radius K hx v)

lemma sum_logs {S : Finset K} {x : K} (hx : x∈S) :
    (∑v : Place K S,log (av K v x)) =
      (∑σ : K →ₐ[ℚ] ℂ,log (infiniteEntry K σ x))+
      ∑ᶠv : Nat.Primes × Gal(K/ℚ), log (finiteEntry K v.1 v.2 x) := by
  change (∑v : (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S),log (av K v x))=_
  rw [Fintype.sum_sum_type]
  congr 1
  change (∑v : ↥(finiteSupport K S), log (finiteEntry K v.val.1 v.val.2 x))=_
  rw [Finset.sum_coe_sort (finiteSupport K S) (fun v => log (finiteEntry K v.1 v.2 x))]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  by_contra hs
  exact hv (log_off_support K hx hs)

lemma sum_log_product_formula [IsGalois ℚ K] {S : Finset K} {x : K}
    (hx : x∈S) (h0 : x≠0) :
    (∑v : Place K S,log (av K v x))/(Module.finrank ℚ K:ℝ)=0 := by
  rw [sum_logs K hx]
  exact weighted_log_product_formula K h0
end
end PlanarUnitDistances.PlaceLevels

end OAI
