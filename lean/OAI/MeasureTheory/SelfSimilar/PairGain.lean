import OAI.MeasureTheory.SelfSimilar.Conditioning

namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def shiftLaw (μ : Measure ℝ) (b : ℝ) : Measure ℝ := μ.map (fun x => x+b)

instance shiftLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    IsProbabilityMeasure (shiftLaw μ b) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const b).aemeasurable).2 inferInstance

theorem CompactlyCarried.shiftLaw {μ : Measure ℝ} (hμ : CompactlyCarried μ) (b : ℝ) :
    CompactlyCarried (shiftLaw μ b) := by simpa only [one_mul,MeasureEntropy.shiftLaw] using hμ.map_affine 1 b

theorem shiftLaw_add (μ : Measure ℝ) (a b : ℝ) :
    shiftLaw (shiftLaw μ a) b = shiftLaw μ (a+b) := by
  unfold shiftLaw
  rw [Measure.map_map (g := fun x : ℝ => x+b) (f := fun x : ℝ => x+a) (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [add_assoc]

noncomputable def window (μ : Measure ℝ) (s t : ℝ) : ℝ := averaged μ s-averaged μ t

theorem window_shiftLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (b : ℝ) :
    window (shiftLaw μ b) s t = window μ s t := by
  simp only [window,shiftLaw,averaged_translate μ hμ hs,averaged_translate μ hμ ht]

noncomputable def pairLaw (μ : Measure ℝ) (x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/2 : ℝ) • shiftLaw μ x+ENNReal.ofReal (1/2 : ℝ) • shiftLaw μ y

instance pairLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (x y : ℝ) :
    IsProbabilityMeasure (pairLaw μ x y) := by
  constructor
  simpa [pairLaw,Measure.add_apply,Measure.smul_apply,measure_univ] using ENNReal.inv_two_add_inv_two

theorem CompactlyCarried.pairLaw {μ : Measure ℝ} (hμ : CompactlyCarried μ) (x y : ℝ) :
    CompactlyCarried (pairLaw μ x y) := by
  have hh := CompactlyCarried.mixture (fun i : Fin 2 => MeasureEntropy.shiftLaw μ (if i=0 then x else y))
    (fun i => hμ.shiftLaw _) (fun _ => (1/2 : ℝ))
  simpa [Fin.sum_univ_two,MeasureEntropy.pairLaw] using hh

theorem pairLaw_comm (μ : Measure ℝ) (x y : ℝ) : pairLaw μ x y=pairLaw μ y x := add_comm _ _

theorem pairLaw_eq_shift_fair (μ : Measure ℝ) (x y : ℝ) :
    pairLaw μ x y = shiftLaw (fairShift μ (y-x)) x := by
  simp only [pairLaw,shiftLaw,fairShift,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
    Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
  rw [Measure.map_add _ _ (by fun_prop),
    Measure.map_smul (f := fun z : ℝ => z+x) _ (by fun_prop),
    Measure.map_smul (f := fun z : ℝ => z+x) _ (by fun_prop),
    Measure.map_map (g := fun z : ℝ => z+x) (f := fun z : ℝ => z) (by fun_prop) (by fun_prop),
    Measure.map_map (g := fun z : ℝ => z+x) (f := fun z : ℝ => z+(y-x)) (by fun_prop) (by fun_prop)]
  have he : (fun z : ℝ => z+x) ∘ (fun z => z+(y-x))=(fun z => z+y) := by
    funext z; simp; ring
  rw [he]
  rfl

theorem pairLaw_gain (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s t x y : ℝ} (hs : 0 < s) (hsv : s < |y-x|) (hvt : |y-x| < t) :
    deficit μ |y-x|-(s/|y-x|+|y-x|/t)*Real.log 2 ≤
      window (pairLaw μ x y) s t-window μ s t := by
  have hv : 0 < |y-x| := hs.trans hsv
  have ht : 0 < t := hv.trans hvt
  let (v : ℝ) : IsProbabilityMeasure (fairShift μ v) := fairShift_probability μ v
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at *
    rw [pairLaw_eq_shift_fair,window_shiftLaw _ (hμ.fairShift _) hs ht]
    exact two_point_gain μ hμ hs hsv hvt
  · have he : |y-x|=x-y := by rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hsv' : s < x-y := he ▸ hsv
    have hvt' : x-y < t := he ▸ hvt
    rw [he,pairLaw_comm,pairLaw_eq_shift_fair,window_shiftLaw _ (hμ.fairShift _) hs ht]
    exact two_point_gain μ hμ hs hsv' hvt'

noncomputable def finiteConv (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ∑ x : ν.support, ENNReal.ofReal (ν.prob x) • shiftLaw μ (a*x)

instance finiteConv_probability (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (finiteConv ν a μ) :=
  mixture_probability _ _ (fun x => (ν.prob_pos x x.property).le) ν.subtype_sum

theorem CompactlyCarried.finiteConv {μ : Measure ℝ} (hμ : CompactlyCarried μ)
    (ν : FairPairs.Law) (a : ℝ) : CompactlyCarried (finiteConv ν a μ) :=
  CompactlyCarried.mixture _ (fun _ => hμ.shiftLaw _) _

theorem finiteConv_window_mono (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    window μ s (N*s) ≤ window (finiteConv ν a μ) s (N*s) :=
  averaged_nested_translate_mixture μ hμ (fun x : ν.support => ν.prob x)
    (fun x => (ν.prob_pos x x.property).le) ν.subtype_sum (fun x => a*x) hs hN

theorem deficit_mixture {α : Type uα} [Fintype α]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : α → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, CompactlyCarried (ν i))
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (hm : μ=∑ i, ENNReal.ofReal (p i) • ν i) {v : ℝ} (hv : 0 < v) :
    deficit μ v ≤ ∑ i, p i*deficit (ν i) v := by
  have hh := averaged_nested_mixture μ hμ ν hν p hp hm hv (by norm_num : 0 < (2 : ℕ))
  simp only [deficit,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hp1,one_mul]
  push_cast at hh
  simp only [mul_sub,Finset.sum_sub_distrib] at hh
  linarith

theorem deficit_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {v a : ℝ} (hv : 0 < v) (ha : a ≠ 0) :
    deficit (μ.map (fun x => a*x)) v=deficit μ (v/|a|) := by
  rw [deficit,averaged_scale μ hμ hv ha,averaged_scale μ hμ (by positivity) ha,deficit]
  congr 2
  ring_nf

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.FairPairs
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

theorem incident_smul_sum (ν : Law) (ℓ : ℤ) (w : ν.edges ℓ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (f : ℝ → Measure ℝ) :
    (∑ x ∈ ν.support, ENNReal.ofReal (incident w x) • f x) =
      ∑ e, (ENNReal.ofReal (w e/2) • f e.val.1+ENNReal.ofReal (w e/2) • f e.val.2) := by
  classical
  have hw2 : ∀ e, 0 ≤ w e/2 := fun e => div_nonneg (hw e) (by norm_num)
  have hv : ∀ x e, 0 ≤ (if e.val.1=x then w e/2 else 0)+(if e.val.2=x then w e/2 else 0) := by
    intro x e
    have hwe := hw2 e
    split_ifs <;> positivity
  simp only [incident,ENNReal.ofReal_sum_of_nonneg (fun e _ => hv _ e),Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hh : ∀ x, ENNReal.ofReal ((if e.val.1=x then w e/2 else 0)+
      (if e.val.2=x then w e/2 else 0)) • f x =
      (if e.val.1=x then ENNReal.ofReal (w e/2) • f e.val.1 else 0)+
      (if e.val.2=x then ENNReal.ofReal (w e/2) • f e.val.2 else 0) := by
    intro x
    have hwe := hw2 e
    rw [ENNReal.ofReal_add (by split_ifs <;> positivity) (by split_ifs <;> positivity)]
    rw [add_smul]
    congr 1 <;> split_ifs <;> simp_all only [ENNReal.ofReal_zero,zero_smul]
  simp_rw [hh,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,edge_mem_left e,edge_mem_right e,ite_true]

noncomputable def residual {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) (x : ν.support) : ℝ :=
  ν.prob x-incident w x

theorem residual_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w)
    (x : ν.support) : 0 ≤ residual w x := sub_nonneg.mpr (hw.2 x x.property)

theorem residual_total {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    (∑ x : ν.support, residual w x)+(∑ e, w e)=1 := by
  classical
  simp only [residual,Finset.sum_sub_distrib,ν.subtype_sum,
    Finset.sum_coe_sort ν.support (fun x => incident w x),incident_sum]
  ring

noncomputable def decompositionWeight {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ν.edges ℓ ⊕ ν.support → ℝ := Sum.elim w (residual w)

noncomputable def decompositionLaw {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) (a : ℝ) :
    ν.edges ℓ ⊕ ν.support → Measure ℝ := Sum.elim
      (fun e => pairLaw μ (a*e.val.1) (a*e.val.2))
      (fun x => shiftLaw μ (a*x))

theorem decompositionWeight_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∀ z, 0 ≤ decompositionWeight w z := by
  intro z
  cases z with
  | inl e => exact hw.1 e
  | inr x => exact residual_nonneg hw x

theorem decompositionWeight_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ z, decompositionWeight w z=1 := by
  rw [Fintype.sum_sum_type]
  exact (add_comm _ _).trans (residual_total w)

instance decompositionLaw_probability {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (z : ν.edges ℓ ⊕ ν.support) : IsProbabilityMeasure (decompositionLaw μ a z) := by
  cases z <;> dsimp [decompositionLaw] <;> infer_instance

theorem decompositionLaw_compact {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) (hμ : CompactlyCarried μ)
    (a : ℝ) (z : ν.edges ℓ ⊕ ν.support) : CompactlyCarried (decompositionLaw μ a z) := by
  cases z with
  | inl e => exact hμ.pairLaw _ _
  | inr x => exact hμ.shiftLaw _

theorem finiteConv_decomposition (ν : Law) (ℓ : ℤ) (w : ν.edges ℓ → ℝ) (hw : Feasible w)
    (μ : Measure ℝ) (a : ℝ) :
    finiteConv ν a μ = ∑ z, ENNReal.ofReal (decompositionWeight w z) • decompositionLaw μ a z := by
  classical
  rw [Fintype.sum_sum_type]
  change finiteConv ν a μ=(∑ e, ENNReal.ofReal (w e) • pairLaw μ (a*e.val.1) (a*e.val.2))+
    ∑ x : ν.support, ENNReal.ofReal (residual w x) • shiftLaw μ (a*x)
  have he : ∀ e : ν.edges ℓ, ENNReal.ofReal (w e) • pairLaw μ (a*e.val.1) (a*e.val.2)=
      ENNReal.ofReal (w e/2) • shiftLaw μ (a*e.val.1)+
      ENNReal.ofReal (w e/2) • shiftLaw μ (a*e.val.2) := by
    intro e
    simp only [pairLaw,smul_add,smul_smul,← ENNReal.ofReal_mul (hw.1 e)]
    congr 2 <;> congr 1 <;> ring
  simp_rw [he]
  rw [← incident_smul_sum ν ℓ w hw.1 (fun x => shiftLaw μ (a*x)),← Finset.sum_coe_sort ν.support (fun x =>
    ENNReal.ofReal (incident w x) • shiftLaw μ (a*x)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hi : 0 ≤ incident w x := by
    apply Finset.sum_nonneg
    intro e _
    have hre := hw.1 e
    split_ifs <;> positivity
  rw [← add_smul,← ENNReal.ofReal_add hi (residual_nonneg hw x)]
  simp only [residual,add_sub_cancel]

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory FairPairs
open scoped BigOperators ENNReal

theorem finiteConv_gain (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ) {ℓ : ℤ}
    (w : ν.edges ℓ → ℝ) (hw : FairPairs.Feasible w)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s) :
    (∑ e, w e*(deficit μ |a*e.val.2-a*e.val.1|-
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) ≤
      window (finiteConv ν a μ) s (N*s)-window μ s (N*s) := by
  classical
  have ht : 0 < (N : ℝ)*s := mul_pos (by exact_mod_cast hN) hs
  have hh := averaged_nested_mixture (finiteConv ν a μ) (hμ.finiteConv ν a)
    (decompositionLaw (ν := ν) (ℓ := ℓ) μ a) (decompositionLaw_compact μ hμ a)
    (decompositionWeight w) (decompositionWeight_nonneg hw)
    (finiteConv_decomposition ν ℓ w hw μ a) hs hN
  change (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s)) ≤ _ at hh
  have hid : (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s))-
      window μ s (N*s) =
      ∑ e, w e*(window (pairLaw μ (a*e.val.1) (a*e.val.2)) s (N*s)-window μ s (N*s)) := by
    calc
      _ = (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s))-
          ∑ z, decompositionWeight w z*window μ s (N*s) := by
        rw [← Finset.sum_mul,decompositionWeight_sum,one_mul]
      _ = ∑ z, decompositionWeight w z*(window (decompositionLaw μ a z) s (N*s)-
          window μ s (N*s)) := by simp only [mul_sub,Finset.sum_sub_distrib]
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp only [decompositionWeight,decompositionLaw,Sum.elim_inl,Sum.elim_inr,
          window_shiftLaw μ hμ hs ht,sub_self,mul_zero,Finset.sum_const_zero,add_zero]
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun (e : ν.edges ℓ) _ =>
    mul_le_mul_of_nonneg_left (pairLaw_gain μ hμ hs (hv e).1 (hv e).2) (hw.1 e))
  rw [← hid] at hl
  exact hl.trans (sub_le_sub_right hh _)

theorem finiteConv_mean_gain {β : Type uβ} [Fintype β]
    (ν : FairPairs.Law) (a b : ℝ) (hb : b ≠ 0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (τ : β → Measure ℝ) [∀ z, IsProbabilityMeasure (τ z)]
    (hτ : ∀ z, CompactlyCarried (τ z))
    (p : β → ℝ) (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z=1)
    (hm : μ.map (fun x => b*x) = ∑ z, ENNReal.ofReal (p z) • τ z)
    {δ η s : ℝ} (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (ℓ : ℤ)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s)
    (herr : ∀ e : ν.edges ℓ,
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2 ≤ η) :
    (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ z, p z*(window (finiteConv ν a (τ z)) s (N*s)-window (τ z) s (N*s)) := by
  classical
  obtain ⟨w,hw,he⟩ := FairPairs.capacity_attained ν ℓ
  let : IsProbabilityMeasure (μ.map (fun x => b*x)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance
  have hmcomp : CompactlyCarried (μ.map (fun x => b*x)) := by
    simpa only [add_zero] using hμ.map_affine b 0
  have hdef (e : ν.edges ℓ) : δ ≤ ∑ z, p z*deficit (τ z) |a*e.val.2-a*e.val.1| := by
    have hpv := hs.trans (hv e).1
    have hd := deficit_mixture (μ.map (fun x => b*x)) hmcomp τ hτ p hp hp1 hm hpv
    rw [deficit_scale μ hμ hpv hb] at hd
    exact (hδ _ (div_pos hpv (abs_pos.mpr hb))).trans hd
  have hz (z : β) := finiteConv_gain ν a (τ z) (hτ z) w hw hs hN hv
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hz z) (hp z))
  simp_rw [Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  have hlo : (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ e, ∑ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) := by
    rw [← he,mul_comm,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    have hh : ∑ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) =
        w e*((∑ z, p z*deficit (τ z) |a*e.val.2-a*e.val.1|)-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2) := by
      simp_rw [show ∀ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) =
        w e*(p z*deficit (τ z) |a*e.val.2-a*e.val.1|)-
        w e*p z*((s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2) by intro z; ring]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,← Finset.mul_sum,hp1]
      ring
    rw [hh]
    exact mul_le_mul_of_nonneg_left (sub_le_sub (hdef e) (herr e)) (hw.1 e)
  exact hlo.trans hsum

end EntropyRateDimension.MeasureEntropy

end OAI
