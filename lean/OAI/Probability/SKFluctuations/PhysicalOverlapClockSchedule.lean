import Mathlib
import OAI.Probability.SKFluctuations.PhysicalForkSumMoments

namespace OAI

/-! Physical Overlap Clock Schedule. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_physical_overlap_clock_schedule (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (fork t : ℕ) (a D : Fin cs.length → ℝ),
      t ≤ steps.length+1 → lastLayerCut cs t=steps.length+1 →
      (∀ j : Fin cs.length, cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀ j, 0 < a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) →
      (∀ i j, i ≤ j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs t i) ≤ H*(a j)^2) →
    physicalOverlapMoment n (k+1) steps μ x hx fork ≤
      (2:ℝ)^(2*(k+1)-1) *
        (2*(physicalRawRatio n (k+1) steps c xs μ x hx)^(4*(k+1)) *
          (xs+physicalCutMass c steps t)^(2*(k+1)) +
          ((physicalOverlapResidualPairs cs).card:ℝ)^(2*(k+1)-1) *
            (((physicalOverlapResidualPairs cs).card:ℝ) *
              (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
                (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀))^(k+1))) := by
  filter_upwards [eventually_physical_overlap_layer_clock_moment k B,
    eventually_ge_atTop 1] with n hn hnpos
  intro P _ steps c D₀ xs H hD₀ hxs hH hs μ _ x hx cs fork t a D ht hlast hends hclock hscale
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let L := 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*Q^2*H/((n:ℝ)*D₀)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hordered : ∀ (i j : Fin (cs.length+1)), i ≤ j → (i,j)≠(0,0) →
      (physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t i j)^(((k+1:ℕ):ℝ)⁻¹) ≤ L := by
    intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij hne
      have hi : i=0 := le_antisymm hij (Fin.zero_le _)
      exact False.elim (hne (by simp only [hi]))
    · intro hij hne
      obtain ⟨ha,hD,hDB,hclk⟩ := hclock j
      have hh := hn P steps (a j) c (D j) xs ha (hD₀.trans_le hD) hDB hxs hs μ x hx
        cs fork t i j ht hends hclk
      apply hh.trans
      have hm := projection_weight_scale_bound (C := projectionLpConstant k) (z := Real.log (n:ℝ)) (Q := Q) hnp ha hD₀ hD (show (0:ℝ)≤1 by norm_num)
        (add_nonneg hxs.le (physicalCutMass_mem steps hs (overlapComponentEnd cs t i)).1) hH
        (by simpa only [one_mul] using hscale i j hij)
      simpa only [one_mul] using hm
  have hpairs : ∀ ij ∈ physicalOverlapResidualPairs cs,
      physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t ij.1 ij.2 ≤ L^(k+1) := by
    intro ij hij
    have hne : ij≠(0,0) := (Finset.mem_erase.mp hij).1
    have hr : (physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t ij.1 ij.2)^(((k+1:ℕ):ℝ)⁻¹) ≤ L := by
      rcases le_total ij.1 ij.2 with hij' | hji
      · exact hordered ij.1 ij.2 hij' hne
      · rw [physicalOverlapLayerMoment_swap n (k+1) steps hs μ x hx cs fork t ij.1 ij.2]
        apply hordered ij.2 ij.1 hji
        intro heq
        apply hne
        have ha := congrArg Prod.fst heq
        have hb := congrArg Prod.snd heq
        exact Prod.ext hb ha
    have hp := pow_le_pow_left₀
      (Real.rpow_nonneg (physicalOverlapLayerMoment_nonneg n (k+1) steps μ x hx cs fork t ij.1 ij.2) _) hr (k+1)
    rwa [Real.rpow_inv_natCast_pow
      (physicalOverlapLayerMoment_nonneg n (k+1) steps μ x hx cs fork t ij.1 ij.2) (Nat.succ_ne_zero k)] at hp
  apply (physicalOverlapMoment_le_double_sum n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx fork t ht cs hlast).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  have hh := Finset.sum_le_sum hpairs
  simpa only [physicalOverlapLayerMoment,Finset.sum_const, nsmul_eq_mul] using hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalProjectionClock_of_full_field_layer (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ}
    (hc : OrderedSteps c steps) (ha : 0 ≤ a)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i)=d st)
    {fork q v w : ℕ} (hf : fork ≤ q) (hq : q ≤ v) (hv : v ≤ w)
    (hvl : v ≤ steps.length) (hw : w ≤ steps.length+1)
    (ham : a ≤ physicalCutMass c steps q) :
    PhysicalProjectionClock n steps fork v w a (physicalFieldDuration d (cutSlice steps q v)) := by
  by_cases hw' : w ≤ steps.length
  · exact physicalProjectionClock_of_field_cuts n steps hc ha d hd hf hq hv hw' ham
  · have he : w=steps.length+1 := by omega
    subst w
    exact physicalProjectionClock_of_terminal_cuts n steps hc ha hf hq hvl ham
      (alignedFieldClock_slice n steps d hd q v)

 theorem overlap_unweighted_later_scale {s c₀ C qi qj S : ℝ}
    (hs : 0 < s) (hc₀ : 0 < c₀) (hC : 0 ≤ C)
    (hsj : s ≤ qj) (hij : qi ≤ qj) (hS : S ≤ C*qi) :
    S ≤ (C/(c₀^2*s))*(c₀*qj)^2 := by
  have hq : 0 ≤ qj := hs.le.trans hsj
  have he : (C/(c₀^2*s))*(c₀*qj)^2 = C*(qj^2/s) := by
    field_simp
  rw [he]
  apply hS.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply hij.trans
  apply (le_div_iff₀ hs).mpr
  nlinarith

 theorem eventually_physical_overlap_field_schedule (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs s c₀ C : ℝ),
      0 < D₀ → 0 < xs → 0 < s → 0 < c₀ → 0 ≤ C → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (fork t : ℕ) (q : Fin (cs.length+1) → ℝ) (pre : Fin cs.length → ℕ)
      (d : GaussianStep (FeatureIndex n) → ℝ≥0),
      t ≤ steps.length+1 → lastLayerCut cs t=steps.length+1 → Monotone q →
      (∀ j, s ≤ q j) →
      (∀ i, xs+physicalCutMass c steps (overlapComponentEnd cs t i) ≤ C*q i) →
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i)=d st) →
      physicalFieldDuration d steps ≤ B →
      (∀ j : Fin cs.length,
        fork ≤ pre j ∧ pre j ≤ cutPredecessor cs t j ∧
        cutPredecessor cs t j ≤ (cs.get j).2 ∧ cutPredecessor cs t j ≤ steps.length ∧
        (cs.get j).2 ≤ steps.length+1 ∧
        c₀*q j.succ ≤ physicalCutMass c steps (pre j) ∧
        D₀ ≤ physicalFieldDuration d (steps.take (cutPredecessor cs t j))-
          physicalFieldDuration d (steps.take (pre j))) →
    physicalOverlapMoment n (k+1) steps μ x hx fork ≤
      (2:ℝ)^(2*(k+1)-1) *
        (2*(physicalRawRatio n (k+1) steps c xs μ x hx)^(4*(k+1)) *
          (xs+physicalCutMass c steps t)^(2*(k+1)) +
          ((physicalOverlapResidualPairs cs).card:ℝ)^(2*(k+1)-1) *
            (((physicalOverlapResidualPairs cs).card:ℝ) *
              (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
                (physicalRawRatio n (k+1) steps c xs μ x hx)^2*(C/(c₀^2*s))/((n:ℝ)*D₀))^(k+1))) := by
  filter_upwards [eventually_physical_overlap_clock_schedule k B] with n hn
  intro P _ steps c D₀ xs s c₀ C hD₀ hxs hs hc₀ hC ho μ _ x hx cs fork t q pre d
    ht hlast hqm hq hupper hd hB hpre
  apply hn P steps c D₀ xs (C/(c₀^2*s)) hD₀ hxs (by positivity) ho μ x hx cs fork t
    (fun j => c₀*q j.succ) (fun j => physicalFieldDuration d (cutSlice steps (pre j) (cutPredecessor cs t j)))
    ht hlast
  · intro j
    exact ⟨(hpre j).2.2.1,(hpre j).2.2.2.2.1⟩
  · intro j
    obtain ⟨hf,hpv,hvw,hvl,hwl,ham,hD⟩ := hpre j
    have ha : 0 < c₀*q j.succ := mul_pos hc₀ (hs.trans_le (hq _))
    refine ⟨ha,?_,(physicalFieldDuration_slice_le d steps _ _).trans hB,?_⟩
    · rw [physicalFieldDuration_slice_eq d steps hpv]
      exact hD
    · exact physicalProjectionClock_of_full_field_layer n steps ho ha.le d hd hf hpv hvw hvl hwl ham
  · intro i j hij
    exact overlap_unweighted_later_scale hs hc₀ hC (hq _) (hqm hij) (hupper i)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem lastLayerCut_append_singleton (cs : List (ℝ × ℕ)) (a t : ℕ) (m : ℝ) :
    lastLayerCut (cs++[(m,t)]) a=t := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => exact ih c.2

 theorem lastLayerCut_ofFn {N : ℕ} (m : Fin N → ℝ) (t : Fin (N+1) → ℕ) :
    lastLayerCut (List.ofFn fun j => (m j,t j.succ)) (t 0) = t (Fin.last N) := by
  cases N with
  | zero => simp [lastLayerCut]
  | succ N =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,lastLayerCut_append_singleton,Fin.succ_last]

 theorem overlapComponentEnd_ofFn {N : ℕ} (m : Fin N → ℝ) (t : Fin (N+1) → ℕ)
    (i : Fin (N+1)) :
    overlapComponentEnd (List.ofFn fun j => (m j,t j.succ)) (t 0)
      (Fin.cast (by simp) i) = t i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [overlapComponentEnd,List.get_ofFn]
    rfl

 theorem physicalOverlapResidualPairs_card_le (cs : List (ℝ × ℕ)) :
    (physicalOverlapResidualPairs cs).card ≤ (cs.length+1)^2 := by
  have hh := Finset.card_erase_le (s := (Finset.univ : Finset (Fin (cs.length+1) × Fin (cs.length+1)))) (a := (0,0))
  simpa only [physicalOverlapResidualPairs,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,pow_two] using hh

end SKFluctuations

 

 

namespace SKFluctuations
open Hierarchy

 theorem PhysicalProjectionClock.earlier_fork {n : ℕ}
    {steps : List (GaussianStep (FeatureIndex n))} {fork v w fork' : ℕ} {a D : ℝ}
    (h : PhysicalProjectionClock n steps fork v w a D) (hf : fork' ≤ fork) :
    PhysicalProjectionClock n steps fork' v w a D := by
  cases h with
  | gaussian common tail mid pre skip a D ho hc =>
    have hh := PhysicalProjectionClock.gaussian (common.take fork') tail mid pre
      (common.drop fork'++skip) a D ho hc
    convert hh using 1
    · simp only [← List.append_assoc,List.take_append_drop]
    · simp only [List.length_take,Nat.min_eq_left hf]
    · simp only [List.length_append,List.length_drop,List.length_take,Nat.min_eq_left hf]
      omega
    · simp only [List.length_append,List.length_drop,List.length_take,Nat.min_eq_left hf]
      omega
  | terminal common tail pre skip a D ho hc =>
    have hh := PhysicalProjectionClock.terminal (common.take fork') tail pre
      (common.drop fork'++skip) a D ho hc
    convert hh using 1
    · simp only [← List.append_assoc,List.take_append_drop]
    · simp only [List.length_take,Nat.min_eq_left hf]
    · simp only [List.length_append,List.length_drop,List.length_take,Nat.min_eq_left hf]
      omega
    · simp only [List.length_append,List.length_drop,List.length_take,Nat.min_eq_left hf]
      omega

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalOverlapDyadicCertificates (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c c₀ xs s D₀ B C R F : ℝ}
    (hc : OrderedSteps c steps) (hc₀ : 0 < c₀) (hxs : 0 ≤ xs) (hxs_s : xs ≤ s)
    (hs : 0 < s) (hC : 0 ≤ C) (hR : 0 < R)
    (hF₁ : 1+2*C ≤ F) (hF₂ : 1+1/R ≤ F)
    {J : ℕ} (hJ : 1 ≤ J) (τ : ℝ → ℕ) (hτ : Monotone τ)
    (hL : ∀ r, τ r ≤ steps.length) (hRend : R ≤ (2:ℝ)^J*s)
    {fork : ℕ} (hf : fork ≤ τ s)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i)=d st)
    (hB : physicalFieldDuration d steps ≤ B)
    (hm : ∀ r ∈ Icc s ((2:ℝ)^J*s), c₀*r ≤ physicalCutMass c steps (τ r))
    (hM : ∀ r ∈ Icc s ((2:ℝ)^J*s), physicalCutMass c steps (τ r) ≤ C*r)
    (hfirst : D₀ ≤ physicalFieldDuration d (steps.take (τ (2*s))) -
      physicalFieldDuration d (steps.take (τ s)))
    (hdyad : ∀ r ∈ Icc (2*s) ((2:ℝ)^J*s),
      D₀ ≤ physicalFieldDuration d (steps.take (τ r)) -
        physicalFieldDuration d (steps.take (τ (3*r/4)))) :
    ∃ (cs : List (ℝ × ℕ)) (t : ℕ) (a D : Fin cs.length → ℝ),
      cs.length=J+2 ∧ t=τ (2*s) ∧ t ≤ steps.length+1 ∧
      lastLayerCut cs t=steps.length+1 ∧
      xs+physicalCutMass c steps t ≤ F*s ∧
      (∀ j : Fin cs.length, cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) ∧
      (∀ j, 0 < a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) ∧
      (∀ i j, i ≤ j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs t i) ≤
        (F/((c₀/4)^2*s))*(a j)^2) := by
  classical
  let ts : Fin (J+3) → ℕ := fun i => dyadicCutIndex J τ steps.length s s (i.val+1)
  let cs : List (ℝ × ℕ) := List.ofFn fun j : Fin (J+2) => ((1:ℝ),ts j.succ)
  have hlen : cs.length=J+2 := List.length_ofFn
  let e : Fin cs.length ≃ Fin (J+2) := finCongr hlen
  let ee : Fin (cs.length+1) ≃ Fin (J+3) := finCongr (by omega)
  have ht : ts 0=τ (2*s) := by simp [ts,dyadicCutIndex_one,two_mul]
  have hterminal : ts (Fin.last (J+2))=steps.length+1 := by
    simp only [ts,Fin.val_last,show J+2+1=J+3 by omega,dyadicCutIndex_terminal]
  have hp : ∀ j, cutPredecessor cs (ts 0) j=ts (e j).castSucc := by
    intro j
    have hj : j=Fin.cast hlen.symm (e j) := Fin.ext rfl
    rw [hj]
    exact cutPredecessor_ofFn (fun _ => 1) ts (e j)
  have hg : ∀ j, (cs.get j).2=ts (e j).succ := by
    intro j
    simp only [cs,List.get_ofFn,e,finCongr_apply]
  have he : ∀ i, overlapComponentEnd cs (ts 0) i=ts (ee i) := by
    intro i
    have hi : i=Fin.cast (by simp [cs]) (ee i) := Fin.ext rfl
    rw [hi]
    exact overlapComponentEnd_ofFn (fun _ => 1) ts (ee i)
  have hclk : ∀ j : Fin (J+2), ∃ D, D₀ ≤ D ∧ D ≤ B ∧
      PhysicalProjectionClock n steps fork (ts j.castSucc) (ts j.succ)
        ((c₀/4)*dyadicLayerScale s (j.val+1)) D := by
    intro j
    obtain ⟨D,hD,hDB,hclock⟩ := physicalDyadicLayer_clock n steps hc hc₀ hs hs.le le_rfl hJ
      τ hτ hL d hd hB hm (by simpa only [two_mul] using hfirst) hdyad j.succ (Fin.succ_ne_zero j)
    exact ⟨D,hD,hDB,hclock.earlier_fork hf⟩
  choose D hD hDB hclock using hclk
  let a : Fin cs.length → ℝ := fun j => (c₀/4)*dyadicLayerScale s ((e j).val+1)
  have hF : 0 ≤ F := by linarith
  have hbound : ∀ i : Fin (J+3), xs+physicalCutMass c steps (ts i) ≤ F*dyadicLayerScale s i.val := by
    intro i
    exact physicalDyadicMass_scale_bound n steps hc hxs hxs_s hs hs.le le_rfl hC hR hF₁ hF₂
      hJ τ hτ hRend hM i
  have hmono := dyadicCutIndex_monotone J hτ steps.length hL hs.le hs.le le_rfl
  have htsle : ∀ i : Fin (J+3), ts i ≤ steps.length+1 := by
    intro i
    unfold ts dyadicCutIndex
    split_ifs
    · exact (hL _).trans (Nat.le_succ _)
    · omega
    · rfl
  refine ⟨cs,ts 0,a,fun j => D (e j),hlen,ht,htsle _,?_,?_,?_,?_,?_⟩
  · exact (lastLayerCut_ofFn (fun _ => 1) ts).trans hterminal
  · simpa only [Fin.val_zero,dyadicLayerScale_zero] using hbound 0
  · intro j
    rw [hp,hg]
    exact ⟨hmono (by simp only [Fin.val_castSucc,Fin.val_succ]; omega),htsle _⟩
  · intro j
    rw [hp,hg]
    exact ⟨mul_pos (by positivity) (dyadicLayerScale_pos hs _),hD _,hDB _,hclock _⟩
  · intro i j hij
    rw [he]
    have hij' : (ee i).val ≤ (e j).val+1 := hij
    have hscale := dyadicLayerScale_monotone hs.le hij'
    exact overlap_unweighted_later_scale hs (by positivity : 0 < c₀/4) hF
      (le_dyadicLayerScale hs.le _) hscale (hbound (ee i))

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem overlapResidual_eq {p L : ℝ} (k : ℕ) :
    p^(2*(k+1)-1)*(p*L^(k+1))=(p^2*L)^(k+1) := by
  rw [← mul_assoc,← pow_succ,show 2*(k+1)-1+1=2*(k+1) by omega,
    mul_pow,pow_mul]

 theorem overlapResidual_le {p L d : ℝ} (k : ℕ)
    (hp : 0 ≤ p) (hL : 0 ≤ L) (hpd : p ≤ d^2) :
    p^(2*(k+1)-1)*(p*L^(k+1)) ≤ (d^4*L)^(k+1) := by
  rw [overlapResidual_eq]
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_right _ hL
  have hh := pow_le_pow_left₀ hp hpd 2
  simpa only [← pow_mul,Nat.reduceMul] using hh

 theorem eventually_physical_overlap_dyadic_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
    (steps : List (GaussianStep (FeatureIndex n))) (c c₀ xs s D₀ C R F : ℝ),
    OrderedSteps c steps → 0 < c₀ → 0 < xs → xs ≤ s → 0 < s → 0 < D₀ →
    0 ≤ C → 0 < R → 1+2*C ≤ F → 1+1/R ≤ F →
    ∀ (J : ℕ), 1 ≤ J → ∀ (τ : ℝ → ℕ), Monotone τ → (∀ r, τ r ≤ steps.length) →
    R ≤ (2:ℝ)^J*s → ∀ (fork : ℕ), fork ≤ τ s →
    ∀ (d : GaussianStep (FeatureIndex n) → ℝ≥0),
    (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i)=d st) →
    physicalFieldDuration d steps ≤ B →
    (∀ r ∈ Icc s ((2:ℝ)^J*s), c₀*r ≤ physicalCutMass c steps (τ r)) →
    (∀ r ∈ Icc s ((2:ℝ)^J*s), physicalCutMass c steps (τ r) ≤ C*r) →
    D₀ ≤ physicalFieldDuration d (steps.take (τ (2*s))) - physicalFieldDuration d (steps.take (τ s)) →
    (∀ r ∈ Icc (2*s) ((2:ℝ)^J*s), D₀ ≤ physicalFieldDuration d (steps.take (τ r)) -
        physicalFieldDuration d (steps.take (τ (3*r/4)))) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
    physicalOverlapMoment n (k+1) steps μ x hx fork ≤
      (2:ℝ)^(2*(k+1)-1) *
        (2*(physicalRawRatio n (k+1) steps c xs μ x hx)^(4*(k+1)) * (F*s)^(2*(k+1)) +
          (((J+3:ℕ):ℝ)^4 *
          (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
            (physicalRawRatio n (k+1) steps c xs μ x hx)^2 *
            (F/((c₀/4)^2*s))/((n:ℝ)*D₀)))^(k+1)) := by
  filter_upwards [eventually_physical_overlap_clock_schedule k B,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro P _ steps c c₀ xs s D₀ C R F hc hc₀ hxs hxs_s hs hD₀ hC hR hF₁ hF₂
    J hJ τ hτ hL hRend fork hf d hd hB hm hM hfirst hdyad μ _ x hx
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hF : 0 ≤ F := by linarith
  have hQ : 0 ≤ physicalRawRatio n (k+1) steps c xs μ x hx :=
    (by norm_num : (0:ℝ) ≤ 1).trans (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  obtain ⟨cs,t,a,D,hlen,ht,htl,hlast,hcore,hends,hclock,hscale⟩ :=
    physicalOverlapDyadicCertificates n steps hc hc₀ hxs.le hxs_s hs hC hR hF₁ hF₂
      hJ τ hτ hL hRend hf d hd hB hm hM hfirst hdyad
  have hh := hn P steps c D₀ xs (F/((c₀/4)^2*s)) hD₀ hxs (by positivity) hc
    μ x hx cs fork t a D htl hlast hends hclock hscale
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (add_nonneg hxs.le (physicalCutMass_mem steps hc t).1) hcore _
  · apply overlapResidual_le k (Nat.cast_nonneg _) (by positivity)
    have hcard := physicalOverlapResidualPairs_card_le cs
    have hsize : (cs.length+1)^2=(J+3)^2 := by rw [hlen]
    exact_mod_cast hcard.trans_eq hsize

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem eventually_comparison_inverse_strength_denominator {m C₀ Ct : ℝ}
    (hm : 0 < m) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
    ∀ᶠ n : ℕ in atTop, ∀ E d xs s : ℝ, ∀ e : ℝ → ℝ,
      0 < E → 0 < d → 0 < xs → xs ≤ s → 0 < e s →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      comparisonLowerScale n E d ≤ s →
      (n:ℝ)*E^2 ≤ Ct*e xs*xs^2 →
      MonotoneOn (fun r => e r*r^2) (Icc xs s) →
      1/((n:ℝ)*e s*s^4) ≤ (3*Ct*C₀^3)*(n:ℝ)^(-(3*m)) := by
  filter_upwards [eventually_comparisonCap_room (δ:=0) (C:=0) hm hC₀ (by norm_num),
    eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro E d xs s e hE hd hxs hxss hes hupper hlower has htest hmono
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hs : 0 < s := hxs.trans_le hxss
  have hden : 0 < (n:ℝ)*e s*s^4 := by positivity
  have hcap : 1 ≤ comparisonCap n 0 (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (0*s) := by
    simpa only [Real.rpow_zero] using comparisonCap_ge_rpow (δ:=0) hN hE hd (show (0:ℝ)≤0*s by simp)
  have hr := comparisonCap_strength_ratio (δ:=0) (C:=0) hN hE hd hxs hxss hes
    (by norm_num) hCt htest hmono
  have hh := (div_le_div_of_nonneg_right hcap hden.le).trans
    (hr.trans (mul_le_mul_of_nonneg_left (hn E d s hE hd hupper hlower has) hCt))
  norm_num at hh
  convert hh using 1 <;> first | rfl | ring

 theorem unweighted_residual_scale {N z s e D p A P C c₀ κ : ℝ}
    (hN : 0 < N) (hz : 0 < z) (hs : 0 < s) (he : 0 < e)
    (hc₀ : 0 < c₀) (hκ : 0 < κ) (hC : 0 ≤ C) (_hA : 0 ≤ A)
    (hp : 0 ≤ p) (hpA : p ≤ A*z^2) (hD : (κ/z)*e*s ≤ D) :
    p^2*(4*P^2*z^4*(C/(c₀^2*s))/(N*D)) ≤
      (A^2*4*P^2*C/(c₀^2*κ))*z^9*(1/(N*e*s^4))*s^2 := by
  have hDmin : 0 < (κ/z)*e*s := by positivity
  have hDpos : 0 < D := hDmin.trans_le hD
  have hpow := pow_le_pow_left₀ hp hpA 2
  have hden := mul_le_mul_of_nonneg_left hD hN.le
  have hfrac := div_le_div_of_nonneg_left
    (show 0 ≤ 4*P^2*z^4*(C/(c₀^2*s)) by positivity)
    (show 0 < N*((κ/z)*e*s) by positivity) hden
  have hh := mul_le_mul hpow hfrac (by positivity) (by positivity : 0 ≤ (A*z^2)^2)
  apply hh.trans_eq
  field_simp

 theorem eventually_comparison_unweighted_residual_small {m C₀ Ct A P C c₀ κ ε : ℝ}
    (hm : 0 < m) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (hc₀ : 0 < c₀) (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ E d xs s D p : ℝ, ∀ e : ℝ → ℝ,
      0 < E → 0 < d → 0 < xs → xs ≤ s → 0 < e s →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      comparisonLowerScale n E d ≤ s →
      (n:ℝ)*E^2 ≤ Ct*e xs*xs^2 →
      MonotoneOn (fun r => e r*r^2) (Icc xs s) →
      0 ≤ p → p ≤ A*(Real.log (n:ℝ))^2 → (κ/Real.log (n:ℝ))*e s*s ≤ D →
      p^2*(4*P^2*(Real.log (n:ℝ))^4*(C/(c₀^2*s))/((n:ℝ)*D)) ≤ ε*s^2 := by
  let V := A^2*4*P^2*C/(c₀^2*κ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ht := (tendsto_raw_log_margin 9 (show 0 < 3*m by positivity)).const_mul (V*(3*Ct*C₀^3))
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)
  filter_upwards [eventually_comparison_inverse_strength_denominator hm hC₀ hCt,
    ht.eventually (gt_mem_nhds (by simpa using hε)),hlog,eventually_gt_atTop (0:ℕ)] with n hn hsmall hnlog hn0
  intro E d xs s D p e hE hd hxs hxss hes hupper hlower has htest hmono hp hpA hD
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hs : 0 < s := hxs.trans_le hxss
  have hr := hn E d xs s e hE hd hxs hxss hes hupper hlower has htest hmono
  have hh := unweighted_residual_scale (P:=P) hN hnlog hs hes hc₀ hκ hC hA hp hpA hD
  apply hh.trans
  have hi := mul_le_mul_of_nonneg_left hr (show 0 ≤ V*(Real.log (n:ℝ))^9 by positivity)
  have heq : V*(Real.log (n:ℝ))^9*((3*Ct*C₀^3)*(n:ℝ)^(-(3*m))) =
      (V*(3*Ct*C₀^3))*((Real.log (n:ℝ))^9*(n:ℝ)^(-(3*m))) := by ring
  rw [heq] at hi
  exact mul_le_mul_of_nonneg_right (hi.trans hsmall.le) (sq_nonneg s)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_comparison_physical_overlap_raw (k : ℕ) (B : ℝ)
    {m C₀ Ct A F c₀ κ : ℝ}
    (hm : 0 < m) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hc₀ : 0 < c₀) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ∀ E d xs s D₀ : ℝ, ∀ e : ℝ → ℝ,
    0 < E → 0 < d → 0 < xs → xs ≤ s → 0 < e s → 0 < D₀ →
    Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
    comparisonLowerScale n E d ≤ s → (n:ℝ)*E^2 ≤ Ct*e xs*xs^2 →
    MonotoneOn (fun r => e r*r^2) (Icc xs s) →
    (κ/Real.log (n:ℝ))*e s*s ≤ D₀ →
    ∀ (P : Type) [MeasurableSpace P] (steps : List (GaussianStep (FeatureIndex n))) (c C R : ℝ),
    OrderedSteps c steps → 0 ≤ C → 0 < R → 1+2*C ≤ F → 1+1/R ≤ F →
    ∀ (J : ℕ), 1 ≤ J → ((J+3:ℕ):ℝ)^2 ≤ A*(Real.log (n:ℝ))^2 →
    ∀ (τ : ℝ → ℕ), Monotone τ → (∀ r, τ r ≤ steps.length) → R ≤ (2:ℝ)^J*s →
    ∀ (fork : ℕ), fork ≤ τ s →
    ∀ (df : GaussianStep (FeatureIndex n) → ℝ≥0),
    (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i)=df st) → physicalFieldDuration df steps ≤ B →
    (∀ r ∈ Icc s ((2:ℝ)^J*s), c₀*r ≤ physicalCutMass c steps (τ r)) →
    (∀ r ∈ Icc s ((2:ℝ)^J*s), physicalCutMass c steps (τ r) ≤ C*r) →
    D₀ ≤ physicalFieldDuration df (steps.take (τ (2*s))) - physicalFieldDuration df (steps.take (τ s)) →
    (∀ r ∈ Icc (2*s) ((2:ℝ)^J*s), D₀ ≤ physicalFieldDuration df (steps.take (τ r)) -
        physicalFieldDuration df (steps.take (τ (3*r/4)))) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
    physicalOverlapMoment n (k+1) steps μ x hx fork ≤
      ((2:ℝ)^(2*(k+1)-1)*(2*F^(2*(k+1))+1)) *
        (physicalRawRatio n (k+1) steps c xs μ x hx)^(4*(k+1))*s^(2*(k+1)) := by
  filter_upwards [eventually_physical_overlap_dyadic_moment k B,
    eventually_comparison_unweighted_residual_small (P:=projectionLpConstant k) (ε:=1)
      hm hC₀ hCt hA hF (by positivity : 0 < c₀/4) hκ (by norm_num)] with n hn hr
  intro E d xs s D₀ e hE hd hxs hxss hes hD₀ hupper hlower has htest hmono hD
    P _ steps c C R hc hC hR hF₁ hF₂ J hJ hJdepth τ hτ hL hRend fork hf df hdf hB
    hmass hMass hfirst hdyad μ _ x hx
  have hs : 0 < s := hxs.trans_le hxss
  have hraw := hn P steps c c₀ xs s D₀ C R F hc hc₀ hxs hxss hs hD₀ hC hR hF₁ hF₂
    J hJ τ hτ hL hRend fork hf df hdf hB hmass hMass hfirst hdyad μ x hx
  have hsmall := hr E d xs s D₀ (((J+3:ℕ):ℝ)^2) e hE hd hxs hxss hes hupper hlower
    has htest hmono (sq_nonneg _) hJdepth hD
  simp only [← pow_mul,Nat.reduceMul,one_mul] at hsmall
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  have hQone : 1 ≤ Q := physicalRawRatio_one_le n (k+1) steps c xs μ x hx
  have hQ : 0 ≤ Q := (by norm_num : (0:ℝ) ≤ 1).trans hQone
  have hres : ((J+3:ℕ):ℝ)^4 *
      (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*Q^2*(F/((c₀/4)^2*s))/((n:ℝ)*D₀)) ≤ Q^4*s^2 := by
    calc
      _ = Q^2*(((J+3:ℕ):ℝ)^4 *
        (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(F/((c₀/4)^2*s))/((n:ℝ)*D₀))) := by ring
      _ ≤ Q^2*s^2 := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ ≤ Q^4*s^2 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQone (by norm_num : 2 ≤ 4)) (sq_nonneg _)
  have hrespow := pow_le_pow_left₀ (by positivity) hres (k+1)
  have heq : (Q^4*s^2)^(k+1)=Q^(4*(k+1))*s^(2*(k+1)) := by
    rw [mul_pow,← pow_mul,← pow_mul]
  rw [heq] at hrespow
  apply hraw.trans
  calc
    _ ≤ (2:ℝ)^(2*(k+1)-1) *
      (2*Q^(4*(k+1))*(F*s)^(2*(k+1))+Q^(4*(k+1))*s^(2*(k+1))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hrespow) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped NNReal

 theorem physicalConstrainedOverlapClocks (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (has : MassOrdered 0 as)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ≤ 1) (hu₀ : 0 ≤ u₀) (hc : 0 < c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    {e : ℝ → ℝ} {s T κ ε cl cu : ℝ}
    (hs : 0 < s) (hT : 2*s ≤ T) (hT₁ : T ≤ 1) (hr₀ : r₀ < s/2)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hεs : ε ≤ s/8)
    (hcl : 0 ≤ cl) (hcu : 0 ≤ cu)
    (hreg : ∀ v ∈ Icc (s/2) T, cl*v ≤ α.val.val v ∧ α.val.val v ≤ cu*v)
    (he : ∀ v ∈ Icc (s/2) T, 0 ≤ e v) (hem : AntitoneOn e (Icc (s/2) T))
    (her : MonotoneOn (fun v => v*e v) (Icc (s/2) T))
    (hH : ∀ x ∈ Icc (s/2) T, ∀ y ∈ Icc (s/2) T, x ≤ y →
      κ*e y*(y-x) ≤ (h (α.val.val y):ℝ)-(h (α.val.val x):ℝ))
    (hmesh : let steps := sampleClockSteps (completedPathClock n b h) 0 as
      let hsteps := sampleClockSteps_ordered (completedPathClock n b h) as has
      ∀ j : Fin (steps.length+1),
        physicalQuantileGrid hr hu hc hk hkc hm hM α steps hsteps j.succ-
          physicalQuantileGrid hr hu hc hk hkc hm hM α steps hsteps j.castSucc ≤ ε) :
    let steps := sampleClockSteps (completedPathClock n b h) 0 as
    let hsteps := sampleClockSteps_ordered (completedPathClock n b h) as has
    let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps hsteps
    let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
    (∀ v ∈ Icc s T, (cl/2)*v ≤ physicalCutMass 0 steps (radiusGridCut r v) ∧
      physicalCutMass 0 steps (radiusGridCut r v) ≤ cu*v) ∧
    (κ/16)*e s*s ≤ physicalFieldDuration d (steps.take (radiusGridCut r (2*s)))-
      physicalFieldDuration d (steps.take (radiusGridCut r s)) ∧
    (∀ v ∈ Icc (2*s) T, (κ/16)*e s*s ≤
      physicalFieldDuration d (steps.take (radiusGridCut r v))-
        physicalFieldDuration d (steps.take (radiusGridCut r (3*v/4)))) := by
  dsimp only at hmesh ⊢
  let steps := sampleClockSteps (completedPathClock n b h) 0 as
  let hsteps := sampleClockSteps_ordered (completedPathClock n b h) as has
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps hsteps
  let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
  have hclock := physicalConstrainedClockLengths n hn b h hb hh as has hr hu hu₀ hc hk hkc hm hM α
    (K:=1) (a:=s) (ab:=s) (η:=s) hs le_rfl (by norm_num) (by simp) hT hT₁ hr₀ hκ hs le_rfl
    hε hεs he hem her hH hmesh
  have hcoeff : κ*e s*s/(8*((1:ℝ)+1))=(κ/16)*e s*s := by ring
  have hdyad : ∀ v ∈ Icc (2*s) T, (κ/16)*e s*s ≤
      physicalFieldDuration d (steps.take (radiusGridCut r v))-
        physicalFieldDuration d (steps.take (radiusGridCut r (3*v/4))) := by
    simpa only [hcoeff] using hclock.2
  refine ⟨physicalQuantileSample_regular hr hu hc hk hkc hm hM α steps hsteps hε
    (by linarith) hr₀ hT₁ hcl hcu hu₀ hmesh hreg,?_,hdyad⟩
  have hfirst := hdyad (2*s) ⟨le_rfl,hT⟩
  have hpre := physicalFieldDuration_prefix_monotone d steps
    (radiusGridCut_monotone r (show s ≤ 3*(2*s)/4 by linarith))
  exact hfirst.trans (sub_le_sub_left hpre _)

end SKFluctuations

end

end OAI
