import Mathlib
import OAI.Probability.SKFluctuations.PhysicalMomentOrder

namespace OAI

/-! Physical Dyadic Clock. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalProjectionClock_of_field_cuts (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ}
    (hc : OrderedSteps c steps) (ha : 0 ≤ a)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st)
    {fork q v w : ℕ} (hf : fork ≤ q) (hq : q ≤ v) (hv : v ≤ w)
    (hw : w ≤ steps.length) (ham : a ≤ physicalCutMass c steps q) :
    PhysicalProjectionClock n steps fork v w a
      (physicalFieldDuration d (cutSlice steps q v)) := by
  exact physicalProjectionClock_of_gaussian_cuts n steps hc ha hf hq hv hw ham
    (alignedFieldClock_slice n steps d hd q v)

theorem physicalProjectionClock_of_field_terminal (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ}
    (hc : OrderedSteps c steps) (ha : 0 ≤ a)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st)
    {fork q : ℕ} (hf : fork ≤ q) (hq : q ≤ steps.length)
    (ham : a ≤ physicalCutMass c steps q) :
    PhysicalProjectionClock n steps fork steps.length (steps.length+1) a
      (physicalFieldDuration d (cutSlice steps q steps.length)) := by
  exact physicalProjectionClock_of_terminal_cuts n steps hc ha hf hq le_rfl ham
    (alignedFieldClock_slice n steps d hd q steps.length)

theorem physicalDyadicLayer_clock (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c c₀ s η D₀ B : ℝ}
    (hc : OrderedSteps c steps) (hc₀ : 0 < c₀) (hs : 0 < s)
    (hη : 0 ≤ η) (hηs : η ≤ s) {J : ℕ} (hJ : 1 ≤ J)
    (τ : ℝ → ℕ) (hτ : Monotone τ) (hL : ∀ r, τ r ≤ steps.length)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st)
    (hB : physicalFieldDuration d steps ≤ B)
    (hm : ∀ r ∈ Icc s ((2:ℝ)^J*s), c₀*r ≤ physicalCutMass c steps (τ r))
    (hfirst : D₀ ≤ physicalFieldDuration d (steps.take (τ (s+η))) -
      physicalFieldDuration d (steps.take (τ s)))
    (hdyad : ∀ r ∈ Icc (2*s) ((2:ℝ)^J*s),
      D₀ ≤ physicalFieldDuration d (steps.take (τ r)) -
        physicalFieldDuration d (steps.take (τ (3*r/4))))
    (i : Fin (J+3)) (hi : i ≠ 0) :
    ∃ D, D₀ ≤ D ∧ D ≤ B ∧ PhysicalProjectionClock n steps (τ s)
      (dyadicCutIndex J τ steps.length s η i.val)
      (dyadicCutIndex J τ steps.length s η (i.val+1))
      ((c₀/4)*dyadicLayerScale s i.val) D := by
  have ha : 0 ≤ (c₀/4)*dyadicLayerScale s i.val := by
    have := dyadicLayerScale_pos hs i.val
    positivity
  have hi0 : 0 < i.val := Nat.pos_of_ne_zero (by simpa only [Fin.val_zero] using Fin.val_ne_of_ne hi)
  have hmono := dyadicCutIndex_monotone J hτ steps.length hL hs.le hη hηs
  by_cases hi1 : i.val=1
  · have hvw : τ (s+η) ≤ τ (2*s) := hτ (by linarith)
    have hsEnd : s ≤ (2:ℝ)^J*s := by
      have := le_dyadicLayerScale hs.le (J+1)
      simpa only [dyadicLayerScale,Nat.add_sub_cancel] using this
    have ham : (c₀/4)*dyadicLayerScale s i.val ≤ physicalCutMass c steps (τ s) := by
      simp only [hi1,dyadicLayerScale_one]
      exact (by nlinarith : (c₀/4)*s ≤ c₀*s).trans (hm s ⟨le_rfl,hsEnd⟩)
    refine ⟨physicalFieldDuration d (cutSlice steps (τ s) (τ (s+η))),?_,
      (physicalFieldDuration_slice_le d steps _ _).trans hB,?_⟩
    · rw [physicalFieldDuration_slice_eq d steps (hτ (by linarith))]
      exact hfirst
    · have hsecond : dyadicCutIndex J τ steps.length s η (1+1) = τ (2*s) := by
        simp [dyadicCutIndex,show 2 ≤ J+1 by omega,dyadicRadiusNode]
      have hh := physicalProjectionClock_of_field_cuts n steps hc ha d hd le_rfl
        (hτ (by linarith : s ≤ s+η)) hvw (hL _) ham
      simpa only [hi1,dyadicCutIndex_one,hsecond] using hh

  · have hi2 : 2 ≤ i.val := by omega
    have htwo : 2*s ≤ dyadicLayerScale s i.val := by
      have hh := dyadicLayerScale_monotone hs.le hi2
      simpa only [dyadicLayerScale,Nat.reduceSub,pow_one] using hh
    by_cases hig : i.val ≤ J+1
    · have hend : dyadicLayerScale s i.val ≤ (2:ℝ)^J*s := by
        have hh := dyadicLayerScale_monotone hs.le hig
        simpa only [dyadicLayerScale,Nat.add_sub_cancel] using hh
      have hpre : 3*dyadicLayerScale s i.val/4 ∈ Icc s ((2:ℝ)^J*s) := by
        constructor <;> nlinarith
      have hqv : τ (3*dyadicLayerScale s i.val/4) ≤ τ (dyadicLayerScale s i.val) :=
        hτ (by have := dyadicLayerScale_pos hs i.val; linarith)
      have hv : dyadicCutIndex J τ steps.length s η i.val = τ (dyadicLayerScale s i.val) := by
        simp only [dyadicCutIndex,hig,↓reduceIte,dyadicRadiusNode,show i.val ≠ 0 by omega,
          show i.val ≠ 1 by omega,dyadicLayerScale]
      have hw : dyadicCutIndex J τ steps.length s η (i.val+1) ≤ steps.length := by
        unfold dyadicCutIndex
        split_ifs with hh hh'
        · exact hL _
        · exact le_rfl
        · omega
      have ham : (c₀/4)*dyadicLayerScale s i.val ≤
          physicalCutMass c steps (τ (3*dyadicLayerScale s i.val/4)) := by
        apply le_trans _ (hm _ hpre)
        nlinarith [dyadicLayerScale_pos hs i.val]
      refine ⟨physicalFieldDuration d (cutSlice steps
        (τ (3*dyadicLayerScale s i.val/4)) (τ (dyadicLayerScale s i.val))),?_,
        (physicalFieldDuration_slice_le d steps _ _).trans hB,?_⟩
      · rw [physicalFieldDuration_slice_eq d steps hqv]
        exact hdyad _ ⟨htwo,hend⟩
      · rw [hv]
        exact physicalProjectionClock_of_field_cuts n steps hc ha d hd (hτ hpre.1) hqv
          (by simpa only [hv] using hmono (Nat.le_succ i.val)) hw ham
    · have hit : i.val=J+2 := by omega
      let r : ℝ := (2:ℝ)^J*s
      have hrpos : 0 < r := by dsimp [r]; positivity
      have hr2 : 2*s ≤ r := by
        apply mul_le_mul_of_nonneg_right _ hs.le
        simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ)
      have hpre : 3*r/4 ∈ Icc s ((2:ℝ)^J*s) := by
        change s ≤ 3*r/4 ∧ 3*r/4 ≤ r
        constructor <;> linarith
      have hqi : dyadicLayerScale s i.val = 2*r := by
        simp only [hit,dyadicLayerScale,show J+2-1=J+1 by omega,pow_succ,r]
        ring
      have ham : (c₀/4)*dyadicLayerScale s i.val ≤ physicalCutMass c steps (τ (3*r/4)) := by
        rw [hqi]
        apply le_trans _ (hm _ hpre)
        nlinarith
      refine ⟨physicalFieldDuration d (cutSlice steps (τ (3*r/4)) steps.length),?_,
        (physicalFieldDuration_slice_le d steps _ _).trans hB,?_⟩
      · rw [physicalFieldDuration_slice_eq d steps (hL _)]
        have hh := hdyad r ⟨hr2,le_rfl⟩
        have hlen := physicalFieldDuration_prefix_monotone d steps (hL r)
        linarith
      · simpa only [hit,dyadicCutIndex_end,show J+2+1=J+3 by omega,
          dyadicCutIndex_terminal] using
          physicalProjectionClock_of_field_terminal n steps hc ha d hd (hτ hpre.1) (hL _) ham

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem hasFarPairClock_of_layer_scales (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs D₀ B C c₀ : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 < xs) (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    {K : ℕ} (q : Fin (K+1) → ℝ) (m : Fin (K+1) → ℝ) (v w : Fin (K+1) → ℕ)
    (fork : ℕ) (hq : ∀ i, 0 < q i) (hqmono : Monotone q)
    (hm : ∀ i, 0 ≤ m i) (hmC : ∀ i, m i ≤ C*q i)
    (hend : ∀ i, xs+physicalCutMass c steps (w i) ≤ C*q i)
    (hvw : ∀ i, v i ≤ w i) (hw : ∀ i, w i ≤ steps.length+1)
    (hclock : ∀ i, i ≠ 0 → ∃ D, D₀ ≤ D ∧ D ≤ B ∧
      PhysicalProjectionClock n steps fork (v i) (w i) (c₀*q i) D)
    (i j : Fin (K+1)) (hij : i ≠ 0 ∨ j ≠ 0) :
    HasFarPairClock n steps c xs D₀ B (C^2/c₀^2) (m j) fork (v i) (w i) (v j) (w j) := by
  refine ⟨hvw i,hw i,hvw j,hw j,?_⟩
  have hscale (i j z : Fin (K+1)) (hiz : i ≤ z) (hjz : j ≤ z) :
      m j*(xs+physicalCutMass c steps (w i)) ≤ (C^2/c₀^2)*(c₀*q z)^2 := by
    have hSj : 0 ≤ xs+physicalCutMass c steps (w i) :=
      add_nonneg hxs.le (physicalCutMass_mem steps hc (w i)).1
    calc
      _ ≤ (C*q j)*(C*q i) := mul_le_mul (hmC j) (hend i) hSj ((hm j).trans (hmC j))
      _ ≤ (C*q z)*(C*q z) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hqmono hjz) hC)
        (mul_le_mul_of_nonneg_left (hqmono hiz) hC)
        (mul_nonneg hC (hq i).le) (mul_nonneg hC (hq z).le)
      _ = _ := by field_simp
  rcases le_total i j with hij' | hji
  · have hj : j ≠ 0 := by intro hz; subst j; have hi : i=0 := le_antisymm hij' (Fin.zero_le i); tauto
    obtain ⟨D,hD,hDB,hcl⟩ := hclock j hj
    exact ⟨c₀*q j,D,mul_pos hc₀ (hq j),hD,hDB,Or.inl ⟨hcl,hscale i j j hij' le_rfl⟩⟩
  · have hi : i ≠ 0 := by intro hz; subst i; have hj : j=0 := le_antisymm hji (Fin.zero_le j); tauto
    obtain ⟨D,hD,hDB,hcl⟩ := hclock i hi
    exact ⟨c₀*q i,D,mul_pos hc₀ (hq i),hD,hDB,Or.inr ⟨hcl,hscale j j i hji hji⟩⟩

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalDyadic_hasFarPairClock (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c c₀ xs s η D₀ B C R F : ℝ}
    (hc : OrderedSteps c steps) (hc₀ : 0 < c₀) (hxs : 0 < xs) (hxs_s : xs ≤ s)
    (hη : 0 ≤ η) (hηs : η ≤ s) (hC : 0 ≤ C) (hR : 0 < R)
    (hF₁ : 1+2*C ≤ F) (hF₂ : 1+1/R ≤ F)
    {J : ℕ} (hJ : 1 ≤ J) (τ : ℝ → ℕ) (hτ : Monotone τ)
    (hL : ∀ r, τ r ≤ steps.length) (hRend : R ≤ (2:ℝ)^J*s)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st)
    (hB : physicalFieldDuration d steps ≤ B)
    (hm : ∀ r ∈ Icc s ((2:ℝ)^J*s),
      c₀*r ≤ physicalCutMass c steps (τ r) ∧ physicalCutMass c steps (τ r) ≤ C*r)
    (hfirst : D₀ ≤ physicalFieldDuration d (steps.take (τ (s+η))) -
      physicalFieldDuration d (steps.take (τ s)))
    (hdyad : ∀ r ∈ Icc (2*s) ((2:ℝ)^J*s),
      D₀ ≤ physicalFieldDuration d (steps.take (τ r)) -
        physicalFieldDuration d (steps.take (τ (3*r/4))))
    (i j : Fin (J+3)) (hij : i ≠ 0 ∨ j ≠ 0) :
    HasFarPairClock n steps c xs D₀ B (F^2/(c₀/4)^2)
      (physicalDyadicMass steps c J τ η j s) (τ s)
      (physicalDyadicCuts J τ steps.length η i.castSucc s)
      (physicalDyadicCuts J τ steps.length η i.succ s)
      (physicalDyadicCuts J τ steps.length η j.castSucc s)
      (physicalDyadicCuts J τ steps.length η j.succ s) := by
  have hs := lt_of_lt_of_le hxs hxs_s
  have hF : 0 ≤ F := (by linarith : 0 ≤ 1+2*C).trans hF₁
  have hbound a := physicalDyadicMass_scale_bound n steps hc hxs.le hxs_s hs hη hηs hC hR
    hF₁ hF₂ hJ τ hτ hRend (fun r hr => (hm r hr).2) a
  have hmono := dyadicCutIndex_monotone J hτ steps.length hL hs.le hη hηs
  apply hasFarPairClock_of_layer_scales n steps hc hxs hF (by positivity : 0 < c₀/4)
    (fun i : Fin (J+3) => dyadicLayerScale s i.val) (fun i => physicalDyadicMass steps c J τ η i s)
    (fun i => physicalDyadicCuts J τ steps.length η i.castSucc s)
    (fun i => physicalDyadicCuts J τ steps.length η i.succ s) (τ s)
    (fun i => dyadicLayerScale_pos hs i.val)
    (fun i j hij => dyadicLayerScale_monotone hs.le hij)
    (fun i => (physicalCutMass_mem steps hc _).1)
  · intro i
    exact (le_add_of_nonneg_left hxs.le).trans (hbound i)
  · exact hbound
  · intro i
    exact hmono (show i.val ≤ i.val+1 by omega)
  · intro i
    have hh := hmono (show i.val+1 ≤ J+3 by omega)
    simpa only [physicalDyadicCuts,Fin.val_succ,dyadicCutIndex_terminal] using hh
  · intro i hi
    exact physicalDyadicLayer_clock n steps hc hc₀ hs hη hηs hJ τ hτ hL d hd hB
      (fun r hr => (hm r hr).1) hfirst hdyad i hi
  · exact hij

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem eventually_physical_dyadic_band (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c c₀ xs D₀ C R F : ℝ),
      OrderedSteps c steps → 0 < c₀ → 0 < xs → 0 < D₀ → 0 ≤ C → 0 < R →
      1+2*C ≤ F → 1+1/R ≤ F →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (τ : ℝ → ℕ), Monotone τ → (∀ r, τ r ≤ steps.length) →
    ∀ (a b η : ℝ), xs ≤ a → a ≤ b → 0 < η → η ≤ a →
    ∀ (J : ℕ), 1 ≤ J → R ≤ (2:ℝ)^J*a →
    ∀ (ζ : Measure ℝ) [IsFiniteMeasure ζ] (A : ℝ), 0 ≤ A →
      ζ ≤ ENNReal.ofReal A • volume.restrict (Ioc a b) →
    ∀ (d : GaussianStep (FeatureIndex n) → ℝ≥0),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ B →
      (∀ r ∈ Icc a ((2:ℝ)^J*b),
        c₀*r ≤ physicalCutMass c steps (τ r) ∧ physicalCutMass c steps (τ r) ≤ C*r) →
      (∀ s ∈ Ioc a b, D₀ ≤ physicalFieldDuration d (steps.take (τ (s+η))) -
        physicalFieldDuration d (steps.take (τ s))) →
      (∀ r ∈ Icc (2*a) ((2:ℝ)^J*b),
        D₀ ≤ physicalFieldDuration d (steps.take (τ r)) -
          physicalFieldDuration d (steps.take (τ (3*r/4)))) →
    (∫ p, (physicalSusceptibilityMassIntegral n steps x ζ τ p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (J+3:ℕ)^3 *
        ((C*(b+η))*A*(4*(nearPairMomentConstant (k+1))^(((k+1:ℕ):ℝ)⁻¹))*η*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2 +
        ζ.real univ*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^2*(F^2/(c₀/4)^2)/((n:ℝ)*D₀))) := by
  filter_upwards [eventually_physical_susceptibility_band k B] with n hn
  intro P _ steps c c₀ xs D₀ C R F hs hc₀ hxs hD₀ hC hR hF₁ hF₂ μ _ x hx τ hτ hL
    a b η hxa hab hη hηa J hJ hRend ζ _ A hA hζ d hd hB hm hfirst hdyad
  have ha : 0 < a := hxs.trans_le hxa
  have hb : 0 < b := ha.trans_le hab
  have hae : ∀ᵐ s ∂ζ, s ∈ Ioc a b :=
    (ae_mono hζ) (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _)
  have hpow : (2:ℝ) ≤ (2:ℝ)^J := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
  have hinterval {s r : ℝ} (hss : s ∈ Ioc a b) (hr : r ∈ Icc s ((2:ℝ)^J*s)) :
      r ∈ Icc a ((2:ℝ)^J*b) :=
    ⟨hss.1.le.trans hr.1,hr.2.trans (mul_le_mul_of_nonneg_left hss.2 (by positivity))⟩
  have htm i : Measurable (physicalDyadicCuts J τ steps.length η i) :=
    dyadicCutIndex_measurable J hτ.measurable steps.length η i.val
  have hmm i : Measurable (physicalDyadicMass steps c J τ η i) :=
    (measurable_of_countable (physicalCutMass c steps)).comp (htm i.succ)
  have hm01 (i : Fin (J+3)) (s : ℝ) := physicalCutMass_mem steps hs
    (physicalDyadicCuts J τ steps.length η i.succ s)
  have hmM : ∀ᵐ s ∂ζ, physicalDyadicMass steps c J τ η 0 s ≤ C*(b+η) := by
    filter_upwards [hae] with s hss
    have hh : s+η ∈ Icc a ((2:ℝ)^J*b) := by
      constructor
      · linarith [hss.1]
      · calc
          s+η ≤ 2*b := by linarith [hss.2]
          _ ≤ _ := mul_le_mul_of_nonneg_right hpow hb.le
    simpa only [physicalDyadicMass,physicalDyadicCuts,Fin.val_succ,Fin.val_zero,zero_add,
      dyadicCutIndex_one] using
      (hm _ hh).2.trans (mul_le_mul_of_nonneg_left (by linarith [hss.2]) hC)
  have hdata : ∀ᵐ s ∂ζ,
      physicalDyadicCuts J τ steps.length η (Fin.last (J+3)) s = steps.length+1 ∧
      physicalDyadicMass steps c J τ η (Fin.last (J+2)) s = 1 ∧
      CutPartition steps (physicalDyadicCuts J τ steps.length η 0 s)
        (List.ofFn fun i : Fin (J+2) => (physicalDyadicMass steps c J τ η i.castSucc s,
          physicalDyadicCuts J τ steps.length η i.succ.castSucc s)) ∧
      ∀ BB ∈ layersOfCuts steps (physicalDyadicCuts J τ steps.length η 0 s)
        (List.ofFn fun i : Fin (J+2) => (physicalDyadicMass steps c J τ η i.castSucc s,
          physicalDyadicCuts J τ steps.length η i.succ.castSucc s)), ∀ st ∈ BB.2, st.1 ≤ BB.1 := by
    filter_upwards [hae] with s hss
    refine ⟨?_,?_,physicalDyadicCuts_partition steps c J hτ hL (ha.le.trans hss.1.le)
      hη.le (hηa.trans hss.1.le),physicalDyadicCuts_mass_bound steps hs J τ s η⟩
    · exact dyadicCutIndex_terminal J τ steps.length s η
    · simp only [physicalDyadicMass,physicalDyadicCuts,Fin.val_succ,Fin.val_last,
        show J+2+1=J+3 by omega,dyadicCutIndex_terminal,physicalCutMass_terminal]
  have hclock (i j : Fin (J+3)) (hij : i ≠ 0 ∨ j ≠ 0) : ∀ᵐ s ∂ζ,
      HasFarPairClock n steps c xs D₀ B (F^2/(c₀/4)^2)
        (physicalDyadicMass steps c J τ η j s) (τ s)
        (physicalDyadicCuts J τ steps.length η i.castSucc s)
        (physicalDyadicCuts J τ steps.length η i.succ s)
        (physicalDyadicCuts J τ steps.length η j.castSucc s)
        (physicalDyadicCuts J τ steps.length η j.succ s) := by
    filter_upwards [hae] with s hss
    exact physicalDyadic_hasFarPairClock n steps hs hc₀ hxs (hxa.trans hss.1.le)
      hη.le (hηa.trans hss.1.le) hC hR hF₁ hF₂ hJ τ hτ hL
      (hRend.trans (mul_le_mul_of_nonneg_left hss.1.le (by positivity))) d hd hB
      (fun r hr => hm r (hinterval hss hr)) (hfirst s hss)
      (fun r hr => hdyad r ⟨by linarith [hr.1,hss.1],
        hr.2.trans (mul_le_mul_of_nonneg_left hss.2 (by positivity))⟩) i j hij
  simpa only [show J+2+1=J+3 by omega, mul_assoc] using hn P steps c D₀ xs (F^2/(c₀/4)^2) hD₀ hxs (by positivity) hs μ x hx τ hτ
    a b η hab hη ((hL _).trans (Nat.le_succ _)) ζ A (C*(b+η)) hA (by positivity) hζ
    (J+2) (physicalDyadicMass steps c J τ η) (physicalDyadicCuts J τ steps.length η)
    hmm htm hm01 hmM (funext fun s => dyadicCutIndex_zero J τ steps.length s η)
    (funext fun s => dyadicCutIndex_one J τ steps.length s η) hdata hclock

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

structure PhysicalBandWindow (n : ℕ) (steps : List (GaussianStep (FeatureIndex n))) (xs : ℝ) where
  selected : Finset (Fin (steps.length+1))
  radius : Fin (steps.length+2) → ℝ
  radius_mono : Monotone radius
  cell_pos : ∀ j, physicalWindowCellMass steps 0 selected j ≠ 0 →
    radius j.castSucc < radius j.succ
  mass_pos : 0 < physicalWindowMass steps 0 selected
  a : ℝ
  b : ℝ
  η : ℝ
  A : ℝ
  D₀ : ℝ
  c₀ : ℝ
  C : ℝ
  R : ℝ
  F : ℝ
  depth : ℕ
  c₀_pos : 0 < c₀
  D₀_pos : 0 < D₀
  C_nonneg : 0 ≤ C
  R_pos : 0 < R
  F_mass : 1+2*C ≤ F
  F_radius : 1+1/R ≤ F
  xa : xs ≤ a
  ab : a ≤ b
  η_pos : 0 < η
  η_le : η ≤ a
  depth_pos : 1 ≤ depth
  last_radius : R ≤ (2:ℝ)^depth*a
  A_nonneg : 0 ≤ A
  cell_cap : ∀ j, physicalWindowCellMass steps 0 selected j ≤ A*(radius j.succ-radius j.castSucc)
  cell_band : ∀ j, physicalWindowCellMass steps 0 selected j ≠ 0 →
    Ioc (radius j.castSucc) (radius j.succ) ⊆ Ioc a b
  mass_comparable : ∀ r ∈ Icc a ((2:ℝ)^depth*b),
    c₀*r ≤ physicalCutMass 0 steps (radiusGridCut radius r) ∧
      physicalCutMass 0 steps (radiusGridCut radius r) ≤ C*r

namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

def mass (w : PhysicalBandWindow n steps xs) : ℝ := physicalWindowMass steps 0 w.selected

def measure (w : PhysicalBandWindow n steps xs) : Measure ℝ :=
  radiusCellMeasure (fun j => w.radius j.castSucc) (fun j => w.radius j.succ)
    (physicalWindowCellMass steps 0 w.selected)

instance (w : PhysicalBandWindow n steps xs) : IsFiniteMeasure w.measure := by
  unfold measure
  infer_instance

def nearCoefficient (k : ℕ) (w : PhysicalBandWindow n steps xs) : ℝ :=
  (w.C*(w.b+w.η))*w.A*(4*(nearPairMomentConstant (k+1))^(((k+1:ℕ):ℝ)⁻¹))*w.η*
    (xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η)))^2

def farCoefficient (k : ℕ) (w : PhysicalBandWindow n steps xs) : ℝ :=
  4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2)/((n:ℝ)*w.D₀)

def coefficient (k : ℕ) (w : PhysicalBandWindow n steps xs) : ℝ :=
  (w.depth+3:ℕ)^3*(w.nearCoefficient k+w.mass*w.farCoefficient k)

def loss (k : ℕ) (w : PhysicalBandWindow n steps xs) : ℝ :=
  2*Real.sqrt ((1+(2*(k+1:ℕ):ℝ)^2/3)*w.mass⁻¹^2*w.coefficient k)

 theorem measure_mass (ha : OrderedSteps 0 steps) (w : PhysicalBandWindow n steps xs) :
    w.measure.real univ = w.mass :=
  physical_radius_window_mass steps ha w.selected w.radius w.cell_pos

 theorem measure_cap (w : PhysicalBandWindow n steps xs) :
    w.measure ≤ ENNReal.ofReal w.A • volume.restrict (Ioc w.a w.b) :=
  physical_radius_window_cap n steps 0 w.selected w.radius w.radius_mono w.cell_pos
    w.A_nonneg w.cell_cap w.cell_band

 theorem nearCoefficient_nonneg (hxs : 0 < xs) (k : ℕ) (w : PhysicalBandWindow n steps xs) :
    0 ≤ w.nearCoefficient k := by
  have hb : 0 < w.b := hxs.trans_le (w.xa.trans w.ab)
  have hC := w.C_nonneg
  have hA := w.A_nonneg
  have hη := w.η_pos
  have hk := nearPairMomentConstant_nonneg (k+1)
  unfold nearCoefficient
  positivity

 theorem farCoefficient_nonneg (k : ℕ) (w : PhysicalBandWindow n steps xs) :
    0 ≤ w.farCoefficient k := by
  have hD := w.D₀_pos
  unfold farCoefficient
  positivity

 theorem coefficient_nonneg (hxs : 0 < xs) (k : ℕ) (w : PhysicalBandWindow n steps xs) :
    0 ≤ w.coefficient k := by
  exact mul_nonneg (by positivity) (add_nonneg (w.nearCoefficient_nonneg hxs k)
    (mul_nonneg w.mass_pos.le (w.farCoefficient_nonneg k)))

end PhysicalBandWindow
end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalIntervalCells {ι : Type} (steps : List (GaussianStep ι)) (p q : ℕ) :
    Finset (Fin (steps.length+1)) := Finset.univ.filter fun j => p ≤ j.val ∧ j.val<q

 @[simp] theorem mem_physicalIntervalCells {ι : Type} (steps : List (GaussianStep ι))
    (p q : ℕ) (j : Fin (steps.length+1)) :
    j ∈ physicalIntervalCells steps p q ↔ p ≤ j.val ∧ j.val<q := by
  simp [physicalIntervalCells]

 theorem physicalIntervalMass {ι : Type} (steps : List (GaussianStep ι)) (a : ℝ)
    {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ steps.length+1) :
    physicalWindowMass steps a (physicalIntervalCells steps p q)=
      physicalCutMass a steps q-physicalCutMass a steps p := by
  unfold physicalWindowMass
  simp_rw [pathMassDifferences_eq_cutMass]
  calc _ = ∑ j ∈ Finset.Ico p q, (physicalCutMass a steps (j+1)-physicalCutMass a steps j) := by
         apply Finset.sum_bij (fun j _ => j.val)
         · intro j hj
           exact Finset.mem_Ico.mpr ((mem_physicalIntervalCells steps p q j).mp hj)
         · intro i hi j hj hij
           exact Fin.ext hij
         · intro j hj
           have hj' := Finset.mem_Ico.mp hj
           let i : Fin (steps.length+1) := ⟨j,hj'.2.trans_le hq⟩
           exact ⟨i,(mem_physicalIntervalCells steps p q i).mpr hj',rfl⟩
         · intros; rfl
       _ = _ := Finset.sum_Ico_sub _ hpq

 theorem physicalIntervalCell_band (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (p q : Fin (steps.length+2)) (j : Fin (steps.length+1))
    (hj : physicalWindowCellMass steps 0 (physicalIntervalCells steps p.val q.val) j≠0) :
    Ioc (r p) (r q) ⊇ Ioc (r j.castSucc) (r j.succ) := by
  have hmem : j ∈ physicalIntervalCells steps p.val q.val := by
    by_contra h
    exact hj (by simp [physicalWindowCellMass,h])
  have hj' := (mem_physicalIntervalCells steps p.val q.val j).mp hmem
  intro s hs
  exact ⟨(hr (show p ≤ j.castSucc from hj'.1)).trans_lt hs.1,
    hs.2.trans (hr (show j.succ ≤ q from Nat.succ_le_iff.mpr hj'.2))⟩

 theorem physicalIntervalCell_cap (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r) (p q : Fin (steps.length+2))
    {α : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hcoord : ∀ j : Fin (steps.length+2), p ≤ j → j ≤ q → physicalCutMass 0 steps j.val=α (r j))
    (hcap : ∀ s ∈ Icc (r p) (r q), ∀ t ∈ Icc (r p) (r q), s ≤ t → α t-α s ≤ A*(t-s))
    (j : Fin (steps.length+1)) :
    physicalWindowCellMass steps 0 (physicalIntervalCells steps p.val q.val) j ≤
      A*(r j.succ-r j.castSucc) := by
  unfold physicalWindowCellMass
  split_ifs with hj
  · have hj' := (mem_physicalIntervalCells steps p.val q.val j).mp hj
    have hpj : p ≤ j.castSucc := hj'.1
    have hjq : j.succ ≤ q := Nat.succ_le_iff.mpr hj'.2
    have hjs : j.castSucc ≤ j.succ := by change j.val ≤ j.val+1; omega
    have hu := hcoord j.succ (hpj.trans hjs) hjq
    have hl := hcoord j.castSucc hpj (hjs.trans hjq)
    simp only [Fin.val_succ,Fin.val_castSucc] at hu hl
    rw [pathMassDifferences_eq_cutMass,hu,hl]
    exact hcap _ ⟨hr hpj,hr (hjs.trans hjq)⟩ _ ⟨hr (hpj.trans hjs),hr hjq⟩ (hr hjs)
  · exact mul_nonneg hA (sub_nonneg.mpr (hr (show j.castSucc ≤ j.succ by change j.val ≤ j.val+1; omega)))

 theorem physicalCell_pos_of_cap (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 steps) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r) {A : ℝ}
    (hcap : ∀ j, physicalWindowCellMass steps 0 J j ≤ A*(r j.succ-r j.castSucc)) :
    ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc<r j.succ := by
  intro j hj
  have hm := physicalWindowCellMass_nonneg steps ha J j
  have hp : 0<physicalWindowCellMass steps 0 J j := lt_of_le_of_ne hm hj.symm
  have hh := hcap j
  have hrj : r j.castSucc ≤ r j.succ := hr (show j.castSucc ≤ j.succ by change j.val ≤ j.val+1; omega)
  by_contra hn
  have he := le_antisymm hrj (le_of_not_gt hn)
  rw [he,sub_self,mul_zero] at hh
  linarith

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverseConstraint_local_cap {r₀ u₀ a b : ℝ} {k M : ℝ → ℝ}
    (hm : MonotoneOn M (Icc (0:ℝ) 1))
    {α : boundedMassProfiles} (hα : α ∈ inverseIntegralConstraints r₀ u₀ k M)
    (ha : a ∈ Icc r₀ 1) (hb : b ∈ Icc r₀ 1) (hab : a≤b) :
    α.val b-α.val a ≤ M (α.val b)*(b-a) := by
  apply (hα.2.2 a ha b hb hab).2.trans
  calc (∫ t in a..b, M (α.val t)) ≤ ∫ _ in a..b, M (α.val b) := by
         apply intervalIntegral.integral_mono_on hab
         · exact (show Monotone (fun t => M (α.val t)) from fun s t hst =>
             hm (α.property.1 s) (α.property.1 t) (α.property.2 hst)).intervalIntegrable
         · exact intervalIntegrable_const
         · intro t ht
           exact hm (α.property.1 t) (α.property.1 b) (α.property.2 ht.2)
       _ = _ := by simp [mul_comm]

 theorem inverseConstraint_window_cap {r₀ u₀ a b : ℝ} {k M : ℝ → ℝ}
    (hm : MonotoneOn M (Icc (0:ℝ) 1))
    {α : boundedMassProfiles} (hα : α ∈ inverseIntegralConstraints r₀ u₀ k M)
    (ha : r₀≤a) (hb : b≤1) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s≤t → α.val t-α.val s ≤ M (α.val b)*(t-s) := by
  intro s hs t ht hst
  apply (inverseConstraint_local_cap hm hα ⟨ha.trans hs.1,hs.2.trans hb⟩
    ⟨ha.trans ht.1,ht.2.trans hb⟩ hst).trans
  exact mul_le_mul_of_nonneg_right
    (hm (α.property.1 t) (α.property.1 b) (α.property.2 ht.2)) (sub_nonneg.mpr hst)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def constrainedPhysicalWindow (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 steps) {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hu : u₀≤1) (hu₀ : 0≤u₀) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0≤M u)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (xs η D₀ cl cu R F ε : ℝ) (J : ℕ) (p q : Fin (steps.length+2))
    (hpq : p≤q) (hup : u₀≤physicalCutMass 0 steps p.val)
    (hmass : physicalCutMass 0 steps p.val<physicalCutMass 0 steps q.val)
    (hcl : 0<cl) (hcu : 0≤cu) (hD : 0<D₀) (hR : 0<R)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/R≤F) (hJ : 1≤J)
    (hε : 0≤ε)
    (hmesh : ∀ j : Fin (steps.length+1),
      physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha j.succ-
        physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha j.castSucc≤ε)
    (hxs : xs≤physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha p)
    (hη : 0<η) (hηa : η≤physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha p)
    (hεa : ε≤physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha p/2)
    (hr₀ : r₀<physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha p/2)
    (hT : (2:ℝ)^J*physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha q≤1)
    (hRJ : R≤(2:ℝ)^J*physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha p)
    (hreg : ∀ t ∈ Icc (physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha p/2)
      ((2:ℝ)^J*physicalQuantileGrid hr hu hc hk hkc hm (hM 1 (by norm_num)) α steps ha q),
      cl*t≤α.val.val t ∧ α.val.val t≤cu*t) : PhysicalBandWindow n steps xs := by
  let hM₁ := hM 1 (by norm_num)
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps ha
  let selected := physicalIntervalCells steps p.val q.val
  have hrm : Monotone r := physicalQuantileGrid_mono hr hu hc hk hkc hm hM₁ α steps ha
  have hqp : q.val ≤ steps.length+1 := Nat.le_of_lt_succ q.isLt
  have hmassid : physicalWindowMass steps 0 selected=
      physicalCutMass 0 steps q.val-physicalCutMass 0 steps p.val := physicalIntervalMass steps 0 hpq hqp
  have hcoord : ∀ j : Fin (steps.length+2), p≤j → j≤q → physicalCutMass 0 steps j.val=α.val.val (r j) := by
    intro j hpj hjq
    exact physicalQuantileGrid_coord hr hu hc hk hkc hm hM₁ α steps ha j
      (hup.trans (physicalCutMass_monotone steps ha hpj))
  have hA : 0≤M (physicalCutMass 0 steps q.val) := hM _ (physicalCutMass_mem steps ha q.val)
  have hcap : ∀ j, physicalWindowCellMass steps 0 selected j≤
      M (physicalCutMass 0 steps q.val)*(r j.succ-r j.castSucc) := by
    apply physicalIntervalCell_cap n steps r hrm p q hA hcoord
    rw [hcoord q hpq le_rfl]
    exact inverseConstraint_window_cap hm α.property
      (physicalQuantileGrid_mem hr hu hc hk hkc hm hM₁ α steps ha p).1
      (physicalQuantileGrid_mem hr hu hc hk hkc hm hM₁ α steps ha q).2
  exact {
    selected := selected
    radius := r
    radius_mono := hrm
    cell_pos := physicalCell_pos_of_cap n steps ha selected r hrm hcap
    mass_pos := by rw [hmassid]; exact sub_pos.mpr hmass
    a := r p
    b := r q
    η := η
    A := M (physicalCutMass 0 steps q.val)
    D₀ := D₀
    c₀ := cl/2
    C := cu
    R := R
    F := F
    depth := J
    c₀_pos := by positivity
    D₀_pos := hD
    C_nonneg := hcu
    R_pos := hR
    F_mass := hFmass
    F_radius := hFradius
    xa := hxs
    ab := hrm hpq
    η_pos := hη
    η_le := hηa
    depth_pos := hJ
    last_radius := hRJ
    A_nonneg := hA
    cell_cap := hcap
    cell_band := physicalIntervalCell_band n steps r hrm p q
    mass_comparable := physicalQuantileSample_regular hr hu hc hk hkc hm hM₁ α steps ha
      hε hεa hr₀ hT hcl.le hcu hu₀ hmesh hreg }

end SKFluctuations

end

end OAI
