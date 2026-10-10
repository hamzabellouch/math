import OAI.Analysis.HenonEmden.Intervals

namespace OAI

section LayerPressure


open Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace HenonLaneEmden.LayerPressure

/-- The actual (nonempty) connected components of an open real line layer. -/
def components (U : Set ℝ) : Set (Set ℝ) := connectedComponentIn U '' U

lemma component_nonempty {U I : Set ℝ} (hI : I ∈ components U) : I.Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hI
  exact ⟨x, mem_connectedComponentIn hx⟩

lemma component_open {U I : Set ℝ} (hU : IsOpen U) (hI : I ∈ components U) : IsOpen I := by
  obtain ⟨x,hx,rfl⟩ := hI
  exact hU.connectedComponentIn

lemma component_connected {U I : Set ℝ} (hI : I ∈ components U) : IsConnected I := by
  obtain ⟨x,hx,rfl⟩ := hI
  exact ⟨⟨x,mem_connectedComponentIn hx⟩,isPreconnected_connectedComponentIn⟩

lemma component_identify {U I : Set ℝ} (hI : I ∈ components U) {x : ℝ} (hx : x ∈ I) :
    connectedComponentIn U x = I := by
  obtain ⟨y,hy,rfl⟩ := hI
  exact (connectedComponentIn_eq hx).symm

lemma components_disjoint (U : Set ℝ) : (components U).PairwiseDisjoint id := by
  intro I hI J hJ hne
  change Disjoint I J
  rw [Set.disjoint_left]
  intro x hxI hxJ
  exact hne ((component_identify hI hxI).symm.trans (component_identify hJ hxJ))

lemma components_countable {U : Set ℝ} (hU : IsOpen U) : (components U).Countable :=
  (components_disjoint U).countable_of_isOpen (fun _ h => component_open hU h)
    (fun _ h => component_nonempty h)

lemma biUnion_components (U : Set ℝ) : (⋃ I ∈ components U, I) = U := by
  apply subset_antisymm
  · apply iUnion₂_subset
    intro I hI
    obtain ⟨x,hx,rfl⟩ := hI
    exact connectedComponentIn_subset U x
  · intro x hx
    exact mem_iUnion₂.mpr ⟨connectedComponentIn U x,⟨x,hx,rfl⟩,mem_connectedComponentIn hx⟩

/-- Nonnegative integration can be summed over two line-layer component families
without any integrability or finiteness assumption on either side. -/
lemma lintegral_layer_comparison {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (F G : ℝ × ℝ → ℝ≥0∞)
    (h : ∀ I ∈ components U, ∀ J ∈ components V,
      (∫⁻ z in I ×ˢ J, F z) ≤ ∫⁻ z in I ×ˢ J, G z) :
    (∫⁻ z in U ×ˢ V, F z) ≤ ∫⁻ z in U ×ˢ V, G z := by
  let C : Set (Set ℝ × Set ℝ) := components U ×ˢ components V
  let S : Set ℝ × Set ℝ → Set (ℝ × ℝ) := fun p => p.1 ×ˢ p.2
  have hC : C.Countable := (components_countable hU).prod (components_countable hV)
  have hop : ∀ p ∈ C, MeasurableSet (S p) := by
    intro p hp
    exact (component_open hU hp.1).measurableSet.prod (component_open hV hp.2).measurableSet
  have hdis : C.PairwiseDisjoint S := by
    intro p hp q hq hpq
    change Disjoint (S p) (S q)
    rw [Set.disjoint_left]
    rintro ⟨x,y⟩ hxp hxq
    apply hpq
    apply Prod.ext
    · exact (component_identify hp.1 hxp.1).symm.trans (component_identify hq.1 hxq.1)
    · exact (component_identify hp.2 hxp.2).symm.trans (component_identify hq.2 hxq.2)
  have heq : (⋃ p ∈ C, S p) = U ×ˢ V := by
    ext z
    simp only [mem_iUnion, mem_prod, C, S]
    constructor
    · rintro ⟨⟨I,J⟩,⟨hI,hJ⟩,hzI,hzJ⟩
      exact ⟨by rw [← biUnion_components U]; exact mem_iUnion₂.mpr ⟨I,hI,hzI⟩,
        by rw [← biUnion_components V]; exact mem_iUnion₂.mpr ⟨J,hJ,hzJ⟩⟩
    · rintro ⟨hzU,hzV⟩
      rw [← biUnion_components U] at hzU
      rw [← biUnion_components V] at hzV
      obtain ⟨I,hI,hzI⟩ := mem_iUnion₂.mp hzU
      obtain ⟨J,hJ,hzJ⟩ := mem_iUnion₂.mp hzV
      exact ⟨(I,J),⟨hI,hJ⟩,hzI,hzJ⟩
  rw [← heq,lintegral_biUnion hC hop hdis F,lintegral_biUnion hC hop hdis G]
  exact ENNReal.tsum_le_tsum fun p => h p.val.1 p.property.1 p.val.2 p.property.2

lemma open_connected_eq_Ioo {I : Set ℝ} (hop : IsOpen I) (hcon : IsConnected I)
    (hlo : BddBelow I) (hhi : BddAbove I) : I = Ioo (sInf I) (sSup I) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hop.mem_nhds hx)
    have hm : (a+x)/2 ∈ I := hsub ⟨by linarith [hab.1], by linarith [hab.1,hab.2]⟩
    have hp : (x+b)/2 ∈ I := hsub ⟨by linarith [hab.1,hab.2], by linarith [hab.2]⟩
    exact ⟨lt_of_le_of_lt (csInf_le hlo hm) (by linarith [hab.1]),
      lt_of_lt_of_le (by linarith [hab.2]) (le_csSup hhi hp)⟩
  · exact hcon.Ioo_csInf_csSup_subset hlo hhi

open IntervalGeometry

/-- The interval comparison stated directly on a product of two open components.
The endpoint values on an unbounded component are immaterial because its weight
is zero. All integrands are nonnegative extended values. -/
lemma component_pair_comparison (n : ℕ) (hn : 3 ≤ n)
    {I J : Set ℝ} (hopI : IsOpen I) (hopJ : IsOpen J)
    (hconI : IsConnected I) (hconJ : IsConnected J)
    {l C cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ)
    (hbI : 0 < cI → BddBelow I ∧ BddAbove I)
    (hbJ : 0 < cJ → BddBelow J ∧ BddAbove J) :
    (∫⁻ z in I ×ˢ J, ENNReal.ofReal ((cI+cJ)*kernel n l C (z.1-z.2))) ≤
    ∫⁻ z in I ×ˢ J, ENNReal.ofReal
      (cI*((kernel n l C (sInf I-z.2)+kernel n l C (sSup I-z.2))/2) +
       cJ*((kernel n l C (z.1-sInf J)+kernel n l C (z.1-sSup J))/2) +
       (((n:ℝ)-2)*min cI cJ*((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+|cI-cJ|)*
         kernel n l C (z.1-z.2)) := by
  by_cases hzI : cI = 0
  · subst cI
    apply lintegral_mono; intro z
    apply ENNReal.ofReal_le_ofReal
    simp only [zero_add, zero_mul, mul_zero, min_eq_left hcJ, zero_sub, abs_neg, abs_of_nonneg hcJ]
    exact le_add_of_nonneg_left (mul_nonneg hcJ (div_nonneg
      (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num)))
  by_cases hzJ : cJ = 0
  · subst cJ
    apply lintegral_mono; intro z
    apply ENNReal.ofReal_le_ofReal
    simp only [add_zero, zero_mul, min_eq_right hcI, mul_zero, zero_add, sub_zero, abs_of_nonneg hcI]
    exact le_add_of_nonneg_left (mul_nonneg hcI (div_nonneg
      (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num)))
  obtain ⟨hloI,hhiI⟩ := hbI (lt_of_le_of_ne hcI (Ne.symm hzI))
  obtain ⟨hloJ,hhiJ⟩ := hbJ (lt_of_le_of_ne hcJ (Ne.symm hzJ))
  have heqI := open_connected_eq_Ioo hopI hconI hloI hhiI
  have heqJ := open_connected_eq_Ioo hopJ hconJ hloJ hhiJ
  have ha : sInf I ≤ sSup I := csInf_le_csSup hconI.nonempty hloI hhiI
  have hb : sInf J ≤ sSup J := csInf_le_csSup hconJ.nonempty hloJ hhiJ
  have hk := kernel_continuous n hl C
  have hD : Continuous (fun z : ℝ × ℝ => (z.1-z.2)^2/(l^2+(z.1-z.2)^2)) :=
    ((continuous_fst.sub continuous_snd).pow 2).div
      (continuous_const.add ((continuous_fst.sub continuous_snd).pow 2))
      (fun z => ne_of_gt (base_pos hl (z.1-z.2)))
  have hcL : Continuous (fun z : ℝ × ℝ => (cI+cJ)*kernel n l C (z.1-z.2)) := by fun_prop
  have hcR : Continuous (fun z : ℝ × ℝ =>
      cI*((kernel n l C (sInf I-z.2)+kernel n l C (sSup I-z.2))/2) +
       cJ*((kernel n l C (z.1-sInf J)+kernel n l C (z.1-sSup J))/2) +
       (((n:ℝ)-2)*min cI cJ*((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+|cI-cJ|)*
         kernel n l C (z.1-z.2)) := by fun_prop
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict, lintegral_prod _ hcL.measurable.ennreal_ofReal.aemeasurable,
    lintegral_prod _ hcR.measurable.ennreal_ofReal.aemeasurable]
  simpa only [← heqI, ← heqJ] using
    (bounded_weighted_interval_lintegral n hn hl hC ha hb hcI hcJ)

/-- Weighted interval comparison summed over two general open line layers.  The
coefficients are arbitrary nonnegative component-constant weights, with positive
weight permitted only on bounded components. -/
lemma open_layer_comparison (n : ℕ) (hn : 3 ≤ n)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (c d : Set ℝ → ℝ) {l C : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hc : ∀ I ∈ components U, 0 ≤ c I) (hd : ∀ J ∈ components V, 0 ≤ d J)
    (hbc : ∀ I ∈ components U, 0 < c I → BddBelow I ∧ BddAbove I)
    (hbd : ∀ J ∈ components V, 0 < d J → BddBelow J ∧ BddAbove J) :
    (∫⁻ z in U ×ˢ V, ENNReal.ofReal
      ((c (connectedComponentIn U z.1)+d (connectedComponentIn V z.2))*kernel n l C (z.1-z.2))) ≤
    ∫⁻ z in U ×ˢ V, ENNReal.ofReal
      (c (connectedComponentIn U z.1)*
        ((kernel n l C (sInf (connectedComponentIn U z.1)-z.2)+
          kernel n l C (sSup (connectedComponentIn U z.1)-z.2))/2) +
       d (connectedComponentIn V z.2)*
        ((kernel n l C (z.1-sInf (connectedComponentIn V z.2))+
          kernel n l C (z.1-sSup (connectedComponentIn V z.2)))/2) +
       (((n:ℝ)-2)*min (c (connectedComponentIn U z.1)) (d (connectedComponentIn V z.2))*
         ((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+
         |c (connectedComponentIn U z.1)-d (connectedComponentIn V z.2)|)*
         kernel n l C (z.1-z.2)) := by
  apply lintegral_layer_comparison hU hV
  intro I hI J hJ
  have hm : MeasurableSet (I ×ˢ J) :=
    (component_open hU hI).measurableSet.prod (component_open hV hJ).measurableSet
  have hp := component_pair_comparison n hn (component_open hU hI) (component_open hV hJ)
    (component_connected hI) (component_connected hJ) hl hC (hc I hI) (hd J hJ)
    (hbc I hI) (hbd J hJ)
  convert hp using 1
  · apply setLIntegral_congr_fun hm
    intro z hz
    dsimp only
    rw [component_identify hI hz.1, component_identify hJ hz.2]
  · apply setLIntegral_congr_fun hm
    intro z hz
    dsimp only
    rw [component_identify hI hz.1, component_identify hJ hz.2]

open LineComponents

noncomputable def lineWeight (U : Set ℝ) (h d : ℝ → ℝ) (δ x : ℝ) : ℝ :=
  (setWeight h d δ (connectedComponentIn U x)).toReal

noncomputable def leftAverage (U : Set ℝ) (k : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (k (sInf (connectedComponentIn U x)-y)+k (sSup (connectedComponentIn U x)-y))/2

noncomputable def rightAverage (V : Set ℝ) (k : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (k (x-sInf (connectedComponentIn V y))+k (x-sSup (connectedComponentIn V y)))/2

lemma lineWeight_nonneg (U : Set ℝ) (h d : ℝ → ℝ) (δ x : ℝ) :
    0 ≤ lineWeight U h d δ x := ENNReal.toReal_nonneg

lemma lineWeight_le {U : Set ℝ} {h d : ℝ → ℝ} {δ x : ℝ}
    (hx : x ∈ U) (hh : 0 ≤ h x) : lineWeight U h d δ x ≤ h x := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (setWeight_le (h := h) (d := d)
    (δ := δ) (mem_connectedComponentIn hx))
  simpa only [lineWeight,ENNReal.toReal_ofReal hh] using he

/-- The actual capped component weights satisfy the summed nonnegative layer
comparison of equation (layer-pair), still before integrations over levels and
transverse variables. No boundedness of either whole layer is assumed. -/
lemma weighted_source_layer_comparison (n : ℕ) (hn : 3 ≤ n)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (h₁ h₂ d₁ d₂ : ℝ → ℝ) (δ : ℝ) {l C : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hh₁ : ∀ x ∈ U, 0 ≤ h₁ x) :
    (∫⁻ z in U ×ˢ V, ENNReal.ofReal
      ((lineWeight U h₁ d₁ δ z.1+lineWeight V h₂ d₂ δ z.2)*kernel n l C (z.1-z.2))) ≤
    ∫⁻ z in U ×ˢ V, ENNReal.ofReal
      (lineWeight U h₁ d₁ δ z.1*leftAverage U (kernel n l C) z.1 z.2 +
       lineWeight V h₂ d₂ δ z.2*rightAverage V (kernel n l C) z.1 z.2 +
       (((n:ℝ)-2)*h₁ z.1*((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+
         |lineWeight U h₁ d₁ δ z.1-lineWeight V h₂ d₂ δ z.2|)*kernel n l C (z.1-z.2)) := by
  have hh := open_layer_comparison n hn hU hV
    (fun I => (setWeight h₁ d₁ δ I).toReal) (fun J => (setWeight h₂ d₂ δ J).toReal) hl hC
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ hI hpos => setWeight_pos_bounded (component_connected hI) hpos)
    (fun _ hJ hpos => setWeight_pos_bounded (component_connected hJ) hpos)
  apply hh.trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (hU.measurableSet.prod hV.measurableSet)] with z hz
  apply ENNReal.ofReal_le_ofReal
  dsimp only [lineWeight,leftAverage,rightAverage]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (kernel_nonneg n hC _)
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) (base_pos hl _).le)
  apply mul_le_mul_of_nonneg_left _ (by
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  exact (min_le_left _ _).trans (lineWeight_le hz.1 (hh₁ z.1 hz.1))

end HenonLaneEmden.LayerPressure
end LayerPressure

end OAI
