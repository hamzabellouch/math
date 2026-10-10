import OAI.Probability.DirectionalWalk.RadiusLaunch

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def finiteHighMaximum {d : ℕ} (v : Fin d → ℝ) (L : ℝ) : Set (Path d) :=
  {X | (∃ b : ℕ, ∀ n, height v (X n) ≤ b) ∧ ∃ j, L ≤ height v (X j)}

lemma measurableSet_finiteHighMaximum {d : ℕ} (v : Fin d → ℝ) (L : ℝ) :
    MeasurableSet (finiteHighMaximum v L) := by
  simp only [finiteHighMaximum,Set.ofPred_and,Set.ofPred_exists]
  exact (MeasurableSet.iUnion fun b : ℕ => measurableSet_alwaysBelow v b).inter
    (MeasurableSet.iUnion fun j => measurableSet_le measurable_const
      ((measurable_of_countable (height v)).comp (measurable_pi_apply j)))

lemma finiteHighMaximum_mono {d : ℕ} (v : Fin d → ℝ) {L U : ℝ} (h : L ≤ U) :
    finiteHighMaximum v U ⊆ finiteHighMaximum v L := by
  rintro X ⟨hb,j,hj⟩
  exact ⟨hb,j,h.trans hj⟩

lemma tendsto_measure_finiteHighMaximum {d : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (v : Fin d → ℝ) : Tendsto (fun n : ℕ => P (finiteHighMaximum v n)) atTop (𝓝 0) := by
  have hh : (⋂ n : ℕ, finiteHighMaximum v n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    have h := Set.mem_iInter.mp hX
    obtain ⟨b,hb⟩ := (h 0).1
    obtain ⟨j,hj⟩ := (h (b+1)).2
    have hb' := hb j
    have : (b:ℝ)+1 ≤ b := by simpa only [Nat.cast_add,Nat.cast_one] using hj.trans hb'
    linarith
  have hm := tendsto_measure_iInter_atTop
    (fun n : ℕ => (measurableSet_finiteHighMaximum v n).nullMeasurableSet (μ := P))
    (fun m n hmn => finiteHighMaximum_mono v (by exact_mod_cast hmn))
    (show ∃ i : ℕ, P (finiteHighMaximum v i) ≠ ⊤ from ⟨0,measure_ne_top _ _⟩)
  simpa only [hh,measure_empty,Function.comp_def] using hm

lemma measurableSet_goodSlabPath {d : ℕ} (v : Fin d → ℝ) :
    MeasurableSet {X : Path d | GoodSlabPath v X} := by
  simp only [GoodSlabPath,Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (MeasurableSet.iInter fun k => (Set.to_countable {γ | RegenerationWord v γ}).measurableSet.preimage
      ((measurable_pi_apply k).comp (measurable_slabs v)))

def radiusTemplate {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (q : ℕ) : Set (Path d) :=
  {Z | GoodSlabPath v Z} ∩ goodRadiusPrefix v a c C b q

lemma measurableSet_radiusTemplate {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (q : ℕ) :
    MeasurableSet (radiusTemplate v a c C b q) :=
  (measurableSet_goodSlabPath v).inter (measurableSet_goodRadiusPrefix v a c C b q)

lemma annealed_radiusTemplate {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (q : ℕ) :
    annealed μ 0 (radiusTemplate v a c C b q) = annealed μ 0 (nonBacktracking v) *
      conditioned μ v (goodRadiusPrefix v a c C b q) := by
  have hsub : radiusTemplate v a c C b q ⊆ nonBacktracking v :=
    fun Z hZ t => goodSlabPath_height_nonneg v Z hZ.1 t
  have he : conditioned μ v (radiusTemplate v a c C b q) =
      conditioned μ v (goodRadiusPrefix v a c C b q) := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with Z hZ
    exact propext ⟨fun h => h.2, fun h => ⟨hZ, h⟩⟩
  have hh := cond_mul_eq_inter (measurableSet_nonBacktracking v) (radiusTemplate v a c C b q) (annealed μ 0)
  rw [Set.inter_eq_right.mpr hsub] at hh
  change conditioned μ v (radiusTemplate v a c C b q) * _ = _ at hh
  rw [he,mul_comm] at hh
  exact hh.symm

lemma shiftPath_add_neg_cancel {d : ℕ} (x : Site d) (Z : Path d) :
    shiftPath (-x) (shiftPath x Z) = Z := by
  funext t
  simp [shiftPath]

lemma shiftPath_neg_add_cancel {d : ℕ} (x : Site d) (Z : Path d) :
    shiftPath x (shiftPath (-x) Z) = Z := by
  funext t
  simp [shiftPath]

lemma annealed_translated_event {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (shiftPath (-x) ⁻¹' E) = annealed μ 0 E := by
  have hh := congrArg (fun P : Measure (Path d) => P (shiftPath (-x) ⁻¹' E)) (annealed_shift μ 0 x)
  rw [zero_add,Measure.map_apply (measurable_shiftPath x) ((measurable_shiftPath (-x)) hE)] at hh
  have he : shiftPath x ⁻¹' (shiftPath (-x) ⁻¹' E) = E := by
    ext Z
    simp only [Set.mem_preimage,shiftPath_add_neg_cancel]
  rw [he] at hh
  exact hh.symm

lemma radius_launch_cylinder_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (u e : Step d) (a β c C b L U : ℝ)
    (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c) (hta : 1 < β*a)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (hq : U-M-c*q+b < 0)
    (γ : Path d) (n : ℕ) (hr : radiusLaunch v u (β*a) L U γ n) :
    (meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)) *
      annealed μ 0 (pathCylinder n γ) ≤
      annealed μ 0 (pathCylinder n γ ∩ finiteHighMaximum v L) := by
  let δ := concatPath n γ (axialRay (γ n) e)
  let x := axialRay (γ n) e M
  let F := shiftPath (-x) ⁻¹' radiusTemplate (-v) a c C b q
  let K : Set (Site d) := {y | ∃ i < n+M, δ i = y}
  have hF : MeasurableSet F :=
    (measurable_shiftPath (-x)) (measurableSet_radiusTemplate (-v) a c C b q)
  have hx : δ (n+M) = x := concatPath_after _ _ _ _
  have hFK : F ⊆ avoids K := by
    intro W hW t
    rintro ⟨i,hi,hii⟩
    let Z := shiftPath (-x) W
    have hz : W = shiftPath x Z := (shiftPath_neg_add_cancel x W).symm
    have hZ : Z ∈ radiusTemplate (-v) a c C b q := hW
    have hsep := radius_template_avoids v u e a β c C b U ha hβ hbc he M q hM hq
      γ hr.1 hr.2.1 (hr.2.2.2 n le_rfl) Z hZ.1 hZ.2 i hi t
    apply hsep
    have hwt : W t = Z t+x := congr_fun hz t
    exact hwt.symm.trans hii.symm
  have hraw : annealed μ x F = annealed μ 0 (radiusTemplate (-v) a c C b q) :=
    annealed_translated_event μ x (measurableSet_radiusTemplate (-v) a c C b q)
  have hfac := annealed_fresh_prefix_tail μ K 0 (n+M) δ (fun i hi => ⟨i,hi,rfl⟩) hF
  rw [Set.inter_eq_left.mpr hFK,hx,hraw] at hfac
  have hscript : annealed μ 0 (pathCylinder (n+M) δ) =
      annealed μ 0 (pathCylinder n γ) * meanStep μ e ^ M := by
    have hh := annealed_disjoint_prefix_tail μ 0 n M γ (axialRay (γ n) e)
      (axialRay_zero _ _).symm (fun i hi j _ => radius_script_fresh v u e (β*a) hta he γ hr.1 i hi j)
    rw [prefix_tail_inter,ite_eq_left (axialRay_zero _ _).symm,annealed_axialRay] at hh
    exact hh
  have hsub : pathCylinder (n+M) δ ∩ tailPath (n+M) ⁻¹' F ⊆
      pathCylinder n γ ∩ finiteHighMaximum v L := by
    rintro Y ⟨hY,hT⟩
    let Z := shiftPath (-x) (tailPath (n+M) Y)
    have hZ : Z ∈ radiusTemplate (-v) a c C b q := hT
    have ht : tailPath (n+M) Y = shiftPath x Z :=
      (shiftPath_neg_add_cancel x (tailPath (n+M) Y)).symm
    have hy : Y ∈ pathCylinder n γ := by
      intro i hi
      rw [hY i (by omega)]
      exact concatPath_before _ _ _ (axialRay_zero _ _).symm hi
    refine ⟨hy,?_,?_⟩
    · obtain ⟨b',hb'⟩ := exists_nat_ge U
      exact ⟨b',fun i => (radius_continuation_maximum v e he γ Y Z n M hY ht hZ.1 U hr.2.2.2 i).trans hb'⟩
    · obtain ⟨j,hj,hjl⟩ := hr.2.2.1
      exact ⟨j,by rw [hy j hj];exact hjl⟩
  have hm := measure_mono (μ := annealed μ 0) hsub
  rw [hfac,hscript] at hm
  convert hm using 1; ac_rfl

lemma radius_launch_probability_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (u e : Step d) (a β c C b L U : ℝ)
    (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c) (hta : 1 < β*a)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (hq : U-M-c*q+b < 0) :
    (meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)) *
      annealed μ 0 {X | ∃ n, radiusLaunch v u (β*a) L U X n} ≤
      annealed μ 0 (finiteHighMaximum v L) :=
  measure_first_prefix_lower (annealed μ 0) (radiusLaunch v u (β*a) L U)
    (measurableSet_radiusLaunch v u (β*a) L U)
    (fun _ _ h _ hY => radiusLaunch_prefix v u (β*a) L U h hY)
    (measurableSet_finiteHighMaximum v L) _
    (radius_launch_cylinder_lower μ v u e a β c C b L U ha hβ hbc hta he M q hM hq)

lemma controlledSlabOccurrence_launch {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (a B β c C b L : ℝ) (ha : 0 < a) (hβ : 0 ≤ β)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hB : Real.sqrt d*(2+β*(C+2)) < B-1)
    (l N : ℕ) (hl : b ≤ l+1) (hL : L ≤ c*l-b)
    (hocc : X ∈ controlledSlabOccurrence v a c C b
      (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N)) :
    ∃ e : Step d, ∃ n, radiusLaunch v e (β*a) L ((C+2)*N) X n := by
  obtain ⟨k,hk,hgp,hbig⟩ := Set.mem_iUnion₂.mp hocc
  have hki := Finset.mem_Ico.mp hk
  have hg := (goodRadiusPrefix_iff v a c C b k X).mp hgp k le_rfl
  have hwidth : slabWidth v (slabs v X k) ≤ k+1 := hbig.2
  apply largeRadius_launch v X hX a B β (C+2) L ((C+2)*N) ha hβ (by linarith) hB hbig.1 hg.2.2
  · have hb : b ≤ (k : ℝ)+1 := hl.trans (by exact_mod_cast Nat.add_le_add_right hki.1 1)
    rw [slabHeightSum,Finset.sum_range_succ]
    change slabHeightSum v X k + slabWidth v (slabs v X k) ≤ _
    nlinarith [hg.2.1]
  · exact hL.trans ((sub_le_sub_right (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr hki.1) hc) b).trans hg.1)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show k+1 ≤ N by omega)) (by linarith)

lemma annealed_goodSlabPath_event {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (E : Set (Path d)) :
    annealed μ 0 ({X | GoodSlabPath v X} ∩ E) =
      annealed μ 0 (nonBacktracking v) * conditioned μ v E := by
  have hsub : {X | GoodSlabPath v X} ∩ E ⊆ nonBacktracking v :=
    fun X hX t => goodSlabPath_height_nonneg v X hX.1 t
  have he : conditioned μ v ({X | GoodSlabPath v X} ∩ E) = conditioned μ v E := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
    exact propext ⟨fun h => h.2,fun h => ⟨hX,h⟩⟩
  have hh := cond_mul_eq_inter (measurableSet_nonBacktracking v)
    ({X | GoodSlabPath v X} ∩ E) (annealed μ 0)
  rw [Set.inter_eq_right.mpr hsub] at hh
  change conditioned μ v ({X | GoodSlabPath v X} ∩ E) * _ = _ at hh
  rw [he,mul_comm] at hh
  exact hh.symm

lemma radius_occurrence_probability_upper {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (e : Step d)
    (a B β c C b L : ℝ) (ha : 0 < a) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hB : Real.sqrt d*(2+β*(C+2)) < B-1)
    (hbc : 1 ≤ β*c) (hta : 1 < β*a) (he : height v (stepVector e) = -1)
    (M q l N : ℕ) (hM : (M : ℝ) < a*(M*β-1-β*b))
    (hq : (C+2)*N-M-c*q+b < 0) (hl : b ≤ l+1) (hL : L ≤ c*l-b) :
    ((meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)).toReal *
      (annealed μ 0).real (nonBacktracking v)) *
      (conditioned μ v).real (controlledSlabOccurrence v a c C b
        (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N)) ≤
      (Fintype.card (Step d) : ℝ) * (annealed μ 0).real (finiteHighMaximum v L) := by
  let A := controlledSlabOccurrence v a c C b
    (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N)
  let E (u : Step d) : Set (Path d) := {X | ∃ n, radiusLaunch v u (β*a) L ((C+2)*N) X n}
  let κ := meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)
  have hsub : {X | GoodSlabPath v X} ∩ A ⊆ ⋃ u : Step d, E u := by
    intro X hX
    obtain ⟨u,n,hn⟩ := controlledSlabOccurrence_launch v X hX.1 a B β c C b L ha hβ hc hC hB l N hl hL hX.2
    exact Set.mem_iUnion.mpr ⟨u,n,hn⟩
  have hmass := (measureReal_mono (μ := annealed μ 0) hsub (measure_ne_top _ _)).trans
    (measureReal_iUnion_fintype_le (μ := annealed μ 0) E)
  have heq : (annealed μ 0).real ({X | GoodSlabPath v X} ∩ A) =
      (annealed μ 0).real (nonBacktracking v) * (conditioned μ v).real A := by
    exact (congrArg ENNReal.toReal (annealed_goodSlabPath_event μ hell v hv hp A)).trans ENNReal.toReal_mul
  rw [heq] at hmass
  have hu (u : Step d) : κ.toReal * (annealed μ 0).real (E u) ≤
      (annealed μ 0).real (finiteHighMaximum v L) := by
    have hh := radius_launch_probability_lower μ v u e a β c C b L ((C+2)*N)
      ha.le hβ hbc hta he M q hM hq
    have hh' := ENNReal.toReal_mono (measure_ne_top (annealed μ 0) _) hh
    simpa only [κ,E,Measure.real,ENNReal.toReal_mul] using hh'
  calc
    _ = κ.toReal*((annealed μ 0).real (nonBacktracking v)*(conditioned μ v).real A) := by ring
    _ ≤ κ.toReal * ∑ u : Step d, (annealed μ 0).real (E u) := mul_le_mul_of_nonneg_left hmass ENNReal.toReal_nonneg
    _ = ∑ u : Step d, κ.toReal * (annealed μ 0).real (E u) := Finset.mul_sum _ _ _
    _ ≤ ∑ _u : Step d, (annealed μ 0).real (finiteHighMaximum v L) := Finset.sum_le_sum (fun u _ => hu u)
    _ = _ := by simp

lemma radius_occurrence_mass_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) (e : Step d)
    (a B β c C b L : ℝ) (ha : 0 < a) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hB : Real.sqrt d*(2+β*(C+2)) < B-1)
    (hbc : 1 ≤ β*c) (hta : 1 < β*a) (he : height v (stepVector e) = -1)
    (M q l N : ℕ) (hM : (M : ℝ) < a*(M*β-1-β*b))
    (hq : (C+2)*N-M-c*q+b < 0) (hl : b ≤ l+1) (hL : L ≤ c*l-b)
    (hgp : ∀ i ∈ Finset.Ico l N, (3:ℝ)/4 ≤
      (conditioned μ v).real (goodRadiusPrefix v a c C b i))
    (htp : (3:ℝ)/4 ≤ (conditioned μ (-v)).real (goodRadiusPrefix (-v) a c C b q))
    (hs : (∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
      (largeRadiusWord slabRadius (slabWidth v) (B*a) i)) ≤ 1/4) :
    ((meanStep μ e ^ M).toReal * (annealed μ 0).real (nonBacktracking v) *
      (annealed μ 0).real (nonBacktracking (-v)) * (3/8)) *
      (∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
        (largeRadiusWord slabRadius (slabWidth v) (B*a) i)) ≤
      (Fintype.card (Step d) : ℝ) * (annealed μ 0).real (finiteHighMaximum v L) := by
  have hh := radius_occurrence_probability_upper μ hell v hv hp e a B β c C b L
    ha hβ hc hC hB hbc hta he M q l N hM hq hl hL
  have ht := congrArg ENNReal.toReal (annealed_radiusTemplate μ hell (-v) (neg_ne_zero.mpr hv) hp' a c C b q)
  rw [ENNReal.toReal_mul] at ht
  have ho := controlledSlabOccurrence_probability_half μ hell v hv hp a c C b
    (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N) hgp hs
  rw [ENNReal.toReal_mul,ht] at hh
  have hn : 0 ≤ ∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
      (largeRadiusWord slabRadius (slabWidth v) (B*a) i) :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hcoef : 0 ≤ (meanStep μ e ^ M).toReal * (annealed μ 0).real (nonBacktracking (-v)) *
      (annealed μ 0).real (nonBacktracking v) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul htp ho (by positivity) measureReal_nonneg) hcoef
  calc
    _ = ((meanStep μ e ^ M).toReal * (annealed μ 0).real (nonBacktracking (-v)) *
      (annealed μ 0).real (nonBacktracking v)) * ((3/4)*
      ((∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
        (largeRadiusWord slabRadius (slabWidth v) (B*a) i))/2)) := by ring
    _ ≤ _ := hmul
    _ = _ := by unfold Measure.real; ring
    _ ≤ _ := hh

lemma goodRadiusPrefix_uniform_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 0 < n)
    (hheight : (15:ℝ)/16 ≤ (conditioned μ v).real
      (heightEnvelope (fun k X => slabHeightSum v X k) c C b))
    (htrunc : truncatedMoment (slabLaw μ v) slabRadius (a*n) ≤ 3*a/32) :
    ∀ i ≤ n, (3:ℝ)/4 ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b i) := by
  let := conditioned_probability μ v hp
  have hh := goodRadiusPrefix_probability μ hell v hv hp a c C b ha n hn
  have hb : 2*truncatedMoment (slabLaw μ v) slabRadius (a*n)/a ≤ 3/16 := by
    apply (div_le_iff₀ ha).mpr
    linarith
  intro i hi
  exact (show (3:ℝ)/4 ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b n) by linarith).trans
    (measureReal_mono (goodRadiusPrefix_mono v a c C b hi) (measure_ne_top _ _))

lemma summable_real_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hfi : Integrable f P) : Summable (fun n : ℕ => P.real {x | (n+1 : ℝ) < f x}) := by
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun n =>
    measureReal_mono (fun x hx => hx.trans_le (le_abs_self (f x))) (measure_ne_top _ _))
  exact summable_real_tail_of_integrable P (fun x => |f x|) hfm.abs (fun _ => abs_nonneg _) hfi.abs

lemma summable_small_Ico (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ i, 0 ≤ f i)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ l : ℕ in atTop, ∀ n, l ≤ n → ∑ i ∈ Finset.Ico l n, f i < ε := by
  have ht : Tendsto (fun l : ℕ => (∑' i, f i) - ∑ i ∈ Finset.range l, f i) atTop (𝓝 0) := by
    have hh : Tendsto (fun _ : ℕ => ∑' i, f i) atTop (𝓝 (∑' i, f i)) := tendsto_const_nhds
    simpa only [sub_self] using hh.sub hf.hasSum.tendsto_sum_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with l hl n hln
  rw [Finset.sum_Ico_eq_sub f hln]
  exact (sub_le_sub_right (hf.sum_le_tsum (Finset.range n) (fun _ _ => hn _)) _).trans_lt hl

lemma measurable_slabHeightSum {d : ℕ} (v : Fin d → ℝ) (k : ℕ) :
    Measurable (fun X : Path d => slabHeightSum v X k) := by
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_of_countable (slabWidth v)).comp
    ((measurable_pi_apply i).comp (measurable_slabs v))

lemma exists_common_heightEnvelope {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) :
    ∃ c C b : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ b ∧
      (15:ℝ)/16 ≤ (conditioned μ v).real
        (heightEnvelope (fun k X => slabHeightSum v X k) c C b) ∧
      (15:ℝ)/16 ≤ (conditioned μ (-v)).real
        (heightEnvelope (fun k X => slabHeightSum (-v) X k) c C b) := by
  let := conditioned_probability μ v hp
  let := conditioned_probability μ (-v) hp'
  have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
  have hvnorm' : ∀ i, |(-v) i| ≤ 1 := by simpa only [Pi.neg_apply,abs_neg] using hvnorm
  let m := ∫ γ, slabWidth v γ ∂slabLaw μ v
  let m' := ∫ γ, slabWidth (-v) γ ∂slabLaw μ (-v)
  have hm : 0 < m := integral_slabWidth_pos μ hell v hv hvnorm hp
  have hm' : 0 < m' := integral_slabWidth_pos μ hell (-v) hv' hvnorm' hp'
  let c := min m m'/2
  let C := m+m'+1
  have hc : 0 < c := half_pos (lt_min hm hm')
  have hcm : c < m := (half_lt_self (lt_min hm hm')).trans_le (min_le_left _ _)
  have hcm' : c < m' := (half_lt_self (lt_min hm hm')).trans_le (min_le_right _ _)
  obtain ⟨b,hb,hbe⟩ := exists_heightEnvelope_probability (conditioned μ v)
    (fun k X => slabHeightSum v X k) (measurable_slabHeightSum v)
    (slabWidth_strongLaw μ hell v hv hvnorm hp) hcm (show m < C by dsimp [C]; linarith)
    (by norm_num : (15:ℝ)/16 < 1)
  obtain ⟨b',hb',hbe'⟩ := exists_heightEnvelope_probability (conditioned μ (-v))
    (fun k X => slabHeightSum (-v) X k) (measurable_slabHeightSum (-v))
    (slabWidth_strongLaw μ hell (-v) hv' hvnorm' hp') hcm' (show m' < C by dsimp [C]; linarith)
    (by norm_num : (15:ℝ)/16 < 1)
  refine ⟨c,C,max b b',hc,by dsimp [C]; linarith,hb.trans (le_max_left _ _),?_,?_⟩
  · exact hbe.le.trans (measureReal_mono (heightEnvelope_mono _ c C (le_max_left _ _)) (measure_ne_top _ _))
  · exact hbe'.le.trans (measureReal_mono (heightEnvelope_mono _ c C (le_max_right _ _)) (measure_ne_top _ _))

lemma truncatedMoment_component_scale {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : Ω → ℝ) (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 < a) (r n : ℕ) (hr : 1 ≤ r)
    (hs : truncatedMoment (P+Q) f (a*n) < a/(32*r)) :
    truncatedMoment P f (a*(r*n)) ≤ 3*a/32 := by
  have hnon := truncatedMoment_nonneg Q f (fun x => hf x) (t := a*(r*n)) (by positivity)
  have hadd := truncatedMoment_add_measure P Q f hfm hf (t := a*(r*n)) (by positivity)
  have ht := truncatedMoment_mul_le (P+Q) f hfm hf (t := a*n) (by positivity)
    (show (1:ℝ) ≤ r by exact_mod_cast hr)
  have hmul := mul_lt_mul_of_pos_left hs (show (0:ℝ) < r by exact_mod_cast (by omega : 0 < r))
  have he : (r : ℝ)*(a/(32*r)) = a/32 := by
    have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    field_simp
  rw [he] at hmul
  have he' : (r:ℝ)*(a*n) = a*(r*n) := by ring
  rw [he'] at ht
  linarith

lemma tendsto_real_finiteHighMaximum {d : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (v : Fin d → ℝ) : Tendsto (fun n : ℕ => P.real (finiteHighMaximum v n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Measure.real,ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_measure_finiteHighMaximum P v)

lemma meanStep_power_real_pos {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (M : ℕ) : 0 < (meanStep μ e ^ M).toReal :=
  ENNReal.toReal_pos (pow_ne_zero _ (ne_of_gt (meanStep_pos μ hell e)))
    (ne_of_lt (lt_of_le_of_lt (pow_le_one₀ zero_le (meanStep_le_one μ e)) ENNReal.one_lt_top))

lemma integrable_radius_from_parameters {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) (e e' : Step d)
    (he : height v (stepVector e) = -1) (he' : height (-v) (stepVector e') = -1)
    (c C b β B : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hβ : 0 < β) (hβc : 1 ≤ β*c) (hB : 1 ≤ B)
    (htilt : Real.sqrt d*(2+β*(C+2)) < B-1)
    (r : ℕ) (hr : 1 ≤ r) (hrc : C+3 < c*r)
    (hheight : (15:ℝ)/16 ≤ (conditioned μ v).real
      (heightEnvelope (fun k X => slabHeightSum v X k) c C b))
    (hheight' : (15:ℝ)/16 ≤ (conditioned μ (-v)).real
      (heightEnvelope (fun k X => slabHeightSum (-v) X k) c C b)) :
    Integrable slabRadius (slabLaw μ v + slabLaw μ (-v)) := by
  let := slabLaw_probability μ v hp
  let := slabLaw_probability μ (-v) hp'
  let := conditioned_probability μ v hp
  let := conditioned_probability μ (-v) hp'
  by_contra hnot
  have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
  have hvnorm' : ∀ i, |(-v) i| ≤ 1 := by simpa only [Pi.neg_apply,abs_neg] using hvnorm
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let η : ℝ := 1/(64*r)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsmall : 2*η ≤ 1/4 := by
    dsimp [η]
    rw [mul_one_div]
    have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 64*r)).mpr
    linarith
  obtain ⟨M,hM⟩ := exists_nat_gt ((2+β*b)/β)
  have hMcoef : 1 < (M:ℝ)*β-1-β*b := by
    have hm := (div_lt_iff₀ hβ).mp hM
    nlinarith only [hm]
  let p := (annealed μ 0).real (nonBacktracking v)
  let p' := (annealed μ 0).real (nonBacktracking (-v))
  have hp0 : 0 < p := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have hp0' : 0 < p' := ENNReal.toReal_pos hp'.ne' (measure_ne_top _ _)
  let A := (meanStep μ e ^ M).toReal*p*p'*(3/8)
  let A' := (meanStep μ e' ^ M).toReal*p'*p*(3/8)
  have hA : 0 < A := by
    have := meanStep_power_real_pos μ hell e M
    dsimp [A]; positivity
  have hA' : 0 < A' := by
    have := meanStep_power_real_pos μ hell e' M
    dsimp [A']; positivity
  let Γ := min A A'
  have hΓ : 0 < Γ := lt_min hA hA'
  let K : ℝ := Fintype.card (Step d)
  have hlim : Tendsto (fun L : ℕ => K*((annealed μ 0).real (finiteHighMaximum v L)+
      (annealed μ 0).real (finiteHighMaximum (-v) L))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using tendsto_const_nhds.mul
      ((tendsto_real_finiteHighMaximum (annealed μ 0) v).add
        (tendsto_real_finiteHighMaximum (annealed μ 0) (-v)))
  obtain ⟨L,hLsmall⟩ := (hlim.eventually (gt_mem_nhds (show (0:ℝ) < Γ*(η/(2*B)) by positivity))).exists
  have hsum := (summable_real_upper_tail (slabLaw μ v) (slabWidth v) (measurable_of_countable _)
    (integrable_slabWidth μ hell v hv hvnorm hp)).add
    (summable_real_upper_tail (slabLaw μ (-v)) (slabWidth (-v)) (measurable_of_countable _)
      (integrable_slabWidth μ hell (-v) hv' hvnorm' hp'))
  have hsmall := summable_small_Ico _ hsum (fun _ => add_nonneg measureReal_nonneg measureReal_nonneg)
    (show 0 < η/(4*B) by positivity)
  obtain ⟨l₁,hl₁⟩ := eventually_atTop.mp hsmall
  obtain ⟨l₀,hl₀⟩ := exists_nat_gt (max (b+1) (((L:ℝ)+b)/c))
  let l := max l₀ l₁
  have hlb : b+1 < (l:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hl₀).trans_le
    (Nat.cast_le.mpr (le_max_left _ _))
  have hlL : (L:ℝ) ≤ c*l-b := by
    have hll : ((L:ℝ)+b)/c < (l:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hl₀).trans_le
      (Nat.cast_le.mpr (le_max_left _ _))
    have hh := (div_lt_iff₀ hc).mp hll
    nlinarith only [hh]
  have hl0 : 0 < l := by
    have hh : (0:ℝ) < l := by linarith
    exact_mod_cast hh
  have hscales := radius_scales (slabLaw μ v + slabLaw μ (-v)) slabRadius
    (measurable_of_countable _) slabRadius_nonneg hnot hη l
    (show 0 < B*((l:ℝ)+1) by positivity)
  obtain ⟨a,ha,hlarge⟩ := ((eventually_gt_atTop (max ((M:ℝ)+1) (1/β+1))).and hscales).exists
  obtain ⟨ha0,N,hN,hsc,hscu,hscs,_⟩ := hlarge
  have hNl : l ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := hl0.trans_le hNl
  have hβa : 1 < β*a := by
    have haa : 1/β+1 < a := lt_of_le_of_lt (le_max_right _ _) ha
    have hh := mul_lt_mul_of_pos_left haa hβ
    rw [mul_add,mul_one_div_cancel hβ.ne',mul_one] at hh
    linarith
  have hMa : (M:ℝ) < a*((M:ℝ)*β-1-β*b) := by
    have haa : (M:ℝ)+1 < a := lt_of_le_of_lt (le_max_left _ _) ha
    nlinarith only [mul_lt_mul_of_pos_left hMcoef ha0,haa]
  have hq : (C+2)*(N:ℝ)-(M:ℝ)-c*(r*N:ℕ)+b < 0 := by
    have hbn : b+1 < (N:ℝ) := hlb.trans_le (Nat.cast_le.mpr hNl)
    have hh := mul_lt_mul_of_pos_right hrc (Nat.cast_pos.mpr hN0)
    push_cast
    nlinarith only [hh,hbn,show (0:ℝ) ≤ M from Nat.cast_nonneg M]
  have hwidth := hl₁ l (le_max_right _ _) N hNl
  rw [Finset.sum_add_distrib] at hwidth
  have hsmallscale : truncatedMoment (slabLaw μ v + slabLaw μ (-v)) slabRadius
      (B*a*(l+1)) < η*a/4 := by
    convert hscs using 1; ring_nf
  have hlo := largeRadius_mass_pair_lower (slabLaw μ v) (slabLaw μ (-v))
    slabRadius (slabWidth v) (slabWidth (-v)) (measurable_of_countable _) slabRadius_nonneg
    ha0 hB hη hNl hsc hsmallscale hwidth
  have hup := largeRadius_mass_pair_upper (slabLaw μ v) (slabLaw μ (-v))
    slabRadius (slabWidth v) (slabWidth (-v)) (measurable_of_countable _) slabRadius_nonneg
    ha0 hB hNl hscu
  let lam := ∑ i ∈ Finset.Ico l N, (slabLaw μ v).real (largeRadiusWord slabRadius (slabWidth v) (B*a) i)
  let lam' := ∑ i ∈ Finset.Ico l N, (slabLaw μ (-v)).real (largeRadiusWord slabRadius (slabWidth (-v)) (B*a) i)
  have hlam : 0 ≤ lam := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hlam' : 0 ≤ lam' := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  change η/(2*B) ≤ lam+lam' at hlo
  change lam+lam' < 2*η at hup
  have hlams : lam ≤ 1/4 := by linarith
  have hlams' : lam' ≤ 1/4 := by linarith
  have hscsimple : truncatedMoment (slabLaw μ v + slabLaw μ (-v)) slabRadius (a*N) < a/(32*r) := by
    convert hscu using 1
    dsimp [η]
    field_simp [ne_of_gt hr0]
    ring
  have htr := truncatedMoment_component_scale (slabLaw μ v) (slabLaw μ (-v)) slabRadius
    (measurable_of_countable _) slabRadius_nonneg ha0 r N hr hscsimple
  have htr' := truncatedMoment_component_scale (slabLaw μ (-v)) (slabLaw μ v) slabRadius
    (measurable_of_countable _) slabRadius_nonneg ha0 r N hr (by simpa only [add_comm] using hscsimple)
  have hq0 : 0 < r*N := Nat.mul_pos (by omega) hN0
  have hNq : N ≤ r*N := Nat.le_mul_of_pos_left N (by omega)
  have hgood := goodRadiusPrefix_uniform_probability μ hell v hv hp a c C b ha0 (r*N) hq0 hheight (by simpa only [Nat.cast_mul] using htr)
  have hgood' := goodRadiusPrefix_uniform_probability μ hell (-v) hv' hp' a c C b ha0 (r*N) hq0 hheight' (by simpa only [Nat.cast_mul] using htr')
  have hpos := radius_occurrence_mass_le μ hell v hv hp hp' e a B β c C b L ha0 hβ.le hc.le hC
    htilt hβc hβa he M (r*N) l N hMa hq (by linarith) hlL
    (fun i hi => hgood i ((Finset.mem_Ico.mp hi).2.le.trans hNq)) (hgood' _ le_rfl) hlams
  have hneg := radius_occurrence_mass_le μ hell (-v) hv' hp' (by simpa only [neg_neg] using hp) e' a B β c C b L ha0 hβ.le hc.le hC
    htilt hβc hβa he' M (r*N) l N hMa hq (by linarith) hlL
    (fun i hi => hgood' i ((Finset.mem_Ico.mp hi).2.le.trans hNq)) (by simpa only [neg_neg] using hgood (r*N) le_rfl) hlams'
  change A*lam ≤ K*(annealed μ 0).real (finiteHighMaximum v L) at hpos
  simp only [neg_neg] at hneg
  change A'*lam' ≤ K*(annealed μ 0).real (finiteHighMaximum (-v) L) at hneg
  have hbound : Γ*(lam+lam') ≤ K*((annealed μ 0).real (finiteHighMaximum v L)+
      (annealed μ 0).real (finiteHighMaximum (-v) L)) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_right (min_le_left A A') hlam)
      (mul_le_mul_of_nonneg_right (min_le_right A A') hlam')
    dsimp [Γ]
    nlinarith only [hh,hpos,hneg]
  have hh := mul_le_mul_of_nonneg_left hlo hΓ.le
  exact (not_lt_of_ge (hh.trans hbound)) hLsmall

lemma exists_down_unit_step {d : ℕ} (v : Fin d → ℝ) (hv : ∃ i, |v i| = 1) :
    ∃ e : Step d, height v (stepVector e) = -1 := by
  obtain ⟨i,hi⟩ := hv
  rcases le_total 0 (v i) with h | h
  · rw [abs_of_nonneg h] at hi
    exact ⟨(i,false),by simp [height_stepVector,hi]⟩
  · rw [abs_of_nonpos h] at hi
    exact ⟨(i,true),by simp [height_stepVector]; linarith⟩

lemma integrable_slabRadius_normalized {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hvunit : ∃ i, |v i| = 1)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) :
    Integrable slabRadius (slabLaw μ v) ∧ Integrable slabRadius (slabLaw μ (-v)) := by
  obtain ⟨c,C,b,hc,hC,hb,hh,hh'⟩ := exists_common_heightEnvelope μ hell v hv hvnorm hp hp'
  let β := 2/c
  have hβ : 0 < β := div_pos (by norm_num) hc
  have hβc : 1 ≤ β*c := by dsimp [β]; rw [div_mul_cancel₀ _ hc.ne']; norm_num
  let B := Real.sqrt d*(2+β*(C+2))+2
  have hB : 1 ≤ B := by
    have ht : 0 ≤ Real.sqrt d*(2+β*(C+2)) := by positivity
    dsimp [B]; linarith
  have htilt : Real.sqrt d*(2+β*(C+2)) < B-1 := by dsimp [B]; linarith
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 ((C+3)/c))
  have hr1 : 1 ≤ r := by
    have hh : (1:ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
    have : 1 < r := by exact_mod_cast hh
    omega
  have hrc : C+3 < c*r := by
    have hh := (div_lt_iff₀ hc).mp (lt_of_le_of_lt (le_max_right _ _) hr)
    nlinarith only [hh]
  obtain ⟨e,he⟩ := exists_down_unit_step v hvunit
  obtain ⟨e',he'⟩ := exists_down_unit_step (-v) (by simpa only [Pi.neg_apply,abs_neg] using hvunit)
  exact integrable_add_measure.mp (integrable_radius_from_parameters μ hell v hv hvnorm hp hp'
    e e' he he' c C b β B hc hC hb hβ hβc hB htilt r hr1 hrc hh hh')

end DirectionalZeroOne

end OAI
