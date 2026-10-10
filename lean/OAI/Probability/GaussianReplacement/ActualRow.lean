import OAI.Probability.GaussianReplacement.Entropy

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def actualExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d × W) × Rows m d)) :
    Measure (((Sphere d × W) × Rows m d) × Rows r d) := P.prod (gaussianRows r d)

instance actualExperiment_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (actualExperiment (r:=r) P) :=
  inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))

def actualRowsSignal {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) : Rows (m+r) d × Sphere d :=
  (Fin.append p.1.2 p.2,p.1.1.1)

def actualObservation {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) :
    (Rows (m+r) d × W) × (Fin (m+r) → ℝ) :=
  ((Fin.append p.1.2 p.2,p.1.1.2), label (Fin.append p.1.2 p.2) (p.1.1.1 : Vector d))

lemma measurable_actualRowsSignal {d m r : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (actualRowsSignal : ((Sphere d×W)×Rows m d)×Rows r d → _) :=
  ((measurable_append (E:=Vector d) m r).comp (measurable_fst.snd.prodMk measurable_snd)).prodMk
    measurable_fst.fst.fst

lemma measurable_actualObservation {d m r : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (actualObservation : ((Sphere d×W)×Rows m d)×Rows r d → _) := by
  have hG : Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d => Fin.append p.1.2 p.2) := (measurable_append (E:=Vector d) m r).comp (measurable_fst.snd.prodMk measurable_snd)
  have hY : Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d => label (Fin.append p.1.2 p.2) (p.1.1.1:Vector d)) := (measurable_own_label (k:=m+r) (d:=d)).comp measurable_actualRowsSignal
  exact (hG.prodMk measurable_fst.fst.snd).prodMk hY

instance actualObservation_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure ((actualExperiment (r:=r) P).map actualObservation) :=
  inferInstance

lemma map_actualRowsSignal {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) :
    (actualExperiment (r:=r) P).map actualRowsSignal = (gaussianRows (m+r) d).prod ν := by
  let f : (Sphere d×W)×Rows m d → Sphere d×Rows m d := fun p => (p.1.1,p.2)
  have hf : Measurable f := measurable_fst.fst.prodMk measurable_snd
  have hBase : P.map f = ν.prod (gaussianRows m d) := by
    rw [Measure.fst, Measure.map_map measurable_fst swapLast.measurable] at hInd
    exact hInd
  let T := Prod.map f (id : Rows r d → Rows r d)
  have hT : Measurable T := hf.prodMap measurable_id
  have hpre : (actualExperiment (r:=r) P).map T =
      (ν.prod (gaussianRows m d)).prod (gaussianRows r d) := by
    change (P.prod (gaussianRows r d)).map (Prod.map f id) = _
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, hBase]
  let U : (Sphere d×Rows m d)×Rows r d → (Rows m d×Rows r d)×Sphere d :=
    fun p => ((p.1.2,p.2),p.1.1)
  have hU : Measurable U := (measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst
  have hmid : ((ν.prod (gaussianRows m d)).prod (gaussianRows r d)).map U =
      ((gaussianRows m d).prod (gaussianRows r d)).prod ν := by
    change Measure.map (Prod.swap ∘ MeasurableEquiv.prodAssoc) _ = _
    rw [← Measure.map_map measurable_swap MeasurableEquiv.prodAssoc.measurable,
      Measure.prodAssoc_prod, Measure.prod_swap]
  let V : (Rows m d×Rows r d)×Sphere d → Rows (m+r) d×Sphere d :=
    Prod.map (fun p => Fin.append p.1 p.2) id
  have hV : Measurable V := (measurable_append (E:=Vector d) m r).prodMap measurable_id
  have hlast : (((gaussianRows m d).prod (gaussianRows r d)).prod ν).map V =
      (gaussianRows (m+r) d).prod ν := by
    rw [show V = Prod.map (fun p : Rows m d×Rows r d => Fin.append p.1 p.2) id from rfl,
      ← Measure.map_prod_map _ _ (measurable_append (E:=Vector d) m r) measurable_id,
      Measure.map_id]
    rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
      gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]
  have hfun : actualRowsSignal = V ∘ U ∘ T := rfl
  rw [hfun, ← Measure.map_map hV (hU.comp hT), ← Measure.map_map hU hT,
    hpre, hmid, hlast]

lemma actualObservation_ac {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d) :
    (actualExperiment (r:=r) P).map actualObservation ≪
      ((gaussianRows (m+r) d).prod (Measure.count : Measure W)).prod
        (volume : Measure (Fin (m+r) → ℝ)) := by
  have hB := dominatedSphere_growth ν hH.le hν (show 1 ≤ d by have := hdim.2.2.2.1; omega)
    (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega)
  have hD := dominatedSphere_growth ν hH.le hν (show 1 ≤ d by have := hdim.2.2.2.1; omega) le_rfl
  have hac := ae_labelLaw_ac_of_growth hdim ν (H*(3*4^d)) (H*(3*4^d))
    (by positivity) (by positivity) hB hD
  have hGY := map_fiber_ac_prod (gaussianRows (m+r) d) ν volume
    (fun gs : Rows (m+r) d×Sphere d => label gs.1 (gs.2:Vector d)) measurable_own_label hac
  let J := (actualExperiment (r:=r) P).map
    (fun p => ((Fin.append p.1.2 p.2,label (Fin.append p.1.2 p.2) (p.1.1.1:Vector d)),p.1.1.2))
  have hJm : Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d =>
      ((Fin.append p.1.2 p.2,label (Fin.append p.1.2 p.2) (p.1.1.1:Vector d)),p.1.1.2)) :=
    (measurable_actualRowsSignal.fst.prodMk
      (measurable_own_label.comp measurable_actualRowsSignal)).prodMk measurable_fst.fst.snd
  let : IsProbabilityMeasure (actualExperiment (r:=r) P) := inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))
  let : IsProbabilityMeasure J := inferInstance
  have hJfst : J.fst = ((gaussianRows (m+r) d).prod ν).map
      (fun gs : Rows (m+r) d×Sphere d => (gs.1,label gs.1 (gs.2:Vector d))) := by
    rw [← map_actualRowsSignal P ν hInd]
    rw [Measure.map_map (measurable_fst.prodMk measurable_own_label) measurable_actualRowsSignal]
    change ((actualExperiment P).map _).fst = _
    rw [Measure.fst, Measure.map_map measurable_fst hJm]
    rfl
  have hjac : J.fst ≪ (gaussianRows (m+r) d).prod (volume : Measure (Fin (m+r) → ℝ)) := by
    rw [hJfst]; exact hGY
  have hh := adjoin_countable_ac J (gaussianRows (m+r) d) volume hjac
  change (J.map swapLast) ≪ _ at hh
  dsimp only [J] at hh
  rw [Measure.map_map swapLast.measurable hJm] at hh
  exact hh


def selectedCube {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d)) (δ : ℝ)
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := cubeAverage (ρ z.1.2) z.1.1 z.2 δ

def selectedExact {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d))
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := exactDensity (ρ z.1.2) z.1.1 z.2

lemma measurable_countable_selection {A B T W : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace T] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (f : W → A×B → T)
    (hf : ∀ w, Measurable (f w)) :
    Measurable (fun z : (A×W)×B => f z.1.2 (z.1.1,z.2)) := by
  have hh : Measurable (fun z : (A×B)×W => f z.2 z.1) :=
    measurable_from_prod_countable_left hf
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_selectedCube {k d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (ρ : W → Measure (Sphere d))
    [∀ w, SFinite (ρ w)] (δ : ℝ) : Measurable (selectedCube (k:=k) ρ δ) :=
  measurable_countable_selection (fun w gy => cubeAverage (ρ w) gy.1 gy.2 δ)
    (fun w => measurable_cubeAverage (ρ w) δ)

lemma measurable_selectedExact {k d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (ρ : W → Measure (Sphere d))
    [∀ w, SFinite (ρ w)] : Measurable (selectedExact (k:=k) ρ) :=
  measurable_countable_selection (fun w gy => exactDensity (ρ w) gy.1 gy.2)
    (fun w => measurable_exactDensity (ρ w))

lemma exactDensity_ne_top {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d) (y : Fin k → ℝ) :
    exactDensity ρ G y ≠ ∞ := by
  unfold exactDensity
  dsimp only
  split_ifs <;> simp

lemma actual_cube_limit {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (ρ : W → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)] :
    ∀ᵐ p ∂actualExperiment (r:=r) P,
      Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
        (𝓝 (selectedExact ρ (actualObservation p))) := by
  have hh := countable_null_transfer ((actualExperiment (r:=r) P).map actualObservation)
    (gaussianRows (m+r) d) (volume : Measure (Fin (m+r) → ℝ))
    (actualObservation_ac hdim P ν hInd H hH hν)
    (fun g w y => Tendsto (fun j : ℕ => cubeAverage (ρ w) g y (1/(j:ℝ))) atTop
      (𝓝 (exactDensity (ρ w) g y)))
    (fun w => measurableSet_tendsto_fun (fun j : ℕ => measurable_cubeAverage (ρ w) (1/(j:ℝ)))
      (measurable_exactDensity (ρ w)))
    (fun w g => volume_ae_cube_limit (ρ w) g)
  exact ae_of_ae_map measurable_actualObservation.aemeasurable hh

lemma actual_conditional_label_ac {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d) :
    ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
      ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume := by
  let : IsProbabilityMeasure (actualExperiment (r:=r) P) :=
    inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))
  let : IsProbabilityMeasure ((actualExperiment (r:=r) P).map actualObservation) :=
    inferInstance
  exact ae_condKernel_ac_of_joint_ac _ _ _ (actualObservation_ac hdim P ν hInd H hH hν)


def momentBound (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ :=
  Real.exp (C*d)*B*(1+max (Real.log (D/B)) 0)

lemma momentBound_nonneg (C : ℝ) (d : ℕ) {B D : ℝ} (hB : 0 ≤ B) :
    0 ≤ momentBound C d B D := by
  unfold momentBound
  positivity

lemma cubeAverage_inner_finite {d m r : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (s : Sphere d) (X : Rows m d) (δ : ℝ) :
    ∫⁻ Z, cubeAverage ρ (Fin.append X Z) (label (Fin.append X Z) (s:Vector d)) δ
      ∂gaussianRows r d ≠ ∞ := by
  apply ne_top_of_le_ne_top (b:=ENNReal.ofReal ((2*δ)⁻¹^(m+r))*ρ univ)
  · finiteness
  · calc
      _ ≤ ∫⁻ _Z : Rows r d, ENNReal.ofReal ((2*δ)⁻¹^(m+r))*ρ univ ∂gaussianRows r d := by
        apply lintegral_mono; intro Z
        exact mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
      _ = _ := by simp

lemma actual_smoothed_log_bound {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hKL : rowInformation P (gaussianRows m d) ≠ ∞)
    (ρ : W → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)]
    (B D : W → ℝ) (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w)
    (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w))
    (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w))
    (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d (B sw.2) (D sw.2))) P.fst)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ p, ENNReal.ofReal (Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      ∂actualExperiment (r:=r) P ≤
        ENNReal.ofReal ((rowInformation P (gaussianRows m d)).toReal/q +
          ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) := by
  apply mixed_entropy_log_bound P (gaussianRows m d) (gaussianRows r d) hKL
    (fun p => selectedCube ρ δ (actualObservation p))
    ((measurable_selectedCube ρ δ).comp measurable_actualObservation)
    (fun p => (cubeAverage_lt_top _ _ _ _).ne)
    (fun p => cubeAverage_inner_finite (ρ p.1.2) p.1.1 p.2 δ)
    (fun sw : Sphere d×W => momentBound 9 d (B sw.2) (D sw.2))
    ((measurable_of_countable (f:=fun w => momentBound 9 d (B w) (D w))).comp measurable_snd)
    (fun sw => momentBound_nonneg 9 d (hB sw.2).le) hCI hdim.2.2.1
  intro sw
  exact mixed_cube_moment hdim (ρ sw.2) (B sw.2) (D sw.2)
    (hB sw.2) (hD sw.2) (hgB sw.2) (hgD sw.2) sw.1 δ hδ

lemma log_lintegral_bound_of_ae_tendsto {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : ℕ → A → ℝ≥0∞) (F : A → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hFt : ∀ a, F a ≠ ∞)
    (ht : ∀ᵐ a ∂μ, Tendsto (fun j => f j a) atTop (𝓝 (F a)))
    (R : ℝ≥0∞) (hR : ∀ j ≥ 1, ∫⁻ a, ENNReal.ofReal (Real.log (1+(f j a).toReal)) ∂μ ≤ R) :
    ∫⁻ a, ENNReal.ofReal (Real.log (1+(F a).toReal)) ∂μ ≤ R := by
  let g : ℕ → A → ℝ≥0∞ := fun j a => ENNReal.ofReal (Real.log (1+(f j a).toReal))
  have hlim : ∀ᵐ a ∂μ, liminf (fun j => g j a) atTop = ENNReal.ofReal (Real.log (1+(F a).toReal)) := by
    filter_upwards [ht] with a ha
    have htr := (ENNReal.continuousAt_toReal (hFt a)).tendsto.comp ha
    have hlog := (tendsto_const_nhds.add htr).log (show 1+(F a).toReal ≠ 0 by positivity)
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hlog).liminf_eq
  calc
    _ = ∫⁻ a, liminf (fun j => g j a) atTop ∂μ := lintegral_congr_ae (hlim.mono fun a ha => ha.symm)
    _ ≤ liminf (fun j => ∫⁻ a, g j a ∂μ) atTop :=
      lintegral_liminf_le (fun j => (measurable_log_one_add (hf j)).ennreal_ofReal)
    _ ≤ R := liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      ((eventually_ge_atTop 1).mono fun j hj => hR j hj).frequently

def logPositive (x : ℝ≥0∞) : ℝ := max (Real.log x.toReal) 0

def logNegative (x : ℝ≥0∞) : ℝ≥0∞ := if x = 0 then ∞ else ENNReal.ofReal (-Real.log x.toReal)


def extendedLogExpectation {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) : EReal :=
  ((∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ) : EReal) -
    ((∫⁻ a, logNegative (f a) ∂μ) : EReal)

lemma logPositive_le_log_one_add (x : ℝ≥0∞) : logPositive x ≤ Real.log (1+x.toReal) := by
  apply max_le _ (log_one_add_nonneg x)
  by_cases h : x.toReal = 0
  · simp only [h, Real.log_zero, add_zero, Real.log_one, le_refl]
  · exact Real.log_le_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)) (le_add_of_nonneg_left zero_le_one)

lemma log_bound_consequences {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) (hf : Measurable f) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∫⁻ a, ENNReal.ofReal (Real.log (1+(f a).toReal)) ∂μ ≤ ENNReal.ofReal R) :
    (Integrable (fun a => Real.log (1+(f a).toReal)) μ ∧
      ∫ a, Real.log (1+(f a).toReal) ∂μ ≤ R) ∧
    Integrable (fun a => logPositive (f a)) μ ∧ extendedLogExpectation μ f ≤ (R:EReal) := by
  have hLi : Integrable (fun a => Real.log (1+(f a).toReal)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_log_one_add hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hR)
  have hLf : ∫ a, Real.log (1+(f a).toReal) ∂μ ≤ R := by
    rw [← ofReal_integral_eq_lintegral_ofReal hLi
      (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)] at hR
    exact (ENNReal.ofReal_le_ofReal_iff hR0).mp hR
  have hPi : Integrable (fun a => logPositive (f a)) μ := by
    apply hLi.mono' ((hf.ennreal_toReal.log.max measurable_const).aestronglyMeasurable)
    apply Filter.Eventually.of_forall; intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact logPositive_le_log_one_add _
  refine ⟨⟨hLi,hLf⟩,hPi,?_⟩
  have hPL : ∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ ≤ ENNReal.ofReal R :=
    (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (logPositive_le_log_one_add _)).trans hR
  apply (EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hPL)
    (EReal.coe_ennreal_nonneg (∫⁻ a, logNegative (f a) ∂μ))).trans
  have he : (ENNReal.ofReal R : EReal) = (R:EReal) :=
    by simpa using (EReal.coe_toENNReal (x := (R:EReal)) (by exact_mod_cast hR0))
  simp only [sub_zero, he, le_refl]



def PositiveMessage {W : Type*} [MeasurableSpace W] (π : Measure W) := {w : W // 0 < π {w}}

def completeFamily {W : Type*} [MeasurableSpace W] {T : Type*} (π : Measure W)
    (f : PositiveMessage π → T) (t₀ : T) (w : W) : T :=
  if h : 0 < π {w} then f ⟨w,h⟩ else t₀

instance completeFamily_finite {W : Type*} [MeasurableSpace W] {d : ℕ}
    (π : Measure W) (ρ : PositiveMessage π → Measure (Sphere d))
    [hρ : ∀ w, IsFiniteMeasure (ρ w)] (w : W) : IsFiniteMeasure (completeFamily π ρ 0 w) := by
  unfold completeFamily
  split_ifs with h
  · exact hρ ⟨w,h⟩
  · infer_instance

lemma completeFamily_pos {W : Type*} [MeasurableSpace W] (π : Measure W)
    (f : PositiveMessage π → ℝ) (hf : ∀ w, 0 < f w) (w : W) :
    0 < completeFamily π f 1 w := by
  unfold completeFamily
  split_ifs with h
  · exact hf ⟨w,h⟩
  · norm_num

lemma completeFamily_growth {W : Type*} [MeasurableSpace W] {d a : ℕ}
    (π : Measure W) (ρ : PositiveMessage π → Measure (Sphere d))
    (B : PositiveMessage π → ℝ) (hg : ∀ w, LocalGrowth (ρ w) a (B w)) (w : W) :
    LocalGrowth (completeFamily π ρ 0 w) a (completeFamily π B 1 w) := by
  unfold completeFamily
  split_ifs with h
  · exact hg ⟨w,h⟩
  · intro z t ht
    simp


structure ActualRowConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : rowInformation P (gaussianRows m d) ≠ ∞
  row_le_entropy : (rowInformation P (gaussianRows m d)).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)


theorem actualRowMain {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hEntropy : shannonEntropy (P.map swapLast).snd ≠ ∞)
    (ρ : PositiveMessage (P.map swapLast).snd → Measure (Sphere d))
    [∀ w, IsFiniteMeasure (ρ w)]
    (_hρac : ∀ w, ρ w ≪ uniformSphere d)
    (B D : PositiveMessage (P.map swapLast).snd → ℝ)
    (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w)
    (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w))
    (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w))
    (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d
      (completeFamily (P.map swapLast).snd B 1 sw.2) (completeFamily (P.map swapLast).snd D 1 sw.2))) P.fst) :
    ActualRowConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1) := by
  let ρ' := completeFamily (P.map swapLast).snd ρ 0
  let B' := completeFamily (P.map swapLast).snd B 1
  let D' := completeFamily (P.map swapLast).snd D 1
  have hB' := completeFamily_pos (P.map swapLast).snd B hB
  have hD' := completeFamily_pos (P.map swapLast).snd D hD
  have hgB' := completeFamily_growth (P.map swapLast).snd ρ B hgB
  have hgD' := completeFamily_growth (P.map swapLast).snd ρ D hgD
  have hH : 0 < H := by
    by_contra hn
    have hh := hν univ
    simp [ENNReal.ofReal_of_nonpos (le_of_not_gt hn)] at hh
  obtain ⟨hKL,hKE⟩ := rowInformation_le_entropy P ν (gaussianRows m d) hInd hEntropy
  have hlim := actual_cube_limit hdim P ν hInd H hH hν ρ'
  let R := (rowInformation P (gaussianRows m d)).toReal/q +
    ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B' sw.2) (D' sw.2)) ∂P.fst
  have hR0 : 0 ≤ R := add_nonneg (div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
    (integral_nonneg fun sw => Real.log_nonneg (le_add_of_nonneg_right (momentBound_nonneg 9 d (hB' sw.2).le)))
  have hsmooth (δ : ℝ) (hδ : 0 < δ) :=
    actual_smoothed_log_bound hdim P hKL ρ' B' D' hB' hD' hgB' hgD' hCI hδ
  have hExact : ∫⁻ p, ENNReal.ofReal (Real.log (1+(selectedExact ρ' (actualObservation p)).toReal))
      ∂actualExperiment (r:=r) P ≤ ENNReal.ofReal R := by
    apply log_lintegral_bound_of_ae_tendsto (actualExperiment (r:=r) P)
      (fun j p => selectedCube ρ' (1/(j:ℝ)) (actualObservation p))
      (fun p => selectedExact ρ' (actualObservation p))
      (fun j => (measurable_selectedCube ρ' (1/(j:ℝ))).comp measurable_actualObservation)
      (fun p => exactDensity_ne_top _ _ _) hlim (ENNReal.ofReal R)
    intro j hj
    exact hsmooth _ (by positivity)
  have hc := log_bound_consequences (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ' (actualObservation p))
    ((measurable_selectedExact ρ').comp measurable_actualObservation) R hR0 hExact
  refine ⟨hKL,hKE,actual_conditional_label_ac hdim P ν hInd H hH hν,hlim,?_,hc.1.1,hc.1.2,?_,hc.2.1,hc.2.2⟩
  · intro δ hδ
    exact (log_bound_consequences (actualExperiment (r:=r) P)
      (fun p => selectedCube ρ' δ (actualObservation p))
      ((measurable_selectedCube ρ' δ).comp measurable_actualObservation) R hR0 (hsmooth δ hδ)).1
  · exact add_le_add (div_le_div_of_nonneg_right hKE (Nat.cast_nonneg q)) le_rfl


theorem actualRowRefinement {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e)
    (_hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) (gaussianRows m d) =
      rowInformation P (gaussianRows m d) :=
  rowInformation_refinement P (gaussianRows m d) e he



end CurrentProjection

end

end OAI
