import Mathlib
import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Analysis.RCDHeat.EntropySubsegment

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: ForkPlans, EntropyCoupledFork, UniformCut. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma map_le_add_of_ae_or {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    (σ : Measure A) (f g h : A → Y) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (he : ∀ᵐ z ∂σ, f z = g z ∨ f z = h z) :
    σ.map f ≤ σ.map g+σ.map h := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.add_apply,Measure.map_apply hf hS,Measure.map_apply hg hS,Measure.map_apply hh hS]
  apply le_trans _ (measure_union_le _ _)
  apply measure_mono_ae
  filter_upwards [he] with z hz
  intro hmem
  change f z ∈ S at hmem
  rcases hz with hz | hz
  · exact Or.inl (by simpa only [mem_preimage,hz] using hmem)
  · exact Or.inr (by simpa only [mem_preimage,hz] using hmem)

lemma optimalPlan_normalize_endpoint_dom
    (plan Q : Measure C(Time,X)) [IsFiniteMeasure plan] [IsFiniteMeasure Q]
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (hcost : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞)
    (hdom : Q.map (fun γ => (γ 0,γ 1)) ≤ plan.map (fun γ => (γ 0,γ 1)))
    (hne : Q univ ≠ 0) :
    let P := (Q univ)⁻¹ • Q
    IsProbabilityMeasure P ∧
    IsOptimalCoupling (P.map (fun γ => γ 0)) (P.map (fun γ => γ 1))
      (P.map (fun γ => (γ 0,γ 1))) := by
  let : NeZero Q := ⟨by intro he; apply hne; rw [he]; rfl⟩
  let P := (Q univ)⁻¹ • Q
  have hpQ := hp.subcoupling hcost hdom
  have hm := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  have he0 : (Q.map (fun γ => (γ 0,γ 1))).map Prod.fst = Q.map (fun γ => γ 0) := by
    rw [Measure.map_map measurable_fst hm]; rfl
  have he1 : (Q.map (fun γ => (γ 0,γ 1))).map Prod.snd = Q.map (fun γ => γ 1) := by
    rw [Measure.map_map measurable_snd hm]; rfl
  rw [he0,he1] at hpQ
  refine ⟨inferInstance,?_⟩
  simpa only [P,Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
    Measure.map_smul _ (measurable_path_eval 1).aemeasurable,
    Measure.map_smul _ hm.aemeasurable] using hpQ.smul
    (ENNReal.inv_ne_zero.mpr (measure_ne_top Q univ)) (ENNReal.inv_ne_top.mpr hne)

 

lemma coupled_fork_unscaled
    (plan : Measure C(Time,X)) [IsFiniteMeasure plan]
    (σ : Measure (C(Time,X) × C(Time,X))) [IsFiniteMeasure σ]
    (hσ0 : σ.map Prod.fst ≤ plan) (hσ1 : σ.map Prod.snd ≤ plan)
    (f : (C(Time,X) × C(Time,X)) → C(Time,X)) (hf : Measurable f)
    (he : ∀ᵐ z ∂σ, (f z) 0 = z.1 0 ∧ (f z) 1 = z.2 1 ∧ z.1 0 = z.2 0)
    (hor : ∀ u : Time, ∀ᵐ z ∂σ, (f z) u = z.1 u ∨ (f z) u = z.2 u) :
    let Q : Fin 3 → Measure C(Time,X) := ![σ.map Prod.fst,σ.map f,
      (1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)]
    (∀ i, Q i univ = σ univ) ∧
    (∀ i, (Q i).map (fun γ => (γ 0,γ 1)) ≤ plan.map (fun γ => (γ 0,γ 1))) ∧
    (∀ i (u : Time), (Q i).map (fun γ => γ u) ≤ (2:ℝ≥0∞) • plan.map (fun γ => γ u)) := by
  let Q : Fin 3 → Measure C(Time,X) := ![σ.map Prod.fst,σ.map f,
      (1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)]
  change (∀ i, Q i univ = σ univ) ∧ _
  have hm (u : Time) := measurable_path_eval (X := X) u
  have hpair := (hm 0).prodMk (hm 1)
  have hdom0 : (σ.map Prod.fst).map (fun γ => (γ 0,γ 1)) ≤ plan.map (fun γ => (γ 0,γ 1)) :=
    Measure.map_mono hσ0 hpair
  have hend : (σ.map f).map (fun γ => (γ 0,γ 1)) =
      (σ.map Prod.snd).map (fun γ => (γ 0,γ 1)) := by
    rw [Measure.map_map hpair hf,Measure.map_map hpair measurable_snd]
    apply Measure.map_congr
    filter_upwards [he] with z hz
    exact Prod.ext (hz.1.trans hz.2.2) hz.2.1
  have hdom1 : (σ.map f).map (fun γ => (γ 0,γ 1)) ≤ plan.map (fun γ => (γ 0,γ 1)) := by
    rw [hend]; exact Measure.map_mono hσ1 hpair
  have heval0 (u : Time) : (σ.map Prod.fst).map (fun γ => γ u) ≤ plan.map (fun γ => γ u) :=
    Measure.map_mono hσ0 (hm u)
  have heval1 (u : Time) : (σ.map f).map (fun γ => γ u) ≤ (2:ℝ≥0∞) • plan.map (fun γ => γ u) := by
    rw [Measure.map_map (hm u) hf]
    have hh := map_le_add_of_ae_or σ (fun z => (f z) u) (fun z => z.1 u) (fun z => z.2 u)
      ((hm u).comp hf) ((hm u).comp measurable_fst) ((hm u).comp measurable_snd) (hor u)
    apply hh.trans
    have hh0 := heval0 u
    have hh1 := Measure.map_mono hσ1 (hm u)
    rw [Measure.map_map (hm u) measurable_fst] at hh0
    rw [Measure.map_map (hm u) measurable_snd] at hh1
    rw [two_smul ℝ≥0∞]
    exact add_le_add hh0 hh1
  have heval0' (u : Time) : (σ.map Prod.fst).map (fun γ => γ u) ≤ (2:ℝ≥0∞) • plan.map (fun γ => γ u) := by
    apply (heval0 u).trans
    rw [two_smul ℝ≥0∞]
    exact le_add_of_nonneg_right (show 0 ≤ plan.map (fun γ => γ u) from bot_le)
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact Measure.map_apply measurable_fst MeasurableSet.univ
    · exact Measure.map_apply hf MeasurableSet.univ
    · change ((1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)) univ = σ univ
      simp only [Measure.smul_apply,
        Measure.add_apply,smul_eq_mul,Measure.map_apply measurable_fst MeasurableSet.univ,
        Measure.map_apply hf MeasurableSet.univ,preimage_univ]
      rw [←two_mul,←mul_assoc,one_div,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]
  · intro i
    fin_cases i
    · exact hdom0
    · exact hdom1
    · change ((1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)).map _ ≤ _
      rw [Measure.map_smul _ hpair.aemeasurable,Measure.map_add _ _ hpair]
      calc
        _ ≤ (1/2:ℝ≥0∞) • (plan.map (fun γ => (γ 0,γ 1))+plan.map (fun γ => (γ 0,γ 1))) :=
          _root_.smul_le_smul_left _ (add_le_add hdom0 hdom1)
        _ = _ := by rw [←two_smul ℝ≥0∞,smul_smul]; norm_num [ENNReal.inv_mul_cancel]
  · intro i u
    fin_cases i
    · exact heval0' u
    · exact heval1 u
    · change ((1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)).map _ ≤ _
      rw [Measure.map_smul _ (hm u).aemeasurable,Measure.map_add _ _ (hm u)]
      calc
        _ ≤ (1/2:ℝ≥0∞) • ((2:ℝ≥0∞) • plan.map (fun γ => γ u)+(2:ℝ≥0∞) • plan.map (fun γ => γ u)) :=
          _root_.smul_le_smul_left _ (add_le_add (heval0' u) (heval1 u))
        _ = _ := by rw [←two_smul ℝ≥0∞,smul_smul]; norm_num [ENNReal.inv_mul_cancel]


 
theorem NoncollapsedRCD.entropy_coupled_fork_gap
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ u : Time,
      plan.map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ u : Time, ∀ᵐ x ∂plan.map (fun γ => γ u), dist x p ≤ R)
    (σ : Measure (C(Time,X) × C(Time,X))) [IsFiniteMeasure σ] (hne : σ univ ≠ 0)
    (hσ0 : σ.map Prod.fst ≤ plan) (hσ1 : σ.map Prod.snd ≤ plan)
    (f : (C(Time,X) × C(Time,X)) → C(Time,X)) (hf : Measurable f)
    (hgf : ∀ᵐ z ∂σ, IsGeodesic (f z))
    (he : ∀ᵐ z ∂σ, (f z) 0 = z.1 0 ∧ (f z) 1 = z.2 1 ∧ z.1 0 = z.2 0)
    (hor : ∀ u : Time, ∀ᵐ z ∂σ, (f z) u = z.1 u ∨ (f z) u = z.2 u)
    {δ : ℝ} (hδ : 0 < δ) (s t : Time) (hδs : δ ≤ (s:ℝ))
    (hst : s ≤ t) (htδ : (t:ℝ) ≤ 1-δ)
    (hes : ∀ᵐ z ∂σ, z.1 s = (f z) s)
    (S : Set X) (hS : MeasurableSet S)
    (hdis : ∀ᵐ z ∂σ, z.1 t ∈ S ∧ (f z) t ∉ S) :
    Real.log 2 ≤ 2*((((Real.log ((σ univ)⁻¹.toReal*(2*C))+
      2*(hausdorff n X (closedBall p R)).toReal+4*|K| *R^2)/δ)+
        4*|K| *R^2)*((t:ℝ)-(s:ℝ))) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : IsProbabilityMeasure (plan.map (fun γ => γ 0)) := inferInstance
  let : IsProbabilityMeasure (plan.map (fun γ => γ 1)) := inferInstance
  let Q : Fin 3 → Measure C(Time,X) := ![σ.map Prod.fst,σ.map f,
      (1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)]
  let a := (σ univ)⁻¹
  let P := fun i => a • Q i
  let D := a.toReal*(2*C)
  have habs : a ≠ ∞ := ENNReal.inv_ne_top.mpr hne
  have ha0 : a ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top σ univ)
  have ha : 0 < a.toReal := ENNReal.toReal_pos ha0 habs
  have hD : 0 < D := mul_pos ha (mul_pos (by norm_num) hC)
  obtain ⟨hmass,hdom,heval⟩ := coupled_fork_unscaled plan σ hσ0 hσ1 f hf he hor
  change ∀ i, Q i univ = σ univ at hmass
  change ∀ i, (Q i).map (fun γ => (γ 0,γ 1)) ≤ _ at hdom
  change ∀ i (u : Time), (Q i).map (fun γ => γ u) ≤ _ at heval
  have hQfin (i) : IsFiniteMeasure (Q i) := by
    exact ⟨by rw [hmass i]; exact measure_lt_top σ univ⟩
  have hcost : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [←wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le _ p (hs 0))
      (finiteSecondMoment_of_ae_dist_le _ p (hs 1))
  have hprob (i) : IsProbabilityMeasure (P i) := by
    let := hQfin i
    have hh := (optimalPlan_normalize_endpoint_dom plan (Q i) hp hcost (hdom i)
      (by rwa [hmass i])).1
    simpa only [hmass] using hh
  have hopt (i) : IsOptimalCoupling ((P i).map (fun γ => γ 0)) ((P i).map (fun γ => γ 1))
      ((P i).map (fun γ => (γ 0,γ 1))) := by
    let := hQfin i
    have hh := (optimalPlan_normalize_endpoint_dom plan (Q i) hp hcost (hdom i)
      (by rwa [hmass i])).2
    simpa only [hmass] using hh
  have hQg0 : ∀ᵐ γ ∂Q 0, IsGeodesic γ := hg.filter_mono (ae_mono hσ0)
  have hQg1 : ∀ᵐ γ ∂Q 1, IsGeodesic γ := by
    exact (ae_map_iff hf.aemeasurable isClosed_geodesicSet.measurableSet).mpr hgf
  have hQg2 : ∀ᵐ γ ∂Q 2, IsGeodesic γ :=
    (ae_add_measure_iff.mpr ⟨hQg0,hQg1⟩).filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hgeo (i) : ∀ᵐ γ ∂P i, IsGeodesic γ := by
    have hgi : ∀ᵐ γ ∂Q i, IsGeodesic γ := by
      fin_cases i
      · exact hQg0
      · exact hQg1
      · exact hQg2
    exact hgi.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hPdom (i) (u : Time) : (P i).map (fun γ => γ u) ≤
      (a*2) • plan.map (fun γ => γ u) := by
    dsimp only [P]
    rw [Measure.map_smul _ (measurable_path_eval u).aemeasurable,←smul_smul]
    exact _root_.smul_le_smul_left a (heval i u)
  have hcomp (i) (u : Time) : (P i).map (fun γ => γ u) ≤ ENNReal.ofReal D • hausdorff n X := by
    apply (hPdom i u).trans
    have hh := _root_.smul_le_smul_left (a*2) (hc u)
    convert hh using 1
    rw [smul_smul]
    congr 1
    dsimp only [D]
    rw [ENNReal.ofReal_mul ha.le,ENNReal.ofReal_toReal habs,ENNReal.ofReal_mul (by norm_num)]
    norm_num
    ring
  have hsupport (i) (u : Time) : ∀ᵐ x ∂(P i).map (fun γ => γ u), dist x p ≤ R :=
    (hs u).filter_mono (Measure.absolutelyContinuous_of_le_smul (hPdom i u)).ae_le
  have hmix : P 2 = (1/2:ℝ≥0∞) • (P 0+P 1) := by
    change a • ((1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map f)) =
      (1/2:ℝ≥0∞) • (a • σ.map Prod.fst+a • σ.map f)
    rw [←smul_add,smul_smul,smul_smul,mul_comm]
  have heq : (P 0).map (fun γ => γ s) = (P 1).map (fun γ => γ s) := by
    change (a • σ.map Prod.fst).map _ = (a • σ.map f).map _
    rw [Measure.map_smul _ (measurable_path_eval s).aemeasurable,
      Measure.map_smul _ (measurable_path_eval s).aemeasurable,
      Measure.map_map (measurable_path_eval s) measurable_fst,
      Measure.map_map (measurable_path_eval s) hf]
    exact congrArg (a • ·) (Measure.map_congr hes)
  have hsing : (P 0).map (fun γ => γ t) ⟂ₘ (P 1).map (fun γ => γ t) := by
    apply Measure.MutuallySingular.mk (s := Sᶜ) (t := S)
    · change (a • σ.map Prod.fst).map _ Sᶜ = 0
      rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable,
        Measure.smul_apply,Measure.map_map (measurable_path_eval t) measurable_fst,
        Measure.map_apply ((measurable_path_eval t).comp measurable_fst) hS.compl]
      have hh : σ ((fun z : C(Time,X) × C(Time,X) => z.1 t) ⁻¹' Sᶜ) = 0 := by
        exact ae_iff.mp (hdis.mono fun z hz => by simpa using hz.1)
      change a * σ ((fun z : C(Time,X) × C(Time,X) => z.1 t) ⁻¹' Sᶜ) = 0
      rw [hh,mul_zero]
    · change (a • σ.map f).map _ S = 0
      rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable,
        Measure.smul_apply,Measure.map_map (measurable_path_eval t) hf,
        Measure.map_apply ((measurable_path_eval t).comp hf) hS]
      have hh : σ ((fun z => (f z) t) ⁻¹' S) = 0 := by
        have hnull := ae_iff.mp (hdis.mono fun z hz => hz.2)
        convert hnull using 1
        congr 1
        ext z
        simp
      change a * σ ((fun z => (f z) t) ⁻¹' S) = 0
      rw [hh,mul_zero]
    · intro x _
      exact (em (x ∈ S)).symm
  exact hX.entropy_fork_gap K n hn P hprob hgeo hopt hmix hD hcomp p hR hsupport
    hδ s t hδs hst htδ heq hsing

end

 

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable def fairBool : Measure Bool := (1/2 : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance fairBool_probability : IsProbabilityMeasure fairBool := by
  constructor
  simp [fairBool,ENNReal.inv_two_add_inv_two]

lemma fairBool_singleton (b : Bool) : fairBool {b} = (1/2 : ℝ≥0∞) := by
  cases b <;> simp [fairBool]

lemma fair_colors_pair {I : Type*} [Fintype I] (i j : I) (hij : i ≠ j) :
    (Measure.pi (fun _ : I => fairBool)) {c : I → Bool | c i = true ∧ c j = false} =
      (1/4 : ℝ≥0∞) := by
  classical
  have he : {c : I → Bool | c i = true ∧ c j = false} =
      (({i,j} : Finset I) : Set I).pi (fun k => if k = i then {true} else {false}) := by
    ext c
    simp only [mem_ofPred_eq,Set.mem_pi,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hi,hj⟩ k (rfl | rfl) <;> simp [hi,hj,hij.symm]
    · intro h
      exact ⟨by simpa using h i (Or.inl rfl),by simpa [hij.symm] using h j (Or.inr rfl)⟩
  rw [he,Measure.pi_pi_finset]
  simp [hij,hij.symm,fairBool_singleton]
  rw [←ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

lemma exists_finite_label_cut {A I : Type*} [MeasurableSpace A]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (σ : Measure A) [IsFiniteMeasure σ] (f g : A → I)
    (hf : Measurable f) (hg : Measurable g) :
    ∃ c : I → Bool, σ {z | f z ≠ g z}/8 ≤ σ {z | c (f z) = true ∧ c (g z) = false} := by
  classical
  let κ := Measure.pi (fun _ : I => fairBool)
  let D := {z | f z ≠ g z}
  have hD : MeasurableSet D := (measurableSet_eq_fun hf hg).compl
  let B := fun c : I → Bool => {z | c (f z) = true ∧ c (g z) = false}
  have hB (c : I → Bool) : MeasurableSet (B c) := by
    exact (measurableSet_eq_fun ((measurable_of_countable c).comp hf) measurable_const).inter
      (measurableSet_eq_fun ((measurable_of_countable c).comp hg) measurable_const)
  let F : (I → Bool) → A → ℝ≥0∞ := fun c z => (B c).indicator 1 z
  have hF : Measurable (Function.uncurry F) := by
    have hev : Measurable (fun z : (I → Bool) × I => z.1 z.2) := measurable_of_countable _
    have h1 := hev.comp (measurable_fst.prodMk (hf.comp measurable_snd))
    have h2 := hev.comp (measurable_fst.prodMk (hg.comp measurable_snd))
    exact measurable_const.indicator ((measurableSet_eq_fun h1 measurable_const).inter
      (measurableSet_eq_fun h2 measurable_const))
  have hinner (z : A) : (∫⁻ c, F c z ∂κ) = (1/4 : ℝ≥0∞) * D.indicator 1 z := by
    by_cases he : f z = g z
    · have hz : z ∉ D := fun h => h he
      have hh : (fun c => F c z) = 0 := by
        funext c
        simp [F,B,he]
      simp only [hh,lintegral_zero_fun,indicator_of_notMem hz,mul_zero]
    · have hh : (fun c => F c z) = {c : I → Bool | c (f z) = true ∧ c (g z) = false}.indicator 1 := rfl
      rw [hh,lintegral_indicator_one (by measurability),fair_colors_pair _ _ he]
      rw [indicator_of_mem (show z ∈ D from he)]
      simp
  have havg : (∫⁻ c, σ (B c) ∂κ) = σ D/4 := by
    calc
      _ = ∫⁻ c, ∫⁻ z, F c z ∂σ ∂κ := by
        apply lintegral_congr
        intro c
        exact (lintegral_indicator_one (hB c)).symm
      _ = ∫⁻ z, ∫⁻ c, F c z ∂κ ∂σ := lintegral_lintegral_swap hF.aemeasurable
      _ = (1/4 : ℝ≥0∞) * σ D := by
        simp_rw [hinner]
        rw [lintegral_const_mul _ (measurable_one.indicator hD),lintegral_indicator_one hD]
      _ = σ D/4 := by simp only [ENNReal.div_eq_inv_mul,one_div]
  by_cases hzero : σ D = 0
  · refine ⟨fun _ => false,?_⟩
    change σ D/8 ≤ _
    rw [hzero,ENNReal.zero_div]
    exact bot_le
  by_contra hh
  push Not at hh
  have hle : σ D/4 ≤ σ D/8 := by
    rw [←havg]
    calc
      _ ≤ ∫⁻ _ : I → Bool, σ D/8 ∂κ := lintegral_mono (fun c => (hh c).le)
      _ = σ D/8 := by simp [κ]
  have hmpos : 0 < (σ D).toReal := ENNReal.toReal_pos hzero (measure_ne_top σ D)
  have hreal := ENNReal.toReal_mono (by finiteness) hle
  simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat] at hreal
  linarith

 

lemma exists_measurable_directed_cut {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
    (σ : Measure A) [IsFiniteMeasure σ] (f g : A → X)
    (hf : Measurable f) (hg : Measurable g) :
    ∃ S : Set X, MeasurableSet S ∧
      σ {z | f z ≠ g z}/16 ≤ σ {z | f z ∈ S ∧ g z ∉ S} := by
  classical
  obtain ⟨e,he,hinj⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated X
  let q := fun (m : ℕ) (x : X) (i : Fin m) => e x i
  have hq (m : ℕ) : Measurable (q m) := Measurable.of_eval (fun index => he.eval)
  let D := {z | f z ≠ g z}
  let Dm := fun m => {z | q m (f z) ≠ q m (g z)}
  have hmono : Monotone Dm := by
    intro m k hmk z hz hk
    apply hz
    funext i
    exact congrFun hk ⟨i.val,lt_of_lt_of_le i.isLt hmk⟩
  have hUnion : (⋃ m, Dm m) = D := by
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨m,hm⟩ hh
      exact hm (congrArg (q m) hh)
    · intro hz
      by_contra hn
      push Not at hn
      apply hz
      apply hinj
      funext k
      have hk : q (k+1) (f z) = q (k+1) (g z) := by simpa only [Dm,mem_ofPred_eq,not_not] using hn (k+1)
      exact congrFun hk ⟨k,Nat.lt_succ_self k⟩
  by_cases hzero : σ D = 0
  · refine ⟨∅,MeasurableSet.empty,?_⟩
    change σ D/16 ≤ _
    simp [hzero]
  have hlt : σ D/2 < σ D := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top σ D)).mp
    rw [ENNReal.toReal_div,ENNReal.toReal_ofNat]
    have hh := ENNReal.toReal_pos hzero (measure_ne_top σ D)
    linarith
  have hsup : σ D = ⨆ m, σ (Dm m) := by
    rw [←hUnion]
    exact hmono.measure_iUnion
  rw [hsup] at hlt
  obtain ⟨m,hm⟩ := lt_iSup_iff.mp hlt
  obtain ⟨c,hc⟩ := exists_finite_label_cut σ (q m ∘ f) (q m ∘ g) ((hq m).comp hf) ((hq m).comp hg)
  let S := {x | c (q m x) = true}
  have hS : MeasurableSet S := measurableSet_eq_fun ((measurable_of_countable c).comp (hq m)) measurable_const
  refine ⟨S,hS,?_⟩
  have hcut : {z | c ((q m ∘ f) z) = true ∧ c ((q m ∘ g) z) = false} =
      {z | f z ∈ S ∧ g z ∉ S} := by
    ext z
    simp only [S,mem_ofPred_eq,Function.comp_apply,Bool.not_eq_true]
  rw [hcut] at hc
  apply le_trans _ hc
  change σ D/16 ≤ σ (Dm m)/8
  have hh := ENNReal.div_le_div_right hm.le 8
  rw [←hsup] at hh
  convert hh using 1
  simp only [div_eq_mul_inv,mul_assoc]
  congr 1
  rw [←ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num


end RegularPointCoordinates

end OAI
