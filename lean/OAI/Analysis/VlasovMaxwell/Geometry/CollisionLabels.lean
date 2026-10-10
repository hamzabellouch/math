import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ReceiverRadialDomain

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def collisionLabels (α : Phase → ℝ → Phase) (z : Phase) (T : ℝ) : Set Phase :=
  {y | ∃ t ∈ Ioo 0 T, (α y t).1 = (α z t).1}

def collisionChart (α : Phase → ℝ → Phase) (z : Phase) (p : ℝ × Vec) : Phase :=
  inversePhase α (p.1, (α z p.1).1, p.2)

lemma PhaseFlowOn.collision_image {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T) (z : Phase) :
    collisionLabels F.flow z T = collisionChart F.flow z '' (Ioo 0 T ×ˢ (univ : Set Vec)) := by
  ext y
  constructor
  · rintro ⟨t,ht,hy⟩
    refine ⟨(t,(F.flow y t).2),⟨ht,mem_univ _⟩,?_⟩
    change inversePhase F.flow (t,((F.flow z t).1,(F.flow y t).2)) = y
    rw [← hy,Prod.mk.eta,F.inversePhase_flow (Ioo_subset_Icc_self ht)]
  · rintro ⟨⟨t,v⟩,ht,rfl⟩
    refine ⟨t,ht.1,?_⟩
    change (F.flow (inversePhase F.flow (t,(F.flow z t).1,v)) t).1=(F.flow z t).1
    rw [F.flow_inversePhase (Ioo_subset_Icc_self ht.1)]

lemma PhaseFlowOn.collisionChart_strict {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) {p : ℝ × Vec} (hp : p.1 ∈ Ioo 0 T) :
    ∃ D : (ℝ × Vec) →L[ℝ] Phase, HasStrictFDerivAt (collisionChart F.flow z) D p := by
  have htime : HasStrictFDerivAt (fun p : ℝ × Vec => (p.1,z))
      ((ContinuousLinearMap.fst ℝ ℝ Vec).prod (0 : (ℝ × Vec) →L[ℝ] Phase)) p :=
    hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_const _ _)
  have hX := ((F.joint z p.1 hp).comp p htime).fst
  have hmap := hasStrictFDerivAt_fst.prodMk (hX.prodMk hasStrictFDerivAt_snd)
  obtain ⟨D,_,hD⟩ := F.inverse_differential hp ((F.flow z p.1).1,p.2)
  have hh := hD.comp p hmap
  exact ⟨_,hh⟩

lemma dimH_strict_image_le {A C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [SecondCountableTopology A] [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : A → C} {s : Set A} (hf : ∀ x ∈ s, ∃ D : A →L[ℝ] C, HasStrictFDerivAt f D x) :
    dimH (f '' s) ≤ dimH s := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro x hx
  obtain ⟨D,hD⟩ := hf x hx
  obtain ⟨K,t,ht,hK⟩ := hD.exists_lipschitzOnWith
  exact ⟨K,t,mem_nhdsWithin_of_mem_nhds ht,hK⟩

lemma PhaseFlowOn.collision_null {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T) (z : Phase) :
    volume (collisionLabels F.flow z T) = 0 := by
  have hdim : dimH (collisionLabels F.flow z T) ≤ 4 := by
    rw [F.collision_image z]
    calc
      _ ≤ dimH (Ioo 0 T ×ˢ (univ : Set Vec)) :=
        dimH_strict_image_le (fun p hp => F.collisionChart_strict z hp.1)
      _ ≤ dimH (univ : Set (ℝ × Vec)) := dimH_mono (subset_univ _)
      _ = 4 := by rw [Real.dimH_univ_eq_finrank]; simp [Vec,Module.finrank_prod]
  have hrank : Module.finrank ℝ Phase = 6 := by simp [Phase,Vec,Module.finrank_prod]
  have hc : (volume : Measure Phase) ≪ Measure.hausdorffMeasure (6 : ℝ) := by
    have hh := Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Phase)
      (Measure.hausdorffMeasure (Module.finrank ℝ Phase : ℝ))
    simpa only [hrank,Nat.cast_ofNat] using hh
  apply measure_zero_of_dimH_lt (d := (6 : ℝ≥0)) hc
  exact hdim.trans_lt (by norm_num)

lemma PhaseFlowOn.closed_collision_null {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) :
    volume {y : Phase | ∃ t ∈ Icc 0 T, (F.flow y t).1=(F.flow z t).1}=0 := by
  apply measure_mono_null (t := collisionLabels F.flow z T ∪
    {y : Phase | (F.flow y 0).1=(F.flow z 0).1} ∪
    {y : Phase | (F.flow y T).1=(F.flow z T).1})
  · rintro y ⟨t,ht,hy⟩
    rcases eq_or_lt_of_le ht.1 with he | hl
    · exact Or.inl (Or.inr (he.symm ▸ hy))
    rcases eq_or_lt_of_le ht.2 with he | hr
    · exact Or.inr (he ▸ hy)
    · exact Or.inl (Or.inl ⟨t,⟨hl,hr⟩,hy⟩)
  · exact measure_union_null (measure_union_null (F.collision_null z)
      (F.tip_null ⟨le_rfl,hT⟩ (F.flow z 0).1))
      (F.tip_null ⟨hT,le_rfl⟩ (F.flow z T).1)

lemma PhaseFlowOn.position_contDiffOn {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) : ContDiffOn ℝ 1 (fun t => (F.flow z t).1) (Ioo 0 T) := by
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivWithinAt (fun t => (F.flow z t).1) (velocity (F.flow z t).2) (Ioo 0 T) t :=
    by
      have hx : HasDerivWithinAt (fun t => (F.flow z t).1)
          (velocity (F.flow z t).2) (Icc 0 T) t := (F.ode z t (Ioo_subset_Icc_self ht)).fst
      exact hx.mono Ioo_subset_Icc_self
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  constructor
  · exact fun t ht => (hd t ht).differentiableWithinAt
  · have hc : ContinuousOn (fun t => velocity (F.flow z t).2) (Ioo 0 T) :=
      ((contDiff_velocity (k := 1)).continuous).comp_continuousOn
        ((F.continuousOn_time z).snd.mono Ioo_subset_Icc_self)
    apply hc.congr
    intro t ht
    exact ((hd t ht).derivWithin (isOpen_Ioo.uniqueDiffWithinAt ht))

def branchDomain (α : Phase → ℝ → Phase) (zX zY : Phase) (T : ℝ) : Set ℝ :=
  {s | s ∈ Ioo 0 T ∧ s+‖(α zX T).1-(α zY s).1‖ < T}

def branchTime (α : Phase → ℝ → Phase) (zX zY : Phase) (T s : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ t, t ∈ Icc s T ∧ t-s=‖(α zX t).1-(α zY s).1‖ then h.choose else 0

lemma PhaseFlowOn.branch_spec {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T) :
    branchTime F.flow zX zY T s ∈ Icc s T ∧
      branchTime F.flow zX zY T s-s =
        ‖(F.flow zX (branchTime F.flow zX zY T s)).1-(F.flow zY s).1‖ := by
  have hy : ‖(F.flow zX T).1-(F.flow zY s).1‖ < T-s := by linarith [hs.2]
  obtain ⟨t,⟨ht,he⟩,_⟩ := F.exists_arrival (Ioo_subset_Icc_self hs.1) zX hy
  have hex : ∃ t, t ∈ Icc s T ∧ t-s=‖(F.flow zX t).1-(F.flow zY s).1‖ :=
    ⟨t,ht,by linarith⟩
  simpa only [branchTime,dite_eq_left hex] using hex.choose_spec

lemma PhaseFlowOn.branch_unique {E B : Field} {T s t : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (ht : t ∈ Icc s T) (he : t-s=‖(F.flow zX t).1-(F.flow zY s).1‖) :
    t=branchTime F.flow zX zY T s := by
  obtain ⟨hσ,hcone⟩ := F.branch_spec zX zY hs
  apply (F.arrival_strictMono (hs.1.1.le.trans hs.1.2.le) zX (F.flow zY s).1).injOn
    ⟨hs.1.1.le.trans ht.1,ht.2⟩ ⟨hs.1.1.le.trans hσ.1,hσ.2⟩
  dsimp only
  linarith

lemma PhaseFlowOn.branch_time_mem {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    s < branchTime F.flow zX zY T s ∧ branchTime F.flow zX zY T s < T := by
  obtain ⟨ht,he⟩ := F.branch_spec zX zY hs
  constructor
  · by_contra h
    have hts := le_antisymm (le_of_not_gt h) ht.1
    rw [hts,sub_self] at he
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp he.symm))
  · by_contra h
    have htT := le_antisymm ht.2 (le_of_not_gt h)
    rw [htT] at he
    linarith [hs.2]

lemma PhaseFlowOn.isOpen_branchDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) : IsOpen (branchDomain F.flow zX zY T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hY := ((F.continuousOn_time zY).fst.continuousAt (Icc_mem_nhds hs.1.1 hs.1.2))
  have hc : ContinuousAt (fun r => r+‖(F.flow zX T).1-(F.flow zY r).1‖) s :=
    continuousAt_id.add ((continuousAt_const.sub hY).norm)
  exact inter_mem (isOpen_Ioo.mem_nhds hs.1) (hc (isOpen_Iio.mem_nhds hs.2))

lemma PhaseFlowOn.branch_differential {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    let τ := branchTime F.flow zX zY T
    let n := (τ s-s)⁻¹ • ((F.flow zX (τ s)).1-(F.flow zY s).1)
    ContDiffAt ℝ 1 τ s ∧ HasDerivAt τ
      ((1-dot n (velocity (F.flow zY s).2))/(1-dot n (velocity (F.flow zX (τ s)).2))) s := by
  dsimp only
  let τ := branchTime F.flow zX zY T
  let t := τ s
  let n := (t-s)⁻¹ • ((F.flow zX t).1-(F.flow zY s).1)
  have ht := F.branch_time_mem zX zY hs hne
  have hti : t ∈ Ioo 0 T := ⟨hs.1.1.trans ht.1,ht.2⟩
  have hspec := (F.branch_spec zX zY hs).2
  have hgeom : (F.flow zX t).1-(F.flow zY s).1=(t-s) • n := by
    dsimp [n]
    rw [smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht.1)),one_smul]
  have hn : ‖n‖=1 := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sub_pos.mpr ht.1)),← hspec]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht.1))
  have hX := ((F.position_contDiffOn zX) t hti).contDiffAt (isOpen_Ioo.mem_nhds hti)
  have hY := ((F.position_contDiffOn zY) s hs.1).contDiffAt (isOpen_Ioo.mem_nhds hs.1)
  have hXd : HasDerivAt (fun r => (F.flow zX r).1) (velocity (F.flow zX t).2) t :=
    ((F.ode zX t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).fst
  have hYd : HasDerivAt (fun r => (F.flow zY r).1) (velocity (F.flow zY s).2) s :=
    ((F.ode zY s (Ioo_subset_Icc_self hs.1)).hasDerivAt (Icc_mem_nhds hs.1.1 hs.1.2)).fst
  obtain ⟨σ,hσ,hσc,hσd,hev⟩ := exists_local_retarded_branch_with_derivative ht.1 hgeom hn
    hX hY hXd hYd (norm_velocity_lt_one (F.flow zX t).2)
  have hupper : ∀ᶠ r in 𝓝 s, σ r < T := hσc.continuousAt (isOpen_Iio.mem_nhds (hσ ▸ ht.2))
  have heq : σ =ᶠ[𝓝 s] τ := by
    filter_upwards [hev,hupper,(F.isOpen_branchDomain zX zY).mem_nhds hs] with r hr hu hdom
    exact F.branch_unique zX zY hdom ⟨hr.1.le,hu.le⟩ hr.2
  exact ⟨hσc.congr_of_eventuallyEq heq.symm, hσd.congr_of_eventuallyEq heq.symm⟩

lemma PhaseFlowOn.branch_strictMono {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) : StrictMonoOn (branchTime F.flow zX zY T) (branchDomain F.flow zX zY T) := by
  intro a ha b hb hab
  obtain ⟨hta,hea⟩ := F.branch_spec zX zY ha
  obtain ⟨htb,heb⟩ := F.branch_spec zX zY hb
  have hT : 0 ≤ T := ha.1.1.le.trans ha.1.2.le
  have he := F.emission_strictMono hT zY (F.flow zX (branchTime F.flow zX zY T a)).1
    (Ioo_subset_Icc_self ha.1) (Ioo_subset_Icc_self hb.1) hab
  have hat : branchTime F.flow zX zY T a ∈ Icc 0 T := ⟨ha.1.1.le.trans hta.1,hta.2⟩
  have hbt : branchTime F.flow zX zY T b ∈ Icc 0 T := ⟨hb.1.1.le.trans htb.1,htb.2⟩
  have hg := F.arrival_strictMono hT zX (F.flow zY b).1
  apply (hg.lt_iff_lt hat hbt).mp
  dsimp only at he ⊢
  linarith

lemma PhaseFlowOn.branch_convex {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) : Convex ℝ (branchDomain F.flow zX zY T) := by
  apply OrdConnected.convex
  refine ⟨?_⟩
  intro a ha b hb c hc
  refine ⟨⟨lt_of_lt_of_le ha.1.1 hc.1,lt_of_le_of_lt hc.2 hb.1.2⟩,?_⟩
  have hle := (F.emission_strictMono (ha.1.1.le.trans ha.1.2.le) zY (F.flow zX T).1).monotoneOn
    ⟨ha.1.1.le.trans hc.1,hc.2.trans hb.1.2.le⟩ (Ioo_subset_Icc_self hb.1) hc.2
  exact lt_of_le_of_lt hle hb.2

def branchRate (α : Phase → ℝ → Phase) (zX zY : Phase) (T s : ℝ) : ℝ :=
  let τ := branchTime α zX zY T s
  let n := (τ-s)⁻¹ • ((α zX τ).1-(α zY s).1)
  (1-dot n (velocity (α zY s).2))/(1-dot n (velocity (α zX τ).2))

lemma PhaseFlowOn.branch_volume_image {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {H : Set ℝ} (hH : MeasurableSet H)
    (hsub : H ⊆ branchDomain F.flow zX zY T)
    (hne : ∀ s ∈ H, (F.flow zX s).1 ≠ (F.flow zY s).1) :
    (∫⁻ s in H, ENNReal.ofReal (branchRate F.flow zX zY T s)) =
      volume (branchTime F.flow zX zY T '' H) := by
  apply lintegral_deriv_eq_volume_image_of_monotoneOn hH
  · intro s hs
    exact (F.branch_differential zX zY (hsub hs) (hne s hs)).2.hasDerivWithinAt
  · exact (F.branch_strictMono zX zY).monotoneOn.mono hsub

lemma PhaseFlowOn.branch_duration_bound {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {H : Set ℝ} (hH : MeasurableSet H)
    (hsub : H ⊆ branchDomain F.flow zX zY T)
    (hne : ∀ s ∈ H, (F.flow zX s).1 ≠ (F.flow zY s).1)
    {c a b : ℝ} (hder : ∀ s ∈ H, c ≤ branchRate F.flow zX zY T s)
    (himage : branchTime F.flow zX zY T '' H ⊆ Icc a b) :
    ENNReal.ofReal c * volume H ≤ ENNReal.ofReal (b-a) := by
  calc
    _ = ∫⁻ _s in H, ENNReal.ofReal c := by simp
    _ ≤ ∫⁻ s in H, ENNReal.ofReal (branchRate F.flow zX zY T s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hH] with s hs
      exact ENNReal.ofReal_le_ofReal (hder s hs)
    _ = volume (branchTime F.flow zX zY T '' H) := F.branch_volume_image zX zY hH hsub hne
    _ ≤ volume (Icc a b) := measure_mono himage
    _ = _ := Real.volume_Icc

end RVM
end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_continuous_scalar_root {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] {H : ℝ × W → ℝ}
    {L : (ℝ × W) →L[ℝ] ℝ} {t : ℝ} {p : W}
    (hH : HasStrictFDerivAt H L (t,p)) (hzero : H (t,p)=0)
    (hk : L (1,0) ≠ 0) :
    ∃ τ : W → ℝ, τ p=t ∧ ContinuousAt τ p ∧ ∀ᶠ q in 𝓝 p, H (τ q,q)=0 := by
  have hL (x : ℝ × W) : L x = x.1 * L (1,0)+L (0,x.2) := by
    have he : x = x.1 • (1,(0 : W))+(0,x.2) := by ext <;> simp
    conv_lhs => rw [he]
    rw [map_add,map_smul,smul_eq_mul]
  let A : (ℝ × W) →L[ℝ] (ℝ × W) := L.prod (ContinuousLinearMap.snd ℝ ℝ W)
  have hi : Function.Injective A := by
    intro x y h
    have hh : L x = L y := congrArg Prod.fst h
    have he : x.2=y.2 := by
      have he := congrArg Prod.snd h
      exact he
    rw [hL x,hL y,he] at hh
    have hf : x.1=y.1 := (mul_right_cancel₀ hk) (add_right_cancel hh)
    exact Prod.ext hf he
  have hs : Function.Surjective A := by
    intro y
    refine ⟨((y.1-L (0,y.2))/L (1,0),y.2),?_⟩
    apply Prod.ext
    · change L ((y.1-L (0,y.2))/L (1,0),y.2)=y.1
      rw [hL]
      dsimp only
      field_simp
      ring
    · rfl
  let e : (ℝ × W) ≃L[ℝ] (ℝ × W) := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  let Φ : ℝ × W → ℝ × W := fun z => (H z,z.2)
  have hΦ : HasStrictFDerivAt Φ (e : (ℝ × W) →L[ℝ] (ℝ × W)) (t,p) :=
    hH.prodMk hasStrictFDerivAt_snd
  let Z := hΦ.localInverse Φ e (t,p)
  have hZ : HasStrictFDerivAt Z (e.symm : (ℝ × W) →L[ℝ] (ℝ × W)) (0,p) := by
    simpa only [Φ,hzero] using hΦ.to_localInverse
  have hZ₀ : Z (0,p)=(t,p) := by
    simpa only [Φ,hzero] using hΦ.localInverse_apply_image
  let τ : W → ℝ := fun q => (Z (0,q)).1
  have hc : ContinuousAt (fun q : W => ((0 : ℝ),q)) p := continuousAt_const.prodMk continuousAt_id
  refine ⟨τ,congrArg Prod.fst hZ₀,hZ.continuousAt.fst.comp hc,?_⟩
  have hev : ∀ᶠ z in 𝓝 (0,p), Φ (Z z)=z := by
    simpa only [Φ,hzero] using hΦ.eventually_right_inverse
  filter_upwards [hc.eventually hev] with q hq
  have he : (Z (0,q)).2=q := congrArg Prod.snd hq
  have hh : H (Z (0,q))=0 := congrArg Prod.fst hq
  have hz : Z (0,q) = (τ q,q) := Prod.ext rfl he
  rwa [hz] at hh

def jointBranchDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Phase) :=
  {p | p.1 ∈ branchDomain α zX p.2 T ∧ (α zX p.1).1 ≠ (α p.2 p.1).1}

lemma PhaseFlowOn.joint_position_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {p : ℝ × Phase} (hp : p.1 ∈ Ioo 0 T) :
    ContinuousAt (fun q : ℝ × Phase => (F.flow q.2 q.1).1) p :=
  (F.joint p.2 p.1 hp).continuousAt.fst

lemma PhaseFlowOn.isOpen_jointBranchDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) : IsOpen (jointBranchDomain F.flow zX T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hY := F.joint_position_continuousAt hp.1.1
  have hX : ContinuousAt (fun q : ℝ × Phase => (F.flow zX q.1).1) p :=
    (((F.continuousOn_time zX).fst.continuousAt (Icc_mem_nhds hp.1.1.1 hp.1.1.2)).comp
      continuousAt_fst)
  have hd : ContinuousAt (fun q : ℝ × Phase => q.1+‖(F.flow zX T).1-(F.flow q.2 q.1).1‖) p :=
    continuousAt_fst.add ((continuousAt_const.sub hY).norm)
  have ht : ∀ᶠ q : ℝ × Phase in 𝓝 p, q.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hp.1.1)
  have hb := hd.eventually (isOpen_Iio.mem_nhds hp.1.2)
  have hn := (hX.sub hY).eventually (isOpen_compl_singleton.mem_nhds (sub_ne_zero.mpr hp.2))
  filter_upwards [ht,hb,hn] with q hq hqt hqn
  exact ⟨⟨hq,hqt⟩,sub_ne_zero.mp hqn⟩

lemma PhaseFlowOn.joint_branch_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Phase} (hp : p ∈ jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ × Phase => branchTime F.flow zX q.2 T q.1) p := by
  let t := branchTime F.flow zX p.2 T p.1
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hti : t ∈ Ioo 0 T := ⟨hp.1.1.1.trans ht.1,ht.2⟩
  have hspec := (F.branch_spec zX p.2 hp.1).2
  have hxy : (F.flow zX t).1 ≠ (F.flow p.2 p.1).1 := by
    intro he
    rw [he,sub_self,norm_zero] at hspec
    linarith [ht.1]
  let H : ℝ × (ℝ × Phase) → ℝ := fun q => q.1-q.2.1-‖(F.flow zX q.1).1-(F.flow q.2.2 q.2.1).1‖
  have hmap : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (q.1,zX))
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × Phase)).prod 0) (t,p) :=
    hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_const _ _)
  have hparam : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × Phase)) (t,p) := hasStrictFDerivAt_snd
  have hX : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (F.flow zX q.1).1)
      _ (t,p) := ((F.joint zX t hti).comp (t,p) hmap).fst
  have hY : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (F.flow q.2.2 q.2.1).1)
      _ (t,p) := ((F.joint p.2 p.1 hp.1.1).comp (t,p) hparam).fst
  have hN := (hasStrictFDerivAt_norm_nonzero (sub_ne_zero.mpr hxy)).comp (t,p) (hX.sub hY)
  have htproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × Phase)) (t,p) := hasStrictFDerivAt_fst
  have hsproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ Phase).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Phase))) (t,p) :=
    hasStrictFDerivAt_fst.comp (t,p) hparam
  have hH := (htproj.sub hsproj).sub hN
  have hroot : ∃ L : (ℝ × (ℝ × Phase)) →L[ℝ] ℝ,
      HasStrictFDerivAt H L (t,p) ∧ L (1,0) =
        1-dot (‖(F.flow zX t).1-(F.flow p.2 p.1).1‖⁻¹ •
          ((F.flow zX t).1-(F.flow p.2 p.1).1)) (velocity (F.flow zX t).2) := by
    refine ⟨_,hH,?_⟩
    change 1 - (0 : ℝ) - inner ℝ
      (‖(F.flow zX t).1-(F.flow p.2 p.1).1‖⁻¹ •
        ((F.flow zX t).1-(F.flow p.2 p.1).1))
      (((1 : ℝ) • lorentzField E B (t,F.flow zX t) + F.differential zX t 0).1 -
        (((0 : ℝ) • lorentzField E B (p.1,F.flow p.2 p.1) + F.differential p.2 p.1 0).1)) = _
    simp only [map_zero,one_smul,zero_smul,add_zero,Prod.fst_zero,sub_zero,← dot_eq_inner]
    rfl
  obtain ⟨L,hL,hk⟩ := hroot
  have hkne : L (1,0) ≠ 0 := by
    rw [hk]
    exact ne_of_gt (cone_deficit_positive hxy (F.flow zX t).2)
  obtain ⟨τ,hτ,hτc,hev⟩ := exists_continuous_scalar_root hL
    (by dsimp [H]; linarith) hkne
  have hle : ∀ᶠ q in 𝓝 p, q.1 < τ q ∧ τ q < T := by
    have hpos : 0 < τ p-p.1 := by rw [hτ]; exact sub_pos.mpr ht.1
    have h1 : ∀ᶠ q in 𝓝 p, 0 < τ q-q.1 :=
      (hτc.sub continuousAt_fst).eventually (isOpen_Ioi.mem_nhds hpos)
    have hend : τ p < T := by rw [hτ]; exact ht.2
    have h2 := hτc.eventually (isOpen_Iio.mem_nhds hend)
    filter_upwards [h1,h2] with q hq hqT
    exact ⟨sub_pos.mp hq,hqT⟩
  apply hτc.congr_of_eventuallyEq
  filter_upwards [hev,hle,(F.isOpen_jointBranchDomain zX).mem_nhds hp] with q hq hqt hqd
  exact (F.branch_unique zX q.2 hqd.1 ⟨hqt.1.le,hqt.2.le⟩ (by change H (τ q,q)=0 at hq; dsimp [H] at hq; linarith)).symm

lemma PhaseFlowOn.measurable_branch_zero {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    Measurable ((jointBranchDomain F.flow zX T).indicator
      (fun p : ℝ × Phase => branchTime F.flow zX p.2 T p.1)) := by
  classical
  have hc : ContinuousOn (fun p : ℝ × Phase => branchTime F.flow zX p.2 T p.1)
      (jointBranchDomain F.flow zX T) :=
    fun _ hp => (F.joint_branch_continuousAt zX hp).continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet

lemma PhaseFlowOn.measurable_joint_flow_zero {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) :
    Measurable ((Ioo 0 T ×ˢ (univ : Set Phase)).indicator
      (fun p : ℝ × Phase => F.flow p.2 p.1)) := by
  classical
  have hc : ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Ioo 0 T ×ˢ (univ : Set Phase)) :=
    fun p hp => (F.joint p.2 p.1 hp.1).continuousAt.continuousWithinAt
  have hh := hc.measurable_piecewise
    (continuousOn_const (c := (0 : Phase))) (measurableSet_Ioo.prod MeasurableSet.univ)
  convert hh using 1
  funext p
  by_cases hp : p ∈ Ioo 0 T ×ˢ (univ : Set Phase) <;>
    simp [Set.indicator,Set.piecewise,hp]

end RVM

end

end OAI
