import OAI.Geometry.KahlerSplitting.FlowVariation

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

abbrev FlowTimes (n : ℕ) := Fin n → ℂ

def trimFlowTimes (n : ℕ) : FlowTimes (n+1) →L[ℂ] FlowTimes n :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj i.castSucc)

@[simp] theorem trimFlowTimes_apply (n : ℕ) (t : FlowTimes (n+1)) (i : Fin n) :
    trimFlowTimes n t i = t i.castSucc := rfl

@[simp] theorem trimFlowTimes_single_castSucc (n : ℕ) (i : Fin n) :
    trimFlowTimes n (Pi.single i.castSucc (1 : ℂ)) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply]

@[simp] theorem trimFlowTimes_single_last (n : ℕ) :
    trimFlowTimes n (Pi.single (Fin.last n) (1 : ℂ)) = 0 := by
  ext j
  simp

structure CommutingFlowData (n : ℕ) (V : Fin n → C(E,E))
    (D : Fin n → C(E,E →L[ℂ] E)) (U : Set E) (p : E) where
  domain : Set (E × FlowTimes n)
  isOpen_domain : IsOpen domain
  base_mem : (p,0) ∈ domain
  map : E × FlowTimes n → E
  contDiff : ContDiffOn ℂ 1 map domain
  mapsTo : MapsTo map domain U
  zero : ∀ x, (x,0) ∈ domain → map (x,0) = x
  time : ∀ q ∈ domain, ∀ i : Fin n,
    fderiv ℂ map q (0,Pi.single i 1) = V i (map q)
  preserves : ∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
    (∀ x ∈ U, HasFDerivAt A (DA x) x) →
    (∀ i x, x ∈ U → DA x (V i x) = D i x (A x)) →
    ∀ q ∈ domain, fderiv ℂ map q (A q.1,0) = A (map q)

theorem exists_commutingFlowData (n : ℕ) (V : Fin n → C(E,E))
    (D : Fin n → C(E,E →L[ℂ] E)) {U : Set E} (hU : IsOpen U)
    (hV : ∀ i x, x ∈ U → HasFDerivAt (V i) (D i x) x)
    (hcomm : ∀ i j x, x ∈ U → D j x (V i x) = D i x (V j x))
    {p : E} (hp : p ∈ U) : Nonempty (CommutingFlowData n V D U p) := by
  induction n with
  | zero =>
    refine ⟨⟨U ×ˢ univ,hU.prod isOpen_univ,⟨hp,mem_univ _⟩,Prod.fst,
      contDiff_fst.contDiffOn,fun q hq ↦ hq.1,fun _ _ ↦ rfl,?_,?_⟩⟩
    · intro q hq i
      exact Fin.elim0 i
    · intro A DA hA hcomm q hq
      simp [fderiv_fst]
  | succ n ih =>
    obtain ⟨G⟩ := ih (fun i ↦ V i.castSucc) (fun i ↦ D i.castSucc)
      (fun i ↦ hV i.castSucc) (fun i j ↦ hcomm i.castSucc j.castSucc)
    obtain ⟨H⟩ := exists_holomorphicFlowData (V (Fin.last n)) (D (Fin.last n))
      hU (hV (Fin.last n)) hp
    let pr : E × FlowTimes (n+1) →L[ℂ] E × FlowTimes n :=
      (ContinuousLinearMap.fst ℂ E (FlowTimes (n+1))).prod
        ((trimFlowTimes n).comp (ContinuousLinearMap.snd ℂ E (FlowTimes (n+1))))
    let last : E × FlowTimes (n+1) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (Fin.last n)).comp
        (ContinuousLinearMap.snd ℂ E (FlowTimes (n+1)))
    let c : E × FlowTimes (n+1) → E × ℂ := fun q ↦ (G.map (pr q),last q)
    let O := pr ⁻¹' G.domain ∩ c ⁻¹' H.domain
    let F : E × FlowTimes (n+1) → E := H.map ∘ c
    have hpr : IsOpen (pr ⁻¹' G.domain) := G.isOpen_domain.preimage pr.continuous
    have hc : ContDiffOn ℂ 1 c (pr ⁻¹' G.domain) :=
      (G.contDiff.comp pr.contDiff.contDiffOn (fun _ hq ↦ hq)).prodMk last.contDiff.contDiffOn
    have hO : IsOpen O := hc.continuousOn.isOpen_inter_preimage hpr H.isOpen_domain
    have hbase : (p,0) ∈ O := by
      have hG0 := G.zero p G.base_mem
      constructor
      · simpa [pr] using G.base_mem
      · simpa [c,pr,last,hG0] using H.base_mem
    have hF : ContDiffOn ℂ 1 F O := H.contDiff.comp (hc.mono inter_subset_left)
      (fun q hq ↦ hq.2)
    have hFd (q : E × FlowTimes (n+1)) (hq : q ∈ O) :
        fderiv ℂ F q = (fderiv ℂ H.map (c q)).comp
          (((fderiv ℂ G.map (pr q)).comp pr).prod last) := by
      have hGq := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds hq.1)).differentiableAt (by norm_num)
      have hHq := (H.contDiff.contDiffAt (H.isOpen_domain.mem_nhds hq.2)).differentiableAt (by norm_num)
      exact (hHq.hasFDerivAt.comp q ((hGq.hasFDerivAt.comp q pr.hasFDerivAt).prodMk
        last.hasFDerivAt)).fderiv
    refine ⟨⟨O,hO,hbase,F,hF,fun q hq ↦ H.mapsTo hq.2,?_,?_,?_⟩⟩
    · intro x hx
      have hGx : G.map (x,0) = x := G.zero x (by simpa [pr] using hx.1)
      have hHx : (x,0) ∈ H.domain := by simpa [c,pr,last,hGx] using hx.2
      simpa [F,c,pr,last,hGx] using H.zero x hHx
    · intro q hq i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [hFd q hq]
        change (fderiv ℂ H.map (c q))
          ((fderiv ℂ G.map (pr q)) (pr (0,Pi.single (Fin.last n) 1)),
            last (0,Pi.single (Fin.last n) 1)) = _
        have hpr0 : pr (0,Pi.single (Fin.last n) 1) = 0 := by simp [pr]
        have hl1 : last (0,Pi.single (Fin.last n) 1) = 1 := by simp [last]
        rw [hpr0,map_zero,hl1]
        exact H.time (c q) hq.2
      · rw [hFd q hq]
        have hGi := G.time (pr q) hq.1 j
        have hHi := H.preserves (V j.castSucc) (D j.castSucc)
          (hV j.castSucc) (fun x hx ↦ hcomm (Fin.last n) j.castSucc x hx) (c q) hq.2
        change (fderiv ℂ H.map (c q))
          ((fderiv ℂ G.map (pr q)) (pr (0,Pi.single j.castSucc 1)),
            last (0,Pi.single j.castSucc 1)) = _
        have hprj : pr (0,Pi.single j.castSucc 1) = (0,Pi.single j 1) := by simp [pr]
        have hlj : last (0,Pi.single j.castSucc 1) = 0 := by simp [last]
        rw [hprj,hlj,hGi]
        exact hHi
    · intro A DA hA hAC q hq
      rw [hFd q hq]
      have hGA := G.preserves A DA hA (fun i ↦ hAC i.castSucc) (pr q) hq.1
      have hHA := H.preserves A DA hA (hAC (Fin.last n)) (c q) hq.2
      change (fderiv ℂ H.map (c q))
        ((fderiv ℂ G.map (pr q)) (pr (A q.1,0)),last (A q.1,0)) = _
      have hprA : pr (A q.1,0) = (A (pr q).1,0) := by simp [pr]
      have hlA : last (A q.1,0) = 0 := by simp [last]
      rw [hprA,hlA,hGA]
      exact hHA

end UniversalCoverSplitting

open Set Filter Topology Metric Complex
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem continuousOn_directional_cauchy {U S : Set E} {f : E → F}
    (hf : ContinuousOn f U) (e : E) {r : ℝ} (hr : 0 < r)
    (hmap : ∀ z ∈ S, ∀ θ : ℝ, z + circleMap 0 r θ • e ∈ U) :
    ContinuousOn (fun z ↦ cderiv r (fun w : ℂ ↦ f (z + w • e)) 0) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  let G : S → ℝ → F := fun z θ ↦
    (circleMap 0 r θ * I) • (((circleMap 0 r θ)^2)⁻¹ •
      f (z.val + circleMap 0 r θ • e))
  have hG : Continuous G.uncurry := by
    have hc : Continuous (fun p : S × ℝ ↦ p.1.val + circleMap 0 r p.2 • e) := by
      fun_prop
    have hm : MapsTo (fun p : S × ℝ ↦ p.1.val + circleMap 0 r p.2 • e) univ U :=
      fun p _ ↦ hmap p.1.val p.1.property p.2
    have hcomp := continuousOn_univ.mp (hf.comp hc.continuousOn hm)
    have hne (p : S × ℝ) : circleMap 0 r p.2 ≠ 0 :=
      circleMap_ne_mem_ball (mem_ball_self hr) p.2
    dsimp [G, Function.uncurry]
    apply Continuous.smul
    · fun_prop
    · exact (((continuous_circleMap 0 r).comp continuous_snd).pow 2).inv₀
        (fun p ↦ pow_ne_zero 2 (hne p)) |>.smul hcomp
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hG (a₀ := 0) (b₀ := 2 * Real.pi)
  convert! hi.const_smul ((2 * Real.pi * I : ℂ)⁻¹) using 1
  ext z
  simp only [cderiv, circleIntegral, deriv_circleMap, G, circleMap, zero_add,
    sub_zero, Pi.smul_apply, Set.domRestrict]

variable [CompleteSpace F]

theorem continuousAt_directional_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {p : E} (hp : p ∈ U) (e : E) :
    ContinuousAt (fun z ↦ fderiv ℂ f z e) p := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r : ℝ := d / (2 * (‖e‖ + 1))
  have he : 0 < ‖e‖ + 1 := by positivity
  have hr : 0 < r := div_pos hd (by positivity)
  have hre : r * ‖e‖ ≤ d / 2 := by
    have hprod : r * (‖e‖ + 1) = d / 2 := by
      dsimp [r]; field_simp
    nlinarith
  let S := ball p (d / 2)
  have hS : S ∈ 𝓝 p := ball_mem_nhds _ (by linarith)
  have hmap (z : E) (hz : z ∈ S) (w : ℂ) (hw : w ∈ closedBall 0 r) :
      z + w • e ∈ U := by
    apply hdU
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    calc
      ‖z + w • e - p‖ = ‖(z-p) + w • e‖ := by congr 1; abel
      _ ≤ ‖z-p‖ + ‖w • e‖ := norm_add_le _ _
      _ = ‖z-p‖ + ‖w‖ * ‖e‖ := by rw [norm_smul]
      _ ≤ ‖z-p‖ + r * ‖e‖ := by gcongr
      _ < d := by linarith
  have hc := continuousOn_directional_cauchy hf.continuousOn e hr
    (fun z hz θ ↦ hmap z hz _ (circleMap_mem_closedBall _ hr.le _))
  have heq : (fun z ↦ cderiv r (fun w : ℂ ↦ f (z + w • e)) 0)
      =ᶠ[𝓝 p] (fun z ↦ fderiv ℂ f z e) := by
    filter_upwards [hS] with z hz
    let V : Set ℂ := (fun w : ℂ ↦ z + w • e) ⁻¹' U
    have hV : IsOpen V := hU.preimage (by fun_prop)
    have hline : DifferentiableOn ℂ (fun w : ℂ ↦ f (z + w • e)) V :=
      hf.comp (by fun_prop) (fun _ hw ↦ hw)
    rw [cderiv_eq_deriv hV hline hr (hmap z hz)]
    have hzU : z ∈ U := by simpa using hmap z hz 0 (mem_closedBall_self hr.le)
    have hdline : HasDerivAt (fun w : ℂ ↦ z + w • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add z
    have hdf := (hf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt
    have hh := (show HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • e) by
      simpa using hdf).comp_hasDerivAt 0 hdline
    simpa only [Function.comp_def] using hh.deriv
  exact (hc.continuousAt hS).congr heq

theorem finite_holomorphic_contDiffOn_one [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from by simp, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hf,by simp,?_⟩
  rw [contDiffOn_zero]
  intro p hp
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_clm_apply]
  exact continuousAt_directional_fderiv hU hf hp

end UniversalCoverSplitting

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialClamp (p : E) (r : ℝ) (x : E) : E :=
  p + (r / max r ‖x-p‖) • (x-p)

 theorem continuous_radialClamp (p : E) {r : ℝ} (hr : 0 < r) :
    Continuous (radialClamp p r) := by
  have hn (x : E) : max r ‖x-p‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))
  unfold radialClamp
  exact continuous_const.add ((continuous_const.div
    (continuous_const.max (continuous_id.sub continuous_const).norm) hn).smul
      (continuous_id.sub continuous_const))

 theorem radialClamp_eq_self_of_mem_closedBall {p x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ closedBall p r) : radialClamp p r x = x := by
  rw [mem_closedBall,dist_eq_norm] at hx
  simp [radialClamp,max_eq_left hx,div_self (ne_of_gt hr)]

 theorem radialClamp_mem_closedBall (p x : E) {r : ℝ} (hr : 0 < r) :
    radialClamp p r x ∈ closedBall p r := by
  by_cases hx : x ∈ closedBall p r
  · simpa [radialClamp_eq_self_of_mem_closedBall hr hx] using hx
  · rw [mem_closedBall,dist_eq_norm] at hx ⊢
    have hnx : r < ‖x-p‖ := lt_of_not_ge hx
    have hnorm : 0 < ‖x-p‖ := hr.trans hnx
    rw [radialClamp,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      max_eq_right hnx.le,abs_of_nonneg (div_nonneg hr.le (norm_nonneg _)),
      div_mul_cancel₀ _ (ne_of_gt hnorm)]

 theorem radialClamp_eventuallyEq_id {p x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ ball p r) : radialClamp p r =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact radialClamp_eq_self_of_mem_closedBall hr (ball_subset_closedBall hy)

end UniversalCoverSplitting
open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [IsScalarTower ℝ ℂ E] in

theorem holomorphic_continuous_representatives {U : Set E} (hU : IsOpen U)
    {V : E → F} (hV : DifferentiableOn ℂ V U) {p : E} (hp : p ∈ U) :
    ∃ r > 0, ∃ f : C(E,F), ∃ D : C(E,E →L[ℂ] F),
      ball p r ⊆ U ∧ ∀ x ∈ ball p r,
        f x = V x ∧ D x = fderiv ℂ V x ∧ HasFDerivAt f (D x) x := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r := d/2
  have hr : 0 < r := half_pos hd
  have hcU : closedBall p r ⊆ U :=
    (closedBall_subset_ball (by dsimp [r]; linarith : r < d)).trans hdU
  have hclamp := continuous_radialClamp p hr
  have hm (x : E) : radialClamp p r x ∈ U := hcU (radialClamp_mem_closedBall p x hr)
  have hDV := (finite_holomorphic_contDiffOn_one hU hV).continuousOn_fderiv_of_isOpen hU le_rfl
  let f : C(E,F) := ⟨V ∘ radialClamp p r,
    hV.continuousOn.comp_continuous hclamp (fun x ↦ hm x)⟩
  let D : C(E,E →L[ℂ] F) := ⟨fderiv ℂ V ∘ radialClamp p r,
    hDV.comp_continuous hclamp (fun x ↦ hm x)⟩
  refine ⟨r,hr,f,D,ball_subset_closedBall.trans hcU,?_⟩
  intro x hx
  have hid := radialClamp_eq_self_of_mem_closedBall hr (ball_subset_closedBall hx)
  have hf : f x = V x := by dsimp [f]; rw [hid]
  have hD : D x = fderiv ℂ V x := by dsimp [D]; rw [hid]
  refine ⟨hf,hD,?_⟩
  rw [hD]
  apply (hV.differentiableAt (hU.mem_nhds (hcU (ball_subset_closedBall hx)))).hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [radialClamp_eventuallyEq_id hr hx] with y hy
  change V (radialClamp p r y) = V y
  rw [hy]; rfl

end UniversalCoverSplitting

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem finite_holomorphic_representatives {ι : Type*} [Finite ι]
    {U : Set E} (hU : IsOpen U) (V : ι → E → F)
    (hV : ∀ i, DifferentiableOn ℂ (V i) U) {p : E} (hp : p ∈ U) :
    ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∃ f : ι → C(E,F), ∃ D : ι → C(E,E →L[ℂ] F),
        ∀ i x, x ∈ O → f i x = V i x ∧ D i x = fderiv ℂ (V i) x ∧
          HasFDerivAt (f i) (D i x) x := by
  choose r hr f D hball hrep using fun i ↦ holomorphic_continuous_representatives hU (hV i) hp
  let O := U ∩ ⋂ i, ball p (r i)
  refine ⟨O,hU.inter (isOpen_iInter_of_finite fun i ↦ isOpen_ball),
    ⟨hp,mem_iInter.mpr (fun i ↦ mem_ball_self (hr i))⟩,inter_subset_left,f,D,?_⟩
  intro i x hx
  exact hrep i x (mem_iInter.mp hx.2 i)

end UniversalCoverSplitting

end

end OAI
