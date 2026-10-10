import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.PhysicalVolume
import OAI.Dynamics.StandardMap.Holonomy.FinePlaqueParameters

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

lemma compact_fibre_descent {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x y, f x=f y → g x=g y) :
    ∃ H : ℝ → ℝ, ContinuousOn H (range f) ∧ ∀ x, H (f x)=g x := by
  classical
  let H : ℝ → ℝ := fun y => if hy : y∈range f then g (Classical.choose hy) else 0
  have hH (x : X) : H (f x)=g x := by
    dsimp only [H]
    rw [dite_eq_left (mem_range_self x)]
    exact hfg _ x (Classical.choose_spec (mem_range_self x))
  refine ⟨H,?_,hH⟩
  let q : X → range f := fun x => ⟨f x,mem_range_self x⟩
  have hq : Continuous q := hf.subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  have hquot := IsQuotientMap.of_surjective_continuous hqs hq
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hquot.continuous_iff.mpr
  have he : (fun y : range f => H y) ∘ q=g := by funext x; exact hH x
  change Continuous ((fun y : range f => H y) ∘ q)
  rw [he]
  exact hg

theorem compact_actual_stable_holonomy {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (P Q W : ℂ) (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfib : ∀ x y, f x=f y ↔ g x=g y)
    (hplaque : ∀ x, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1/12 ∧ |u|≤1/12 ∧
      |(fineInverse k χ ε δ (complexProjection v) W).1|≤
        |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 ∧
      P+f x•W=fineStableCurve k χ ε δ hδ hq v hv s ∧
      Q+g x•W=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∃ H J : ℝ → ℝ,
      ContinuousOn H (range f) ∧ ContinuousOn J (range g) ∧
      (∀ x, H (f x)=g x ∧ J (g x)=f x) ∧
      (∀ y∈range f, J (H y)=y) ∧ (∀ y∈range g, H (J y)=y) ∧
      (∀ Z : Set ℝ, Z⊆range f → volume Z=0 → volume (H '' Z)=0) ∧
      (∀ Z : Set ℝ, Z⊆range g → volume Z=0 → volume (J '' Z)=0) := by
  obtain ⟨H,hH,hHval⟩ := compact_fibre_descent hf hg (fun x y h => (hfib x y).mp h)
  obtain ⟨J,hJ,hJval⟩ := compact_fibre_descent hg hf (fun x y h => (hfib x y).mpr h)
  refine ⟨H,J,hH,hJ,fun x => ⟨hHval x,hJval x⟩,?_,?_,?_,?_⟩
  · rintro y ⟨x,rfl⟩; rw [hHval,hJval]
  · rintro y ⟨x,rfl⟩; rw [hJval,hHval]
  · intro Z hZS hZ
    apply actual_stable_holonomy_null_image k hk χ ε δ hε hδ hδ' hq hslow P Q W (range f) H hH _ hZS hZ
    rintro t ⟨x,rfl⟩
    obtain ⟨v,hv,s,u,hs,hu,hc,hn,hp,hq'⟩ := hplaque x
    exact ⟨v,hv,s,u,hs,hu,hc,hn,hp,by rw [hHval]; exact hq'⟩
  · intro Z hZS hZ
    apply actual_stable_holonomy_null_image k hk χ ε δ hε hδ hδ' hq hslow Q P W (range g) J hJ _ hZS hZ
    rintro t ⟨x,rfl⟩
    obtain ⟨v,hv,s,u,hs,hu,hc,hn,hp,hq'⟩ := hplaque x
    exact ⟨v,hv,u,s,hu,hs,hc,hn,hq',by rw [hJval]; exact hp⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_transverse_cone (k χ ε δ : ℝ) (w v : ℂ)
    (hc : ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4) :
    let W := fineFrame k χ ε δ (complexProjection w) (0,1)
    |(fineInverse k χ ε δ (complexProjection v) W).1|≤
      |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 := by
  dsimp only
  let A := (fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))
  have h := (ContinuousLinearMap.le_opNorm (A-ContinuousLinearMap.id ℝ Plane) ((0,1) : Plane)).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hnorm : ‖((0,1) : Plane)‖=1 := by simp [Prod.norm_def]
  rw [hnorm,mul_one] at h
  have he : ((A-ContinuousLinearMap.id ℝ Plane) (0,1))=A (0,1)-(0,1) := rfl
  rw [he] at h
  have h1 : |(A (0,1)).1|≤1/4 := by simpa using (norm_fst_le _).trans h
  have h2 : |(A (0,1)).2-1|≤1/4 := (norm_snd_le _).trans h
  have h2' : 3/4≤(A (0,1)).2 := by linarith [(abs_le.mp h2).1]
  change |(A (0,1)).1|≤|(A (0,1)).2| ∧ (A (0,1)).2≠0
  exact ⟨h1.trans (by linarith [le_abs_self ((A (0,1)).2)]),ne_of_gt (by linarith)⟩

theorem actual_compact_slice_holonomy {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (w : ℂ) (hw : wedge (stableVector k (complexProjection w)) (unstableVector k (complexProjection w))≠0)
    (v : X → ℂ) (hvc : Continuous v)
    (hv : ∀ x, ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v x))))
    (hdata : ∀ n : ℕ, Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (v x)))))
    {r R : ℝ} (hr : 0<r) (hrsmall : r≤1/12) (hR : 0<R)
    (hRv : ∀ x, R≤codingRadius k χ ε δ (complexProjection (v x)))
    (hsize : (4*fineScale k ε δ*r)/(100*R)+r≤1)
    (hclose : ∀ x, ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection (v x)))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (hclose' : ∀ x, ‖(fineInverse k χ ε δ (complexProjection (v x))).comp (fineFrame k χ ε δ (complexProjection w))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (hcentre : ∀ x, |(fineInverse k χ ε δ (complexProjection w) (v x-w)).1|≤r/4) :
    ∃ σ : (X×Icc (-r/2) (r/2)) → Icc (-r) r, Continuous σ ∧
      (∀ p : X×Icc (-r/2) (r/2),
        (finePlaqueInChart k χ ε δ hδ hq w (v p.1) (hv p.1) (σ p)).1=(p.2 : ℝ)) ∧
      ∀ c d : Icc (-r/2) (r/2),
      let f := fun x => (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,c))).2
      let g := fun x => (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,d))).2
      ∃ H J : ℝ → ℝ,
        ContinuousOn H (range f) ∧ ContinuousOn J (range g) ∧
        (∀ x, H (f x)=g x ∧ J (g x)=f x) ∧
        (∀ y∈range f, J (H y)=y) ∧ (∀ y∈range g, H (J y)=y) ∧
        (∀ Z : Set ℝ, Z⊆range f → volume Z=0 → volume (H '' Z)=0) ∧
        (∀ Z : Set ℝ, Z⊆range g → volume Z=0 → volume (J '' Z)=0) := by
  have hr1 : r≤1 := by linarith
  obtain ⟨σ,hσ,hσval⟩ := fine_compact_graph_crossing k χ ε δ hδ hq w v hvc hv hdata hr hr1 hclose hcentre
  refine ⟨σ,hσ,hσval,?_⟩
  intro c d
  dsimp only
  let f (x : X) := (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,c))).2
  let g (x : X) := (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,d))).2
  have hs (x : X) (a : Icc (-r/2) (r/2)) : |(σ (x,a) : ℝ)|≤r := abs_le.mpr (σ (x,a)).property
  have hc (a : Icc (-r/2) (r/2)) : Continuous
      (fun x => fineStableCurve k χ ε δ hδ hq (v x) (hv x) (σ (x,a))) := by
    let s : X → Icc (-1 : ℝ) 1 := fun x => ⟨σ (x,a),abs_le.mp ((hs x a).trans hr1)⟩
    have hsc : Continuous s := ((hσ.comp (continuous_id.prodMk continuous_const)).subtype_val).subtype_mk _
    exact (continuous_fineStableCurve_family k χ ε δ hδ hq v hvc hv hdata).comp
      (continuous_id.prodMk hsc)
  have hf : Continuous f := continuous_snd.comp ((fineInverse k χ ε δ (complexProjection w)).continuous.comp
    ((hc c).sub continuous_const))
  have hg : Continuous g := continuous_snd.comp ((fineInverse k χ ε δ (complexProjection w)).continuous.comp
    ((hc d).sub continuous_const))
  have hslow2 : Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)≤1 := by
    apply le_trans _ hslow.le
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have meet (a : Icc (-r/2) (r/2)) (x y : X)
      (he : (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,a))).2=
        (finePlaqueInChart k χ ε δ hδ hq w (v y) (hv y) (σ (y,a))).2) :
      fineStableCurve k χ ε δ hδ hq (v x) (hv x) (σ (x,a))=
        fineStableCurve k χ ε δ hδ hq (v y) (hv y) (σ (y,a)) := by
    have hi : finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,a))=
        finePlaqueInChart k χ ε δ hδ hq w (v y) (hv y) (σ (y,a)) :=
      Prod.ext ((hσval (x,a)).trans (hσval (y,a)).symm) he
    have hi' := congrArg (fineFrame k χ ε δ (complexProjection w)) hi
    simp only [finePlaqueInChart,fineFrame_inverse k χ ε hδ _ hw] at hi'
    exact sub_left_injective hi'
  have hfib : ∀ x y, f x=f y ↔ g x=g y := by
    intro x y
    constructor
    · intro he
      have hp := fine_small_crossings_coincide k χ ε δ hδ hq hslow2 w (v x) (v y) (hv x) (hv y)
        hr hr1 hR (hRv x) hsize (hclose x) (hs x c) (hs x d) (hs y c) (hs y d)
        (meet c x y he) ((hσval (x,d)).trans (hσval (y,d)).symm)
      exact congrArg (fun p => (fineInverse k χ ε δ (complexProjection w) (p-w)).2) hp
    · intro he
      have hp := fine_small_crossings_coincide k χ ε δ hδ hq hslow2 w (v x) (v y) (hv x) (hv y)
        hr hr1 hR (hRv x) hsize (hclose x) (hs x d) (hs x c) (hs y d) (hs y c)
        (meet d x y he) ((hσval (x,c)).trans (hσval (y,c)).symm)
      exact congrArg (fun p => (fineInverse k χ ε δ (complexProjection w) (p-w)).2) hp
  let W := fineFrame k χ ε δ (complexProjection w) (0,1)
  have endpoint (a : Icc (-r/2) (r/2)) (x : X) :
      w+fineFrame k χ ε δ (complexProjection w) ((a : ℝ),0)+
      (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,a))).2•W=
      fineStableCurve k χ ε δ hδ hq (v x) (hv x) (σ (x,a)) := by
    let p := finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ (x,a))
    have hp : ((a : ℝ),0)+p.2•((0,1) : Plane)=p := by
      change ((a : ℝ)+p.2*0,0+p.2*1)=p
      apply Prod.ext
      · change (a : ℝ)+p.2*0=p.1
        simpa only [mul_zero,add_zero] using (hσval (x,a)).symm
      · change 0+p.2*1=p.2
        ring
    change w+fineFrame k χ ε δ (complexProjection w) ((a : ℝ),0)+p.2•fineFrame k χ ε δ (complexProjection w) (0,1)=_
    rw [← map_smul,add_assoc,← map_add,hp]
    dsimp only [p,finePlaqueInChart]
    rw [fineFrame_inverse k χ ε hδ _ hw]
    abel
  apply compact_actual_stable_holonomy k hk χ ε δ hε hδ hδ' hq hslow
    (w+fineFrame k χ ε δ (complexProjection w) ((c : ℝ),0))
    (w+fineFrame k χ ε δ (complexProjection w) ((d : ℝ),0)) W f g hf hg hfib
  intro x
  exact ⟨v x,hv x,σ (x,c),σ (x,d),(hs x c).trans hrsmall,(hs x d).trans hrsmall,
    (fine_transverse_cone k χ ε δ w (v x) (hclose' x)).1,
    (fine_transverse_cone k χ ε δ w (v x) (hclose' x)).2,endpoint c x,endpoint d x⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma complexRep_norm_le_two (z : Torus) : ‖complexRep z‖≤2 := by
  have h1 := circleRep_mem z.1
  have h2 := circleRep_mem z.2
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |circleRep z.1|+|circleRep z.2|≤2
  rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]
  linarith [h1.2,h2.2]

theorem compact_lift_fineRegular_block (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ C : Set ℂ, IsCompact C ∧ 0<volume C ∧
      (∀ v∈C,complexProjection v∈spectralGapRegion k hk χ) ∧
      ContinuousOn (fun v => orbitChartData k χ ε (complexProjection v)) C ∧
      ∀ v∈C, ∀ n : ℕ,
        FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)) ∧
        FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] v)) := by
  obtain ⟨K,hKG,hK,hKpos,hdata,hreg⟩ := compact_fineRegular_block k hk hχ hε hgap
  let C : Set ℂ := complexProjection ⁻¹' K ∩ Metric.closedBall 0 2
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) 2).inter_left
    (hK.isClosed.preimage continuous_complexProjection)
  have hKC : area K≤volume C := area_le_volume_of_complexRep_subset hK.measurableSet (by
    intro z hz
    exact ⟨by simpa only [mem_preimage,complexProjection_complexRep] using hz,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using complexRep_norm_le_two z⟩)
  refine ⟨C,hC,hKpos.trans_le hKC,fun v hv => hKG hv.1,?_,?_⟩
  · exact hdata.comp continuous_complexProjection.continuousOn (fun _ hv => hv.1)
  · intro v hv n
    have h := hreg (complexProjection v) hv.1 n
    simpa only [complexProjection_iterate,complexProjection_inverse_iterate] using h

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma positive_compact_neighborhood {C : Set ℂ} (hC : IsCompact C) (hpos : 0<volume C) :
    ∃ w∈C, ∀ P : ℂ → Prop, (∀ᶠ v in 𝓝[C] w, P v) →
      ∃ K : Set ℂ, K⊆C ∧ IsCompact K ∧ 0<volume K ∧ ∀ v∈K,P v := by
  have hpos' : 0<(volume.restrict C) C := by simpa only [Measure.restrict_apply hC.measurableSet,inter_self] using hpos
  obtain ⟨w,hwC,hwSupp⟩ := Measure.nonempty_inter_support_of_pos hpos'
  refine ⟨w,hwC,?_⟩
  intro P hP
  obtain ⟨a,ha,hak⟩ := Metric.mem_nhdsWithin_iff.mp hP
  let K := C∩Metric.closedBall w (a/2)
  have hb : Metric.ball w (a/2)∈𝓝 w := Metric.ball_mem_nhds _ (by linarith)
  have hbp : 0<volume (Metric.ball w (a/2)∩C) := by
    have h := ((Measure.mem_support_iff_forall w).mp hwSupp) _ hb
    simpa only [Measure.restrict_apply measurableSet_ball] using h
  refine ⟨K,inter_subset_left,hC.inter_right Metric.isClosed_closedBall,?_,?_⟩
  · apply hbp.trans_le (measure_mono _)
    rintro v ⟨hv,hvC⟩
    exact ⟨hvC,Metric.ball_subset_closedBall hv⟩
  · intro v hv
    apply hak
    exact ⟨(Metric.mem_ball).mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hv.2) (by linarith)),hv.1⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

structure SmallPesinBlock (k χ ε δ : ℝ) where
  carrier : Set ℂ
  compact : IsCompact carrier
  positive : 0<volume carrier
  centre : ℂ
  centre_regular : wedge (stableVector k (complexProjection centre)) (unstableVector k (complexProjection centre))≠0
  r : ℝ
  r_pos : 0<r
  r_small : r≤1/12
  R : ℝ
  R_pos : 0<R
  radius_lower : ∀ v∈carrier,R≤codingRadius k χ ε δ (complexProjection v)
  size : (4*fineScale k ε δ*r)/(100*R)+r≤1
  data : ContinuousOn (fun v => orbitChartData k χ ε (complexProjection v)) carrier
  regular : ∀ v∈carrier,∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)) ∧
    FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] v))
  frame_close : ∀ v∈carrier, ‖(fineInverse k χ ε δ (complexProjection centre)).comp (fineFrame k χ ε δ (complexProjection v))-
    ContinuousLinearMap.id ℝ Plane‖≤1/4
  coframe_close : ∀ v∈carrier, ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection centre))-
    ContinuousLinearMap.id ℝ Plane‖≤1/4
  centre_close : ∀ v∈carrier, |(fineInverse k χ ε δ (complexProjection centre) (v-centre)).1|≤r/4

theorem smallPesinBlock_within (k χ ε δ : ℝ) (hδ : 0<δ)
    {C : Set ℂ} (hC : IsCompact C) (hCpos : 0<volume C)
    (hdata : ContinuousOn (fun v => orbitChartData k χ ε (complexProjection v)) C)
    (hreg : ∀ v∈C,∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)) ∧
      FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] v))) :
    ∃ B : SmallPesinBlock k χ ε δ, B.carrier⊆C := by
  obtain ⟨w,hwC,hw⟩ := positive_compact_neighborhood hC hCpos
  have hwreg : wedge (stableVector k (complexProjection w)) (unstableVector k (complexProjection w))≠0 :=
    (hreg w hwC 0).1.1
  let R := codingRadius k χ ε δ (complexProjection w)/2
  have hR : 0<R := half_pos (codingRadius_pos k χ ε hδ _)
  let a := (4*fineScale k ε δ)/(100*R)
  have hscale := fineScale_pos k ε hδ
  have ha : 0≤a := by dsimp only [a]; positivity
  let r := 1/(24*(1+a))
  have hr : 0<r := by dsimp only [r]; positivity
  have hrsmall : r≤1/12 := by
    dsimp only [r]
    apply (div_le_iff₀ (by positivity : 0<24*(1+a))).mpr
    nlinarith
  have hsize : (4*fineScale k ε δ*r)/(100*R)+r≤1 := by
    have he : (4*fineScale k ε δ*r)/(100*R)+r=r*(1+a) := by dsimp only [a]; ring
    rw [he]
    dsimp only [r]
    have : 1+a≠0 := by positivity
    field_simp
    norm_num
  have hdc : Continuous (fun v : C => orbitChartData k χ ε (complexProjection v)) :=
    continuousOn_iff_continuous_domRestrict.mp hdata
  have hdata0 : Continuous (fun v : C => lyapunovChartData k χ ε (complexProjection v)) := by
    change Continuous (fun v : C => (orbitChartData k χ ε (complexProjection v) 0).1)
    exact ((continuous_apply 0).comp hdc).fst
  have hF : ContinuousOn (fun v => fineFrame k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineFrame_of_data k χ ε δ _ hdata0)
  have hI : ContinuousOn (fun v => fineInverse k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineInverse_of_data k χ ε δ hδ _ hdata0)
  have hrad : ContinuousOn (fun v => codingRadius k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_const.mul (hdata0.snd.snd.pow 2))
  have hIF : (fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection w))=
      ContinuousLinearMap.id ℝ Plane := by
    apply ContinuousLinearMap.ext
    intro p
    exact fineInverse_frame k χ ε hδ _ hwreg p
  have hclose : ∀ᶠ v in 𝓝[C] w, ‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖<1/4 := by
    have hc : ContinuousWithinAt (fun v : ℂ => ‖(fineInverse k χ ε δ (complexProjection w)).comp
        (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖) C w :=
      ((continuousOn_const.clm_comp hF).sub continuousOn_const).norm w hwC
    apply hc.eventually (p := fun y : ℝ => y<1/4)
    dsimp only
    rw [hIF,sub_self,norm_zero]
    exact eventually_lt_nhds (by norm_num)
  have hclose' : ∀ᶠ v in 𝓝[C] w, ‖(fineInverse k χ ε δ (complexProjection v)).comp
      (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖<1/4 := by
    have hc : ContinuousWithinAt (fun v : ℂ => ‖(fineInverse k χ ε δ (complexProjection v)).comp
        (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖) C w :=
      ((hI.clm_comp continuousOn_const).sub continuousOn_const).norm w hwC
    apply hc.eventually (p := fun y : ℝ => y<1/4)
    dsimp only
    rw [hIF,sub_self,norm_zero]
    exact eventually_lt_nhds (by norm_num)
  have hRlower : ∀ᶠ v in 𝓝[C] w, R<codingRadius k χ ε δ (complexProjection v) := by
    apply (hrad w hwC).eventually
    exact eventually_gt_nhds (by dsimp only [R]; linarith [codingRadius_pos k χ ε hδ (complexProjection w)])
  have hcentre : ∀ᶠ v in 𝓝[C] w, |(fineInverse k χ ε δ (complexProjection w) (v-w)).1|<r/4 := by
    have hc : Continuous (fun v : ℂ => |(fineInverse k χ ε δ (complexProjection w) (v-w)).1|) :=
      (continuous_fst.comp ((fineInverse k χ ε δ (complexProjection w)).continuous.comp
        (continuous_id.sub continuous_const))).abs
    have hc' : Tendsto (fun v : ℂ => |(fineInverse k χ ε δ (complexProjection w) (v-w)).1|) (𝓝[C] w) (𝓝 0) := by
      simpa only [ContinuousWithinAt,sub_self,map_zero,Prod.fst_zero,abs_zero] using hc.continuousWithinAt (s := C) (x := w)
    exact hc'.eventually (eventually_lt_nhds (show (0 : ℝ)<r/4 by positivity))
  obtain ⟨K,hKC,hK,hKpos,hKP⟩ := hw
    (fun v => R<codingRadius k χ ε δ (complexProjection v) ∧
      ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
        ContinuousLinearMap.id ℝ Plane‖<1/4 ∧
      ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))-
        ContinuousLinearMap.id ℝ Plane‖<1/4 ∧
      |(fineInverse k χ ε δ (complexProjection w) (v-w)).1|<r/4)
    (hRlower.and (hclose.and (hclose'.and hcentre)))
  exact ⟨{
    carrier := K, compact := hK, positive := hKpos, centre := w, centre_regular := hwreg,
    r := r, r_pos := hr, r_small := hrsmall, R := R, R_pos := hR,
    radius_lower := fun v hv => (hKP v hv).1.le, size := hsize,
    data := hdata.mono hKC, regular := fun v hv => hreg v (hKC hv),
    frame_close := fun v hv => (hKP v hv).2.1.le,
    coframe_close := fun v hv => (hKP v hv).2.2.1.le,
    centre_close := fun v hv => (hKP v hv).2.2.2.le },hKC⟩

theorem exists_smallPesinBlock (k : ℝ) (hk : 0≤k) {χ ε δ : ℝ}
    (hχ : 0<χ) (hε : 0<ε) (hδ : 0<δ) (hgap : 0<area (spectralGapRegion k hk χ)) :
    Nonempty (SmallPesinBlock k χ ε δ) := by
  obtain ⟨C,hC,hCpos,_,hdata,hreg⟩ := compact_lift_fineRegular_block k hk hχ hε hgap
  obtain ⟨B,_⟩ := smallPesinBlock_within k χ ε δ hδ hC hCpos hdata hreg
  exact ⟨B⟩

end StandardMapEntropy

end
end

end OAI
