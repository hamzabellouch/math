import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Holonomy.DerivativeQuantitative

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineStableGraph (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) : ℝ → ℝ :=
  (fineLocalRecurrence k χ ε δ hδ w hw).extend.graph hq
noncomputable def fineStableCurve (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) : ℝ → ℂ :=
  fun s => w+fineFrame k χ ε δ (complexProjection w) (s,fineStableGraph k χ ε δ hδ hq w hw s)
@[simp] lemma fineStableCurve_zero (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    fineStableCurve k χ ε δ hδ hq w hw 0=w := by
  have hz := NonlinearStable.graph_zero (fineLocalRecurrence k χ ε δ hδ w hw).extend hq
  dsimp only [fineStableCurve,fineStableGraph]
  rw [hz,Prod.mk_zero_zero,map_zero,add_zero]

lemma fineStableCurve_orbit (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw s)=(standardLift k)^[n] w+
      fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s n) := by
  induction n with
  | zero =>
    have hi : (fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s 0=
        (s,fineStableGraph k χ ε δ hδ hq w hw s) := Prod.ext (solution_initial _ _ s) rfl
    simp only [Function.iterate_zero,id_eq,hi,fineStableCurve]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,fine_lift_step k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n)]
    rw [local_solution_orbit _ hq hs n]
    simp only [Function.iterate_succ_apply',complexProjection_standardLift,fineLocalRecurrence,LocalRecurrence.step]

lemma fineStableCoordinate (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n=
      (fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s n := by
  dsimp only [fineCoordinate]
  rw [fineStableCurve_orbit k χ ε δ hδ hq w hw hs n,add_sub_cancel_left,
    fineInverse_frame k χ ε hδ _ (hw n).1]

lemma fineStableCurve_contraction (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw s)-
      (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw t)‖≤
      (2*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n*|s-t| := by
  rw [fineStableCurve_orbit k χ ε δ hδ hq w hw hs,fineStableCurve_orbit k χ ε δ hδ hq w hw ht,
    add_sub_add_left_eq_sub,←map_sub]
  have hn : ‖fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤2*fineScale k ε δ :=
    (fineFrame_norm_le k χ ε hδ _).trans (mul_le_mul_of_nonneg_left (fineSize_le_scale k χ ε hδ _) (by norm_num))
  have hx := solution_exponential_contraction (fineLocalRecurrence k χ ε δ hδ w hw).extend hq s t n
  exact ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hn hx (norm_nonneg _)
    (by linarith [fineScale_pos k ε hδ]))).trans_eq (by
      change (2*fineScale k ε δ)*((Real.exp (-χ+ε)+δ)^n*|s-t|)=_; ring)

lemma fineStableGraph_contDiffOn (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    ContDiffOn ℝ 1 (fineStableGraph k χ ε δ hδ hq w hw) (Ioo (-1 : ℝ) 1) := by
  apply graph_contDiffOn (fineLocalRecurrence k χ ε δ hδ w hw) hq
    (fun n => fineRemainderDerivative k χ ε δ ((standardLift k)^[n] w))
    (fun n v hv => fineRemainderDerivative_bound k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) hv) hδ.le
  · intro n v u _ _
    exact fineRemainder_taylor k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) v u
  · intro n v u _ _
    exact fineRemainderDerivative_lipschitz k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) v u
lemma fineStableCurve_contDiffOn (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    ContDiffOn ℝ 1 (fineStableCurve k χ ε δ hδ hq w hw) (Ioo (-1 : ℝ) 1) :=
  contDiffOn_const.add ((fineFrame k χ ε δ (complexProjection w)).contDiff.comp_contDiffOn
    (contDiffOn_id.prodMk (fineStableGraph_contDiffOn k χ ε δ hδ hq w hw)))

theorem fineStableCurve_unique (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w p : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (hp : ∀ n : ℕ, ‖fineCoordinate k χ ε δ w p n‖≤1) :
    p=fineStableCurve k χ ε δ hδ hq w hw (fineCoordinate k χ ε δ w p 0).1 := by
  let x : Sequence := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fineCoordinate k χ ε δ w p) 1 hp
  have hx : x=(fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq (x 0).1 := by
    apply solution_unique
    · rfl
    · intro n
      change fineCoordinate k χ ε δ w p (n+1)=
        (fineLocalRecurrence k χ ε δ hδ w hw).extend.step n (fineCoordinate k χ ε δ w p n)
      rw [extend_step_eq _ n (hp n),fineCoordinate_step]
  have hi := congrArg (fun u : Sequence => u 0) hx
  have he : x 0=((x 0).1,fineStableGraph k χ ε δ hδ hq w hw (x 0).1) := by
    exact hi.trans (Prod.ext (solution_initial _ hq _) rfl)
  have he' := congrArg (fun v => w+fineFrame k χ ε δ (complexProjection w) v) he
  change w+fineFrame k χ ε δ (complexProjection w)
    (fineInverse k χ ε δ (complexProjection w) (p-w))=_ at he'
  have hw0 : FineRegular k χ ε (complexProjection w) := hw 0
  rw [fineFrame_inverse k χ ε hδ _ hw0.1] at he'
  have hx0 : x 0=fineCoordinate k χ ε δ w p 0 := rfl
  rw [hx0] at he'
  dsimp only [fineStableCurve]
  simpa only [add_sub_cancel] using he'

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma slow_sequence_ratio {a : ℕ → ℝ} {b : ℝ} (hb : 0≤b)
    (h : ∀ n : ℕ, a n≤b*a (n+1)) (n : ℕ) : a 0≤b^n*a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply ih.trans
    exact (mul_le_mul_of_nonneg_left (h n) (pow_nonneg hb n)).trans_eq (by rw [pow_succ]; ring)

lemma fineInverse_forward_radius_bound (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
      codingRadius k χ ε δ (complexProjection w)≤(Real.exp (2*ε))^n/100 := by
  have hstep (j : ℕ) : codingRadius k χ ε δ (complexProjection ((standardLift k)^[j] w))≤
      Real.exp (2*ε)*codingRadius k χ ε δ (complexProjection ((standardLift k)^[j+1] w)) := by
    simpa only [Function.iterate_succ_apply',complexProjection_standardLift] using
      (codingRadius_ratio k χ ε hδ _ (hw j)).1
  have hr := slow_sequence_ratio (Real.exp_pos (2*ε)).le hstep n
  calc
    _ ≤ ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        ((Real.exp (2*ε))^n*codingRadius k χ ε δ (complexProjection ((standardLift k)^[n] w))) :=
      mul_le_mul_of_nonneg_left hr (norm_nonneg _)
    _ = (Real.exp (2*ε))^n*(‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        codingRadius k χ ε δ (complexProjection ((standardLift k)^[n] w))) := by ring
    _ ≤ (Real.exp (2*ε))^n*(1/100) :=
      mul_le_mul_of_nonneg_left (fineInverse_codingRadius k χ ε hδ _ (hw n)) (by positivity)
    _ = _ := by ring

lemma fineCoordinate_tracking_difference (k χ ε δ : ℝ) (hδ : 0<δ) (w p p' : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {D r : ℝ} (hD : 0≤D) (hr : 0≤r) (hslow : Real.exp (2*ε)*r≤1)
    (htrack : ∀ n : ℕ, ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖≤D*r^n) (n : ℕ) :
    ‖fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n‖≤
      D/(100*codingRadius k χ ε δ (complexProjection w)) := by
  let R := codingRadius k χ ε δ (complexProjection w)
  have hR : 0<R := codingRadius_pos k χ ε hδ _
  have hI := fineInverse_forward_radius_bound k χ ε δ hδ w hw n
  have hI' : ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤
      (Real.exp (2*ε))^n/(100*R) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hR)).mpr
    dsimp [R] at ⊢
    nlinarith
  have hpow : (Real.exp (2*ε)*r)^n≤1 := pow_le_one₀ (mul_nonneg (Real.exp_pos _).le hr) hslow
  have he : fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n=
      fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((standardLift k)^[n] p-(standardLift k)^[n] p') := by
    dsimp only [fineCoordinate]
    rw [←map_sub,sub_sub_sub_cancel_right]
  rw [he]
  calc
    _ ≤ ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((Real.exp (2*ε))^n/(100*R))*(D*r^n) := mul_le_mul hI' (htrack n) (norm_nonneg _) (by positivity)
    _ = (D/(100*R))*(Real.exp (2*ε)*r)^n := by rw [mul_pow]; ring
    _ ≤ (D/(100*R))*1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_one _

lemma fineStableCoordinate_bound (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    ‖fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n‖≤|s| := by
  rw [fineStableCoordinate k χ ε δ hδ hq w hw hs n]
  exact ((fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s).norm_coe_le_norm n |>.trans
    (solution_norm_bound _ hq s)

theorem fineStablePlaque_overlap (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)≤1)
    (w v : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    {s t : ℝ} (hs : |s|<1) (ht : |t|<1)
    (he : fineStableCurve k χ ε δ hδ hq w hw s=fineStableCurve k χ ε δ hδ hq v hv t) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ u : ℝ, |u-t|<ρ → |u|<1 ∧ ∃ a : ℝ, |a|<1 ∧
      fineStableCurve k χ ε δ hδ hq v hv u=fineStableCurve k χ ε δ hδ hq w hw a := by
  have hη := fineScale_pos k ε hδ
  let C := (2*fineScale k ε δ)/(100*codingRadius k χ ε δ (complexProjection w))
  have hC : 0<C := div_pos (mul_pos (by norm_num) (fineScale_pos k ε hδ))
    (mul_pos (by norm_num) (codingRadius_pos k χ ε hδ _))
  let ρ := min ((1-|t|)/2) ((1-|s|)/(2*(C+1)))
  have hρ : 0<ρ := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  refine ⟨ρ,hρ,fun u hu => ?_⟩
  have hu' : |u|<1 := by
    have ha := abs_add_le (u-t) t
    rw [sub_add_cancel] at ha
    have hb := hu.trans_le (min_le_left _ _)
    linarith
  have hCd : C*|u-t|<1-|s| := by
    have hh := hu.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (by linarith : 0<2*(C+1))).mp hh
    nlinarith [abs_nonneg (u-t)]
  have htrack (n : ℕ) :
      ‖(standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq v hv u)-
        (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq v hv t)‖≤
      ((2*fineScale k ε δ)*|u-t|)*(Real.exp (-χ+ε)+δ)^n := by
    exact (fineStableCurve_contraction k χ ε δ hδ hq v hv hu'.le ht.le n).trans_eq (by ring)
  have hd (n : ℕ) :
      ‖fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq v hv u) n-
        fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n‖≤C*|u-t| := by
    rw [he]
    exact (fineCoordinate_tracking_difference k χ ε δ hδ w _ _ hw
      (by positivity : 0≤(2*fineScale k ε δ)*|u-t|)
      (by positivity : 0≤Real.exp (-χ+ε)+δ) hslow htrack n).trans_eq (by dsimp [C]; ring)
  have hb (n : ℕ) : ‖fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq v hv u) n‖<1 := by
    have hh := norm_add_le
      (fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq v hv u) n-
        fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n)
      (fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n)
    rw [sub_add_cancel] at hh
    have hm := fineStableCoordinate_bound k χ ε δ hδ hq w hw hs.le n
    linarith [hd n]
  refine ⟨hu', (fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq v hv u) 0).1,?_,?_⟩
  · exact (norm_fst_le _).trans_lt (hb 0)
  · exact fineStableCurve_unique k χ ε δ hδ hq w _ hw (fun n => (hb n).le)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma measurable_compact_continuity_block {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {A : Set X} (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : r<μ A) :
    ∃ K : Set X, K⊆A ∧ IsCompact K ∧ ContinuousOn f K ∧ r<μ K := by
  let g : X → X×Y := fun x => (x,f x)
  have hg : Measurable g := measurable_id.prodMk hf
  let G : Set (X×Y) := {p | p.1∈A ∧ p.2=f p.1}
  have hG : MeasurableSet G :=
    (hA.preimage measurable_fst).inter (measurableSet_eq_fun measurable_snd (hf.comp measurable_fst))
  have hpre : g ⁻¹' G=A := by ext x; simp [g,G]
  have hmass : μ.map g G=μ A := by rw [Measure.map_apply hg hG,hpre]
  obtain ⟨C,hCG,hC,hCr⟩ := hG.exists_lt_isCompact (μ := μ.map g) (r := r) (by simpa only [hmass] using hr)
  let K : Set X := Prod.fst '' C
  have hK : IsCompact K := hC.image continuous_fst
  have hKA : K⊆A := by rintro x ⟨p,hp,rfl⟩; exact (hCG hp).1
  have hCK : g ⁻¹' C=K := by
    ext x
    constructor
    · intro hx; exact ⟨g x,hx,rfl⟩
    · rintro ⟨p,hp,hpx⟩
      have he : g x=p := by
        apply Prod.ext
        · exact hpx.symm
        · change f x=p.2; rw [←hpx]; exact (hCG hp).2.symm
      simpa only [mem_preimage,he] using hp
  have hmeasure : μ.map g C=μ K := by rw [Measure.map_apply hg hC.measurableSet,hCK]
  refine ⟨K,hKA,hK,?_,by rwa [←hmeasure]⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let q : C → K := fun p => ⟨p.1.1,⟨p.1,p.2,rfl⟩⟩
  have hq : Continuous q := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨x,p,hp,hpx⟩
    refine ⟨⟨p,hp⟩,?_⟩
    exact Subtype.ext hpx
  have hquot := IsQuotientMap.of_surjective_continuous hqs hq
  rw [continuousOn_iff_continuous_domRestrict]
  apply hquot.continuous_iff.mpr
  have he : (fun x : K => f x) ∘ q=(fun p : C => p.1.2) := by
    funext p
    exact (hCG p.2).2.symm
  change Continuous ((fun x : K => f x) ∘ q)
  rw [he]
  exact continuous_snd.comp continuous_subtype_val

abbrev LyapunovChartData := (ℂ →L[ℝ] ℂ) × (ℂ →L[ℝ] ℂ) × ℝ
noncomputable def lyapunovChartData (k χ ε : ℝ) (z : Torus) : LyapunovChartData :=
  (lyapunovFrame k χ z,lyapunovCoframe k χ z,chartRadius k χ ε z)
noncomputable def orbitChartData (k χ ε : ℝ) (z : Torus) : ℕ → LyapunovChartData × LyapunovChartData :=
  fun n => (lyapunovChartData k χ ε ((standardMap k)^[n] z),
    lyapunovChartData k χ ε ((inverseMap k)^[n] z))
lemma measurable_lyapunovChartData (k χ ε : ℝ) : Measurable (lyapunovChartData k χ ε) :=
  (measurable_lyapunovFrame k χ).prodMk
    ((measurable_lyapunovCoframe k χ).prodMk (measurable_chartRadius k χ ε))
lemma measurable_orbitChartData (k χ ε : ℝ) : Measurable (orbitChartData k χ ε) :=
  Measurable.of_eval fun n =>
    ((measurable_lyapunovChartData k χ ε).comp ((measurePreserving_standardMap k).measurable.iterate n)).prodMk
      ((measurable_lyapunovChartData k χ ε).comp ((measurePreserving_inverseMap k).measurable.iterate n))

theorem compact_fineRegular_block (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε)
    {r : ℝ≥0∞} (hr : r<area (spectralGapRegion k hk χ)) :
    ∃ K : Set Torus, K⊆spectralGapRegion k hk χ ∧ IsCompact K ∧ r<area K ∧
      ContinuousOn (orbitChartData k χ ε) K ∧
      ∀ z∈K, ∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧
        FineRegular k χ ε ((inverseMap k)^[n] z) := by
  obtain ⟨B,hBae,hB,hBG⟩ := IsMeasurablyGenerated.exists_measurable_subset
    (ae_fineRegular_all_iterates k hk hχ hε)
  have hgap := measurableSet_spectralGapRegion k hk χ
  have hfull : (B∩spectralGapRegion k hk χ : Set Torus) =ᵐ[area] spectralGapRegion k hk χ := by
    filter_upwards [(ae_restrict_iff' hgap).mp hBae] with z hz
    apply propext
    change (z∈B ∧ z∈spectralGapRegion k hk χ) ↔ z∈spectralGapRegion k hk χ
    exact ⟨And.right,fun h => ⟨hz h,h⟩⟩
  have hm : area (B∩spectralGapRegion k hk χ)=area (spectralGapRegion k hk χ) := measure_congr hfull
  let : PolishSpace LyapunovChartData := inferInstance
  let : PolishSpace (LyapunovChartData × LyapunovChartData) := by constructor
  let : TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → LyapunovChartData × LyapunovChartData) :=
    @TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable ℕ _
      (fun _ => LyapunovChartData × LyapunovChartData) _ (fun _ => inferInstance)
  let : PolishSpace (ℕ → LyapunovChartData × LyapunovChartData) :=
    { toSecondCountableTopology := inferInstance, toIsCompletelyMetrizableSpace := inferInstance }
  let : BorelSpace LyapunovChartData := inferInstance
  let : BorelSpace (LyapunovChartData × LyapunovChartData) := inferInstance
  obtain ⟨K,hKA,hK,hcont,hKr⟩ := measurable_compact_continuity_block area
    (measurable_orbitChartData k χ ε) (hB.inter hgap) (r := r) (by rwa [hm])
  exact ⟨K,fun z hz => (hKA hz).2,hK,hKr,hcont,fun z hz => hBG (hKA hz).1⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def Recurrence.perronApprox (r : Recurrence ℓ δ) (s : ℝ) : ℕ → ℕ → Plane
  | 0, _ => 0
  | N+1, n =>
    ((match n with | 0 => s | m+1 => r.a m*(r.perronApprox s N m).1+(r.remainder m (r.perronApprox s N m)).1),
      (r.b n)⁻¹*((r.perronApprox s N (n+1)).2-(r.remainder n (r.perronApprox s N n)).2))
lemma perronApprox_eq_iterate (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (N n : ℕ) :
    r.perronApprox s N n=((r.perron hℓ s)^[N] 0) n := by
  induction N generalizing n with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    simp only [Recurrence.perronApprox,perron_apply,Recurrence.perronValue,ih]; rfl

lemma perronApprox_error (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (N n : ℕ) :
    ‖r.perronApprox s N n-r.solution h s n‖≤((ℓ+δ : ℝ≥0) : ℝ)^N*|s| := by
  let hℓ : ℓ≤1 := le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le
  have hc := (perron_contracting r h (s := s)).2.iterate N
  have he : (r.perron hℓ s)^[N] (r.solution h s)=r.solution h s :=
    by
      clear hc
      induction N with
      | zero => rfl
      | succ N ih => rw [Function.iterate_succ_apply',ih,solution_fixed]
  have hb := hc.dist_le_mul 0 (r.solution h s)
  rw [he,dist_zero_left,dist_eq_norm,NNReal.coe_pow] at hb
  rw [perronApprox_eq_iterate r hℓ]
  apply (point_sub_bound _ _ n).trans
  exact hb.trans (mul_le_mul_of_nonneg_left (solution_norm_bound r h s) (by positivity))

lemma continuous_perronApprox {X : Type*} [TopologicalSpace X] (r : X → Recurrence ℓ δ)
    (hA : ∀ n, Continuous (fun x => (r x).a n))
    (hB : ∀ n, Continuous (fun x => ((r x).b n)⁻¹))
    (hR : ∀ n, Continuous (fun p : X×Plane => (r p.1).remainder n p.2)) (N n : ℕ) :
    Continuous (fun p : X×ℝ => (r p.1).perronApprox p.2 N n) := by
  induction N generalizing n with
  | zero => exact continuous_const
  | succ N ih =>
    have hm (j : ℕ) : Continuous (fun p : X×ℝ => (r p.1).remainder j ((r p.1).perronApprox p.2 N j)) :=
      (hR j).comp (continuous_fst.prodMk (ih j))
    apply Continuous.prodMk
    · cases n with
      | zero => exact continuous_snd
      | succ m => exact ((hA m).comp continuous_fst |>.mul (ih m).fst).add (hm m).fst
    · exact ((hB n).comp continuous_fst).mul ((ih (n+1)).snd.sub (hm n).snd)

theorem continuous_solution_eval_on_strip {X : Type*} [TopologicalSpace X]
    (r : X → Recurrence ℓ δ) (h : ℓ+δ<1)
    (hA : ∀ n, Continuous (fun x => (r x).a n))
    (hB : ∀ n, Continuous (fun x => ((r x).b n)⁻¹))
    (hR : ∀ n, Continuous (fun p : X×Plane => (r p.1).remainder n p.2)) (n : ℕ) :
    Continuous (fun p : X×Icc (-1 : ℝ) 1 => (r p.1).solution h p.2 n) := by
  let f (N : ℕ) (p : X×Icc (-1 : ℝ) 1) := (r p.1).perronApprox p.2 N n
  have hf (N : ℕ) : Continuous (f N) :=
    (continuous_perronApprox r hA hB hR N n).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hq0 : 0≤((ℓ+δ : ℝ≥0) : ℝ) := (ℓ+δ).coe_nonneg
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  have ht : TendstoUniformly f (fun p : X×Icc (-1 : ℝ) 1 => (r p.1).solution h p.2 n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hpow.eventually (gt_mem_nhds hε)] with N hN
    intro p
    have hs : |(p.2 : ℝ)|≤1 := abs_le.mpr p.2.2
    have he := (perronApprox_error (r p.1) h (p.2 : ℝ) N n).trans
      ((mul_le_mul_of_nonneg_left hs (pow_nonneg hq0 N)).trans_eq (mul_one _))
    change ‖(r p.1).solution h (p.2 : ℝ) n-(r p.1).perronApprox (p.2 : ℝ) N n‖<ε
    rw [norm_sub_rev]
    exact he.trans_lt hN
  exact ht.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall hf))

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma continuous_complexProjection : Continuous complexProjection :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_im)
lemma continuous_liftRemainder (k : ℝ) : Continuous (fun p : ℂ × ℂ => liftRemainder k p.1 p.2) :=
  (((contDiff_standardLift k).continuous.comp (continuous_fst.add continuous_snd)).sub
    ((contDiff_standardLift k).continuous.comp continuous_fst)).sub
    (((continuous_standardDerivative k).comp (continuous_complexProjection.comp continuous_fst)).clm_apply continuous_snd)

lemma continuous_fineFrame_of_data {X : Type*} [TopologicalSpace X] (k χ ε δ : ℝ)
    (z : X → Torus) (h : Continuous (fun x => lyapunovChartData k χ ε (z x))) :
    Continuous (fun x => fineFrame k χ ε δ (z x)) :=
  ((continuous_const.mul h.snd.snd).smul h.fst).clm_comp continuous_const
lemma continuous_fineInverse_of_data {X : Type*} [TopologicalSpace X] (k χ ε δ : ℝ) (hδ : 0<δ)
    (z : X → Torus) (h : Continuous (fun x => lyapunovChartData k χ ε (z x))) :
    Continuous (fun x => fineInverse k χ ε δ (z x)) :=
  continuous_const.clm_comp (((continuous_const.mul h.snd.snd).inv₀
    (fun x => (fineSize_pos k χ ε hδ (z x)).ne')).smul h.snd.fst)

theorem continuous_fineStableCurve_family {X : Type*} [TopologicalSpace X]
    (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : X → ℂ) (hwc : Continuous w)
    (hw : ∀ x, ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (w x))))
    (hdata : ∀ n : ℕ, Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (w x))))) :
    Continuous (fun p : X×Icc (-1 : ℝ) 1 => fineStableCurve k χ ε δ hδ hq (w p.1) (hw p.1) p.2) := by
  let z (n : ℕ) (x : X) := complexProjection ((standardLift k)^[n] (w x))
  have hzc (n : ℕ) : Continuous (z n) :=
    continuous_complexProjection.comp (((contDiff_standardLift k).continuous.iterate n).comp hwc)
  have hF (n : ℕ) : Continuous (fun x => fineFrame k χ ε δ (z n x)) :=
    continuous_fineFrame_of_data k χ ε δ _ (hdata n)
  have hI (n : ℕ) : Continuous (fun x => fineInverse k χ ε δ (z n x)) :=
    continuous_fineInverse_of_data k χ ε δ hδ _ (hdata n)
  have hNext (n : ℕ) : Continuous (fun x => fineInverse k χ ε δ (standardMap k (z n x))) := by
    simpa only [z,Function.iterate_succ_apply',complexProjection_standardLift] using hI (n+1)
  have hDc (n : ℕ) : Continuous (fun x => standardDerivative k (z n x)) :=
    (continuous_standardDerivative k).comp (hzc n)
  have hA (n : ℕ) : Continuous (fun x => fineStableMultiplier k χ ε δ (z n x)) := by
    have hc := ((hNext n).clm_apply ((hDc n).clm_apply ((hF n).clm_apply
      (continuous_const : Continuous (fun _ : X => ((1,0) : RealPlane)))))).fst
    have he : (fun x => (fineInverse k χ ε δ (standardMap k (z n x))
        (standardDerivative k (z n x) (fineFrame k χ ε δ (z n x) (1,0)))).1)=
        (fun x => fineStableMultiplier k χ ε δ (z n x)) := by
      funext x
      simpa only [mul_one] using congrArg Prod.fst (fine_derivative_diagonal k χ ε δ (z n x) (hw x n) (1,0))
    rwa [he] at hc
  have hB (n : ℕ) : Continuous (fun x => (fineUnstableMultiplier k χ ε δ (z n x))⁻¹) := by
    have hc := ((hNext n).clm_apply ((hDc n).clm_apply ((hF n).clm_apply
      (continuous_const : Continuous (fun _ : X => ((0,1) : RealPlane)))))).snd
    have he : (fun x => (fineInverse k χ ε δ (standardMap k (z n x))
        (standardDerivative k (z n x) (fineFrame k χ ε δ (z n x) (0,1)))).2)=
        (fun x => fineUnstableMultiplier k χ ε δ (z n x)) := by
      funext x
      simpa only [mul_one] using congrArg Prod.snd (fine_derivative_diagonal k χ ε δ (z n x) (hw x n) (0,1))
    rw [he] at hc
    exact hc.inv₀ (fun x => fineUnstableMultiplier_ne k χ ε hδ _ (hw x n))
  have hR (n : ℕ) : Continuous (fun p : X×RealPlane => fineRemainder k χ ε δ
      ((standardLift k)^[n] (w p.1)) p.2) := by
    have hW : Continuous (fun x : X => (standardLift k)^[n] (w x)) :=
      ((contDiff_standardLift k).continuous.iterate n).comp hwc
    exact ((hNext n).comp continuous_fst).clm_apply ((continuous_liftRemainder k).comp
      ((hW.comp continuous_fst).prodMk (((hF n).comp continuous_fst).clm_apply continuous_snd)))
  let r (x : X) := (fineLocalRecurrence k χ ε δ hδ (w x) (hw x)).extend
  have hR' (n : ℕ) : Continuous (fun p : X×Plane => (r p.1).remainder n p.2) :=
    (hR n).comp (continuous_fst.prodMk (planeClip_lipschitz.continuous.comp continuous_snd))
  have hs := continuous_solution_eval_on_strip r hq hA hB hR' 0
  have hFrame : Continuous (fun p : X×Icc (-1 : ℝ) 1 => fineFrame k χ ε δ (complexProjection (w p.1))) :=
    (hF 0).comp continuous_fst
  exact (hwc.comp continuous_fst).add (hFrame.clm_apply
    ((continuous_subtype_val.comp continuous_snd).prodMk hs.snd))

end StandardMapEntropy

end
end

end OAI
