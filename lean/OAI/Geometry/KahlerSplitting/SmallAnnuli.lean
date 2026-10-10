import OAI.Geometry.KahlerSplitting.ShellFilling

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.toMixed {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (hV : MapsTo (mixedEquiv c hc) V U) :
    IsMixedBox (S := S) c hc V (f ∘ mixedEquiv c hc) := by
  have he : (f ∘ mixedEquiv c hc) ∘ (mixedEquiv c hc).symm = f := by
    funext q
    exact congrArg f ((mixedEquiv c hc).apply_symm_apply q)
  unfold IsMixedBox
  rw [he]
  exact hf.mono (image_subset_iff.mpr hV)

lemma IsMixedBox.comp_translation {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc U f) (p : ℂ × ℂ)
    (hp : MapsTo (fun q ↦ p+q) V U) :
    IsMixedBox (S := S) c hc V (fun q ↦ f (p+q)) := by
  let M := mixedEquiv c hc
  have hm : MapsTo (separatedAffine (M p) (1,1)) (M '' V) (M '' U) := by
    rintro z ⟨q,hq,rfl⟩
    refine ⟨p+q,hp hq,?_⟩
    simp only [map_add,separatedAffine,one_mul]
    rfl
  have h := IsBox.comp_separatedAffine (M.toHomeomorph.isOpenMap _ hU) hf (M p) (1,1) hm
  have he : (f ∘ M.symm) ∘ separatedAffine (M p) (1,1) = (fun q ↦ f (p+q)) ∘ M.symm := by
    funext z
    simp only [Function.comp_apply,separatedAffine,one_mul]
    change f (M.symm (M p+z)) = f (p+M.symm z)
    rw [map_add,M.symm_apply_apply]
  rw [he] at h
  exact h

lemma IsMixedBox.slice_holomorphic_on {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc U f) (w : ℂ) {D : Set ℂ}
    (hD : MapsTo (fun v ↦ (w,v)) D U) :
    MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun v ↦ f (w,v)) D :=
  hf.holomorphic.comp
    (fun z _ ↦ (hasFDerivAt_prodMk_right w z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt) hD

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma mixed_shift_in_annulus {l η : ℝ} (hl : 0 < l) {c w v : ℂ}
    (hc : ‖c‖*η ≤ 1/8) (hw : ‖w‖ < η*l)
    (hv : l < ‖v‖ ∧ ‖v‖ < 5*l/4) :
    3*l/4 < ‖v+c*w‖ ∧ ‖v+c*w‖ < 3*l/2 := by
  have hcw : ‖c*w‖ ≤ l/8 := by
    rw [norm_mul]
    calc
      ‖c‖*‖w‖ ≤ ‖c‖*(η*l) := mul_le_mul_of_nonneg_left hw.le (norm_nonneg _)
      _ = (‖c‖*η)*l := by ring
      _ ≤ (1/8)*l := mul_le_mul_of_nonneg_right hc hl.le
      _ = l/8 := by ring
  have hl : ‖v‖ ≤ ‖v+c*w‖+‖c*w‖ := by
    calc
      ‖v‖ = ‖(v+c*w)-(c*w)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hu := norm_add_le v (c*w)
  constructor <;> linarith [hv.1,hv.2]

theorem chart_annulus_mixed_extension [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    (e : SplittingChart S) {l η : ℝ} (hl : 0 < l) (hη : 0 < η)
    (hc₁ : ‖c.1‖*η ≤ 1/8) (hc₂ : ‖c.2‖*η ≤ 1/8)
    {H : ℂ → X.Carrier} (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (ball 0 (2*l)))
    (hmap : MapsTo H (complexAnnulus (3*l/4) (3*l/2)) e.chart.source) :
    ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball 0 (η*l) ×ˢ ball 0 (5*l/4)) F ∧
      ∀ v ∈ ball 0 (5*l/4), F (0,v) = H v := by
  let A := complexAnnulus (3*l/4) (3*l/2)
  have hAH : A ⊆ ball (0:ℂ) (2*l) := by
    intro v hv
    rw [mem_ball_zero_iff]
    linarith [hv.2]
  obtain ⟨hG,hGH⟩ := e.diagonal_box (isOpen_complexAnnulus _ _) (hH.mono hAH) hmap
  let G : ℂ × ℂ → X.Carrier := fun q ↦ e.chart.symm ((e.chart (H q.1)).1,(e.chart (H q.2)).2)
  let Fs := G ∘ mixedEquiv c hc
  have hs : IsMixedBox (S := S) c hc (ball 0 (η*l) ×ˢ complexAnnulus l (5*l/4)) Fs := by
    apply hG.toMixed
    intro q hq
    have hw : ‖q.1‖ < η*l := by simpa using hq.1
    exact ⟨mixed_shift_in_annulus hl hc₁ hw hq.2,mixed_shift_in_annulus hl hc₂ hw hq.2⟩
  have hHs : ∀ v ∈ complexAnnulus l (5*l/4), H v = Fs (0,v) := by
    intro v hv
    have hvA : v ∈ A := by constructor <;> linarith [hv.1,hv.2]
    simpa [Fs,G,mixedEquiv_apply] using (hGH v hvA).symm
  have hsmall : ball (0:ℂ) (5*l/4) ⊆ ball 0 (2*l) := ball_subset_ball (by linarith)
  obtain ⟨F,hF,hFs⟩ := mixed_shell_extension g h₁ h₂ isOpen_ball
    (convex_ball (0:ℂ) (η*l)).isPreconnected hl.le (by linarith : l < 5*l/4) hs
    (mem_ball_self (mul_pos hη hl)) (hH.mono hsmall) hHs
  refine ⟨F,hF,?_⟩
  obtain ⟨v,hv⟩ := complexAnnulus_nonempty hl.le (by linarith : l < 5*l/4)
  have he : (fun v ↦ F (0,v)) =ᶠ[𝓝 v] H := by
    filter_upwards [(isOpen_complexAnnulus l (5*l/4)).mem_nhds hv] with z hz
    exact (hFs ⟨mem_ball_self (mul_pos hη hl),hz⟩).trans (hHs z hz).symm
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq isOpen_ball
    (convex_ball (0:ℂ) (5*l/4)).isPreconnected
    (hF.slice_holomorphic (mem_ball_self (mul_pos hη hl))) (hH.mono hsmall)
    (complexAnnulus_subset_ball _ _ hv) he

end UniversalCoverSplitting

open Set Metric
namespace UniversalCoverSplitting

def annulusPath (z : ℂ) (t : ℝ) : ℂ :=
  ((1 + t * (‖z‖ - 1) : ℝ) : ℂ) * Complex.exp (((t * z.arg : ℝ) : ℂ) * Complex.I)

@[simp] theorem annulusPath_zero (z : ℂ) : annulusPath z 0 = 1 := by
  simp [annulusPath]

@[simp] theorem annulusPath_one (z : ℂ) : annulusPath z 1 = z := by
  simp [annulusPath, Complex.norm_mul_exp_arg_mul_I]

theorem annulusPath_norm {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖annulusPath z t‖ = 1 + t * (‖z‖ - 1) := by
  have ha : 0 ≤ 1 + t * (‖z‖ - 1) := by nlinarith [hz.1, ht.1, ht.2]
  simp only [annulusPath, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg ha]

theorem annulusPath_mem {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    3 / 4 ≤ ‖annulusPath z t‖ ∧ ‖annulusPath z t‖ ≤ 3 / 2 := by
  rw [annulusPath_norm hz ht]
  constructor <;> nlinarith [hz.1, hz.2, ht.1, ht.2]

theorem annulusPath_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (annulusPath z)
      ((((‖z‖ - 1 : ℝ) : ℂ) + ((1 + t * (‖z‖ - 1) : ℝ) : ℂ) *
        ((z.arg : ℂ) * Complex.I)) * Complex.exp (((t * z.arg : ℝ) : ℂ) * Complex.I)) t := by
  have h₁ := (((hasDerivAt_id t).mul_const (‖z‖ - 1)).const_add 1).ofReal_comp
  have h₂ := (((hasDerivAt_id t).mul_const z.arg).ofReal_comp.mul_const Complex.I).cexp
  exact (h₁.mul h₂).congr_deriv (by
    simp only [id_eq, one_mul]
    ring)

theorem annulusPath_deriv_bound {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖deriv (annulusPath z) t‖ ≤ 7 := by
  rw [(annulusPath_hasDerivAt z t).deriv, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have ha : 0 ≤ 1 + t * (‖z‖ - 1) := by nlinarith [hz.1, ht.1, ht.2]
  have hb : 1 + t * (‖z‖ - 1) ≤ 3 / 2 := by nlinarith [hz.2, ht.1, ht.2]
  have hc : |‖z‖ - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hz.1,hz.2]
  calc
    _ ≤ ‖((‖z‖ - 1 : ℝ) : ℂ)‖ +
        ‖((1 + t * (‖z‖ - 1) : ℝ) : ℂ) * ((z.arg : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = |‖z‖ - 1| + (1+t*(‖z‖-1)) * |z.arg| := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ 1 + (3/2) * Real.pi := by
      exact add_le_add hc (mul_le_mul hb (Complex.abs_arg_le_pi z) (abs_nonneg _) (by norm_num))
    _ ≤ 7 := by linarith [Real.pi_lt_four]

end UniversalCoverSplitting

open Set Metric
namespace UniversalCoverSplitting
section
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem chart_trapping_on_annulus (e : OpenPartialHomeomorph M E)
    {c : E} {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (he : closedBall c R ⊆ e.target) {h : ℂ → M}
    (hc : ContinuousOn h {z | 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2})
    (hzero : h 1 ∈ e.source ∧ dist (e (h 1)) c < R - 7 * L)
    (hder : ∀ z, 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2 →
      h z ∈ e.symm '' closedBall c R →
      DifferentiableAt ℂ (e ∘ h) z ∧ ‖fderiv ℂ (e ∘ h) z‖ ≤ L) :
    ∀ z, 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2 →
      h z ∈ e.source ∧ e (h z) ∈ ball c R := by
  intro z hz
  have hp : Continuous (annulusPath z) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (annulusPath_hasDerivAt z t).continuousAt)
  have hγ : ContinuousOn (h ∘ annulusPath z) (Icc 0 1) :=
    hc.comp hp.continuousOn (fun t ht ↦ annulusPath_mem hz ht)
  have hinit : (h ∘ annulusPath z) 0 ∈ e.source ∧
      dist (e ((h ∘ annulusPath z) 0)) c < R - (7 * L) * 1 := by
    simpa only [Function.comp_apply, annulusPath_zero, mul_one] using hzero
  have htrap := chart_trapping_on_interval e hR (mul_nonneg (by norm_num) hL)
    zero_le_one he hγ hinit (fun t ht hk ↦ ?_) 1 (by norm_num)
  · simpa only [Function.comp_apply, annulusPath_one] using htrap
  obtain ⟨hd,hb⟩ := hder (annulusPath z t) (annulusPath_mem hz ht) hk
  refine ⟨fderiv ℂ (e ∘ h) (annulusPath z t) (deriv (annulusPath z) t), ?_, ?_⟩
  · have hh := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (annulusPath_hasDerivAt z t |>.differentiableAt.hasDerivAt)
    exact hh.hasDerivWithinAt
  · calc
      _ ≤ ‖fderiv ℂ (e ∘ h) (annulusPath z t)‖ * ‖deriv (annulusPath z) t‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * 7 := mul_le_mul hb (annulusPath_deriv_bound hz ht) (norm_nonneg _) hL
      _ = 7 * L := mul_comm _ _

end
end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

def compactAnnulus : Set ℂ := {z | 3/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3/2}
def openAnnulus : Set ℂ := {z | 1/2 < ‖z‖ ∧ ‖z‖ < 2}

theorem isCompact_compactAnnulus : IsCompact compactAnnulus := by
  have he : compactAnnulus = closedBall (0 : ℂ) (3/2) ∩ {z | 3/4 ≤ ‖z‖} := by
    ext z; simp [compactAnnulus, and_comm]
  rw [he]
  exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)

theorem isOpen_openAnnulus : IsOpen openAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem compactAnnulus_subset_openAnnulus : compactAnnulus ⊆ openAnnulus := by
  intro z hz
  constructor <;> dsimp [compactAnnulus] at hz <;> linarith [hz.1,hz.2]

theorem exists_annulus_speed_trapping (g : KahlerMetric X) (c : X.Carrier)
    {U : Set X.Carrier} (hU : IsOpen U) (hcU : c ∈ U) :
    ∃ V ∈ 𝓝 c, ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h openAnnulus → h 1 ∈ V →
      (∀ z ∈ compactAnnulus, curveSpeed g h z < ε) → MapsTo h compactAnnulus U := by
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  have hN : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e c) :=
    (e.symm.isOpen_inter_preimage hU).mem_nhds ⟨e.map_source hc, by simpa only [mem_preimage,e.left_inv hc] using hcU⟩
  obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hN
  have he : closedBall (e c) R ⊆ e.target := fun z hz ↦ (hball hz).1
  obtain ⟨Cforward,Cback,hC,_,hcomp⟩ := g.exists_chart_speed_comparison c (isCompact_closedBall (e c) R) he
  let V := e.source ∩ e ⁻¹' ball (e c) (R/2)
  have hV : V ∈ 𝓝 c := (e.isOpen_inter_preimage isOpen_ball).mem_nhds
    ⟨hc, by simpa using half_pos hR⟩
  let ε := R / (28 * Cforward)
  have hε : 0 < ε := div_pos hR (by positivity)
  have hL : 7 * (Cforward * ε) = R/4 := by dsimp [ε]; field_simp; ring
  refine ⟨V,hV,ε,hε,?_⟩
  intro h hh hstart hspeed
  have htrap : ∀ z ∈ compactAnnulus, h z ∈ e.source ∧ e (h z) ∈ ball (e c) R := by
    apply chart_trapping_on_annulus e hR (mul_nonneg hC.le hε.le) he
      (hh.continuousOn.mono compactAnnulus_subset_openAnnulus)
    · refine ⟨hstart.1,?_⟩
      rw [hL]
      have hi : dist (e (h 1)) (e c) < R/2 := hstart.2
      linarith
    · intro z hz hk
      obtain ⟨w,hw,hwz⟩ := hk
      have hs : h z ∈ e.source := hwz ▸ e.map_target (he hw)
      have hw' : e (h z) ∈ closedBall (e c) R := by rw [← hwz,e.right_inv (he hw)]; exact hw
      have hhz := hh.mdifferentiableAt
        (isOpen_openAnnulus.mem_nhds (compactAnnulus_subset_openAnnulus hz))
      have he' : MDifferentiableAt (model n) (model n) e (h z) :=
        mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hs)
      refine ⟨(he'.comp z hhz).differentiableAt,?_⟩
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv ((extChartAt (model n) c) ∘ h) z‖ ≤ _
      rw [chart_deriv_curve hhz c hs]
      exact ((hcomp (h z) hs hw' (mfderiv 𝓘(ℂ, ℂ) (model n) h z (1 : ℂ))).1).trans
        (mul_le_mul_of_nonneg_left (hspeed z hz).le hC.le)
  intro z hz
  have hn := (hball (ball_subset_closedBall (htrap z hz).2)).2
  simpa only [mem_preimage,e.left_inv (htrap z hz).1] using hn

theorem exists_small_area_annulus_image_in_cover [CompactSpace X.Carrier]
    (g : KahlerMetric X) (U : X.Carrier → Set X.Carrier)
    (hU : ∀ c, IsOpen (U c)) (hcU : ∀ c, c ∈ U c) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h openAnnulus →
      curveArea g h openAnnulus < ENNReal.ofReal η →
      ∃ c, MapsTo h compactAnnulus (U c) := by
  classical
  choose V hV ε hε hb using fun c ↦ exists_annulus_speed_trapping g c (hU c) (hcU c)
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have covered (x : X.Carrier) : ∃ c ∈ s, x ∈ V c := by
    have hx : x ∈ ⋃ c ∈ s, V c := by rw [hs]; trivial
    simpa only [mem_iUnion,exists_prop] using hx
  by_cases hne : s.Nonempty
  · have heps : 0 < s.inf' hne ε := (Finset.lt_inf'_iff hne).mpr (fun c _ ↦ hε c)
    obtain ⟨η,hη,hbη⟩ := exists_small_area_speed_bound g isOpen_openAnnulus
      isCompact_compactAnnulus compactAnnulus_subset_openAnnulus heps
    refine ⟨η,hη,?_⟩
    intro h hh harea
    obtain ⟨c,hcs,hc⟩ := covered (h 1)
    refine ⟨c,hb c h hh hc (fun z hz ↦ (hbη h hh harea z hz).trans_le (s.inf'_le ε hcs))⟩
  · refine ⟨1,by norm_num,?_⟩
    intro h
    obtain ⟨c,hcs,_⟩ := covered (h 1)
    exact (hne ⟨c,hcs⟩).elim

end UniversalCoverSplitting

open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace UniversalCoverSplitting

def scaledAnnulus (r : ℝ) : Set ℂ := {z | r/2 < ‖z‖ ∧ ‖z‖ < 2*r}

lemma measurableSet_scaledAnnulus (r : ℝ) : MeasurableSet (scaledAnnulus r) :=
  ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet

lemma scaledAnnulus_disjoint {a b : ℝ} (ha : 0 < a) (hab : 5*a ≤ b) :
    Disjoint (scaledAnnulus a) (scaledAnnulus b) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have h₁ := hz.2
  have h₂ := hz'.1
  linarith

lemma geometric_annuli_pairwiseDisjoint {r : ℝ} (hr : 0 < r) :
    Pairwise fun i j : ℕ ↦ Disjoint (scaledAnnulus ((5:ℝ)^i*r))
      (scaledAnnulus ((5:ℝ)^j*r)) := by
  have H (i j : ℕ) (h : i < j) :
      Disjoint (scaledAnnulus ((5:ℝ)^i*r)) (scaledAnnulus ((5:ℝ)^j*r)) := by
    apply scaledAnnulus_disjoint (mul_pos (pow_pos (by norm_num) _) hr)
    have hj : i+1 ≤ j := h
    have hp : (5:ℝ)^(i+1) ≤ 5^j := pow_le_pow_right₀ (by norm_num) hj
    calc
      5*(5^i*r) = 5^(i+1)*r := by rw [pow_succ]; ring
      _ ≤ 5^j*r := mul_le_mul_of_nonneg_right hp hr.le
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact H i j h
  · exact (H j i h).symm

theorem exists_small_energy_annulus (q : ℂ → ℝ≥0∞) {D : Set ℂ}
    {N : ℕ} {r η : ℝ} {M : ℝ≥0∞}
    (hr : 0 < r)
    (hs : ∀ i < N, scaledAnnulus ((5:ℝ)^i*r) ⊆ D)
    (hbound : ∫⁻ z in D, q z ≤ M)
    (hlarge : M < N * ENNReal.ofReal η) :
    ∃ i < N, ∫⁻ z in scaledAnnulus ((5:ℝ)^i*r), q z < ENNReal.ofReal η := by
  classical
  by_contra! h
  have hpair : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun i ↦ scaledAnnulus ((5:ℝ)^i*r)) := by
    intro i hi j hj hij
    exact geometric_annuli_pairwiseDisjoint hr hij
  have hsum : ∑ i ∈ Finset.range N, ∫⁻ z in scaledAnnulus ((5:ℝ)^i*r), q z ≤ M := by
    rw [← lintegral_biUnion_finset hpair (fun i _ ↦ measurableSet_scaledAnnulus _) q]
    apply le_trans (lintegral_mono_set _) hbound
    intro z hz
    simp only [mem_iUnion,Finset.mem_range,exists_prop] at hz
    obtain ⟨i,hi,hzi⟩ := hz
    exact hs i hi hzi
  have hlow : N*ENNReal.ofReal η ≤ ∑ i ∈ Finset.range N,
      ∫⁻ z in scaledAnnulus ((5:ℝ)^i*r), q z := by
    calc
      N*ENNReal.ofReal η = ∑ i ∈ Finset.range N, ENNReal.ofReal η := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ h i (Finset.mem_range.mp hi))
  exact (not_lt_of_ge (hlow.trans hsum)) hlarge

theorem exists_number_of_annuli {M : ℝ≥0∞} (hM : M ≠ ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ M < N*ENNReal.ofReal η := by
  obtain ⟨N,hN⟩ := exists_nat_gt (M.toReal/η+1)
  have hNN : (0:ℝ) < N := lt_trans (by positivity : (0:ℝ) < M.toReal/η+1) hN
  refine ⟨N,Nat.cast_pos.mp hNN,?_⟩
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg N),← ENNReal.ofReal_toReal hM]
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hNN hη)).mpr
  have hR : M.toReal/η < (N:ℝ) := by linarith
  exact (div_lt_iff₀ hη).mp hR

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

lemma positive_smul_openAnnulus {l : ℝ} (hl : 0 < l) :
    (fun z : ℂ ↦ l • z) '' openAnnulus = scaledAnnulus l := by
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    change l/2 < ‖l • z‖ ∧ ‖l • z‖ < 2*l
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hl]
    constructor <;> nlinarith [hz.1,hz.2]
  · intro hv
    refine ⟨l⁻¹ • v,?_,?_⟩
    · change 1/2 < ‖l⁻¹ • v‖ ∧ ‖l⁻¹ • v‖ < 2
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hl)]
      have he : l⁻¹ * ‖v‖ = ‖v‖ / l := by ring
      rw [he]
      exact ⟨(lt_div_iff₀ hl).mpr (by linarith [hv.1]),
        (div_lt_iff₀ hl).mpr (by linarith [hv.2])⟩
    · dsimp only
      rw [smul_smul,mul_inv_cancel₀ hl.ne',one_smul]

lemma inv_smul_mem_compactAnnulus {l : ℝ} (hl : 0 < l) {v : ℂ}
    (hv : v ∈ complexAnnulus (3*l/4) (3*l/2)) : l⁻¹ • v ∈ compactAnnulus := by
  change 3/4 ≤ ‖l⁻¹ • v‖ ∧ ‖l⁻¹ • v‖ ≤ 3/2
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hl)]
  have he : l⁻¹ * ‖v‖ = ‖v‖ / l := by ring
  rw [he]
  exact ⟨(le_div_iff₀ hl).mpr (by linarith [hv.1]),
    (div_le_iff₀ hl).mpr (by linarith [hv.2])⟩

lemma curveArea_rescale_annulus (g : KahlerMetric X) {H : ℂ → X.Carrier}
    {l : ℝ} (hl : 0 < l) (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (scaledAnnulus l)) :
    curveArea g (fun z ↦ H (l • z)) openAnnulus = curveArea g H (scaledAnnulus l) := by
  have he : (fun z : ℂ ↦ (0:ℂ)+l • z) '' openAnnulus = scaledAnnulus l := by
    simpa only [zero_add] using positive_smul_openAnnulus hl
  have hAo : IsOpen (scaledAnnulus l) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have h := curveArea_positive_affine g openAnnulus isOpen_openAnnulus.measurableSet 0 hl
    (fun z hz ↦ hH.mdifferentiableAt (hAo.mem_nhds (he ▸ hz)))
  simpa only [zero_add,positive_smul_openAnnulus hl] using h

lemma scaled_slice_holomorphic {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)}
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f U) {x : ℂ} {l : ℝ}
    (hmap : MapsTo (fun z : ℂ ↦ (x,l • z)) openAnnulus U) :
    MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (x,l • z)) openAnnulus := by
  apply hf.comp _ hmap
  intro z _
  exact ((hasFDerivAt_const x z).prodMk ((hasFDerivAt_id z).const_smul l)).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt

end UniversalCoverSplitting

end

end OAI
