import OAI.Geometry.IsometricImmersion.Curvature.CurvatureParameter

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def intervalExtensionEvalCLM (r : ℝ) (hr : 0 < r) (x : ℝ) :
    IntervalFunctions r →L[ℝ] ℝ :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.evalCLM ℝ (ContinuousMap.projIccCM (a := -r) (b := r) x)

theorem intervalExtensionEvalCLM_apply (r : ℝ) (hr : 0 < r)
    (x : ℝ) (h : IntervalFunctions r) :
    intervalExtensionEvalCLM r hr x h = intervalExtension r hr h x := rfl

theorem intervalExtension_mul (r : ℝ) (hr : 0 < r)
    (h k : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (h * k) x =
      intervalExtension r hr h x * intervalExtension r hr k x := rfl

theorem intervalExtension_family_continuousOn (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} {F : ℝ → IntervalFunctions r} (hF : ContinuousOn F s) :
    ContinuousOn (fun p : ℝ × ℝ => intervalExtension r hr (F p.2) p.1)
      (univ ×ˢ s) := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  have hext : ContinuousOn (fun y => intervalExtension r hr (F y)) s :=
    ContinuousMap.IccExtendCM.continuous.comp_continuousOn hF
  exact (hext.comp continuous_snd.continuousOn (fun _ hp => hp.2)).eval
    continuous_fst.continuousOn

theorem intervalExtension_family_hasDerivAt (r : ℝ) (hr : 0 < r)
    {F : ℝ → IntervalFunctions r} {F' : IntervalFunctions r} {y : ℝ}
    (hF : HasDerivAt F F' y) (x : ℝ) :
    HasDerivAt (fun t => intervalExtension r hr (F t) x)
      (intervalExtension r hr F' x) y := by
  exact (intervalExtensionEvalCLM r hr x).hasFDerivAt.comp_hasDerivAt y hF

theorem intervalExtension_primitive_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun t => intervalExtension r hr (primitiveCLM r hr h) t)
      (intervalExtension r hr h x) x := by
  apply (primitiveFunction_hasDerivAt r hr h x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [intervalExtension_apply_of_mem r hr _ ⟨ht.1.le, ht.2.le⟩]
  rfl

def volterraScalar (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) (x : ℝ) : ℝ :=
  intervalExtension r hr (volterraSolution r hr k) x

def volterraVelocity (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) (x : ℝ) : ℝ :=
  -primitiveFunction r hr (k * volterraSolution r hr k) x

theorem volterraScalar_hasDerivAt (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000)
    {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (volterraScalar r hr k) (volterraVelocity r hr k x) x := by
  let g := k * volterraSolution r hr k
  have hd := (primitiveFunction_hasDerivAt r hr (primitiveCLM r hr g) x).const_sub 1
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩] at hd
  change HasDerivAt (fun t => 1 - primitiveFunction r hr (primitiveCLM r hr g) t)
    (volterraVelocity r hr k x) x at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  have htc : t ∈ Icc (-r) r := ⟨ht.1.le, ht.2.le⟩
  have he := congrArg (fun h : IntervalFunctions r => h ⟨t, htc⟩)
    (volterraSolution_equation r hr hr1 k hk)
  change volterraSolution r hr k ⟨t, htc⟩ +
    primitiveFunction r hr (primitiveCLM r hr g) t = 1 at he
  unfold volterraScalar
  rw [intervalExtension_apply_of_mem r hr _ htc]
  linarith

theorem volterraVelocity_hasDerivAt (r : ℝ) (hr : 0 < r)
    (k : IntervalFunctions r) (x : ℝ) :
    HasDerivAt (volterraVelocity r hr k)
      (-intervalExtension r hr k x * volterraScalar r hr k x) x := by
  change HasDerivAt (fun t => -primitiveFunction r hr (k * volterraSolution r hr k) t)
    (-intervalExtension r hr k x * intervalExtension r hr (volterraSolution r hr k) x) x
  simpa only [Pi.neg_def, intervalExtension_mul, neg_mul] using
    (primitiveFunction_hasDerivAt r hr (k * volterraSolution r hr k) x).neg

theorem volterraScalar_initial (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    volterraScalar r hr k 0 = 1 := by
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have he := congrArg (fun h : IntervalFunctions r => h ⟨0, hz⟩)
    (volterraSolution_equation r hr hr1 k hk)
  change volterraSolution r hr k ⟨0, hz⟩ +
    primitiveFunction r hr (primitiveCLM r hr (k * volterraSolution r hr k)) 0 = 1 at he
  simpa [volterraScalar, intervalExtension_apply_of_mem r hr _ hz, primitiveFunction] using he

theorem volterraVelocity_initial (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) :
    volterraVelocity r hr k 0 = 0 := by
  simp [volterraVelocity, primitiveFunction]

theorem prescribedVolterraScalar_continuousOn
    {K : SmoothLocal.Geometry.Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K SmoothLocal.Geometry.square)
    (hbound : ∀ p ∈ SmoothLocal.Geometry.square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ContinuousOn (fun p : ℝ × ℝ =>
      intervalExtension r hr (prescribedVolterraFamily K r hr p.2) p.1)
      (univ ×ˢ Ioo (-1 : ℝ) 1) :=
  intervalExtension_family_continuousOn r hr
    (prescribedVolterraFamily_contDiffOn hK hbound r hr hr1).continuousOn

end SmoothLocal.ODE

end

end OAI
