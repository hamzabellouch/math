import OAI.Geometry.KahlerSplitting.BoundaryExtension

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold
open Set Metric Filter Topology

namespace UniversalCoverSplitting

def superPotential (m : ℕ) (z : ℂ × ℂ) : ℝ :=
  Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m

def superDomain (m : ℕ) (a : ℝ) : Set (ℂ × ℂ) := {z | superPotential m z < a}

lemma normSq_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k Complex.normSq := by
  change ContDiff ℝ k (fun z : ℂ ↦ z.re*z.re+z.im*z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

lemma superPotential_contDiff (m : ℕ) {k : WithTop ℕ∞} : ContDiff ℝ k (superPotential m) :=
  ((normSq_contDiff.comp contDiff_fst).pow m).add ((normSq_contDiff.comp contDiff_snd).pow m)

lemma superPotential_nonneg (m : ℕ) (z : ℂ × ℂ) : 0 ≤ superPotential m z := by
  exact add_nonneg (pow_nonneg (Complex.normSq_nonneg _) _) (pow_nonneg (Complex.normSq_nonneg _) _)

lemma superDomain_open (m : ℕ) (a : ℝ) : IsOpen (superDomain m a) :=
  isOpen_lt (superPotential_contDiff m (k := 0)).continuous continuous_const

lemma superPotential_convex (m : ℕ) : ConvexOn ℝ univ (superPotential m) := by
  have h : ConvexOn ℝ (univ : Set ℂ) (fun z : ℂ ↦ ‖z‖^(2*m)) :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) _
  have h₁ := h.comp_linearMap (LinearMap.fst ℝ ℂ ℂ)
  have h₂ := h.comp_linearMap (LinearMap.snd ℝ ℂ ℂ)
  have hh := h₁.add h₂
  change ConvexOn ℝ univ (fun z : ℂ × ℂ ↦ ‖z.1‖^(2*m)+‖z.2‖^(2*m)) at hh
  change ConvexOn ℝ univ (fun z : ℂ × ℂ ↦ Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m)
  simpa only [Complex.normSq_eq_norm_sq,pow_mul] using hh

lemma superDomain_convex (m : ℕ) (a : ℝ) : Convex ℝ (superDomain m a) := by
  have h := (superPotential_convex m).convex_lt a
  simp only [mem_univ,true_and] at h
  exact h

lemma superPotential_zero {m : ℕ} (hm : 0 < m) : superPotential m 0 = 0 := by
  simp [superPotential,zero_pow hm.ne']

lemma superDomain_zero {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) : (0:ℂ × ℂ) ∈ superDomain m a := by
  simpa only [superDomain,mem_ofPred_eq,superPotential_zero hm] using ha

lemma superPotential_smul (m : ℕ) (t : ℝ) (z : ℂ × ℂ) :
    superPotential m (t • z) = t^(2*m) * superPotential m z := by
  simp only [superPotential,Prod.smul_fst,Prod.smul_snd,Complex.real_smul,Complex.normSq_mul,Complex.normSq_ofReal,
    mul_pow,pow_mul,mul_add]
  ring

lemma superDomain_mono (m : ℕ) {a b : ℝ} (hab : a ≤ b) : superDomain m a ⊆ superDomain m b :=
  fun _ h ↦ h.trans_le hab

lemma superDomain_subset_bidisk {m : ℕ} (_hm : 0 < m) {a : ℝ} (ha : a ≤ 1) :
    superDomain m a ⊆ ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
  intro z hz
  have h₁ : Complex.normSq z.1 ^ m < 1 := lt_of_lt_of_le (lt_of_le_of_lt (le_add_of_nonneg_right
    (pow_nonneg (Complex.normSq_nonneg z.2) m)) hz) ha
  have h₂ : Complex.normSq z.2 ^ m < 1 := lt_of_lt_of_le (lt_of_le_of_lt (le_add_of_nonneg_left
    (pow_nonneg (Complex.normSq_nonneg z.1) m)) hz) ha
  have hnorm : ∀ w : ℂ, Complex.normSq w ^ m < 1 → w ∈ ball (0:ℂ) 1 := by
    intro w hw
    rw [mem_ball,dist_zero_right]
    by_contra hh
    have hn : 1 ≤ ‖w‖ := le_of_not_gt hh
    have hn₂ : 1 ≤ Complex.normSq w := by rw [Complex.normSq_eq_norm_sq]; nlinarith
    exact not_lt_of_ge (one_le_pow₀ hn₂) hw
  exact ⟨hnorm z.1 h₁,hnorm z.2 h₂⟩

lemma normSq_hasFDerivAt (z : ℂ) : HasFDerivAt Complex.normSq
    ((2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM) z := by
  convert! ((Complex.reCLM.hasFDerivAt.pow 2).add (Complex.imCLM.hasFDerivAt.pow 2)) using 1
  · ext x; simp [Complex.normSq_apply,pow_two]
  · simp [two_smul,two_mul]

lemma normSq_fderiv_apply (z w : ℂ) :
    fderiv ℝ Complex.normSq z w = 2*(z.re*w.re+z.im*w.im) := by
  rw [(normSq_hasFDerivAt z).fderiv]
  simp only [add_apply,smul_apply,Complex.reCLM_apply,
    Complex.imCLM_apply,smul_eq_mul]
  ring

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma normSqPow_fderiv_mul {m : ℕ} (hm : 0 < m) (p w : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ Complex.normSq z ^ m) p (p*w) =
      (2*m*Complex.normSq p^m)*w.re := by
  rw [((normSq_hasFDerivAt p).pow m).fderiv]
  simp only [smul_apply,smul_eq_mul,nsmul_eq_mul,add_apply,Complex.reCLM_apply,
    Complex.imCLM_apply,Complex.mul_re,Complex.mul_im]
  have hp : Complex.normSq p^(m-1)*Complex.normSq p = Complex.normSq p^m := by
    rw [← pow_succ,Nat.sub_add_cancel hm]
  rw [← hp,Complex.normSq_apply]
  ring

def superSource (m : ℕ) (p : ℂ × ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  (p.1*(1+q.1+(Complex.normSq p.2^m:ℝ)*q.2),
    p.2*(1+q.1-(Complex.normSq p.1^m:ℝ)*q.2))

lemma superSource_zero (m : ℕ) (p : ℂ × ℂ) : superSource m p 0 = p := by simp [superSource]

lemma superSource_contDiff (m : ℕ) (p : ℂ × ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (superSource m p) := by
  change ContDiff ℝ k (fun q : ℂ × ℂ ↦
    (p.1*(1+q.1+(Complex.normSq p.2^m:ℝ)*q.2),p.2*(1+q.1-(Complex.normSq p.1^m:ℝ)*q.2)))
  fun_prop

lemma superSource_hasFDerivAt (m : ℕ) (p q : ℂ × ℂ) :
    HasFDerivAt (superSource m p)
      ((p.1 • (ContinuousLinearMap.fst ℂ ℂ ℂ + (Complex.normSq p.2^m:ℝ) • ContinuousLinearMap.snd ℂ ℂ ℂ)).prod
       (p.2 • (ContinuousLinearMap.fst ℂ ℂ ℂ - (Complex.normSq p.1^m:ℝ) • ContinuousLinearMap.snd ℂ ℂ ℂ))) q := by
  exact (((hasFDerivAt_fst.const_add 1).add (hasFDerivAt_snd.const_mul _)).const_mul _).prodMk
    (((hasFDerivAt_fst.const_add 1).sub (hasFDerivAt_snd.const_mul _)).const_mul _)

lemma superSource_fderiv (m : ℕ) (p q h : ℂ × ℂ) :
    fderiv ℝ (superSource m p) q h =
      (p.1*(h.1+(Complex.normSq p.2^m:ℝ)*h.2),p.2*(h.1-(Complex.normSq p.1^m:ℝ)*h.2)) := by
  rw [((superSource_hasFDerivAt m p q).restrictScalars ℝ).fderiv]
  rfl

lemma superPotential_fderiv_mul {m : ℕ} (hm : 0 < m) (p w : ℂ × ℂ) :
    fderiv ℝ (superPotential m) p (p.1*w.1,p.2*w.2) =
      2*m*(Complex.normSq p.1^m*w.1.re+Complex.normSq p.2^m*w.2.re) := by
  have h₁ := ((normSq_hasFDerivAt p.1).pow m).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h₂ := ((normSq_hasFDerivAt p.2).pow m).comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hD : HasFDerivAt (superPotential m) _ p := h₁.add h₂
  rw [hD.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply]
  rw [← ((normSq_hasFDerivAt p.1).pow m).fderiv,← ((normSq_hasFDerivAt p.2).pow m).fderiv]
  change (fderiv ℝ (fun z : ℂ ↦ Complex.normSq z^m) p.1) (p.1*w.1) +
    (fderiv ℝ (fun z : ℂ ↦ Complex.normSq z^m) p.2) (p.2*w.2) = _
  rw [normSqPow_fderiv_mul hm,normSqPow_fderiv_mul hm]
  ring

lemma superPotential_superSource_fderiv {m : ℕ} (hm : 0 < m) (p : ℂ × ℂ)
    (x : ℝ) (v : ℂ) :
    fderiv ℝ ((superPotential m) ∘ superSource m p) 0 ((x:ℂ),v) =
      (2*m*superPotential m p)*x := by
  rw [fderiv_comp _ ((superPotential_contDiff m (k := 1)).differentiable (by norm_num) _)
    ((superSource_contDiff m p (k := 1)).differentiable (by norm_num) _)]
  rw [ContinuousLinearMap.comp_apply,superSource_fderiv,superSource_zero]
  rw [superPotential_fderiv_mul hm p (
    (x:ℂ)+(Complex.normSq p.2^m:ℝ)*v,(x:ℂ)-(Complex.normSq p.1^m:ℝ)*v)]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,superPotential]
  ring

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem superDomain_mixed_boundary [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {m : ℕ} (hm : 0 < m)
    {a : ℝ} (ha : 0 < a) {f : ℂ × ℂ → X.Carrier} (hf : IsBox S (superDomain m a) f)
    {p : ℂ × ℂ} (hp : superPotential m p = a) (hp₁ : p.1 ≠ 0) (hp₂ : p.2 ≠ 0) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ superDomain m a) := by
  let A : ℝ := Complex.normSq p.1^m
  let B : ℝ := Complex.normSq p.2^m
  have hA : 0 < A := pow_pos (Complex.normSq_pos.mpr hp₁) _
  have hB : 0 < B := pow_pos (Complex.normSq_pos.mpr hp₂) _
  have hAc : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hBc : (B:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  let b : ℂ × ℂ := ((B:ℂ)*p.1,-(A:ℂ)*p.2)
  let c : ℂ × ℂ := ((B⁻¹:ℝ),(-A⁻¹:ℝ))
  have hb₁ : b.1 ≠ 0 := mul_ne_zero hBc hp₁
  have hb₂ : b.2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hAc) hp₂
  have hc : c.1 ≠ c.2 := by
    intro h
    have hh := congrArg Complex.re h
    change B⁻¹ = -A⁻¹ at hh
    linarith [inv_pos.mpr hA,inv_pos.mpr hB]
  have heq : (mixedSource p b c hb₁ hb₂ hc : ℂ × ℂ → ℂ × ℂ) = superSource m p := by
    funext q
    change (p.1+(B:ℂ)*p.1*(q.2+(B⁻¹:ℝ)*q.1),
      p.2+(-(A:ℂ)*p.2)*(q.2+(-A⁻¹:ℝ)*q.1)) =
      (p.1*(1+q.1+(B:ℂ)*q.2),p.2*(1+q.1-(A:ℂ)*q.2))
    ext <;> push_cast <;> field_simp <;> ring
  let ρ : ℂ × ℂ → ℝ := fun z ↦ superPotential m (superSource m p z)-a
  have hρ : ContDiff ℝ 2 ρ := ((superPotential_contDiff m).comp (superSource_contDiff m p)).sub contDiff_const
  have hρ0 : ρ 0 = 0 := by simp [ρ,superSource_zero,hp]
  have hD : ∀ (x : ℝ) (v : ℂ), fderiv ℝ ρ 0 ((x:ℂ),v) = (2*m*a)*x := by
    intro x v
    have hh : DifferentiableAt ℝ ((superPotential m) ∘ superSource m p) 0 :=
      (((superPotential_contDiff m (k := 1)).comp (superSource_contDiff m p)).differentiable (by norm_num)) 0
    have h : HasFDerivAt ρ (fderiv ℝ ((superPotential m) ∘ superSource m p) 0) 0 := hh.hasFDerivAt.sub_const a
    rw [h.fderiv]
    simpa only [hp] using superPotential_superSource_fderiv hm p x v
  apply affine_mixed_boundary_extension g h₁ h₂ (superDomain_open m a) (superDomain_convex m a) hf
    p b c hb₁ hb₂ hc hρ.contDiffAt hρ0 (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hm)) ha)
    (show (0:ℝ)<1 by norm_num) hD
  intro z _ hz
  rw [heq]
  exact sub_neg.mp hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def IsHorizontalCurve (S : HolomorphicSplitting X r s) (U : Set ℂ) (f : ℂ → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f U ∧ ∀ z ∈ U,
    S.projection (f z) (mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ)) = mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ)

def IsVerticalCurve (S : HolomorphicSplitting X r s) (U : Set ℂ) (f : ℂ → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f U ∧ ∀ z ∈ U,
    S.projection (f z) (mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ)) = 0

lemma IsHorizontalCurve.mono {U V : Set ℂ} {f : ℂ → X.Carrier}
    (hf : IsHorizontalCurve S U f) (hV : V ⊆ U) : IsHorizontalCurve S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

lemma IsVerticalCurve.mono {U V : Set ℂ} {f : ℂ → X.Carrier}
    (hf : IsVerticalCurve S U f) (hV : V ⊆ U) : IsVerticalCurve S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

lemma SplittingChart.horizontal_coordinate_constant (e : SplittingChart S) {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) {f : ℂ → X.Carrier}
    (hf : IsHorizontalCurve S U f) (he : MapsTo f U e.chart.source)
    {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) : (e.chart (f u)).2 = (e.chart (f v)).2 := by
  have hd (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun z ↦ (e.chart (f z)).2) 0 z := by
    have h := mfderiv_comp z (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz)))
      (hf.1.mdifferentiableAt (hU.mem_nhds hz))
    have hh : DifferentiableAt ℂ (e.chart ∘ f) z := mdifferentiableAt_iff_differentiableAt.mp
      ((e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz))).comp z
        (hf.1.mdifferentiableAt (hU.mem_nhds hz)))
    have ht := (e.horizontal _ (he hz) _).mp (hf.2 z hz)
    have hh' := hh.hasFDerivAt.snd.hasDerivAt
    change HasDerivAt (fun z ↦ (e.chart (f z)).2) ((fderiv ℂ (e.chart ∘ f) z (1:ℂ)).2) z at hh'
    simp only [mfderiv_eq_fderiv] at h
    have hz0 : (fderiv ℂ (e.chart ∘ f) z (1:ℂ)).2 = 0 := by rw [h]; exact ht
    rwa [hz0] at hh'
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hd z hz).deriv) hu hv

lemma SplittingChart.vertical_coordinate_constant (e : SplittingChart S) {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) {f : ℂ → X.Carrier}
    (hf : IsVerticalCurve S U f) (he : MapsTo f U e.chart.source)
    {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) : (e.chart (f u)).1 = (e.chart (f v)).1 := by
  have hd (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun z ↦ (e.chart (f z)).1) 0 z := by
    have h := mfderiv_comp z (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz)))
      (hf.1.mdifferentiableAt (hU.mem_nhds hz))
    have hh : DifferentiableAt ℂ (e.chart ∘ f) z := mdifferentiableAt_iff_differentiableAt.mp
      ((e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz))).comp z
        (hf.1.mdifferentiableAt (hU.mem_nhds hz)))
    have ht := (e.vertical _ (he hz) _).mp (hf.2 z hz)
    have hh' := hh.hasFDerivAt.fst.hasDerivAt
    change HasDerivAt (fun z ↦ (e.chart (f z)).1) ((fderiv ℂ (e.chart ∘ f) z (1:ℂ)).1) z at hh'
    simp only [mfderiv_eq_fderiv] at h
    have hz0 : (fderiv ℂ (e.chart ∘ f) z (1:ℂ)).1 = 0 := by rw [h]; exact ht
    rwa [hz0] at hh'
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hd z hz).deriv) hu hv

lemma SplittingChart.mix_curves (e : SplittingChart S) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {α β : ℂ → X.Carrier}
    (hα : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) α U)
    (hβ : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) β V)
    (hαe : MapsTo α U e.chart.source) (hβe : MapsTo β V e.chart.source) :
    IsBox S (U ×ˢ V) (fun z ↦ e.chart.symm ((e.chart (α z.1)).1,(e.chart (β z.2)).2)) := by
  let A := e.chart ∘ α
  let B := e.chart ∘ β
  have hA : DifferentiableOn ℂ A U := mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hα hαe)
  have hB : DifferentiableOn ℂ B V := mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hβ hβe)
  let G : ℂ × ℂ → Model r × Model s := fun z ↦ ((A z.1).1,(B z.2).2)
  have hd (z : ℂ × ℂ) (hz : z ∈ U ×ˢ V) :
      HasFDerivAt G ((((ContinuousLinearMap.fst ℂ (Model r) (Model s)).comp (fderiv ℂ A z.1)).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)).prod
        (((ContinuousLinearMap.snd ℂ (Model r) (Model s)).comp (fderiv ℂ B z.2)).comp (ContinuousLinearMap.snd ℂ ℂ ℂ))) z := by
    exact ((hA.differentiableAt (hU.mem_nhds hz.1)).hasFDerivAt.fst.comp z hasFDerivAt_fst).prodMk
      ((hB.differentiableAt (hV.mem_nhds hz.2)).hasFDerivAt.snd.comp z hasFDerivAt_snd)
  apply e.box_of_coordinate_tangencies (hU.prod hV) (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
  · intro z hz
    have ha := e.chart.map_source (hαe hz.1)
    have hb := e.chart.map_source (hβe hz.2)
    rw [e.product_range] at ha hb ⊢
    exact ⟨ha.1,hb.2⟩
  · intro z hz
    rw [(hd z hz).fderiv]
    simp

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

section Separation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
lemma separated_eq_axes {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    {f : ℂ × ℂ → E × F} (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (ht : ∀ z ∈ U ×ˢ V, (fderiv ℂ f z (1,0)).2 = 0 ∧ (fderiv ℂ f z (0,1)).1 = 0)
    {u u₀ v v₀ : ℂ} (hu : u ∈ U) (hu₀ : u₀ ∈ U) (hv : v ∈ V) (hv₀ : v₀ ∈ V) :
    f (u,v) = ((f (u,v₀)).1,(f (u₀,v)).2) := by
  have h₁ (z : ℂ) (hz : z ∈ V) : HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hV).mem_nhds (show (u,z) ∈ U ×ˢ V from ⟨hu,hz⟩))).hasFDerivAt
    have hh := hd.fst.comp_hasDerivAt z ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))
    change HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) ((fderiv ℂ f (u,z) (0,1)).1) z at hh
    rwa [(ht (u,z) ⟨hu,hz⟩).2] at hh
  have h₂ (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hV).mem_nhds (show (z,v) ∈ U ×ˢ V from ⟨hz,hv⟩))).hasFDerivAt
    have hh := hd.snd.comp_hasDerivAt z ((hasDerivAt_id z).prodMk (hasDerivAt_const z v))
    change HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) ((fderiv ℂ f (z,v) (1,0)).2) z at hh
    rwa [(ht (z,v) ⟨hz,hv⟩).1] at hh
  exact Prod.ext (hV.is_const_of_deriv_eq_zero hVc
      (fun z hz ↦ (h₁ z hz).differentiableAt.differentiableWithinAt) (fun z hz ↦ (h₁ z hz).deriv) hv hv₀)
    (hU.is_const_of_deriv_eq_zero hUc
      (fun z hz ↦ (h₂ z hz).differentiableAt.differentiableWithinAt) (fun z hz ↦ (h₂ z hz).deriv) hu hu₀)
end Separation

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma SplittingChart.mix_curves_axes (e : SplittingChart S) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S U α) (hβ : IsVerticalCurve S V β)
    (hαe : MapsTo α U e.chart.source) (hβe : MapsTo β V e.chart.source)
    {u₀ v₀ : ℂ} (hu₀ : u₀ ∈ U) (hv₀ : v₀ ∈ V) (hbase : α u₀ = β v₀) :
    (∀ u ∈ U, e.chart.symm ((e.chart (α u)).1,(e.chart (β v₀)).2) = α u) ∧
    (∀ v ∈ V, e.chart.symm ((e.chart (α u₀)).1,(e.chart (β v)).2) = β v) := by
  constructor
  · intro u hu
    rw [← hbase,← e.horizontal_coordinate_constant hU hUc hα hαe hu hu₀]
    exact e.chart.left_inv (hαe hu)
  · intro v hv
    rw [hbase,← e.vertical_coordinate_constant hV hVc hβ hβe hv hv₀]
    exact e.chart.left_inv (hβe hv)

lemma exists_axis_box_germ (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {u₀ v₀ : ℂ} (hu₀ : u₀ ∈ U) (hv₀ : v₀ ∈ V)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S U α) (hβ : IsVerticalCurve S V β)
    (hbase : α u₀ = β v₀) :
    ∃ d : ℝ, 0 < d ∧ ball u₀ d ⊆ U ∧ ball v₀ d ⊆ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S (ball u₀ d ×ˢ ball v₀ d) F ∧
        (∀ u ∈ ball u₀ d, F (u,v₀) = α u) ∧ (∀ v ∈ ball v₀ d, F (u₀,v) = β v) := by
  obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (α u₀)
  have hαn := (hα.1.continuousOn.continuousAt (hU.mem_nhds hu₀)) (e.chart.open_source.mem_nhds he)
  have hβn := (hβ.1.continuousOn.continuousAt (hV.mem_nhds hv₀))
    (e.chart.open_source.mem_nhds (hbase ▸ he))
  obtain ⟨a,ha,haU⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hu₀) hαn)
  obtain ⟨b,hb,hbV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hv₀) hβn)
  let d := min a b
  have hd : 0 < d := lt_min ha hb
  have hdU : ball u₀ d ⊆ U := fun _ hz ↦ (haU ((ball_subset_ball (min_le_left _ _)) hz)).1
  have hdV : ball v₀ d ⊆ V := fun _ hz ↦ (hbV ((ball_subset_ball (min_le_right _ _)) hz)).1
  have hdae : MapsTo α (ball u₀ d) e.chart.source := fun _ hz ↦ (haU ((ball_subset_ball (min_le_left _ _)) hz)).2
  have hdbe : MapsTo β (ball v₀ d) e.chart.source := fun _ hz ↦ (hbV ((ball_subset_ball (min_le_right _ _)) hz)).2
  refine ⟨d,hd,hdU,hdV,_,e.mix_curves isOpen_ball isOpen_ball (hα.1.mono hdU) (hβ.1.mono hdV) hdae hdbe,?_⟩
  exact e.mix_curves_axes isOpen_ball isOpen_ball (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected
    (hα.mono hdU) (hβ.mono hdV) hdae hdbe (mem_ball_self hd) (mem_ball_self hd) hbase

lemma IsBox.horizontal_slice {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) {D : Set ℂ} (v : ℂ) (hmap : ∀ z ∈ D, (z,v) ∈ U) :
    IsHorizontalCurve S D (fun z ↦ f (z,v)) := by
  have hd (z : ℂ) : HasFDerivAt (fun z : ℂ ↦ (z,v))
      ((ContinuousLinearMap.id ℂ ℂ).prod (0:ℂ →L[ℂ] ℂ)) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const v z)
  refine ⟨hf.1.comp (fun z _ ↦ (hd z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt) hmap,?_⟩
  intro z hz
  have hh := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap z hz))) (hd z).differentiableAt.mdifferentiableAt
  simp only [mfderiv_eq_fderiv,(hd z).fderiv] at hh
  change S.projection (f (z,v)) ((mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (z,v)) z) (1:ℂ)) = _
  have he : (mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (z,v)) z : ℂ →L[ℂ] Model n) (1:ℂ) =
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (z,v) : (ℂ × ℂ) →L[ℂ] Model n) (1,0) :=
    congrArg (fun D : ℂ →L[ℂ] Model n ↦ D (1:ℂ)) hh
  rw [he]
  exact (hf.2 (z,v) (hmap z hz)).1

lemma IsBox.vertical_slice {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) {D : Set ℂ} (u : ℂ) (hmap : ∀ z ∈ D, (u,z) ∈ U) :
    IsVerticalCurve S D (fun z ↦ f (u,z)) := by
  have hd (z : ℂ) : HasFDerivAt (fun z : ℂ ↦ (u,z))
      ((0:ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) z :=
    (hasFDerivAt_const u z).prodMk (hasFDerivAt_id z)
  refine ⟨hf.1.comp (fun z _ ↦ (hd z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt) hmap,?_⟩
  intro z hz
  have hh := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap z hz))) (hd z).differentiableAt.mdifferentiableAt
  simp only [mfderiv_eq_fderiv,(hd z).fderiv] at hh
  change S.projection (f (u,z)) ((mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (u,z)) z) (1:ℂ)) = 0
  have he : (mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (u,z)) z : ℂ →L[ℂ] Model n) (1:ℂ) =
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (u,z) : (ℂ × ℂ) →L[ℂ] Model n) (0,1) :=
    congrArg (fun D : ℂ →L[ℂ] Model n ↦ D (1:ℂ)) hh
  rw [he]
  exact (hf.2 (u,z) (hmap z hz)).2

end UniversalCoverSplitting

end

end OAI
