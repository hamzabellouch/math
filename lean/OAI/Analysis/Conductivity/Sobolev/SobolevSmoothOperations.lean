import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevChain
import OAI.Analysis.Conductivity.Variational.CrossingProfiles

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

structure SmoothLipZero where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) toFun
  at_zero : toFun 0=0
  bound : ℝ
  bound_nonneg : 0≤bound
  deriv_bound : ∀ r, ‖deriv toFun r‖≤bound

instance : CoeFun SmoothLipZero (fun _ => ℝ → ℝ) := ⟨SmoothLipZero.toFun⟩

namespace SmoothLipZero

lemma growth (F : SmoothLipZero) (r : ℝ) : ‖F r‖≤F.bound*‖r‖ := by
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => F.smooth.differentiable (by simp) x) (fun x _ => F.deriv_bound x)
    (mem_univ (0:ℝ)) (mem_univ r)
  simpa [F.at_zero] using hh

lemma derivative (F : SmoothLipZero) (r : ℝ) : HasDerivAt F (deriv F r) r :=
  (F.smooth.differentiable (by simp) r).hasDerivAt

def onLp (F : SmoothLipZero) : JetSpace → JetSpace :=
  sobolevChainLp F.smooth (smooth_deriv_infty F.smooth).continuous F.bound_nonneg F.growth F.deriv_bound

lemma onLp_continuous (F : SmoothLipZero) : Continuous F.onLp :=
  sobolevChainLp_continuous _ _ _ _ _

lemma onLp_ae (F : SmoothLipZero) (z : JetSpace) :
    F.onLp z =ᵐ[ballMeasure] fun x => jetSuperposition F (deriv F) (z x) :=
  sobolevChainLp_coe_ae _ _ _ _ _ _

lemma preserves_H1 (F : SmoothLipZero) {z : JetSpace} (hz : z∈H1Space) :
    F.onLp z∈H1Space :=
  sobolevChainLp_preserves_H1 _ _ F.derivative _ _ _ hz

lemma preserves_H10 (F : SmoothLipZero) {z : JetSpace} (hz : z∈zeroTraceAmbient) :
    F.onLp z∈zeroTraceAmbient :=
  sobolevChainLp_preserves_H10 _ _ F.derivative _ _ _ F.at_zero hz

def onH1 (F : SmoothLipZero) (u : H1) : H1 := ⟨F.onLp u.val,F.preserves_H1 u.property⟩

lemma onH1_continuous (F : SmoothLipZero) : Continuous F.onH1 :=
  (F.onLp_continuous.comp continuous_subtype_val).subtype_mk _

lemma onH1_value (F : SmoothLipZero) (u : H1) :
    (fun x => jetValue ((F.onH1 u).val x)) =ᵐ[ballMeasure] fun x => F (jetValue (u.val x)) :=
  sobolevChain_value _ _ F.derivative _ _ _ _

lemma onH1_gradient (F : SmoothLipZero) (u : H1) :
    weakGradient (F.onH1 u) =ᵐ[ballMeasure] fun x => deriv F (jetValue (u.val x)) • weakGradient u x :=
  sobolevChain_gradient _ _ F.derivative _ _ _ _

lemma fixes_of_eq (F : SmoothLipZero) {u : H1}
    (hv : ∀ᵐ x ∂ballMeasure, F (jetValue (u.val x))=jetValue (u.val x))
    (hd : ∀ᵐ x ∂ballMeasure, deriv F (jetValue (u.val x))=1) : F.onH1 u=u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [F.onLp_ae u.val,hv,hd] with x hx hv hd
  change F.onLp u.val x=u.val x
  rw [hx]
  unfold jetSuperposition
  rw [hv,hd,one_smul,←jetFiber_decomposition]

def ofCompact (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hc : HasCompactSupport g) (hg0 : g 0=0) : SmoothLipZero := by
  let he := hc.deriv.exists_bound_of_continuous (smooth_deriv_infty hg).continuous
  let C := Classical.choose he
  have hC : ∀ r, ‖deriv g r‖ ≤ C := Classical.choose_spec he
  exact ⟨g,hg,hg0,max 0 C,le_max_left _ _,fun r => (hC r).trans (le_max_right _ _)⟩

lemma ofCompact_apply (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hc : HasCompactSupport g) (hg0 : g 0=0) (r : ℝ) :
    ofCompact g hg hc hg0 r=g r := by
  rfl

end SmoothLipZero

def valueBump (M : ℝ) : ContDiffBump (0:ℝ) :=
  ⟨|M|+1,|M|+2,by positivity,by linarith⟩

def clippedValue (M r : ℝ) : ℝ := valueBump M r*r

lemma clippedValue_smooth (M : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (clippedValue M) :=
  (valueBump M).contDiff.mul contDiff_id

lemma clippedValue_compact (M : ℝ) : HasCompactSupport (clippedValue M) :=
  (valueBump M).hasCompactSupport.mul_right

lemma clippedValue_zero (M : ℝ) : clippedValue M 0=0 := by simp [clippedValue]

lemma clippedValue_eventually {M r : ℝ} (hr : |r|≤M) : clippedValue M =ᶠ[𝓝 r] id := by
  have hb : r ∈ Metric.ball 0 (valueBump M).rIn := by
    change dist r 0 < |M|+1
    rw [dist_zero_right,Real.norm_eq_abs]
    linarith [le_abs_self M]
  filter_upwards [(valueBump M).eventuallyEq_one_of_mem_ball hb] with s hs
  simp only [clippedValue,hs,Pi.one_apply,one_mul,id_eq]

lemma clippedValue_eq {M r : ℝ} (hr : |r|≤M) : clippedValue M r=r :=
  (clippedValue_eventually hr).eq_of_nhds

lemma clippedValue_deriv {M r : ℝ} (hr : |r|≤M) : deriv (clippedValue M) r=1 := by
  rw [(clippedValue_eventually hr).deriv_eq]
  exact deriv_id r

lemma exists_clippedValue_bound (M : ℝ) : ∃ C : ℝ, 0<C ∧ ∀ r, |clippedValue M r|≤C := by
  obtain ⟨C,hC⟩ := (clippedValue_compact M).exists_bound_of_continuous (clippedValue_smooth M).continuous
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun r => ?_⟩
  exact (show |clippedValue M r|≤C from hC r).trans (le_max_right _ _)

def squaredValue (M r : ℝ) : ℝ := valueBump M r * r^2

lemma squaredValue_smooth (M : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (squaredValue M) :=
  (valueBump M).contDiff.mul (contDiff_id.pow 2)

lemma squaredValue_compact (M : ℝ) : HasCompactSupport (squaredValue M) :=
  (valueBump M).hasCompactSupport.mul_right

lemma squaredValue_zero (M : ℝ) : squaredValue M 0=0 := by simp [squaredValue]

lemma squaredValue_eventually {M r : ℝ} (hr : |r|≤M) :
    squaredValue M =ᶠ[𝓝 r] fun s => s^2 := by
  have hb : r ∈ Metric.ball 0 (valueBump M).rIn := by
    change dist r 0 < |M|+1
    rw [dist_zero_right,Real.norm_eq_abs]
    linarith [le_abs_self M]
  filter_upwards [(valueBump M).eventuallyEq_one_of_mem_ball hb] with s hs
  simp only [squaredValue,hs,Pi.one_apply,one_mul]

lemma squaredValue_eq {M r : ℝ} (hr : |r|≤M) : squaredValue M r=r^2 :=
  (squaredValue_eventually hr).eq_of_nhds

lemma squaredValue_deriv {M r : ℝ} (hr : |r|≤M) : deriv (squaredValue M) r=2*r := by
  rw [(squaredValue_eventually hr).deriv_eq]
  simp

def squareOperation (M : ℝ) : SmoothLipZero :=
  SmoothLipZero.ofCompact (squaredValue M) (squaredValue_smooth M)
    (squaredValue_compact M) (squaredValue_zero M)

def clipOperation (M : ℝ) : SmoothLipZero :=
  SmoothLipZero.ofCompact (clippedValue M) (clippedValue_smooth M)
    (clippedValue_compact M) (clippedValue_zero M)

lemma jet_squareOperation {M : ℝ} {z : JetFiber} (hz : |jetValue z|≤M) :
    jetSuperposition (squareOperation M) (deriv (squareOperation M)) z =
      jetLiftValue (jetValue z ^ 2) + jetLiftGradient ((2*jetValue z) • jetGradient z) := by
  change jetLiftValue (squaredValue M (jetValue z)) +
    jetLiftGradient (deriv (squaredValue M) (jetValue z) • jetGradient z)=_
  rw [squaredValue_eq hz,squaredValue_deriv hz]

def jetProduct (z w : JetFiber) : JetFiber :=
  jetLiftValue (jetValue z*jetValue w) +
    jetLiftGradient (jetValue z • jetGradient w + jetValue w • jetGradient z)

lemma gradient_product {f g : R3 → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : R3) :
    gradient (f*g) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_mul (hf x) (hg x)]
  simp

lemma smoothJet_product {f g : R3 → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : R3) :
    smoothJet (f*g) x=jetProduct (smoothJet f x) (smoothJet g x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change f x*g x=f x*g x+0; simp
  · change gradient (f*g) x j=0+(f x • gradient g x+g x • gradient f x) j
    rw [gradient_product hf hg]; simp

lemma square_polarization {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    {z w : JetFiber} (hz : |jetValue z|≤A) (hw : |jetValue w|≤B) :
    (1/2:ℝ) • (jetSuperposition (squareOperation (A+B)) (deriv (squareOperation (A+B))) (z+w) -
      jetSuperposition (squareOperation (A+B)) (deriv (squareOperation (A+B))) z -
      jetSuperposition (squareOperation (A+B)) (deriv (squareOperation (A+B))) w) =
    jetProduct z w := by
  have hzw : |jetValue (z+w)|≤A+B := by
    rw [map_add]; exact (abs_add_le _ _).trans (add_le_add hz hw)
  rw [jet_squareOperation hzw,jet_squareOperation (hz.trans (le_add_of_nonneg_right hB)),
    jet_squareOperation (hw.trans (le_add_of_nonneg_left hA))]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (1/2:ℝ)*(((jetValue z+jetValue w)^2+0)-(jetValue z^2+0)-(jetValue w^2+0))=
      jetValue z*jetValue w+0
    ring
  · change (1/2:ℝ)*((0+(2*(jetValue z+jetValue w))*((jetGradient z) j+(jetGradient w) j))-
      (0+(2*jetValue z)*(jetGradient z) j)-(0+(2*jetValue w)*(jetGradient w) j))=
      0+((jetValue z)*(jetGradient w) j+(jetValue w)*(jetGradient z) j)
    ring

variable (F G : SmoothLipZero) (A B : ℝ)

def clippedProductLp (z w : JetSpace) : JetSpace :=
  (1/2:ℝ) • ((squareOperation (A+B)).onLp (F.onLp z+G.onLp w) -
    (squareOperation (A+B)).onLp (F.onLp z) -
    (squareOperation (A+B)).onLp (G.onLp w))

lemma clippedProductLp_continuous : Continuous (fun p : JetSpace × JetSpace =>
    clippedProductLp F G A B p.1 p.2) := by
  exact (((squareOperation (A+B)).onLp_continuous.comp
    ((F.onLp_continuous.comp continuous_fst).add (G.onLp_continuous.comp continuous_snd))).sub
    ((squareOperation (A+B)).onLp_continuous.comp (F.onLp_continuous.comp continuous_fst)) |>.sub
    ((squareOperation (A+B)).onLp_continuous.comp (G.onLp_continuous.comp continuous_snd))).const_smul (1/2:ℝ)

lemma clippedProductLp_preserves_H1 {z w : JetSpace} (hz : z∈H1Space) (hw : w∈H1Space) :
    clippedProductLp F G A B z w∈H1Space := by
  apply H1Space.smul_mem
  apply H1Space.sub_mem
  · apply H1Space.sub_mem
    · exact (squareOperation (A+B)).preserves_H1
        (H1Space.add_mem (F.preserves_H1 hz) (G.preserves_H1 hw))
    · exact (squareOperation (A+B)).preserves_H1 (F.preserves_H1 hz)
  · exact (squareOperation (A+B)).preserves_H1 (G.preserves_H1 hw)

variable (hA : 0≤A) (hB : 0≤B) (hF : ∀ r, |F r|≤A) (hG : ∀ r, |G r|≤B)
include hA hB hF hG

lemma clippedProductLp_ae (z w : JetSpace) :
    clippedProductLp F G A B z w =ᵐ[ballMeasure] fun x =>
      jetProduct (jetSuperposition F (deriv F) (z x)) (jetSuperposition G (deriv G) (w x)) := by
  let S := squareOperation (A+B)
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) (S.onLp (F.onLp z+G.onLp w)-S.onLp (F.onLp z)-S.onLp (G.onLp w)),
    Lp.coeFn_sub (S.onLp (F.onLp z+G.onLp w)-S.onLp (F.onLp z)) (S.onLp (G.onLp w)),
    Lp.coeFn_sub (S.onLp (F.onLp z+G.onLp w)) (S.onLp (F.onLp z)),
    S.onLp_ae (F.onLp z+G.onLp w),S.onLp_ae (F.onLp z),S.onLp_ae (G.onLp w),
    Lp.coeFn_add (F.onLp z) (G.onLp w),F.onLp_ae z,G.onLp_ae w] with x hs hsub hsub' hsum h1 h2 ha hf hg
  change ((1/2:ℝ) • (S.onLp (F.onLp z+G.onLp w)-S.onLp (F.onLp z)-S.onLp (G.onLp w))) x=_
  rw [hs,Pi.smul_apply,hsub,Pi.sub_apply,hsub',Pi.sub_apply,hsum,h1,h2,ha,Pi.add_apply,hf,hg]
  apply square_polarization hA hB
  · change |F (jetValue (z x))+0|≤A; simpa using hF (jetValue (z x))
  · change |G (jetValue (w x))+0|≤B; simpa using hG (jetValue (w x))

lemma clippedProductLp_smooth {f g : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hfm : MemLp (smoothJet f) 2 ballMeasure) (hgm : MemLp (smoothJet g) 2 ballMeasure) :
    ∃ hm : MemLp (smoothJet ((F ∘ f)*(G ∘ g))) 2 ballMeasure,
      clippedProductLp F G A B (hfm.toLp _) (hgm.toLp _) = hm.toLp _ := by
  have he : clippedProductLp F G A B (hfm.toLp _) (hgm.toLp _) =ᵐ[ballMeasure]
      smoothJet ((F ∘ f)*(G ∘ g)) := by
    filter_upwards [clippedProductLp_ae F G A B hA hB hF hG (hfm.toLp _) (hgm.toLp _),
      hfm.coeFn_toLp,hgm.coeFn_toLp] with x hx hy hz
    rw [hx,hy,hz,←smoothJet_comp F.derivative (hf.differentiable (by simp)),
      ←smoothJet_comp G.derivative (hg.differentiable (by simp)),
      ←smoothJet_product ((F.smooth.comp hf).differentiable (by simp))
        ((G.smooth.comp hg).differentiable (by simp))]
  have hm := MemLp.ae_eq he (Lp.memLp (clippedProductLp F G A B (hfm.toLp _) (hgm.toLp _)))
  exact ⟨hm,Lp.ext (he.trans hm.coeFn_toLp.symm)⟩

lemma clippedProductLp_smooth_compact {z w : JetSpace} (hz : z∈smoothJets) (hw : w∈compactSmoothJets) :
    clippedProductLp F G A B z w∈compactSmoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  obtain ⟨g,hg,hgc,hgs,hgm,rfl⟩ := hw
  obtain ⟨hm,he⟩ := clippedProductLp_smooth F G A B hA hB hF hG hf hg hfm hgm
  refine ⟨(F ∘ f)*(G ∘ g),(F.smooth.comp hf).mul (G.smooth.comp hg),
    (hgc.comp_left G.at_zero).mul_left,?_,hm,he⟩
  exact (closure_mono (Function.support_mul_subset_right _ _)).trans
    ((closure_mono (Function.support_comp_subset G.at_zero g)).trans hgs)

lemma clippedProductLp_preserves_H10 {z w : JetSpace} (hz : z∈H1Space) (hw : w∈zeroTraceAmbient) :
    clippedProductLp F G A B z w∈zeroTraceAmbient := by
  have hc := clippedProductLp_continuous F G A B
  have hb {z : JetSpace} (hz : z∈smoothJets) {w : JetSpace} (hw : w∈closure compactSmoothJets) :
      clippedProductLp F G A B z w∈closure compactSmoothJets := by
    apply (image_closure_subset_closure_image (hc.comp (continuous_const.prodMk continuous_id))).trans
      (closure_mono (show (fun w => clippedProductLp F G A B z w) '' compactSmoothJets ⊆ compactSmoothJets from ?_))
      ⟨w,hw,rfl⟩
    rintro _ ⟨w,hw,rfl⟩
    exact clippedProductLp_smooth_compact F G A B hA hB hF hG hz hw
  change z∈(H1Space : Set JetSpace) at hz
  change w∈(zeroTraceAmbient : Set JetSpace) at hw
  change _∈(zeroTraceAmbient : Set JetSpace)
  rw [H1Space_eq_closure] at hz
  rw [zeroTraceAmbient_eq_closure] at hw ⊢
  have ht : (fun z => clippedProductLp F G A B z w) '' smoothJets ⊆ closure compactSmoothJets := by
    rintro _ ⟨z,hz,rfl⟩; exact hb hz hw
  have hh := (image_closure_subset_closure_image (hc.comp (continuous_id.prodMk continuous_const))).trans
    (closure_mono ht)
  simpa only [closure_closure,Function.comp_apply,id_eq] using hh ⟨z,hz,rfl⟩

end ScalarConductivity

end

end OAI
