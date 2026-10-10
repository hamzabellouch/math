import OAI.Geometry.Immersion.ClosedSurface.OscillatoryModel
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



structure ModeDomain (G : Field n) (U : Set Base) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ G U
  determinant : ∀ p ∈ U, gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0
  good : ∀ p ∈ U, goodSecond G p ⬝ᵥ goodSecond G p ≠ 0

lemma ModeDomain.smoothAt {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {p : Base} (hp : p ∈ U) : ContDiffAt ℝ ∞ G p :=
  (h.smooth p hp).contDiffAt (h.isOpen.mem_nhds hp)

lemma ModeDomain.connectionX {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (connectionX G v w) U := by
  intro p hp
  exact (contDiffAt_connectionX (h.smoothAt hp) (h.determinant p hp) v w).contDiffWithinAt

lemma ModeDomain.connectionY {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (connectionY G v w) U := by
  intro p hp
  exact (contDiffAt_connectionY (h.smoothAt hp) (h.determinant p hp) v w).contDiffWithinAt

lemma ModeDomain.secondRatio {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (secondRatio G v w) U := by
  intro p hp
  exact (contDiffAt_secondRatio (h.smoothAt hp) (h.determinant p hp) (h.good p hp) v w).contDiffWithinAt

lemma contDiffOn_coordDeriv {U : Set Base} (hU : IsOpen U) {f : Scalar}
    (hf : ContDiffOn ℝ ∞ f U) (v : Base) : ContDiffOn ℝ ∞ (coordDeriv v f) U := by
  intro p hp
  exact (contDiffAt_coordDeriv ((hf p hp).contDiffAt (hU.mem_nhds hp)) v).contDiffWithinAt

lemma contDiffOn_connectionTerm {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {ux uy : Scalar} (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U) (v w : Base) :
    ContDiffOn ℝ ∞ (connectionTerm G ux uy v w) U :=
  ((h.connectionX v w).mul hx).add ((h.connectionY v w).mul hy)


structure ModeCoefficientBound (G : Field n) (U : Set Base) (s : ℝ) (m : ℕ) (K : ℝ) : Prop where
  xxX : WeightedBound U s m K (connectionX G dx dx)
  xxY : WeightedBound U s m K (connectionY G dx dx)
  xyX : WeightedBound U s m K (connectionX G dx dy)
  xyY : WeightedBound U s m K (connectionY G dx dy)
  yyX : WeightedBound U s m K (connectionX G dy dy)
  yyY : WeightedBound U s m K (connectionY G dy dy)
  ratioxx : WeightedBound U s m K (secondRatio G dx dx)
  ratioxy : WeightedBound U s m K (secondRatio G dx dy)

lemma ModeCoefficientBound.mono_order {G : Field n} {U : Set Base} {s K : ℝ} {m r : ℕ}
    (h : ModeCoefficientBound G U s m K) (hr : r ≤ m) : ModeCoefficientBound G U s r K :=
  ⟨h.xxX.mono_order hr, h.xxY.mono_order hr, h.xyX.mono_order hr, h.xyY.mono_order hr,
    h.yyX.mono_order hr, h.yyY.mono_order hr, h.ratioxx.mono_order hr, h.ratioxy.mono_order hr⟩

lemma weighted_connectionTerm {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {ux uy : Scalar} (hs : 0 ≤ s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U) (v w : Base)
    (hΓx : WeightedBound U s m K (connectionX G v w))
    (hΓy : WeightedBound U s m K (connectionY G v w))
    (hbx : WeightedBound U s m C ux) (hby : WeightedBound U s m C uy) :
    WeightedBound U s m (2 ^ (m + 1) * K * C) (connectionTerm G ux uy v w) := by
  have h1 := hΓx.mul h.isOpen.uniqueDiffOn hs hK hC (h.connectionX v w) hx hbx
  have h2 := hΓy.mul h.isOpen.uniqueDiffOn hs hK hC (h.connectionY v w) hy hby
  have hh := h1.add h.isOpen.uniqueDiffOn hs ((h.connectionX v w).mul hx)
    ((h.connectionY v w).mul hy) h2
  convert hh using 1 <;> try rfl
  rw [pow_succ]
  ring

lemma weighted_dx {U : Set Base} (hU : IsOpen U) {s C : ℝ} {m : ℕ} {f : Scalar}
    (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (coordDeriv dx f) := by
  unfold coordDeriv
  simpa [dx, Prod.norm_def] using hb.directional hU hs hf dx

lemma weighted_dy {U : Set Base} (hU : IsOpen U) {s C : ℝ} {m : ℕ} {f : Scalar}
    (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (coordDeriv dy f) := by
  unfold coordDeriv
  simpa [dy, Prod.norm_def] using hb.directional hU hs hf dy

lemma weighted_mono_div_scale {U : Set Base} {s C : ℝ} {m : ℕ} {f : Scalar}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) f := by
  apply (hb.mono_order (Nat.le_succ m)).mono_const
  exact (le_div_iff₀ hs).2 (mul_le_of_le_one_right hC hs1)


def reducedConstant (m : ℕ) (K : ℝ) : ℝ :=
  (1 + 2 ^ (m + 1) * K) * (1 + 2 ^ m * K)

lemma reducedConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ reducedConstant m K := by
  unfold reducedConstant
  positivity

lemma weighted_reducedLx {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {ux uy : Scalar} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ModeCoefficientBound G U s m K)
    (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U)
    (hbx : WeightedBound U s (m + 1) C ux) (hby : WeightedBound U s (m + 1) C uy) :
    WeightedBound U s m (reducedConstant m K * (C / s)) (reducedLx G ux uy) := by
  have hc0 : 0 ≤ C / s := div_nonneg hC hs.le
  have hux := weighted_mono_div_scale hs hs1 hC hbx
  have huy := weighted_mono_div_scale hs hs1 hC hby
  have hxx := weighted_connectionTerm h hs.le hK hc0 hx hy dx dx hc.xxX hc.xxY hux huy
  have hyy := weighted_connectionTerm h hs.le hK hc0 hx hy dy dy hc.yyX hc.yyY hux huy
  have dxsm := contDiffOn_coordDeriv h.isOpen hx dx
  have dysm := contDiffOn_coordDeriv h.isOpen hy dy
  have xxsm := contDiffOn_connectionTerm h hx hy dx dx
  have yysm := contDiffOn_connectionTerm h hx hy dy dy
  have hd1 := (weighted_dx h.isOpen hs hx hbx).sub h.isOpen.uniqueDiffOn hs.le dxsm xxsm hxx
  have hd2 := (weighted_dy h.isOpen hs hy hby).sub h.isOpen.uniqueDiffOn hs.le dysm yysm hyy
  have hp := hc.ratioxx.mul h.isOpen.uniqueDiffOn hs.le hK (by positivity)
    (h.secondRatio dx dx) (dysm.sub yysm) hd2
  have hh := hd1.sub h.isOpen.uniqueDiffOn hs.le (dxsm.sub xxsm)
    ((h.secondRatio dx dx).mul (dysm.sub yysm)) hp
  convert hh using 1 <;> try rfl
  unfold reducedConstant
  ring

lemma weighted_reducedLy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {ux uy : Scalar} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ModeCoefficientBound G U s m K)
    (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U)
    (hbx : WeightedBound U s (m + 1) C ux) (hby : WeightedBound U s (m + 1) C uy) :
    WeightedBound U s m (2 * reducedConstant m K * (C / s)) (reducedLy G ux uy) := by
  have hc0 : 0 ≤ C / s := div_nonneg hC hs.le
  have hux := weighted_mono_div_scale hs hs1 hC hbx
  have huy := weighted_mono_div_scale hs hs1 hC hby
  have hxy := weighted_connectionTerm h hs.le hK hc0 hx hy dx dy hc.xyX hc.xyY hux huy
  have hyy := weighted_connectionTerm h hs.le hK hc0 hx hy dy dy hc.yyX hc.yyY hux huy
  have dxsm := contDiffOn_coordDeriv h.isOpen hy dx
  have dysm := contDiffOn_coordDeriv h.isOpen hx dy
  have yysm := contDiffOn_coordDeriv h.isOpen hy dy
  have cxysm := contDiffOn_connectionTerm h hx hy dx dy
  have cyysm := contDiffOn_connectionTerm h hx hy dy dy
  have hxy2 := hxy.const_mul h.isOpen.uniqueDiffOn cxysm 2
  have hterm := (weighted_dx h.isOpen hs hy hby).add h.isOpen.uniqueDiffOn hs.le dxsm dysm
    (weighted_dy h.isOpen hs hx hbx)
  have hterm2 := hterm.sub h.isOpen.uniqueDiffOn hs.le (dxsm.add dysm) (contDiffOn_const.mul cxysm) hxy2
  have hdiff := (weighted_dy h.isOpen hs hy hby).sub h.isOpen.uniqueDiffOn hs.le yysm cyysm hyy
  have hprod := hc.ratioxy.mul h.isOpen.uniqueDiffOn hs.le hK (by positivity)
    (h.secondRatio dx dy) (yysm.sub cyysm) hdiff
  have hprod2 := hprod.const_mul h.isOpen.uniqueDiffOn ((h.secondRatio dx dy).mul (yysm.sub cyysm)) 2
  have hh := hterm2.sub h.isOpen.uniqueDiffOn hs.le
    ((dxsm.add dysm).sub (contDiffOn_const.mul cxysm))
    (contDiffOn_const.mul ((h.secondRatio dx dy).mul (yysm.sub cyysm))) hprod2
  have hin : WeightedBound U s m
      ((C / s + C / s + 2 * (2 ^ (m + 1) * K * (C / s))) +
        2 * (2 ^ m * K * (C / s + 2 ^ (m + 1) * K * (C / s))))
      (reducedLy G ux uy) := by
    unfold reducedLy
    simpa only [Complex.norm_ofNat, mul_assoc] using hh
  convert hin using 1
  try rfl
  unfold reducedConstant
  ring

lemma contDiffOn_reducedKx {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {a b : Scalar} (hV : ContDiffOn ℝ ∞ V U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (reducedKx G V a b) U := by
  intro p hp
  exact (contDiffAt_reducedKx (h.smoothAt hp) ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((ha p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hb p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma contDiffOn_reducedKy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {a b : Scalar} (hV : ContDiffOn ℝ ∞ V U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (reducedKy G V a b) U := by
  intro p hp
  exact (contDiffAt_reducedKy (h.smoothAt hp) ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((ha p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hb p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma contDiffOn_errorGenerator {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (errorGenerator G V f) U := by
  intro p hp
  exact (contDiffAt_errorGenerator (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma weighted_reducedK_zero {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 ≤ s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : ModeCoefficientBound G U s m K) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((1 + 2 ^ m * K) * C)
      (reducedKx G (fun _ => 0) (component f 0) (component f 2)) ∧
    WeightedBound U s m ((1 + 2 ^ m * K) * C)
      (reducedKy G (fun _ => 0) (component f 1) (component f 2)) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hcomp (i : Fin 3) := hb.component h.isOpen.uniqueDiffOn hs hC hf i
  have hmulx := hc.ratioxx.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dx)
    (hsm 2) (hcomp 2)
  have hmuly := hc.ratioxy.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dy)
    (hsm 2) (hcomp 2)
  have hsubx := (hcomp 0).sub h.isOpen.uniqueDiffOn hs (hsm 0)
    ((h.secondRatio dx dx).mul (hsm 2)) hmulx
  have hsuby := (hcomp 1).sub h.isOpen.uniqueDiffOn hs (hsm 1)
    ((h.secondRatio dx dy).mul (hsm 2)) hmuly
  constructor
  · have hhalf := hsubx.const_mul h.isOpen.uniqueDiffOn
      ((hsm 0).sub ((h.secondRatio dx dx).mul (hsm 2))) (1 / 2)
    have hbound : WeightedBound U s m ((C + 2 ^ m * K * C) / 2)
        (reducedKx G (fun _ => 0) (component f 0) (component f 2)) := by
      convert hhalf using 1
      · norm_num
        ring
      · funext p
        simp only [reducedKx, component, dotProduct_zero, add_zero]
        ring
    apply hbound.mono_const
    nlinarith [show 0 ≤ 2 ^ m * K * C by positivity]
  · convert hsuby using 1
    · ring
    · funext p
      simp [reducedKy, component]


def errorConstant (m : ℕ) (K : ℝ) : ℝ :=
  2 * reducedConstant m K * (1 + 2 ^ (m + 1) * K)

lemma errorConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ errorConstant m K := by
  unfold errorConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK)) (by positivity)

lemma weighted_errorGenerator_zero {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ModeCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (errorConstant m K * C / s) (errorGenerator G (fun _ => 0) f) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hxb := (weighted_reducedK_zero h hs.le hK hC hc hf hb).1
  have hyb := (weighted_reducedK_zero h hs.le hK hC hc hf hb).2
  have hxsm := contDiffOn_reducedKx h (V := fun _ => 0) contDiffOn_const (hsm 0) (hsm 2)
  have hysm := contDiffOn_reducedKy h (V := fun _ => 0) contDiffOn_const (hsm 1) (hsm 2)
  have hc0 : 0 ≤ (1 + 2 ^ (m + 1) * K) * C := by positivity
  have hxx := weighted_reducedLx h hs hs1 hK hc0 (hc.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hyy := weighted_reducedLy h hs hs1 hK hc0 (hc.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hx2 := hxx.const_mul h.isOpen.uniqueDiffOn (by
    intro p hp
    exact (contDiffAt_reducedLx (h.smoothAt hp)
      ((hxsm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hysm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      (h.determinant p hp) (h.good p hp)).contDiffWithinAt) 2
  have hfsm := contDiffOn_errorGenerator h (V := fun _ => 0) contDiffOn_const hf
  have hcomponent : ∀ i : Fin 3, WeightedBound U s m (errorConstant m K * C / s)
      (component (errorGenerator G (fun _ => 0) f) i) := by
    intro i
    fin_cases i
    · convert hx2 using 1
      · simp only [Complex.norm_ofNat, errorConstant]
        ring
      · rfl
    · convert hyy using 1
      · unfold errorConstant
        ring
      · rfl
    · exact (weightedBound_zero U s m).mono_const (by
        exact div_nonneg (mul_nonneg (errorConstant_nonneg m hK) hC) hs.le)
  exact WeightedBound.pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (errorConstant_nonneg m hK) hC) hs.le)
    (fun i => contDiffOn_pi.mp hfsm i) hcomponent

lemma errorConstant_mono {m r : ℕ} (hmr : m ≤ r) {K : ℝ} (hK : 0 ≤ K) :
    errorConstant m K ≤ errorConstant r K := by
  unfold errorConstant reducedConstant
  gcongr <;> norm_num

lemma contDiffOn_errorHierarchy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    ContDiffOn ℝ ∞ (errorHierarchy G V f q) U := by
  intro p hp
  exact (contDiffAt_errorHierarchy (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp) q).contDiffWithinAt


theorem weighted_errorHierarchy_zero {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (q m : ℕ)
    (hc : ModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f) :
    WeightedBound U s m ((errorConstant (m + q) K / s) ^ (q + 1) * C)
      (errorHierarchy G (fun _ => 0) f q) := by
  induction q generalizing m with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, pow_one, div_mul_eq_mul_div, errorHierarchy] using
      weighted_errorGenerator_zero h hs hs1 hK hC hc hf hb
  | succ q ih =>
    have hce : ModeCoefficientBound G U s (m + 1 + q + 1) K := by
      convert hc using 1
      omega
    have hbe : WeightedBound U s (m + 1 + q + 1) C f := by
      convert hb using 1
      omega
    have iht := ih (m + 1) hce hbe
    have han : 0 ≤ errorConstant (m + 1 + q) K / s :=
      div_nonneg (errorConstant_nonneg _ hK) hs.le
    have hbase := weighted_errorGenerator_zero h hs hs1 hK
      (mul_nonneg (pow_nonneg han _) hC) (hc.mono_order (by omega))
      (contDiffOn_errorHierarchy h (V := fun _ => 0) contDiffOn_const hf q) iht
    change WeightedBound U s m _ (errorGenerator G (fun _ => 0) (errorHierarchy G (fun _ => 0) f q))
    apply hbase.mono_const
    have he : m + 1 + q = m + (q + 1) := by omega
    rw [he]
    calc
      _ = (errorConstant m K / s) *
          ((errorConstant (m + (q + 1)) K / s) ^ (q + 1) * C) := by ring
      _ ≤ (errorConstant (m + (q + 1)) K / s) *
          ((errorConstant (m + (q + 1)) K / s) ^ (q + 1) * C) := by
        apply mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (errorConstant_mono (Nat.le_add_right m (q + 1)) hK) hs.le)
        exact mul_nonneg (pow_nonneg (div_nonneg (errorConstant_nonneg _ hK) hs.le) _) hC
      _ = _ := by ring

lemma weighted_tensor_complex_smul {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun p => a • f p) := by
  apply WeightedBound.pi hU hs (mul_nonneg (norm_nonneg _) hC)
  · intro i
    exact contDiffOn_const.mul (contDiffOn_pi.mp hf i)
  · intro i
    exact (hb.component hU hs.le hC hf i).const_mul hU (contDiffOn_pi.mp hf i) a




theorem weighted_residual_modeApprox_zero {τ : ℝ} (hτ : 0 < τ)
    {G : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (q m : ℕ)
    (hc : ModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f) :
    WeightedBound U s m (errorConstant (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
      (residual τ G f (modeApprox τ G (fun _ => 0) f q)) := by
  have hbound := weighted_errorHierarchy_zero h hs hs1 hK hC hf q m hc hb
  have hn : 0 ≤ (errorConstant (m + q) K / s) ^ (q + 1) * C :=
    mul_nonneg (pow_nonneg (div_nonneg (errorConstant_nonneg _ hK) hs.le) _) hC
  have hsm := contDiffOn_errorHierarchy h (V := fun _ => 0) contDiffOn_const hf q
  have hh := weighted_tensor_complex_smul h.isOpen.uniqueDiffOn hs hn hsm hbound
    ((-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I))
  have hnorm : ‖(-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I)‖ = τ ^ (q + 1) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_div, Complex.norm_I, div_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ, pow_succ]
  rw [hnorm] at hh
  have hconstant : τ ^ (q + 1) * ((errorConstant (m + q) K / s) ^ (q + 1) * C) =
      errorConstant (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C := by
    rw [div_pow, div_pow]
    ring
  rw [hconstant] at hh
  apply hh.congr
  intro p hp
  exact residual_modeApprox_power (ne_of_gt hτ) hG h.isOpen contDiffOn_const hf h.determinant
    (fun _ _ => dotProduct_zero _) (fun _ _ => dotProduct_zero _) h.good
    (fun _ _ => dotProduct_zero _) q p hp

lemma ModeDomain.secondForm {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (secondForm G v w) U := by
  intro p hp
  exact (contDiffAt_secondForm (h.smoothAt hp) (h.determinant p hp) v w).contDiffWithinAt



structure FullModeCoefficientBound (G : Field n) (U : Set Base) (s : ℝ) (m : ℕ) (K : ℝ) :
    Prop extends ModeCoefficientBound G U s m K where
  secondxx : WeightedBound U s m K (secondForm G dx dx)
  secondxy : WeightedBound U s m K (secondForm G dx dy)

lemma FullModeCoefficientBound.mono_order {G : Field n} {U : Set Base} {s K : ℝ} {m r : ℕ}
    (h : FullModeCoefficientBound G U s m K) (hr : r ≤ m) : FullModeCoefficientBound G U s r K :=
  ⟨h.toModeCoefficientBound.mono_order hr, h.secondxx.mono_order hr, h.secondxy.mono_order hr⟩

lemma weighted_half {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : Scalar} (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => f p / 2) := by
  have hh := hb.const_mul hU hf (1 / 2)
  have hh' : WeightedBound U s m (C / 2) (fun p => f p / 2) := by
    convert hh using 1
    · norm_num
      ring
    · funext p
      ring
  exact hh'.mono_const (by linarith)

def targetConstant (n m : ℕ) (K : ℝ) : ℝ := 1 + ((2 * n + 1 : ℕ) : ℝ) * 2 ^ m * K

lemma targetConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ targetConstant n m K := by
  unfold targetConstant
  positivity

lemma weighted_reducedK {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 ≤ s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : FullModeCoefficientBound G U s m K) (hf : ContDiffOn ℝ ∞ f U)
    (hV : ContDiffOn ℝ ∞ V U) (hb : WeightedBound U s m C f) (hbV : WeightedBound U s m C V) :
    WeightedBound U s m (targetConstant n m K * C)
      (reducedKx G V (component f 0) (component f 2)) ∧
    WeightedBound U s m (targetConstant n m K * C)
      (reducedKy G V (component f 1) (component f 2)) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hbcomp (i : Fin 3) := hb.component h.isOpen.uniqueDiffOn hs hC hf i
  have hbx := hc.secondxx.dot h.isOpen.uniqueDiffOn hs hK hC (h.secondForm dx dx) hV hbV
  have hby := hc.secondxy.dot h.isOpen.uniqueDiffOn hs hK hC (h.secondForm dx dy) hV hbV
  have bxsm : ContDiffOn ℝ ∞ (fun p => secondForm G dx dx p ⬝ᵥ V p) U := by
    intro p hp
    exact (contDiffAt_dot ((h.secondForm dx dx p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))).contDiffWithinAt
  have bysm : ContDiffOn ℝ ∞ (fun p => secondForm G dx dy p ⬝ᵥ V p) U := by
    intro p hp
    exact (contDiffAt_dot ((h.secondForm dx dy p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))).contDiffWithinAt
  have hmulx := hc.ratioxx.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dx)
    (hsm 2) (hbcomp 2)
  have hmuly := hc.ratioxy.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dy)
    (hsm 2) (hbcomp 2)
  have hhalf := weighted_half h.isOpen.uniqueDiffOn hC (hsm 0) (hbcomp 0)
  have hxa := hhalf.add h.isOpen.uniqueDiffOn hs ((hsm 0).div_const 2) bxsm hbx
  have hxr := weighted_half h.isOpen.uniqueDiffOn (by positivity)
    ((h.secondRatio dx dx).mul (hsm 2)) hmulx
  have hxx := hxa.sub h.isOpen.uniqueDiffOn hs (((hsm 0).div_const 2).add bxsm)
    (((h.secondRatio dx dx).mul (hsm 2)).div_const 2) hxr
  have hy2 := hby.const_mul h.isOpen.uniqueDiffOn bysm 2
  have hya := (hbcomp 1).add h.isOpen.uniqueDiffOn hs (hsm 1) (contDiffOn_const.mul bysm) hy2
  have hyy := hya.sub h.isOpen.uniqueDiffOn hs ((hsm 1).add (contDiffOn_const.mul bysm))
    ((h.secondRatio dx dy).mul (hsm 2)) hmuly
  constructor
  · apply hxx.mono_const
    simp only [targetConstant, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    nlinarith [show 0 ≤ (n : ℝ) * (2 ^ m * K * C) by positivity]
  · convert hyy using 1
    · simp only [targetConstant, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, Complex.norm_ofNat]
      ring
    · rfl


def fullErrorConstant (n m : ℕ) (K : ℝ) : ℝ :=
  2 * reducedConstant m K * targetConstant n (m + 1) K

lemma fullErrorConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ fullErrorConstant n m K :=
  mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK))
    (targetConstant_nonneg n (m + 1) hK)

lemma fullErrorConstant_mono {m r : ℕ} (hmr : m ≤ r) (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    fullErrorConstant n m K ≤ fullErrorConstant n r K := by
  unfold fullErrorConstant reducedConstant targetConstant
  gcongr <;> norm_num

lemma weighted_errorGenerator {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : FullModeCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (fullErrorConstant n m K * C / s) (errorGenerator G V f) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hxb := (weighted_reducedK h hs.le hK hC hc hf hV hb hbV).1
  have hyb := (weighted_reducedK h hs.le hK hC hc hf hV hb hbV).2
  have hxsm := contDiffOn_reducedKx h hV (hsm 0) (hsm 2)
  have hysm := contDiffOn_reducedKy h hV (hsm 1) (hsm 2)
  have hc0 : 0 ≤ targetConstant n (m + 1) K * C :=
    mul_nonneg (targetConstant_nonneg _ _ hK) hC
  have hxx := weighted_reducedLx h hs hs1 hK hc0 (hc.toModeCoefficientBound.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hyy := weighted_reducedLy h hs hs1 hK hc0 (hc.toModeCoefficientBound.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hx2 := hxx.const_mul h.isOpen.uniqueDiffOn (by
    intro p hp
    exact (contDiffAt_reducedLx (h.smoothAt hp)
      ((hxsm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hysm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      (h.determinant p hp) (h.good p hp)).contDiffWithinAt) 2
  have hfsm := contDiffOn_errorGenerator h hV hf
  have hcomponent : ∀ i : Fin 3, WeightedBound U s m (fullErrorConstant n m K * C / s)
      (component (errorGenerator G V f) i) := by
    intro i
    fin_cases i
    · convert hx2 using 1
      · simp only [Complex.norm_ofNat, fullErrorConstant]
        ring
      · rfl
    · convert hyy using 1
      · unfold fullErrorConstant
        ring
      · rfl
    · exact (weightedBound_zero U s m).mono_const (by
        exact div_nonneg (mul_nonneg (fullErrorConstant_nonneg n m hK) hC) hs.le)
  exact WeightedBound.pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (fullErrorConstant_nonneg n m hK) hC) hs.le)
    (fun i => contDiffOn_pi.mp hfsm i) hcomponent



theorem weighted_errorHierarchy {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U) (q m : ℕ)
    (hc : FullModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m ((fullErrorConstant n (m + q) K / s) ^ (q + 1) * C)
      (errorHierarchy G V f q) := by
  induction q generalizing m with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, pow_one, div_mul_eq_mul_div, errorHierarchy] using
      weighted_errorGenerator h hs hs1 hK hC hc hf hV hb hbV
  | succ q ih =>
    have hm : m + 1 + q + 1 = m + (q + 1) + 1 := by omega
    have iht := ih (m + 1) (hm ▸ hc) (hm ▸ hb) (hm ▸ hbV)
    have han : 0 ≤ fullErrorConstant n (m + 1 + q) K / s :=
      div_nonneg (fullErrorConstant_nonneg n _ hK) hs.le
    have hn : 0 ≤ (fullErrorConstant n (m + 1 + q) K / s) ^ (q + 1) * C :=
      mul_nonneg (pow_nonneg han _) hC
    have hbase := weighted_errorGenerator h hs hs1 hK hn
      (hc.mono_order (by omega)) (contDiffOn_errorHierarchy h hV hf q)
      (V := fun _ => 0) contDiffOn_const iht ((weightedBound_zero U s (m + 1)).mono_const hn)
    change WeightedBound U s m _ (errorGenerator G (fun _ => 0) (errorHierarchy G V f q))
    apply hbase.mono_const
    have he : m + 1 + q = m + (q + 1) := by omega
    rw [he]
    calc
      _ = (fullErrorConstant n m K / s) *
          ((fullErrorConstant n (m + (q + 1)) K / s) ^ (q + 1) * C) := by ring
      _ ≤ (fullErrorConstant n (m + (q + 1)) K / s) *
          ((fullErrorConstant n (m + (q + 1)) K / s) ^ (q + 1) * C) := by
        apply mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (fullErrorConstant_mono (Nat.le_add_right m (q + 1)) n hK) hs.le)
        exact mul_nonneg (pow_nonneg (div_nonneg (fullErrorConstant_nonneg n _ hK) hs.le) _) hC
      _ = _ := by ring



theorem weighted_residual_modeApprox {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : FullModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
      (residual τ G f (modeApprox τ G V f q)) := by
  have hbound := weighted_errorHierarchy h hs hs1 hK hC hf hVsm q m hc hb hbV
  have hn : 0 ≤ (fullErrorConstant n (m + q) K / s) ^ (q + 1) * C :=
    mul_nonneg (pow_nonneg (div_nonneg (fullErrorConstant_nonneg n _ hK) hs.le) _) hC
  have hsm := contDiffOn_errorHierarchy h hVsm hf q
  have hh := weighted_tensor_complex_smul h.isOpen.uniqueDiffOn hs hn hsm hbound
    ((-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I))
  have hnorm : ‖(-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I)‖ = τ ^ (q + 1) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_div, Complex.norm_I, div_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ, pow_succ]
  rw [hnorm] at hh
  have hconstant : τ ^ (q + 1) * ((fullErrorConstant n (m + q) K / s) ^ (q + 1) * C) =
      fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C := by
    rw [div_pow, div_pow]
    ring
  rw [hconstant] at hh
  apply hh.congr
  intro p hp
  exact residual_modeApprox_power (ne_of_gt hτ) hG h.isOpen hVsm hf h.determinant
    hX hY h.good hV q p hp


def tangentDualX (G : Field n) : Field n := fun p =>
  tangentLift (coordDeriv dx G p) (coordDeriv dy G p) 1 0

def tangentDualY (G : Field n) : Field n := fun p =>
  tangentLift (coordDeriv dx G p) (coordDeriv dy G p) 0 1

def normalDual (G : Field n) : Field n := fun p =>
  (goodSecond G p ⬝ᵥ goodSecond G p)⁻¹ • goodSecond G p

lemma tangentLift_columns (G : Field n) (p : Base) (u v : ℂ) :
    tangentLift (coordDeriv dx G p) (coordDeriv dy G p) u v =
      u • tangentDualX G p + v • tangentDualY G p := by
  ext i
  simp only [tangentLift, tangentDualX, tangentDualY, liftX, liftY,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma ModeDomain.tangentDualX {G : Field n} {U : Set Base} (h : ModeDomain G U) :
    ContDiffOn ℝ ∞ (tangentDualX G) U := by
  intro p hp
  exact (contDiffAt_tangentLift (contDiffAt_coordDeriv (h.smoothAt hp) dx)
    (contDiffAt_coordDeriv (h.smoothAt hp) dy) contDiffAt_const contDiffAt_const
    (h.determinant p hp)).contDiffWithinAt

lemma ModeDomain.tangentDualY {G : Field n} {U : Set Base} (h : ModeDomain G U) :
    ContDiffOn ℝ ∞ (tangentDualY G) U := by
  intro p hp
  exact (contDiffAt_tangentLift (contDiffAt_coordDeriv (h.smoothAt hp) dx)
    (contDiffAt_coordDeriv (h.smoothAt hp) dy) contDiffAt_const contDiffAt_const
    (h.determinant p hp)).contDiffWithinAt

lemma ModeDomain.normalDual {G : Field n} {U : Set Base} (h : ModeDomain G U) :
    ContDiffOn ℝ ∞ (normalDual G) U := by
  intro p hp
  have hb := contDiffAt_secondForm (h.smoothAt hp) (h.determinant p hp) dy dy
  unfold ClosedSurfaceR4.SmallModes.normalDual
  change ContDiffWithinAt ℝ ∞ (fun q => (ClosedSurfaceR4.SmallModes.secondForm G dy dy q ⬝ᵥ ClosedSurfaceR4.SmallModes.secondForm G dy dy q)⁻¹ • ClosedSurfaceR4.SmallModes.secondForm G dy dy q) U p
  simpa only [one_div, Pi.smul_def'] using
    ((contDiffAt_cdiv (a := fun _ => (1 : ℂ)) contDiffAt_const (contDiffAt_dot hb hb)
      (h.good p hp)).smul hb).contDiffWithinAt (s := U)



structure ReconstructionCoefficientBound (G : Field n) (U : Set Base) (s : ℝ) (m : ℕ) (K : ℝ) :
    Prop extends FullModeCoefficientBound G U s m K where
  dualx : WeightedBound U s m K (tangentDualX G)
  dualy : WeightedBound U s m K (tangentDualY G)
  dualn : WeightedBound U s m K (normalDual G)

lemma ReconstructionCoefficientBound.mono_order {G : Field n} {U : Set Base} {s K : ℝ} {m r : ℕ}
    (h : ReconstructionCoefficientBound G U s m K) (hr : r ≤ m) :
    ReconstructionCoefficientBound G U s r K :=
  ⟨h.toFullModeCoefficientBound.mono_order hr, h.dualx.mono_order hr,
    h.dualy.mono_order hr, h.dualn.mono_order hr⟩

lemma weighted_smul_field {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f : Scalar} {V : Field n} (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hbf : WeightedBound U s m C f) (hbV : WeightedBound U s m D V) :
    WeightedBound U s m (2 ^ m * C * D) (fun p => f p • V p) := by
  apply WeightedBound.pi hU hs (by positivity)
  · intro i
    exact hf.mul (contDiffOn_pi.mp hV i)
  · intro i
    exact hbf.mul hU hs.le hC hD hf (contDiffOn_pi.mp hV i) (hbV.component hU hs.le hD hV i)



def amplitudeCorrection (G V : Field n) (f : Tensor) : Field n :=
  let kx := reducedKx G V (component f 0) (component f 2)
  let ky := reducedKy G V (component f 1) (component f 2)
  fun p => kx p • tangentDualX G p + ky p • tangentDualY G p +
    (coordDeriv dy ky p - connectionTerm G kx ky dy dy p) • normalDual G p

lemma initialAmplitude_expansion (τ : ℝ) {G V : Field n} {f : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hf : ContDiffAt ℝ ∞ f p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G V f p = V p - (f p 2 / 2) • normalDual G p +
      ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p := by
  have hy := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hf 1) (contDiffAt_pi.mp hf 2) hD hb
  unfold initialAmplitude firstParametrix firstCovectorX firstCovectorY reconstruct normalElimination
  simp only [component]
  rw [partial_const_mul (a := (τ : ℂ) / Complex.I)
    (f := reducedKy G V (component f 1) (component f 2))
    (hy.differentiableAt (by simp)) dy, connectionTerm_mul, tangentLift_mul, tangentLift_columns]
  ext i
  simp only [amplitudeCorrection, normalDual, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

lemma contDiffOn_amplitudeCorrection {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (amplitudeCorrection G V f) U := by
  have hx := contDiffOn_reducedKx h hV (contDiffOn_pi.mp hf 0) (contDiffOn_pi.mp hf 2)
  have hy := contDiffOn_reducedKy h hV (contDiffOn_pi.mp hf 1) (contDiffOn_pi.mp hf 2)
  exact ((hx.smul h.tangentDualX).add (hy.smul h.tangentDualY)).add
    (((contDiffOn_coordDeriv h.isOpen hy dy).sub (contDiffOn_connectionTerm h hx hy dy dy)).smul h.normalDual)


def amplitudeConstant (n m : ℕ) (K : ℝ) : ℝ :=
  (2 ^ (m + 1) * K + 2 ^ m * K * (1 + 2 ^ (m + 1) * K)) * targetConstant n (m + 1) K

lemma amplitudeConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ amplitudeConstant n m K := by
  unfold amplitudeConstant
  exact mul_nonneg (by positivity) (targetConstant_nonneg _ _ hK)

lemma weighted_amplitudeCorrection {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (amplitudeConstant n m K * C / s) (amplitudeCorrection G V f) := by
  have hks := weighted_reducedK h hs.le hK hC hc.toFullModeCoefficientBound hf hV hb hbV
  have hx := contDiffOn_reducedKx h hV (contDiffOn_pi.mp hf 0) (contDiffOn_pi.mp hf 2)
  have hy := contDiffOn_reducedKy h hV (contDiffOn_pi.mp hf 1) (contDiffOn_pi.mp hf 2)
  have hn : 0 ≤ targetConstant n (m + 1) K * C := mul_nonneg (targetConstant_nonneg _ _ hK) hC
  have hcn := div_nonneg hn hs.le
  have hxm := weighted_mono_div_scale hs hs1 hn hks.1
  have hym := weighted_mono_div_scale hs hs1 hn hks.2
  have htx := weighted_smul_field h.isOpen.uniqueDiffOn hs hcn hK hx h.tangentDualX hxm
    (hc.dualx.mono_order (Nat.le_succ m))
  have hty := weighted_smul_field h.isOpen.uniqueDiffOn hs hcn hK hy h.tangentDualY hym
    (hc.dualy.mono_order (Nat.le_succ m))
  have ht := htx.add h.isOpen.uniqueDiffOn hs.le (hx.smul h.tangentDualX) (hy.smul h.tangentDualY) hty
  have hΓ := weighted_connectionTerm h hs.le hK hcn hx hy dy dy
    (hc.yyX.mono_order (Nat.le_succ m)) (hc.yyY.mono_order (Nat.le_succ m)) hxm hym
  have hd := (weighted_dy h.isOpen hs hy hks.2).sub h.isOpen.uniqueDiffOn hs.le
    (contDiffOn_coordDeriv h.isOpen hy dy) (contDiffOn_connectionTerm h hx hy dy dy) hΓ
  have hnormal := weighted_smul_field h.isOpen.uniqueDiffOn hs (by positivity) hK
    ((contDiffOn_coordDeriv h.isOpen hy dy).sub (contDiffOn_connectionTerm h hx hy dy dy))
    h.normalDual hd (hc.dualn.mono_order (Nat.le_succ m))
  have hh := ht.add h.isOpen.uniqueDiffOn hs.le
    ((hx.smul h.tangentDualX).add (hy.smul h.tangentDualY))
    (((contDiffOn_coordDeriv h.isOpen hy dy).sub (contDiffOn_connectionTerm h hx hy dy dy)).smul h.normalDual)
    hnormal
  convert hh using 1
  · unfold amplitudeConstant
    ring
  · rfl

lemma contDiffOn_initialAmplitude (τ : ℝ) {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (initialAmplitude τ G V f) U := by
  intro p hp
  exact (contDiffAt_initialAmplitude τ (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

def initialConstant (n m : ℕ) (K : ℝ) : ℝ := 1 + 2 ^ m * K + amplitudeConstant n m K

lemma initialConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ initialConstant n m K := by
  unfold initialConstant
  exact add_nonneg (by positivity) (amplitudeConstant_nonneg _ _ hK)

lemma weighted_reconstructedLeading {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : ReconstructionCoefficientBound G U s m K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s m C f) (hbV : WeightedBound U s m C V) :
    WeightedBound U s m (C + 2 ^ m * C * K)
      (fun p => V p - (f p 2 / 2) • normalDual G p) := by
  have hf2 := contDiffOn_pi.mp hf 2
  have hhalf := weighted_half h.isOpen.uniqueDiffOn hC hf2
    (hb.component h.isOpen.uniqueDiffOn hs.le hC hf 2)
  have hn := weighted_smul_field h.isOpen.uniqueDiffOn hs hC hK (hf2.div_const 2) h.normalDual
    hhalf hc.dualn
  exact hbV.sub h.isOpen.uniqueDiffOn hs.le hV ((hf2.div_const 2).smul h.normalDual) hn

lemma weighted_scaledAmplitudeCorrection {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (amplitudeConstant n m K * C)
      (fun p => ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) := by
  have hcorr := weighted_amplitudeCorrection h hs hs1 hK hC hc hf hV hb hbV
  have hsm := contDiffOn_amplitudeCorrection h hV hf
  have hsmall := hcorr.complex_smul_pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hK) hC) hs.le)
    hsm ((τ : ℂ) / Complex.I)
  have hnorm : ‖(τ : ℂ) / Complex.I‖ = τ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  rw [hnorm] at hsmall
  apply hsmall.mono_const
  calc
    _ ≤ s * (amplitudeConstant n m K * C / s) :=
      mul_le_mul_of_nonneg_right hτs
        (div_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hK) hC) hs.le)
    _ = _ := by field_simp

lemma weighted_initialAmplitude_expanded {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (initialConstant n m K * C) (fun p => V p - (f p 2 / 2) • normalDual G p +
        ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) := by
  have hvn := weighted_reconstructedLeading h hs hK hC (hc.mono_order (Nat.le_succ m))
    hf hV (hb.mono_order (Nat.le_succ m)) (hbV.mono_order (Nat.le_succ m))
  have hsmall := weighted_scaledAmplitudeCorrection hτ h hs hτs hs1 hK hC hc hf hV hb hbV
  have hf2 := contDiffOn_pi.mp hf 2
  have hlead : ContDiffOn ℝ ∞ (fun p => V p - (f p 2 / 2) • normalDual G p) U :=
    hV.sub ((hf2.div_const 2).smul h.normalDual)
  have hsc : ContDiffOn ℝ ∞ (fun p => ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) U :=
    by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := (τ : ℂ) / Complex.I)).smul (contDiffOn_amplitudeCorrection h hV hf)
  have hsum : WeightedBound U s m (C + 2 ^ m * C * K + amplitudeConstant n m K * C)
      (fun p => V p - (f p 2 / 2) • normalDual G p +
        ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) :=
    hvn.add h.isOpen.uniqueDiffOn hs.le hlead hsc hsmall
  have he : C + 2 ^ m * C * K + amplitudeConstant n m K * C = initialConstant n m K * C := by
    unfold initialConstant
    ring
  rw [he] at hsum
  exact hsum

lemma weighted_initialAmplitude {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (initialConstant n m K * C) (initialAmplitude τ G V f) := by
  have hh := weighted_initialAmplitude_expanded hτ h hs hτs hs1 hK hC hc hf hV hb hbV
  exact hh.congr (fun p hp => initialAmplitude_expansion τ (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp)) (h.determinant p hp) (h.good p hp))



lemma weighted_initialAmplitude_free_sub {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hV : ContDiffOn ℝ ∞ V U) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (amplitudeConstant n m K * (τ / s) * C)
      (fun p => initialAmplitude τ G V (fun _ => 0) p - V p) := by
  have hz : WeightedBound U s (m + 1) C (fun _ : Base => (0 : Fin 3 → ℂ)) :=
    (weightedBound_zero U s (m + 1)).mono_const hC
  have hcorr := weighted_amplitudeCorrection h hs hs1 hK hC hc contDiffOn_const hV hz hbV
  have hsm := contDiffOn_amplitudeCorrection h hV (f := fun _ => 0) contDiffOn_const
  have hh := hcorr.complex_smul_pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hK) hC) hs.le)
    hsm ((τ : ℂ) / Complex.I)
  have hnorm : ‖(τ : ℂ) / Complex.I‖ = τ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  rw [hnorm] at hh
  have he : τ * (amplitudeConstant n m K * C / s) =
      amplitudeConstant n m K * (τ / s) * C := by ring
  rw [he] at hh
  apply hh.congr
  intro p hp
  dsimp only
  rw [initialAmplitude_expansion τ (f := fun _ => 0) (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) contDiffAt_const
    (h.determinant p hp) (h.good p hp)]
  simp

lemma contDiffOn_modeApprox (τ : ℝ) {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    ContDiffOn ℝ ∞ (modeApprox τ G V f q) U := by
  intro p hp
  exact (contDiffAt_modeApprox τ (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp) q).contDiffWithinAt

lemma contDiffOn_residual (τ : ℝ) {G Z : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hZ : ContDiffOn ℝ ∞ Z U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (residual τ G f Z) U := by
  intro p hp
  exact (contDiffAt_residual τ (h.smoothAt hp)
    ((hZ p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))).contDiffWithinAt

def freeModeConstant (n m : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => amplitudeConstant n m K
  | q + 1 => freeModeConstant n m K q +
      initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1)

lemma freeModeConstant_nonneg (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ freeModeConstant n m K q := by
  induction q with
  | zero => exact amplitudeConstant_nonneg _ _ hK
  | succ q ih => exact add_nonneg ih (mul_nonneg (initialConstant_nonneg _ _ hK)
      (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _))




theorem weighted_modeApprox_free_sub {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 1) K)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m (freeModeConstant n m K q * (τ / s) * C)
      (fun p => modeApprox τ G V (fun _ => 0) q p - V p) := by
  induction q with
  | zero =>
    simpa only [Nat.add_zero, freeModeConstant, modeApprox] using
      weighted_initialAmplitude_free_sub hτ h hs hs1 hK hC hc hVsm hbV
  | succ q ih =>
    have hi := ih (hc.mono_order (by omega)) (hbV.mono_order (by omega))
    have hm : m + 1 + q + 1 = m + (q + 1) + 1 := by omega
    have hce : ReconstructionCoefficientBound G U s (m + 1 + q + 1) K := hm ▸ hc
    have hbe : WeightedBound U s (m + 1 + q + 1) C V := hm ▸ hbV
    have hzero : WeightedBound U s (m + 1 + q + 1) C (fun _ : Base => (0 : Fin 3 → ℂ)) :=
      (weightedBound_zero U s _).mono_const hC
    have hr := weighted_residual_modeApprox hτ hG h hs hs1 hK hC
      contDiffOn_const hVsm hX hY hV q (m + 1) hce.toFullModeCoefficientBound hzero hbe
    have hrsm := contDiffOn_residual τ h (contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q)
      (f := fun _ => 0) contDiffOn_const
    have hn : 0 ≤ fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C :=
      mul_nonneg (mul_nonneg (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)
        (pow_nonneg (div_nonneg hτ.le hs.le) _)) hC
    have hp := weighted_initialAmplitude hτ h hs hτs hs1 hK hn
      (hc.mono_order (by omega)) hrsm (V := fun _ => 0) contDiffOn_const hr
      ((weightedBound_zero U s (m + 1)).mono_const hn)
    have hp' : WeightedBound U s m
        (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) * C)
        (zeroParametrix τ G (residual τ G (fun _ => 0) (modeApprox τ G V (fun _ => 0) q))) := by
      apply hp.mono_const
      have hpow : (τ / s) ^ (q + 1) ≤ τ / s := by
        simpa only [pow_one] using pow_le_pow_of_le_one (div_nonneg hτ.le hs.le)
          ((div_le_one hs).2 hτs) (Nat.le_add_left 1 q)
      calc
        _ = (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C) *
          (τ / s) ^ (q + 1) := by ring
        _ ≤ (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C) *
          (τ / s) := mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (initialConstant_nonneg _ _ hK)
              (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)) hC)
        _ = _ := by ring
    have hpSm := contDiffOn_initialAmplitude τ h (V := fun _ => 0) contDiffOn_const hrsm
    have hh := hi.sub h.isOpen.uniqueDiffOn hs.le
      ((contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q).sub hVsm) hpSm hp'
    have he : freeModeConstant n m K q * (τ / s) * C +
        initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) * C =
        freeModeConstant n m K (q + 1) * (τ / s) * C := by
      simp only [freeModeConstant]
      ring
    rw [he] at hh
    apply hh.congr
    intro p hp
    simp only [modeApprox, zeroParametrix]
    abel

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
