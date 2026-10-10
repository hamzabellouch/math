import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.ConstructedOuterMetric

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart
open scoped Topology ContDiff

lemma eventually_norm_ge (R : ℝ) : ∀ᶠ x : E in spatialInfinity, R ≤ ‖x‖ :=
  Filter.eventually_comap.mpr ((eventually_ge_atTop R).mono (fun _radius hr _point hx => hx ▸ hr))

lemma eventually_norm_gt (R : ℝ) : ∀ᶠ x : E in spatialInfinity, R < ‖x‖ :=
  Filter.eventually_comap.mpr ((eventually_gt_atTop R).mono (fun _radius hr _point hx => hx ▸ hr))

lemma spatial_eventually_nhds {P : E → Prop} (hP : ∀ᶠ x in spatialInfinity, P x) :
    ∀ᶠ x in spatialInfinity, ∀ᶠ y in 𝓝 x, P y := by
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp hP)
  filter_upwards [eventually_norm_gt R] with x hx
  have ho : IsOpen {y : E | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [ho.mem_nhds hx] with y hy
  exact hR ‖y‖ hy.le y rfl

lemma spatial_pd_congr {F G : E → ℝ} (h : F =ᶠ[spatialInfinity] G) (j : Ix) :
    pd j F =ᶠ[spatialInfinity] pd j G := by
  filter_upwards [spatial_eventually_nhds h] with x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e j)) (Filter.EventuallyEq.fderiv_eq hx)

lemma TailRegular.pd {F : E → ℝ} (h : TailRegular F) (j : Ix) : TailRegular (pd j F) := by
  filter_upwards [h] with x hx
  exact (hx.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma TailRegular.mul {F G : E → ℝ} (hF : TailRegular F) (hG : TailRegular G) :
    TailRegular (fun x => F x*G x) := by
  filter_upwards [hF,hG] with x hf hg
  exact hf.mul hg

lemma TailRegular.add {F G : E → ℝ} (hF : TailRegular F) (hG : TailRegular G) :
    TailRegular (fun x => F x+G x) := by
  filter_upwards [hF,hG] with x hf hg
  exact hf.add hg

lemma TailRegular.congr {F G : E → ℝ} (hF : TailRegular F) (he : F =ᶠ[spatialInfinity] G) :
    TailRegular G := by
  filter_upwards [hF,spatial_eventually_nhds he] with x hf he
  exact hf.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)

lemma Decay.congr {F G : E → ℝ} {d : ℝ} (hF : Decay d F) (he : F =ᶠ[spatialInfinity] G) :
    Decay d G := by
  obtain ⟨C,hC,h⟩ := hF
  refine ⟨C,hC,?_⟩
  filter_upwards [h,he] with x hx he
  simpa only [←he] using hx

lemma Decay.zero (d : ℝ) : Decay d (fun _ : E => 0) :=
  ⟨0,le_rfl,Filter.Eventually.of_forall (by intro x; simp)⟩

lemma Decay.const (c : ℝ) : Decay 0 (fun _ : E => c) :=
  ⟨|c|,abs_nonneg c,Filter.Eventually.of_forall (by intro x; simp)⟩

lemma Decay.add {F G : E → ℝ} {d : ℝ} (hF : Decay d F) (hG : Decay d G) :
    Decay d (fun x => F x+G x) := by
  obtain ⟨A,hA,ha⟩ := hF
  obtain ⟨B,hB,hb⟩ := hG
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  filter_upwards [ha,hb] with x hx hy
  exact (abs_add_le _ _).trans ((add_le_add hx hy).trans_eq (by ring))

lemma Decay.mul {F G : E → ℝ} {d e : ℝ} (hF : Decay d F) (hG : Decay e G) :
    Decay (d+e) (fun x => F x*G x) := by
  obtain ⟨A,hA,ha⟩ := hF
  obtain ⟨B,hB,hb⟩ := hG
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  filter_upwards [ha,hb,eventually_norm_gt 0] with x hx hy hr
  rw [abs_mul]
  calc
    |F x| * |G x| ≤ (A*‖x‖^(-d))*(B*‖x‖^(-e)) :=
      mul_le_mul hx hy (abs_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _))
    _ = A*B*‖x‖^(-(d+e)) := by
      rw [neg_add,Real.rpow_add hr]
      ring

lemma Decay.weaken {F : E → ℝ} {d e : ℝ} (hF : Decay d F) (he : e ≤ d) : Decay e F := by
  obtain ⟨C,hC,h⟩ := hF
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_norm_ge 1] with x hx hr
  exact hx.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr (neg_le_neg he)) hC)

lemma SymbolN.congr {F G : E → ℝ} {n : ℕ} {d : ℝ} (hF : SymbolN n d F)
    (he : F =ᶠ[spatialInfinity] G) : SymbolN n d G := by
  induction n generalizing F G d with
  | zero => exact Decay.congr hF he
  | succ n ih => exact ⟨hF.1.congr he,fun j => ih (hF.2 j) (spatial_pd_congr he j)⟩

lemma SymbolN.zero (n : ℕ) (d : ℝ) : SymbolN n d (fun _ : E => 0) := by
  induction n generalizing d with
  | zero => exact Decay.zero d
  | succ n ih =>
    refine ⟨Decay.zero d,?_⟩
    intro j
    simpa only [show pd j (fun _ : E => (0:ℝ)) = (fun _ => 0) from funext (fun x => pd_const j 0 x)] using ih (d+1)

lemma SymbolN.const (n : ℕ) (c : ℝ) : SymbolN n 0 (fun _ : E => c) := by
  cases n with
  | zero => exact Decay.const c
  | succ n =>
    refine ⟨Decay.const c,?_⟩
    intro j
    simpa only [show pd j (fun _ : E => c) = (fun _ => 0) from funext (fun x => pd_const j c x),zero_add] using SymbolN.zero n 1

lemma SymbolN.weaken {F : E → ℝ} {n : ℕ} {d e : ℝ} (hF : SymbolN n d F)
    (he : e ≤ d) : SymbolN n e F := by
  induction n generalizing F d e with
  | zero => exact Decay.weaken hF he
  | succ n ih => exact ⟨hF.1.weaken he,fun j => ih (hF.2 j) (by linarith)⟩

lemma SymbolN.add {F G : E → ℝ} {n : ℕ} {d : ℝ} (rF : TailRegular F) (rG : TailRegular G)
    (hF : SymbolN n d F) (hG : SymbolN n d G) : SymbolN n d (fun x => F x+G x) := by
  induction n generalizing F G d with
  | zero => exact Decay.add hF hG
  | succ n ih =>
    refine ⟨hF.1.add hG.1,?_⟩
    intro j
    apply (ih (rF.pd j) (rG.pd j) (hF.2 j) (hG.2 j)).congr
    filter_upwards [rF,rG] with x hf hg
    exact (pd_add (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)) j).symm

lemma SymbolN.lower {F : E → ℝ} {n : ℕ} {d : ℝ} (hF : SymbolN (n+1) d F) :
    SymbolN n d F := by
  induction n generalizing F d with
  | zero => exact hF.1
  | succ n ih => exact ⟨hF.1,fun j => ih (hF.2 j)⟩

lemma SymbolN.mul {F G : E → ℝ} {n : ℕ} {d e : ℝ} (rF : TailRegular F) (rG : TailRegular G)
    (hF : SymbolN n d F) (hG : SymbolN n e G) : SymbolN n (d+e) (fun x => F x*G x) := by
  induction n generalizing F G d e with
  | zero => exact Decay.mul hF hG
  | succ n ih =>
    refine ⟨hF.1.mul hG.1,?_⟩
    intro j
    have hF' := hF.lower
    have hG' := hG.lower
    have ha := ih (rF.pd j) rG (hF.2 j) hG'
    have hb := ih rF (rG.pd j) hF' (hG.2 j)
    have hd : d+1+e = d+e+1 := by ring
    have he : d+(e+1) = d+e+1 := by ring
    rw [hd] at ha
    rw [he] at hb
    apply (ha.add ((rF.pd j).mul rG) (rF.mul (rG.pd j)) hb).congr
    filter_upwards [rF,rG] with x hf hg
    exact (pd_mul (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)) j).symm

lemma Symbol.const (c : ℝ) : Symbol 0 (fun _ : E => c) :=
  ⟨Filter.Eventually.of_forall (fun _ => contDiffAt_const),fun n => SymbolN.const n c⟩

lemma Symbol.congr {F G : E → ℝ} {d : ℝ} (hF : Symbol d F)
    (he : F =ᶠ[spatialInfinity] G) : Symbol d G :=
  ⟨hF.1.congr he,fun n => (hF.2 n).congr he⟩

lemma Symbol.add {F G : E → ℝ} {d : ℝ} (hF : Symbol d F) (hG : Symbol d G) :
    Symbol d (fun x => F x+G x) :=
  ⟨hF.1.add hG.1,fun n => (hF.2 n).add hF.1 hG.1 (hG.2 n)⟩

lemma Symbol.mul {F G : E → ℝ} {d e : ℝ} (hF : Symbol d F) (hG : Symbol e G) :
    Symbol (d+e) (fun x => F x*G x) :=
  ⟨hF.1.mul hG.1,fun n => (hF.2 n).mul hF.1 hG.1 (hG.2 n)⟩

lemma Symbol.weaken {F : E → ℝ} {d e : ℝ} (hF : Symbol d F) (he : e ≤ d) : Symbol e F :=
  ⟨hF.1,fun n => (hF.2 n).weaken he⟩

lemma Symbol.pd {F : E → ℝ} {d : ℝ} (hF : Symbol d F) (j : Ix) : Symbol (d+1) (pd j F) :=
  ⟨hF.1.pd j,fun n => (hF.2 (n+1)).2 j⟩

lemma Symbol.const_mul {F : E → ℝ} {d : ℝ} (hF : Symbol d F) (c : ℝ) :
    Symbol d (fun x => c*F x) := by
  simpa only [zero_add] using (Symbol.const c).mul hF

lemma Symbol.neg {F : E → ℝ} {d : ℝ} (hF : Symbol d F) : Symbol d (fun x => -F x) := by
  simpa only [neg_one_mul] using hF.const_mul (-1)

lemma Symbol.sub {F G : E → ℝ} {d : ℝ} (hF : Symbol d F) (hG : Symbol d G) :
    Symbol d (fun x => F x-G x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma pd_inverse {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x) (hne : F x ≠ 0) (j : Ix) :
    pd j (fun y => (F y)⁻¹) x = -(pd j F x)*(F x)⁻¹*(F x)⁻¹ := by
  have hh := (hasFDerivAt_inv' (𝕜 := ℝ) hne).comp x hF.hasFDerivAt
  unfold pd
  erw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  ring

lemma SymbolN.inverse {F : E → ℝ} {n : ℕ} (rF : TailRegular F) (hF : SymbolN n 0 F)
    {c : ℝ} (hc : 0 < c) (hl : ∀ᶠ x in spatialInfinity, c ≤ |F x|) :
    SymbolN n 0 (fun x => (F x)⁻¹) := by
  have hn : ∀ᶠ x in spatialInfinity, F x ≠ 0 := hl.mono (fun _ hx => abs_pos.mp (hc.trans_le hx))
  have ri : TailRegular (fun x => (F x)⁻¹) := by
    filter_upwards [rF,hn] with x hx hn
    exact hx.inv hn
  have hi : Decay 0 (fun x => (F x)⁻¹) := by
    refine ⟨c⁻¹,inv_nonneg.mpr hc.le,?_⟩
    filter_upwards [hl] with x hx
    simp only [abs_inv,neg_zero,Real.rpow_zero,mul_one]
    exact (inv_le_inv₀ (hc.trans_le hx) hc).mpr hx
  induction n with
  | zero => exact hi
  | succ n ih =>
    refine ⟨hi,?_⟩
    intro j
    have hh := ih hF.lower
    have hs := SymbolN.mul ri ri hh hh
    have hd := SymbolN.mul (rF.pd j) (ri.mul ri) (hF.2 j) hs
    have hz := SymbolN.mul (Symbol.const (-1)).1 ((rF.pd j).mul (ri.mul ri))
      (SymbolN.const n (-1)) hd
    simp only [zero_add,add_zero] at hz
    simp only [zero_add]
    apply hz.congr
    filter_upwards [rF,hn] with x hx hn
    rw [pd_inverse (hx.differentiableAt (by simp)) hn]
    ring

lemma Symbol.inverse {F : E → ℝ} (hF : Symbol 0 F) {c : ℝ} (hc : 0 < c)
    (hl : ∀ᶠ x in spatialInfinity, c ≤ |F x|) : Symbol 0 (fun x => (F x)⁻¹) := by
  refine ⟨?_,fun n => SymbolN.inverse hF.1 (hF.2 n) hc hl⟩
  filter_upwards [hF.1,hl] with x hx hl
  exact hx.inv (abs_pos.mp (hc.trans_le hl))

end
end CKSADM

end

end OAI
