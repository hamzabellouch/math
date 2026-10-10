import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.RetardedMomentumForce

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped ENNReal Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffAt_physicalCutoffCoordinates {T : ℝ} {z : CutoffState}
    (_hr : 0<z.1) (hn : ‖z.2.1‖=1) :
    ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
  apply contDiffAt_pi.mpr
  intro i
  have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
    (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
  have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
    (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
  have hd := (contDiffAt_const (c:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
  have hD := (contDiffAt_const (c:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
  · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
  · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
  · exact contDiffAt_id.fst.div_const _

lemma hasDerivAt_cutoffRay (z h : CutoffState) :
    HasDerivAt (fun s : ℝ => z+s • h) h 0 := by
  have hh := (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id (0:ℝ)).smul_const h)
  change HasDerivAt (fun s : ℝ=>z+s • h) (0+(1:ℝ) • h) 0 at hh
  simpa only [zero_add,one_smul] using hh

lemma stateCutoff_ray_deriv {T : ℝ} {z : CutoffState} (Q : Set (Fin 4→ℕ))
    (hr : 0<z.1) (hn : ‖z.2.1‖=1) (h : CutoffState) :
    deriv (fun s : ℝ=>stateCutoff T Q (z+s • h)) 0 =
      fderiv ℝ (stateCutoff T Q) z h := by
  have hd := ((contDiffAt_stateCutoff T Q hr hn).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (stateCutoff T Q) (fderiv ℝ (stateCutoff T Q) z) (z+(0:ℝ) • h) := by
    simpa only [zero_smul,add_zero] using hd
  exact (hd'.comp_hasDerivAt 0 (hasDerivAt_cutoffRay z h)).deriv

lemma stateCutoff_partial_cancel {T : ℝ} {z : CutoffState} (Q : Set (Fin 4→ℕ))
    (hr : 0<z.1) (hT : z.1≤ max 1 T) (hn : ‖z.2.1‖=1) (h : CutoffState) :
    fderiv ℝ (stateCutoff T Q) z h = -fderiv ℝ (stateCutoff T Qᶜ) z h := by
  let g : Fin 4→ℝ→ℝ := fun i s=>
    physicalCutoffCoordinates T (z+s • h).1 (z+s • h).2.1 (z+s • h).2.2.1 (z+s • h).2.2.2 i
  have hg : ∀i,DifferentiableAt ℝ (g i) 0 := by
    intro i
    have hc := (contDiffAt_physicalCutoffCoordinates (T:=T) hr hn).differentiableAt (by simp)
    have hc' : DifferentiableAt ℝ (fun z : CutoffState=>
        physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) (z+(0:ℝ) • h) := by
      simpa only [zero_smul,add_zero] using hc
    exact differentiableAt_pi.mp (hc'.comp (f:=fun s : ℝ=>z+s • h) 0 (hasDerivAt_cutoffRay z h).differentiableAt) i
  have hp : ∀i,0<g i 0 := by simpa only [g,zero_smul,add_zero] using physicalCutoffCoordinates_pos (T:=T) hn hr
  have h1 : ∀i,g i 0≤1 := by simpa only [g,zero_smul,add_zero] using physicalCutoffCoordinates_le_one hn hT
  have hh := selectedDyadicCutoff_derivative_cancel hg hp h1 Q
  change deriv (fun s=>stateCutoff T Q (z+s • h)) 0 = -deriv (fun s=>stateCutoff T Qᶜ (z+s • h)) 0 at hh
  simpa only [stateCutoff_ray_deriv Q hr hn h,stateCutoff_ray_deriv Qᶜ hr hn h] using hh

lemma stateCutoff_partial_boundary {T : ℝ} {z : CutoffState} (Q : Set (Fin 4→ℕ))
    (hr : 0<z.1) (hT : z.1≤ max 1 T) (hn : ‖z.2.1‖=1) (h : CutoffState)
    (hne : fderiv ℝ (stateCutoff T Q) z h≠0) :
    ∃j∈Q,∃k∉Q,
      0<dyadicMultiFactor j (physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
      0<dyadicMultiFactor k (physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
      ∀i,k i≤j i+2 ∧ j i≤k i+2 := by
  let g : Fin 4→ℝ→ℝ := fun i s=>
    physicalCutoffCoordinates T (z+s • h).1 (z+s • h).2.1 (z+s • h).2.2.1 (z+s • h).2.2.2 i
  have hg : ∀i,DifferentiableAt ℝ (g i) 0 := by
    intro i
    have hc := (contDiffAt_physicalCutoffCoordinates (T:=T) hr hn).differentiableAt (by simp)
    have hc' : DifferentiableAt ℝ (fun z : CutoffState=>
        physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) (z+(0:ℝ) • h) := by
      simpa only [zero_smul,add_zero] using hc
    exact differentiableAt_pi.mp (hc'.comp (f:=fun s : ℝ=>z+s • h) 0 (hasDerivAt_cutoffRay z h).differentiableAt) i
  have hp : ∀i,0<g i 0 := by simpa only [g,zero_smul,add_zero] using physicalCutoffCoordinates_pos (T:=T) hn hr
  have h1 : ∀i,g i 0≤1 := by simpa only [g,zero_smul,add_zero] using physicalCutoffCoordinates_le_one hn hT
  have hd : deriv (fun s=>selectedDyadicCutoff Q (fun i=>g i s)) 0≠0 := by
    change deriv (fun s=>stateCutoff T Q (z+s • h)) 0≠0
    rwa [stateCutoff_ray_deriv Q hr hn h]
  simpa only [g,zero_smul,add_zero] using selectedDyadicCutoff_derivative_boundary hg hp h1 Q hd

def cutoffSourceTangent (K : Vec) : CutoffState := (0,0,K,0)
def cutoffGeometryTangent (r ρ : ℝ) (a u n : Vec) : CutoffState :=
  (ρ-1,r⁻¹ • coneMotion a u n,0,0)
def cutoffReceiverTangent (ρ : ℝ) (K : Vec) : CutoffState := (0,0,0,ρ • K)

lemma branchCutoffStateRate_split (E B : Field) (α : Phase→ℝ→Phase)
    (T : ℝ) (zX zY : Phase) (σ : ℝ) :
    branchCutoffStateRate E B α T zX zY σ =
      cutoffSourceTangent (lorentzField E B (σ,α zY σ)).2 +
      cutoffGeometryTangent (branchTime α zX zY T σ-σ) (branchRate α zX zY T σ)
        (velocity (α zX (branchTime α zX zY T σ)).2) (velocity (α zY σ).2)
        (branchDirection α zX zY T σ) +
      cutoffReceiverTangent (branchRate α zX zY T σ)
        (lorentzField E B (branchTime α zX zY T σ,α zX (branchTime α zX zY T σ))).2 := by
  simp only [branchCutoffStateRate,cutoffSourceTangent,cutoffGeometryTangent,
    cutoffReceiverTangent,Prod.mk_add_mk,zero_add,add_zero]

lemma branchSelectedRate_split (E B : Field) (α : Phase→ℝ→Phase)
    (T : ℝ) (zX zY : Phase) (σ : ℝ) (Q : Set (Fin 4→ℕ)) :
    branchSelectedRate E B α T zX zY Q σ =
      fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX zY σ)
        (cutoffSourceTangent (lorentzField E B (σ,α zY σ)).2) +
      fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX zY σ)
        (cutoffGeometryTangent (branchTime α zX zY T σ-σ) (branchRate α zX zY T σ)
          (velocity (α zX (branchTime α zX zY T σ)).2) (velocity (α zY σ).2)
          (branchDirection α zX zY T σ)) +
      fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX zY σ)
        (cutoffReceiverTangent (branchRate α zX zY T σ)
          (lorentzField E B (branchTime α zX zY T σ,α zX (branchTime α zX zY T σ))).2) := by
  rw [branchSelectedRate,branchCutoffStateRate_split,map_add,map_add]

lemma stateCutoff_partial_cancel_smul {T : ℝ} {z : CutoffState} (Q : Set (Fin 4→ℕ))
    (hr : 0<z.1) (hT : z.1≤ max 1 T) (hn : ‖z.2.1‖=1) (h : CutoffState) (A : Vec) :
    (fderiv ℝ (stateCutoff T Q) z h) • A =
      -(fderiv ℝ (stateCutoff T Qᶜ) z h) • A := by
  rw [stateCutoff_partial_cancel Q hr hT hn h]

lemma stateCutoff_curve_log_bound {C T t : ℝ}
    (hC0 : 0≤C) (hC : ∀n : ℕ,∀x : ℝ,|x*deriv (dyadicFactor n) x|≤C)
    {z : ℝ→CutoffState} {h : CutoffState}
    (hz : HasDerivAt z h t) (hr : 0<(z t).1) (hn : ‖(z t).2.1‖=1)
    (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (z t) h| ≤
      625*C*∑i : Fin 4,|deriv (fun s=>physicalCutoffCoordinates T
        (z s).1 (z s).2.1 (z s).2.2.1 (z s).2.2.2 i) t /
        physicalCutoffCoordinates T (z t).1 (z t).2.1 (z t).2.2.1 (z t).2.2.2 i| := by
  have hd := ((contDiffAt_stateCutoff T Q hr hn).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hz
  rw [←hd.deriv]
  change |deriv (fun s=>selectedDyadicCutoff Q (physicalCutoffCoordinates T
    (z s).1 (z s).2.1 (z s).2.2.1 (z s).2.2.2)) t| ≤ _
  have hc := (contDiffAt_physicalCutoffCoordinates (T:=T) hr hn).differentiableAt (by simp)
  have hh := selectedDyadicCutoff_uniform_log_bound hC0 hC
    (fun i=>differentiableAt_pi.mp (hc.comp t hz.differentiableAt) i)
    (physicalCutoffCoordinates_pos (T:=T) hn hr) Q
  simpa only [stateCutoff,Function.comp_apply,Fintype.card_fin,show (5:ℝ)^4=625 by norm_num] using hh

lemma stateCutoff_source_bound {C T r : ℝ} {n v w E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hr : 0<r) (hn : ‖n‖=1) (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (r,n,v,w)
      (cutoffSourceTangent (E+cross (velocity v) B))| ≤
      625*C*((3/q v)*(goodField E B n/Real.sqrt ((1-dot n (velocity v))/2)+
        Real.sqrt ((1-dot n (velocity v))/2)*‖B‖)) := by
  let V : ℝ→Vec := fun t=>v+t • (E+cross (velocity v) B)
  have hV : HasDerivAt V (E+cross (velocity v) B) 0 := hasDerivAt_line_rvm v _
  have hv0 : V 0=v := by simp [V]
  have hz : HasDerivAt (fun t : ℝ=>(r,n,V t,w))
      (cutoffSourceTangent (E+cross (velocity v) B)) 0 :=
    (hasDerivAt_const 0 r).prodMk ((hasDerivAt_const 0 n).prodMk (hV.prodMk (hasDerivAt_const 0 w)))
  have hb := stateCutoff_curve_log_bound (T:=T) hC0 hC hz hr hn Q
  have hs := source_cutoff_logarithmic_rates (hV.congr_deriv (by rw [hv0])) hn
  simp only [hv0] at hb hs
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    deriv_const,zero_div,abs_zero] using hs

lemma stateCutoff_geometry_bound {C T r : ℝ} {n v w : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hr : 0<r) (hn : ‖n‖=1)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity w)) (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (r,n,v,w)
      (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity w)))
        (velocity w) (velocity v) n)| ≤ 625*C*(5/r) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity w)
  let M := r⁻¹ • coneMotion (velocity w) (velocity v) n
  let N : ℝ→Vec := fun s=>n+s • M
  let R : ℝ→ℝ := fun s=>r+s*(d/D-1)
  have hN : HasDerivAt N M 0 := hasDerivAt_line_rvm n M
  have hR : HasDerivAt R (d/D-1) 0 := by
    convert (hasDerivAt_const (0:ℝ) r).add ((hasDerivAt_id (0:ℝ)).mul_const (d/D-1)) using 1 <;>
      first | rfl | simp only [zero_add,one_mul]
  have hn0 : N 0=n := by simp [N]
  have hr0 : R 0=r := by simp [R]
  have hz : HasDerivAt (fun s : ℝ=>(R s,N s,v,w))
      (cutoffGeometryTangent r (d/D) (velocity w) (velocity v) n) 0 :=
    hR.prodMk (hN.prodMk ((hasDerivAt_const 0 v).prodMk (hasDerivAt_const 0 w)))
  have hb := stateCutoff_curve_log_bound (T:=T) hC0 hC hz (by rwa [hr0]) (by rwa [hn0]) Q
  simp only [hr0,hn0] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hd : HasDerivAt (fun s=>1-dot (N s) (velocity v)) (-dot M (velocity v)) 0 := by
    have hh := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_dot hN (hasDerivAt_const 0 (velocity v)))
    convert hh using 1; first | rfl | simp only [dot_zero_right_rvm,zero_add,zero_sub]
  have hD : HasDerivAt (fun s=>1-dot (N s) (velocity w)) (-dot M (velocity w)) 0 := by
    have hh := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_dot hN (hasDerivAt_const 0 (velocity w)))
    convert hh using 1; first | rfl | simp only [dot_zero_right_rvm,zero_add,zero_sub]
  have hed := angularCoordinate_log_deriv hd (by rw [hn0]; exact cone_denom_pos _ _ hn)
  have heD := angularCoordinate_log_deriv hD (by rw [hn0]; exact cone_denom_pos _ _ hn)
  have her : deriv (fun s=>R s/max 1 T) 0/(r/max 1 T)=(d/D-1)/r := by
    rw [(hR.div_const (max 1 T)).deriv]
    have hm : max 1 T≠0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'
    field_simp
  simp only [hn0] at hed heD
  simp only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    deriv_const,zero_div,abs_zero,zero_add]
  rw [hed,heD,her]
  simp only [neg_div,abs_neg]
  have hh := geometric_cutoff_logarithmic_rates (v:=v) (w:=w) hn hr hsmall
  dsimp only at hh
  dsimp only [d,D,M]
  linarith

lemma stateCutoff_receiver_bound {C T r : ℝ} {n v w K : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hr : 0<r) (hn : ‖n‖=1) (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (r,n,v,w)
      (cutoffReceiverTangent ((1-dot n (velocity v))/(1-dot n (velocity w))) K)| ≤
      625*C*(Real.sqrt ((1-dot n (velocity v))/2)^2*‖K‖/
        (q w*Real.sqrt ((1-dot n (velocity w))/2)^3)) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity w)
  let W : ℝ→Vec := fun s=>w+s • ((d/D) • K)
  have hW : HasDerivAt W ((d/D) • K) 0 := hasDerivAt_line_rvm w _
  have hw0 : W 0=w := by simp [W]
  have hz : HasDerivAt (fun s : ℝ=>(r,n,v,W s)) (cutoffReceiverTangent (d/D) K) 0 :=
    (hasDerivAt_const 0 r).prodMk ((hasDerivAt_const 0 n).prodMk ((hasDerivAt_const 0 v).prodMk hW))
  have hb := stateCutoff_curve_log_bound (T:=T) hC0 hC hz hr hn Q
  simp only [hw0] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ha : HasDerivAt (fun s=>velocity (W s)) ((d/D) • fderiv ℝ velocity w K) 0 := by
    have hv : HasFDerivAt velocity (fderiv ℝ velocity w) (W 0) := by
      rw [hw0]
      exact ((contDiff_velocity (k:=1)).differentiable one_ne_zero w).hasFDerivAt
    convert hv.comp_hasDerivAt 0 hW using 1 <;> first | rfl | simp only [map_smul]
  have hD : HasDerivAt (fun s=>1-dot n (velocity (W s)))
      (-(d/D)*dot n (fderiv ℝ velocity w K)) 0 := by
    have hh := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_dot (hasDerivAt_const 0 n) ha)
    convert hh using 1; first | rfl | simp only [dot_zero_left_rvm,add_zero,dot_smul_right,zero_sub,neg_mul]
  have heD := angularCoordinate_log_deriv hD (by rw [hw0]; exact cone_denom_pos _ _ hn)
  simp only [hw0] at heD
  simp only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    deriv_const,zero_div,abs_zero,zero_add]
  rw [heD]
  simpa only [neg_mul,neg_div,abs_neg,mul_comm] using receiver_cutoff_logarithmic_rate v w K n hn

def partialCutoffLabelCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (H : ℝ×Phase→CutoffState) (p : ℝ×Phase) : Vec :=
  (jointBranchDomain α zX T).indicator
    (fun p=>fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX p.2 p.1) (H p)) p •
      actualLabelPrimitive s α zX T p

lemma actualLabelCutoffCost_split (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (Q : Set (Fin 4→ℕ)) (p : ℝ×Phase) :
    actualLabelCutoffCost s α zX T Q p =
      partialCutoffLabelCost s α zX T Q
        (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,α p.2 p.1)).2) p +
      partialCutoffLabelCost s α zX T Q
        (fun p=>cutoffGeometryTangent (branchTime α zX p.2 T p.1-p.1) (branchRate α zX p.2 T p.1)
          (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
          (branchDirection α zX p.2 T p.1)) p +
      partialCutoffLabelCost s α zX T Q
        (fun p=>cutoffReceiverTangent (branchRate α zX p.2 T p.1)
          (lorentzField s.E s.B (branchTime α zX p.2 T p.1,α zX (branchTime α zX p.2 T p.1))).2) p := by
  classical
  by_cases hp : p∈jointBranchDomain α zX T
  · simp only [actualLabelCutoffCost,partialCutoffLabelCost,indicator_of_mem hp,
      branchSelectedRate_split,add_smul]
  · simp only [actualLabelCutoffCost,partialCutoffLabelCost,indicator_of_notMem hp,zero_smul,add_zero]

lemma PhaseFlowOn.partialCutoffLabelCost_compl {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (H : ℝ×Phase→CutoffState) (p : ℝ×Phase) :
    partialCutoffLabelCost s F.flow zX T Q H p =
      -partialCutoffLabelCost s F.flow zX T Qᶜ H p := by
  classical
  by_cases hp : p∈jointBranchDomain F.flow zX T
  · have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    have hr : 0<(branchCutoffState F.flow T zX p.2 p.1).1 := sub_pos.mpr ht.1
    have hrT : (branchCutoffState F.flow T zX p.2 p.1).1≤ max 1 T := by
      change branchTime F.flow zX p.2 T p.1-p.1≤ max 1 T
      linarith [ht.2.le,hp.1.1.1,le_max_right (1:ℝ) T]
    have hn : ‖(branchCutoffState F.flow T zX p.2 p.1).2.1‖=1 := F.branchDirection_norm zX p.2 hp.1 hp.2
    simp only [partialCutoffLabelCost,indicator_of_mem hp]
    rw [stateCutoff_partial_cancel Q hr hrT hn (H p),neg_smul]
  · simp only [partialCutoffLabelCost,indicator_of_notMem hp,zero_smul,neg_zero]

lemma PhaseFlowOn.partialCutoffLabelCost_boundary {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (H : ℝ×Phase→CutoffState) {p : ℝ×Phase}
    (hne : partialCutoffLabelCost s F.flow zX T Q H p≠0) :
    ∃j∈Q,∃k∉Q,0<dyadicMultiFactor j (actualCutoffCoordinates F.flow T zX p.2 p.1) ∧
      0<dyadicMultiFactor k (actualCutoffCoordinates F.flow T zX p.2 p.1) ∧
      ∀i,k i≤j i+2 ∧ j i≤k i+2 := by
  classical
  have hp : p∈jointBranchDomain F.flow zX T := by
    by_contra hp
    exact hne (by simp only [partialCutoffLabelCost,indicator_of_notMem hp,zero_smul])
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hr : 0<(branchCutoffState F.flow T zX p.2 p.1).1 := sub_pos.mpr ht.1
  have hrT : (branchCutoffState F.flow T zX p.2 p.1).1≤ max 1 T := by
    change branchTime F.flow zX p.2 T p.1-p.1≤ max 1 T
    linarith [ht.2.le,hp.1.1.1,le_max_right (1:ℝ) T]
  have hn : ‖(branchCutoffState F.flow T zX p.2 p.1).2.1‖=1 := F.branchDirection_norm zX p.2 hp.1 hp.2
  have hd : fderiv ℝ (stateCutoff T Q) (branchCutoffState F.flow T zX p.2 p.1) (H p)≠0 := by
    intro hz
    exact hne (by simp only [partialCutoffLabelCost,indicator_of_mem hp,hz,zero_smul])
  have hb := stateCutoff_partial_boundary (z:=branchCutoffState F.flow T zX p.2 p.1) Q hr hrT hn (H p) hd
  simpa only [branchCutoffState, actualCutoffCoordinates] using hb

lemma projected_physical_small_primitive {v W n : Vec} {w : ℝ}
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) :
    ‖angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      3136*Real.sqrt ((1-dot n (velocity v))/2) := by
  let θ := Real.sqrt ((1-dot n (velocity v))/2)
  let φ := Real.sqrt ((1-dot n (velocity W))/2)
  have hd := cone_denom_pos v n hn
  have hD := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=(1-dot n (velocity v))/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=(1-dot n (velocity W))/2 := Real.sq_sqrt (by positivity)
  have hθφ : θ≤φ := Real.sqrt_le_sqrt (by linarith)
  have hun : ‖velocity v-n‖≤4*θ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have han : ‖velocity W-n‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have he := small_deficit_difference hn hθ.le hφ.le hθφ hd.le (by nlinarith) hun han
  simpa only [one_div_one,one_smul,div_one,mul_one] using
    projected_primitive_highband_kernel (w:=w) (f:=1) (r:=1) hw hW (by norm_num) (by norm_num)
      hθ.le hφ (by nlinarith) hun han he

lemma projected_physical_cutoff_cost {v W n : Vec} {w r f c L : ℝ}
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (hL : |L|≤c) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*L) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      3136*(f/r)*(φ^2/θ)*c := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hcb : 0≤c := (abs_nonneg _).trans hL
  have hp := projected_physical_small_primitive hn hw hW hsmall
  change ‖(f*D/(r*d)*L) • _‖≤3136*(f/r)*(φ^2/θ)*c
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤f*D/(r*d))]
  calc
    _ ≤ (f*D/(r*d)*c)*(3136*θ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : d=2*θ^2 := by linarith
      have hE : D=2*φ^2 := by linarith
      rw [he,hE]
      field_simp

lemma projected_source_cutoff_cost {C T r f w : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      5880000*C*(f/r)*(φ^2/q v)*(goodField E B n/θ^2+‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hθ : 0<Real.sqrt ((1-dot n (velocity v))/2) := Real.sqrt_pos.mpr (by positivity)
  have hb := projected_physical_cutoff_cost hn hw hW hr hf hsmall
    (stateCutoff_source_bound (T:=T) (v:=v) (w:=W) (E:=E) (B:=B) hC0 hC hr hn Q)
  exact hb.trans_eq (by field_simp; ring)

lemma projected_geometry_cutoff_cost {C T r f w : ℝ} {n v W : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity W)))
          (velocity W) (velocity v) n)) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      9800000*C*f*φ^2/(r^2*θ) := by
  have hb := projected_physical_cutoff_cost hn hw hW hr hf hsmall
    (stateCutoff_geometry_bound (T:=T) (v:=v) (w:=W) hC0 hC hr hn hsmall Q)
  exact hb.trans_eq (by field_simp; ring)

lemma projected_receiver_cutoff_cost {C T r f w : ℝ} {n v W K : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffReceiverTangent ((1-dot n (velocity v))/(1-dot n (velocity W))) K)) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      1960000*C*f*θ*‖K‖/(r*q W*φ) := by
  have hd := cone_denom_pos v n hn
  have hD := cone_denom_pos W n hn
  have hθ : 0<Real.sqrt ((1-dot n (velocity v))/2) := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<Real.sqrt ((1-dot n (velocity W))/2) := Real.sqrt_pos.mpr (by positivity)
  have hb := projected_physical_cutoff_cost hn hw hW hr hf hsmall
    (stateCutoff_receiver_bound (T:=T) (v:=v) (w:=W) (K:=K) hC0 hC hr hn Q)
  exact hb.trans_eq (by field_simp; ring)

def dyadicSelectionBoundary {ι : Type*} (Q : Set (ι→ℕ)) : Set (ι→ℕ) :=
  {k | (∃j∈Q,∀i,j i≤k i+2 ∧ k i≤j i+2) ∧
       (∃j∉Q,∀i,j i≤k i+2 ∧ k i≤j i+2)}

lemma selectedDyadicCutoff_eq_one_of_active {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hp : ∀i,0<x i) (h1 : ∀i,x i≤1) (Q : Set (ι→ℕ))
    (hQ : ∀k,0<dyadicMultiFactor k x→k∈Q) : selectedDyadicCutoff Q x=1 := by
  classical
  obtain ⟨N,hN,he⟩ := selectedDyadicCutoff_curve_eventually
    (t:=0) (g:=fun i (_r : ℝ)=>x i) (fun _=>continuousAt_const) hp Q
  have hh := he.eq_of_nhds
  change selectedDyadicCutoff Q x=∑k∈selectedDyadicBox N Q,dyadicMultiFactor k x at hh
  rw [hh]
  calc
    _ = ∑k∈dyadicBox ι N,dyadicMultiFactor k x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hkn
      apply le_antisymm _ (dyadicMultiFactor_nonneg _ _)
      by_contra hh
      exact hkn (Finset.mem_filter.mpr ⟨hk,hQ k (lt_of_not_ge hh)⟩)
    _ = 1 := sum_dyadicMultiFactor_eq_one N x h1 hN

lemma stateCutoff_partial_boundary_localization {T : ℝ} {z : CutoffState}
    (Q : Set (Fin 4→ℕ)) (hr : 0<z.1) (hT : z.1≤ max 1 T) (hn : ‖z.2.1‖=1)
    (h : CutoffState) :
    fderiv ℝ (stateCutoff T Q) z h=
      stateCutoff T (dyadicSelectionBoundary Q) z*fderiv ℝ (stateCutoff T Q) z h := by
  by_cases hd : fderiv ℝ (stateCutoff T Q) z h=0
  · rw [hd,mul_zero]
  obtain ⟨j,hj,k,hk,hjp,hkp,_hnear⟩ := stateCutoff_partial_boundary Q hr hT hn h hd
  have hb : stateCutoff T (dyadicSelectionBoundary Q) z=1 := by
    apply selectedDyadicCutoff_eq_one_of_active (physicalCutoffCoordinates_pos hn hr)
      (physicalCutoffCoordinates_le_one hn hT)
    intro a ha
    exact ⟨⟨j,hj,dyadicMultiFactor_positive_index_comparison ha hjp⟩,
      ⟨k,hk,dyadicMultiFactor_positive_index_comparison ha hkp⟩⟩
  rw [hb,one_mul]

lemma PhaseFlowOn.partialCutoffLabelCost_boundary_localization {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (H : ℝ×Phase→CutoffState) (p : ℝ×Phase) :
    partialCutoffLabelCost s F.flow zX T Q H p=
      selectedDyadicCutoff (dyadicSelectionBoundary Q) (actualCutoffCoordinates F.flow T zX p.2 p.1) •
        partialCutoffLabelCost s F.flow zX T Q H p := by
  classical
  by_cases hp : p∈jointBranchDomain F.flow zX T
  · have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    have hr : 0<(branchCutoffState F.flow T zX p.2 p.1).1 := sub_pos.mpr ht.1
    have hrT : (branchCutoffState F.flow T zX p.2 p.1).1≤ max 1 T := by
      change branchTime F.flow zX p.2 T p.1-p.1≤ max 1 T
      linarith [ht.2.le,hp.1.1.1,le_max_right (1:ℝ) T]
    have hn : ‖(branchCutoffState F.flow T zX p.2 p.1).2.1‖=1 := F.branchDirection_norm zX p.2 hp.1 hp.2
    have he := stateCutoff_partial_boundary_localization Q hr hrT hn (H p)
    have hc : stateCutoff T (dyadicSelectionBoundary Q) (branchCutoffState F.flow T zX p.2 p.1)=
        selectedDyadicCutoff (dyadicSelectionBoundary Q) (actualCutoffCoordinates F.flow T zX p.2 p.1) := rfl
    rw [hc] at he
    simp only [partialCutoffLabelCost,indicator_of_mem hp,smul_smul]
    conv_lhs => rw [he]
  · simp only [partialCutoffLabelCost,indicator_of_notMem hp,zero_smul,smul_zero]

end RVM

end

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma projected_receiver_cutoff_bin_cost {A T r f w θ φ : ℝ} {n v W K : Vec}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16 ≤ ‖W‖) (hr : 0<r) (hf : 0 ≤ f)
    (hθ : 0 ≤ θ) (hφ : 0<φ) (hd : 1-dot n (velocity v) ≤ 8*θ^2)
    (hD : φ^2/2 ≤ 1-dot n (velocity W))
    (hsmall : 1-dot n (velocity v) ≤ 1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffReceiverTangent ((1-dot n (velocity v))/(1-dot n (velocity W))) K)) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖  ≤
      (125440000*A*θ/(w*φ)*‖K‖/r)*f := by
  let θa := Real.sqrt ((1-dot n (velocity v))/2)
  let φa := Real.sqrt ((1-dot n (velocity W))/2)
  have hθa : 0 ≤ θa := Real.sqrt_nonneg _
  have hφa : 0<φa := Real.sqrt_pos.mpr (div_pos (cone_denom_pos W n hn) (by norm_num))
  have hθl : θa ≤ 2*θ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hφl : φ/2 ≤ φa := by
    apply (Real.le_sqrt (by positivity) (div_nonneg (cone_denom_pos W n hn).le (by norm_num))).mpr
    nlinarith
  have hq : w/16 ≤ q W := hW.trans (norm_lt_q _).le
  have hb := projected_receiver_cutoff_cost (T:=T) (K:=K) hA0 hA hn hw hW hr hf hsmall Q
  change _ ≤ 1960000*A*f*θa*‖K‖/(r*q W*φa) at hb
  have hden : r*(w/16)*(φ/2) ≤ r*q W*φa := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hq hr.le) hφl (by positivity) (mul_nonneg hr.le (q_pos W).le)
  have hden0 : 0<r*(w/16)*(φ/2) := by positivity
  calc
    _  ≤  1960000*A*f*θa*‖K‖/(r*q W*φa) := hb
    _  ≤  1960000*A*f*(2*θ)*‖K‖/(r*(w/16)*(φ/2)) := by
      exact div_le_div₀ (by positivity) (by gcongr) hden0 hden
    _ = _ := by field_simp; ring

def physicalReceiverCutoffDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (T w : ℝ) (Q : Set (Fin 4→ℕ)) (K : ℝ→Vec)
    (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1)))) (K z.1))) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

lemma physicalReceiverCutoffDensity_bound {s : Solution} {X V K : ℝ→Vec}
    {B : ClosedConeBin} {A T w θ φ : ℝ} {z : ConeCoordinate}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hw : 0<w) (hv : w/16 ≤ ‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0 ≤ θ) (hφ : 0<φ) (hd : B.dmax ≤ 8*θ^2)
    (hDlo : φ^2/2 ≤ 1-dot z.2.2.1 (velocity (V z.1)))
    (hsmall : B.dmax ≤ 1-dot z.2.2.1 (velocity (V z.1)))
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))
    (Q : Set (Fin 4→ℕ)) :
    physicalReceiverCutoffDensity s X V B T w Q K z ≤
      ENNReal.ofReal (125440000*A*θ/(w*φ)*‖K z.1‖)*ENNReal.ofReal (z.1-z.2.1)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have hp : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1)))) (K z.1))) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖ ≤
      ENNReal.ofReal (125440000*A*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*
        ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 125440000*A*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))]
    exact ENNReal.ofReal_le_ofReal (projected_receiver_cutoff_bin_cost hA0 hA (sphere_norm z.2.2)
      hw hv hr (hf v) hθ hφ (hvbin.2.1.2.trans hd) hDlo (hvbin.2.1.2.trans hsmall) Q)
  unfold physicalReceiverCutoffDensity
  calc
    _  ≤  ENNReal.ofReal ((z.1-z.2.1)^2)* ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        ENNReal.ofReal (125440000*A*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*
          ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :=
      mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hp)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(125440000*A*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))=
          (125440000*A*θ/(w*φ)*‖K z.1‖)*(z.1-z.2.1) := by field_simp [hr.ne']
      rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ 125440000*A*θ/(w*φ)*‖K z.1‖)]
      rfl

lemma physicalReceiverCutoff_near {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {X V K : ℝ→Vec} (hV : Measurable V) (hK : Measurable K) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {A w C p θ φ : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A) (hw : 0<w) (hC : 0 ≤ C) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (hφ : 0<φ)
    (hsmall : B.dmax ≤ B.Dmin) (hr : 0<B.rmin) (hDlo : φ^2/2 ≤ B.Dmin)
    (hDhi : B.Dmax ≤ 8*φ^2) (hd : B.dmax ≤ 8*θ^2)
    (hband : ∀t∈J,w/16 ≤ ‖V t‖)
    (Q : Set (Fin 4→ℕ))
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V B T w Q K z
      ∂physicalBinMeasure V B J) ≤
    (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
      ENNReal.ofReal ((125440000*49152)*A*C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
  by_cases hwidth : B.rmin ≤ B.rmax
  · have hb := physicalBin_radial_density_near hV B hJ hC hp hθ hφ.le (hr.le.trans hwidth) hDhi hdensity hK.norm.ennreal_ofReal
    calc
      _  ≤  ∫⁻z : ConeCoordinate,ENNReal.ofReal (125440000*A*θ/(w*φ))*
          (ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
        have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
        have hk := physicalReceiverCutoffDensity_bound (X:=X) (s:=s) (z:=z) (K:=K) (T:=T) hA0 hA hw (hband z.1 hz.1)
          (hr.trans_le hz.2.2.1.1) hθ hφ hd (hDlo.trans hz.2.2.2.2.1)
          (hsmall.trans hz.2.2.2.2.1) (fun v=>hs.nonnegative _ hzT _) Q
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 125440000*A*θ/(w*φ))] at hk
        convert hk using 1; ac_rfl
      _ = ENNReal.ofReal (125440000*A*θ/(w*φ))*
          (∫⁻z : ConeCoordinate,ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
            ∂physicalBinMeasure V B J) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _  ≤  ENNReal.ofReal (125440000*A*θ/(w*φ))*((∫⁻t in J,ENNReal.ofReal ‖K t‖)*
          ENNReal.ofReal (49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin))) := mul_le_mul' le_rfl hb
      _ = _ := by
        have he : (125440000*49152)*A*C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)=
            (125440000*A*θ/(w*φ))*(49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)) := by
          field_simp
        rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ 125440000*A*θ/(w*φ))]
        ac_rfl
  · have he : physicalBinBase V B J=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hwidth (hz.2.2.1.1.trans hz.2.2.1.2)
    simp only [physicalBinMeasure,he,Measure.restrict_empty,lintegral_zero_measure]
    exact bot_le

lemma Admissible.receiver_cutoff_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(X V K : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) (w p θ φ : ℝ)
        (Q : Set (Fin 4→ℕ)),
      Measurable V → Measurable K → MeasurableSet J → J⊆Icc 0 T →
      0<w → 0 ≤ p → 0 ≤ θ → 0<φ → B.dmax ≤ B.Dmin → 0<B.rmin →
      φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 → B.dmax ≤ 8*θ^2 → B.qmax ≤ p →
      (∀t∈J,w/16 ≤ ‖V t‖) →
      (∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V B T w Q K z
        ∂physicalBinMeasure V B J) ≤
      (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
  obtain ⟨A,hA,hAb⟩ := dyadicFactor_log_derivative_bound
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨(125440000*49152)*A*C,by positivity,?_⟩
  intro s T F hs h0 X V K B J w p θ φ Q hV hK hJ hJT hw hp hθ hφ hsmall hr hDlo hDhi hd hq hband
  apply physicalReceiverCutoff_near hs hV hK B hJ hJT hA hAb hw hC hp hθ hφ hsmall hr hDlo hDhi hd hband Q
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma unprojected_physical_small_primitive {v W n : Vec}
    (hn : ‖n‖=1) (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) :
    ‖signedPrimitive (velocity W) (velocity v) n‖ ≤
      52*Real.sqrt ((1-dot n (velocity v))/2)/Real.sqrt ((1-dot n (velocity W))/2) := by
  let θ := Real.sqrt ((1-dot n (velocity v))/2)
  let φ := Real.sqrt ((1-dot n (velocity W))/2)
  have hd := cone_denom_pos v n hn
  have hD := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=(1-dot n (velocity v))/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=(1-dot n (velocity W))/2 := Real.sq_sqrt (by positivity)
  have hφ1 : φ≤1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith [cone_denom_le_two W n hn]⟩
  have hθφ : θ≤φ := Real.sqrt_le_sqrt (by linarith)
  have hun : ‖velocity v-n‖≤4*θ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have han : ‖velocity W-n‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have he := small_deficit_difference hn hθ.le hφ.le hθφ hd.le (by nlinarith) hun han
  exact small_primitive_norm hn hθ.le hφ hφ1 (by nlinarith) hun he

lemma unprojected_physical_cutoff_cost {v W n : Vec} {r f c L : ℝ}
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (hL : |L|≤c) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*L) •
      signedPrimitive (velocity W) (velocity v) n‖ ≤
      52*(f/r)*(φ/θ)*c := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hcb : 0≤c := (abs_nonneg _).trans hL
  have hp := unprojected_physical_small_primitive hn hsmall
  change ‖(f*D/(r*d)*L) • _‖≤52*(f/r)*(φ/θ)*c
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤f*D/(r*d))]
  calc
    _ ≤ (f*D/(r*d)*c)*(52*θ/φ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : d=2*θ^2 := by linarith
      have hE : D=2*φ^2 := by linarith
      rw [he,hE]
      field_simp

lemma unprojected_source_cutoff_cost {C T r f : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      signedPrimitive (velocity W) (velocity v) n‖ ≤
      97500*C*(f/r)*(φ/q v)*(goodField E B n/θ^2+‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hθ : 0<Real.sqrt ((1-dot n (velocity v))/2) := Real.sqrt_pos.mpr (by positivity)
  have hb := unprojected_physical_cutoff_cost hn hr hf hsmall
    (stateCutoff_source_bound (T:=T) (v:=v) (w:=W) (E:=E) (B:=B) hC0 hC hr hn Q)
  exact hb.trans_eq (by field_simp; ring)

lemma unprojected_geometry_cutoff_cost {C T r f : ℝ} {n v W : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity W)))
          (velocity W) (velocity v) n)) •
      signedPrimitive (velocity W) (velocity v) n‖ ≤
      162500*C*f*φ/(r^2*θ) := by
  have hb := unprojected_physical_cutoff_cost hn hr hf hsmall
    (stateCutoff_geometry_bound (T:=T) (v:=v) (w:=W) hC0 hC hr hn hsmall Q)
  exact hb.trans_eq (by field_simp; ring)

lemma unprojected_receiver_cutoff_cost {C T r f : ℝ} {n v W K : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffReceiverTangent ((1-dot n (velocity v))/(1-dot n (velocity W))) K)) •
      signedPrimitive (velocity W) (velocity v) n‖ ≤
      32500*C*f*θ*‖K‖/(r*q W*φ^2) := by
  have hd := cone_denom_pos v n hn
  have hD := cone_denom_pos W n hn
  have hθ : 0<Real.sqrt ((1-dot n (velocity v))/2) := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<Real.sqrt ((1-dot n (velocity W))/2) := Real.sqrt_pos.mpr (by positivity)
  have hb := unprojected_physical_cutoff_cost hn hr hf hsmall
    (stateCutoff_receiver_bound (T:=T) (v:=v) (w:=W) (K:=K) hC0 hC hr hn Q)
  exact hb.trans_eq (by field_simp; ring)

lemma unprojected_time_weight_cost {v W n : Vec} {f r c : ℝ}
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f) (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) :
    ‖(f/r*c) • signedPrimitive (velocity W) (velocity v) n‖ ≤
      52*(f/r)*Real.sqrt ((1-dot n (velocity v))/2)/Real.sqrt ((1-dot n (velocity W))/2)*|c| := by
  have hp := unprojected_physical_small_primitive hn hsmall
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hf hr.le)]
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq
  ring

end RVM

end

end OAI
