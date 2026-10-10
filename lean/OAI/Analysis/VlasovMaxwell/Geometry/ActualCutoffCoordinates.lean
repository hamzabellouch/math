import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.BinHits
import OAI.Analysis.VlasovMaxwell.Population.ContDiffDyadicMultiFactor

namespace OAI

noncomputable section

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma receiver_cutoff_logarithmic_rate (v w K n : Vec) (hn : ‖n‖=1) :
    let d := 1-dot n (velocity v)
    let D := 1-dot n (velocity w)
    let θ := Real.sqrt (d/2)
    let φ := Real.sqrt (D/2)
    |dot n (fderiv ℝ velocity w K)*(d/D)/(2*D)| ≤
      θ^2*‖K‖/(q w*φ^3) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity w)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos w n hn
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hb : |dot n (fderiv ℝ velocity w K)|≤4*φ*(‖K‖/q w) := by
    rw [dot_comm]
    exact (receiver_acceleration_bounds w K n hn hφ.le (by dsimp only [D] at hφsq; nlinarith)).2
  change |dot n (fderiv ℝ velocity w K)*(d/D)/(2*D)|≤θ^2*‖K‖/(q w*φ^3)
  rw [abs_div,abs_mul,abs_of_pos (div_pos hd hD),abs_of_pos (by positivity : 0<2*D)]
  calc
    _ ≤ (4*φ*(‖K‖/q w))*(d/D)/(2*D) := by gcongr
    _ = _ := by
      have hdθ : d=2*θ^2 := by linarith
      have hDφ : D=2*φ^2 := by linarith
      rw [hdθ,hDφ]
      field_simp
      ring

def actualCutoffCoordinates (α : Phase→ℝ→Phase) (T : ℝ) (zX zY : Phase) (σ : ℝ) : Fin 4→ℝ :=
  physicalCutoffCoordinates T (branchTime α zX zY T σ-σ) (branchDirection α zX zY T σ)
    (α zY σ).2 (α zX (branchTime α zX zY T σ)).2

lemma PhaseFlowOn.actualCutoffCoordinates_pos {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ∀ i,0<actualCutoffCoordinates F.flow T zX zY σ i :=
  physicalCutoffCoordinates_pos (F.branchDirection_norm zX zY hσ hne)
    (sub_pos.mpr (F.branch_time_mem zX zY hσ hne).1)

lemma PhaseFlowOn.actualCutoffCoordinates_le_one {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ∀ i,actualCutoffCoordinates F.flow T zX zY σ i≤1 := by
  apply physicalCutoffCoordinates_le_one (F.branchDirection_norm zX zY hσ hne)
  linarith [(F.branch_time_mem zX zY hσ hne).2,hσ.1.1,le_max_right (1:ℝ) T]

lemma PhaseFlowOn.actualCutoffCoordinates_contDiffAt {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ∀ i,ContDiffAt ℝ 1 (fun r=>actualCutoffCoordinates F.flow T zX zY r i) σ := by
  let τ := branchTime F.flow zX zY T
  have ht := F.branch_time_mem zX zY hσ hne
  have hτ : ContDiffAt ℝ 1 τ σ := (F.branch_differential zX zY hσ hne).1
  have hX : ContDiffAt ℝ 1 (fun r=>F.flow zX (τ r)) σ :=
    ((F.flow_contDiffOn hs zX).contDiffAt (isOpen_Ioo.mem_nhds ⟨hσ.1.1.trans ht.1,ht.2⟩)).comp σ hτ
  have hY := (F.flow_contDiffOn hs zY).contDiffAt (isOpen_Ioo.mem_nhds hσ.1)
  have hr : ContDiffAt ℝ 1 (fun r=>τ r-r) σ := hτ.sub contDiffAt_id
  have hn : ContDiffAt ℝ 1 (branchDirection F.flow zX zY T) σ :=
    (hr.inv (sub_pos.mpr ht.1).ne').smul (hX.fst.sub hY.fst)
  have hunit := F.branchDirection_norm zX zY hσ hne
  have hu := (contDiff_velocity (k:=1)).contDiffAt.comp σ hY.snd
  have ha := (contDiff_velocity (k:=1)).contDiffAt.comp σ hX.snd
  have hd := (contDiffAt_const (c:=(1:ℝ))).sub ((contDiff_dot_pair (k:=1)).contDiffAt.comp σ (hn.prodMk hu))
  have hD := (contDiffAt_const (c:=(1:ℝ))).sub ((contDiff_dot_pair (k:=1)).contDiffAt.comp σ (hn.prodMk ha))
  intro i
  fin_cases i <;> simp only [actualCutoffCoordinates,physicalCutoffCoordinates]
  · exact contDiffAt_const.div ((contDiff_q (k:=1)).contDiffAt.comp σ hY.snd) (q_pos _).ne'
  · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hunit) (by norm_num)).ne'
  · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hunit) (by norm_num)).ne'
  · exact hr.div_const _

lemma PhaseFlowOn.actual_selectedCutoff_contDiffAt {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) (Q : Set (Fin 4→ℕ)) :
    ContDiffAt ℝ 1 (fun r=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY r)) σ :=
  contDiffAt_selectedDyadicCutoff_curve (by simp)
    (F.actualCutoffCoordinates_contDiffAt hs zX zY hσ hne)
    (F.actualCutoffCoordinates_pos zX zY hσ hne) Q

lemma PhaseFlowOn.actual_selectedCutoff_absoluteContinuous {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c,(F.flow zX r).1≠(F.flow zY r).1) (Q : Set (Fin 4→ℕ)) :
    AbsolutelyContinuousOnInterval
      (fun r=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY r)) b c := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  intro r hr
  exact (F.actual_selectedCutoff_contDiffAt hs zX zY (hS hr) (hne r hr) Q).contDiffWithinAt

lemma PhaseFlowOn.actual_selected_weighted_identity {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c,(F.flow zX r).1≠(F.flow zY r).1)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {W W' : ℝ→Vec→L[ℝ]Vec}
    (hψ : AbsolutelyContinuousOnInterval ψ b c)
    (hW : ContDiffOn ℝ 1 W (uIcc b c)) (hW' : ContinuousOn W' (uIcc b c))
    (hWd : ∀ r∈uIoo b c,HasDerivAt W (W' r) r) :
    let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY σ)
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in b..c,(ψ σ*χ σ) • W σ (signedForceKernel (r σ) (a σ) (u σ) (n σ)
      (phaseAcceleration s.E s.B F.flow zY σ)) =
      (ψ b*χ b) • W b (retardedPrimitive (r b) (a b) (u b) (n b)) -
      (ψ c*χ c) • W c (retardedPrimitive (r c) (a c) (u c) (n c)) +
      ∫ σ in b..c,deriv (fun ξ=>ψ ξ*χ ξ) σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ)) +
        (ψ σ*χ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ)) +
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  exact F.actual_weighted_signed_identity hs zX zY hS hne
    (hψ.mul (F.actual_selectedCutoff_absoluteContinuous hs zX zY hS hne Q)) hW hW' hWd

end RVM

end

end OAI
