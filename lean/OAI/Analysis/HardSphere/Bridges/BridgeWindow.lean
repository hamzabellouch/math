import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.BridgeScaleTail

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma leg_window_coord {t S C : ℝ} (hS : 0< S) (hC : 0≤ C) (y u : Point)
    (hdis : ‖u-y‖≤ C) (β : Noise) (w q : Time) (hq : (q:ℝ)≤(w:ℝ)) (i : Fin 3) :
    |leg t y u β q i-leg t y u β 0 i|≤
      (w:ℝ)*C+S*incrementFluctuation t S 0 w β := by
  have he : suffixTime 0 q=q := by apply Subtype.ext; simp [suffixTime]
  have hd : |(q:ℝ)*(u i-y i)|≤(w:ℝ)*C := by
    rw [abs_mul,abs_of_nonneg q.property.1]
    exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (u-y) i).trans hdis) q.property.1).trans
      (mul_le_mul_of_nonneg_right hq hC)
  have hn := incrementFluctuation_eval (t:=t) hS 0 w q hq β i
  rw [he] at hn
  have hl := leg_segment_increment t y u β 0 q i
  rw [he] at hl
  simp only [show ((0:Time):ℝ)=0 from rfl,sub_zero,one_mul] at hl
  rw [hl,show leg t y u β 0 i+(q:ℝ)*(u i-y i)+Real.sqrt (2*t)*(β i q-β i 0)-leg t y u β 0 i=(q:ℝ)*(u i-y i)+Real.sqrt (2*t)*(β i q-β i 0) by ring]
  exact (abs_add_le _ _).trans (add_le_add hd hn)

lemma leg_window_diameter {t S C : ℝ} (hS : 0< S) (hC : 0≤ C) (y u : Point)
    (hdis : ‖u-y‖≤ C) (β : Noise) (w : Time) :
    liftedDiameter 0 w (pathCoordinates (leg t y u β))≤
      6*((w:ℝ)*C+S*incrementFluctuation t S 0 w β) := by
  have hR : 0≤(w:ℝ)*C+S*incrementFluctuation t S 0 w β :=
    add_nonneg (mul_nonneg w.property.1 hC) (mul_nonneg hS.le (incrementFluctuation_nonneg hS.le 0 w β))
  have hw (q : Time) : (intervalTime 0 w q:ℝ)≤(w:ℝ) := by
    change (1-(q:ℝ))*0+(q:ℝ)*(w:ℝ)≤(w:ℝ)
    nlinarith [q.property.2,w.property.1]
  have h := liftedDiameter_coord_le (pathCoordinates (leg t y u β)) 0 w
    (mul_nonneg (by norm_num : (0:ℝ)≤2) hR) (fun i s q ↦ by
      have hs := leg_window_coord (t:=t) hS hC y u hdis β w (intervalTime 0 w s) (hw s) i
      have hq := leg_window_coord (t:=t) hS hC y u hdis β w (intervalTime 0 w q) (hw q) i
      change |leg t y u β (intervalTime 0 w s) i-leg t y u β (intervalTime 0 w q) i|≤_
      have he : leg t y u β (intervalTime 0 w s) i-leg t y u β (intervalTime 0 w q) i=
        (leg t y u β (intervalTime 0 w s) i-leg t y u β 0 i)-(leg t y u β (intervalTime 0 w q) i-leg t y u β 0 i) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith))
  linarith

lemma leg_window_tail {t S C : ℝ} (ht : 0≤ t) (hS : 0< S) (hC : 0≤ C) (y u : Point)
    (hdis : ‖u-y‖≤ C) (w : Time) (hdrift : (w:ℝ)*C≤ S/12) (p : ℕ) (hp : p≠0) :
    law {β | S≤ liftedDiameter 0 w (pathCoordinates (leg t y u β))}≤
      ENNReal.ofReal (scaleMoment p t S 0 w)/(ENNReal.ofReal (1/12:ℝ))^p := by
  apply (measure_mono (show {β | S≤ liftedDiameter 0 w (pathCoordinates (leg t y u β))}⊆
    {β | (1/12:ℝ)≤ incrementFluctuation t S 0 w β} from ?_)).trans
    (incrementFluctuation_scale_tail ht hS (by norm_num) 0 w p hp)
  intro β hβ
  have h := leg_window_diameter (t:=t) hS hC y u hdis β w
  change S≤_ at hβ
  change (1/12:ℝ)≤ incrementFluctuation t S 0 w β
  nlinarith

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma torusDistance_nonnegative (L : Length) (x y : Torus L) : 0≤torusDistance L x y := Real.sqrt_nonneg _

abbrev projectPoint (L : Length) (y : Point) : Torus L := fun j ↦ (y j : AddCircle L.val)

def nearestLift (L : Length) (v : Point) (x : Torus L) : Point := fun j ↦
  (((AddCircle.equivIco L.val (-L.val/2)) (x j-(v j : AddCircle L.val))).val)+v j

lemma nearestLift_project (L : Length) (v : Point) (x : Torus L) :
    projectPoint L (nearestLift L v x)=x := by
  ext j
  simp only [projectPoint,nearestLift,AddCircle.coe_add,AddCircle.coe_equivIco,sub_add_cancel]

lemma nearestLift_coord (L : Length) (v : Point) (x : Torus L) (j : Fin 3) :
    |nearestLift L v x j-v j|=dist (x j) (projectPoint L v j) := by
  let z := (AddCircle.equivIco L.val (-L.val/2)) (x j-(v j : AddCircle L.val))
  have hz : |z.val|≤|L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    exact ⟨by linarith [z.property.1],by linarith [z.property.2]⟩
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hz
  rw [AddCircle.coe_equivIco,←dist_eq_norm] at he
  simpa only [nearestLift,add_sub_cancel_right] using he.symm

lemma nearestLift_bound (L : Length) (v : Point) (x : Torus L) {R : ℝ}
    (h : torusDistance L x (projectPoint L v)≤R) : ‖nearestLift L v x-v‖≤R := by
  apply (pi_norm_le_iff_of_nonneg ((torusDistance_nonnegative L x _).trans h)).mpr
  intro j
  change |nearestLift L v x j-v j|≤R
  rw [nearestLift_coord]
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ j).trans h

lemma exists_pathLift_at {L : Length} (ω : ConfigurationPath 1 L) (y : Point)
    (hy : projectPoint L y=ω 0 0) : ∃ζ : EuclideanPath,IsPathLift ω ζ ∧ (fun j ↦ ζ j 0)=y := by
  have hx (j : Fin 3) : ∃ ζ : C(Time,ℝ),(∀s,(ζ s : AddCircle L.val)=ω s 0 j) ∧ ζ 0=y j := by
    let γ : C(Time,AddCircle L.val) := ⟨fun s ↦ ω s 0 j,by fun_prop⟩
    have h0 : γ 0=(y j : AddCircle L.val) := (congrFun hy j).symm
    obtain ⟨ζ,hζ,hζ0⟩ := (AddCircle.isCoveringMap_coe L.val).exists_path_lifts γ (y j) h0
    exact ⟨ζ,(fun s ↦ congrFun hζ s),hζ0⟩
  choose ζ hζ using hx
  exact ⟨ζ,fun j s ↦ (hζ j).1 s,funext (fun j ↦ (hζ j).2)⟩

lemma local_collision_lifts {L : Length} {v x c c₀ : Point}
    (hL : 50<L.val) (hx : ‖x-v‖≤10) (hc₀ : ‖c₀-v‖≤12) (hc : ‖c-c₀‖≤1)
    {r : ℝ} (hh : torusDistance L (projectPoint L x) (projectPoint L c)≤r) : ‖x-c‖≤r := by
  have hr : 0≤r := (torusDistance_nonnegative L _ _).trans hh
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro j
  have hnorm : |x j-c j|≤23 := by
    have hxj := (norm_le_pi_norm (x-v) j).trans hx
    have hcj := (norm_le_pi_norm (c-c₀) j).trans hc
    have hc₀j := (norm_le_pi_norm (c₀-v) j).trans hc₀
    change |x j-v j|≤10 at hxj
    change |c j-c₀ j|≤1 at hcj
    change |c₀ j-v j|≤12 at hc₀j
    have he : x j-c j=(x j-v j)-(c₀ j-v j)-(c j-c₀ j) := by ring
    rw [he]
    exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hxj hc₀j)) hcj)).trans (by norm_num)
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr
    (show |x j-c j|≤|L.val|/2 by rw [abs_of_pos L.property]; linarith)
  rw [AddCircle.coe_sub,←dist_eq_norm] at he
  change |x j-c j|≤r
  rw [←he]
  exact (CellOrbital.dist_coord_le_torusDistance L (projectPoint L x) (projectPoint L c) j).trans hh

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma bridge_start_zero : ∀ᵐβ ∂law,∀j : Fin 3,β j 0=0 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : Fin 3↦bridgeLaw) j).quasiMeasurePreserving.ae
    (bridge_endpoints.mono (fun _ h↦h.1))

lemma leg_confined_of_fluctuation (L : Length) (t : ℝ) (y u v : Point) (β : Noise)
    (hy : ‖y-v‖≤3) (hu : ‖u-v‖≤3) (hzero : ∀j,β j 0=0)
    (hnoise : incrementFluctuation t 1 0 1 β≤1/3) (s : Time) :
    ‖leg t y u β s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y u β s)) (projectPoint L v)≤10 := by
  have hc (j : Fin 3) : |leg t y u β s j-v j|≤10/3 := by
    have hn := incrementFluctuation_eval (t:=t) (by norm_num : (0:ℝ)<1) 0 1 s s.property.2 β j
    have hs : suffixTime 0 s=s := by apply Subtype.ext; simp [suffixTime]
    rw [hs,hzero j,sub_zero,one_mul] at hn
    have hyj : |y j-v j|≤3 := (norm_le_pi_norm (y-v) j).trans hy
    have huj : |u j-v j|≤3 := (norm_le_pi_norm (u-v) j).trans hu
    have hm : |(1-(s:ℝ))*(y j-v j)+(s:ℝ)*(u j-v j)|≤3 := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr s.property.2),abs_of_nonneg s.property.1]
      have h₁ := mul_le_mul_of_nonneg_left hyj (sub_nonneg.mpr s.property.2)
      have h₂ := mul_le_mul_of_nonneg_left huj s.property.1
      linarith
    change |(1-(s:ℝ))*y j+(s:ℝ)*u j+Real.sqrt (2*t)*β j s-v j|≤10/3
    rw [show (1-(s:ℝ))*y j+(s:ℝ)*u j+Real.sqrt (2*t)*β j s-v j=
      ((1-(s:ℝ))*(y j-v j)+(s:ℝ)*(u j-v j))+Real.sqrt (2*t)*β j s by ring]
    exact (abs_add_le _ _).trans (by linarith)
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤10)).mpr
    intro j
    exact (hc j).trans (by norm_num)
  · unfold torusDistance
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ ∑ _j : Fin 3, (10/3:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro j _
        apply (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ)≤10/3)).mpr
        rw [dist_eq_norm, ← AddCircle.coe_sub]
        exact (QuotientAddGroup.norm_mk_le_norm (m := leg t y u β s j-v j)).trans
          (by simpa only [Real.norm_eq_abs] using hc j)
      _ ≤ (10:ℝ)^2 := by norm_num

lemma leg_confinement_tail (L : Length) {t : ℝ} (ht : 0≤ t) (y u v : Point)
    (hy : ‖y-v‖≤3) (hu : ‖u-v‖≤3) (p : ℕ) (hp : p≠0) :
    law {β | ∃s : Time,¬(‖leg t y u β s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y u β s)) (projectPoint L v)≤10)}≤
      ENNReal.ofReal (scaleMoment p t 1 0 1)/(ENNReal.ofReal (1/3:ℝ))^p := by
  apply (measure_mono_ae (show {β | ∃s : Time,¬(‖leg t y u β s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y u β s)) (projectPoint L v)≤10)}≤ᵐ[law]
      {β | (1/3:ℝ)≤ incrementFluctuation t 1 0 1 β} from ?_)).trans
    (incrementFluctuation_scale_tail ht (by norm_num) (by norm_num) 0 1 p hp)
  filter_upwards [bridge_start_zero] with β hβ
  rintro ⟨s,hs⟩
  by_contra hn
  exact hs (leg_confined_of_fluctuation L t y u v β hy hu hβ (le_of_not_ge hn) s)

end HardSphere.Bridge

end
end

end

end OAI
