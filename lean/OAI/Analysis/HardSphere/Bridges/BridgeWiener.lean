import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeHighMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def rawNoise (w : CoordinatePaths 1) : Noise := fun j ↦ w (0,j)
def centeredNoise (w : CoordinatePaths 1) : Noise := fun j ↦ centerMap (rawNoise w j)
lemma rawNoise_preserving : MeasurePreserving rawNoise (coordinateWiener 1)
    (Measure.pi (fun _ : Fin 3 ↦ wiener)) := by
  convert measurePreserving_piCongrLeft (fun _ : Fin 3 ↦ wiener)
    (Equiv.uniqueProd (Fin 3) (Fin 1)) using 1
  · ext w j s
    rfl
  · rfl
lemma centeredNoise_preserving : MeasurePreserving centeredNoise (coordinateWiener 1) law := by
  have hm : Measurable (fun β : Noise ↦ fun j ↦ centerMap (β j)) := by fun_prop
  have he : (Measure.pi (fun _ : Fin 3 ↦ wiener)).map (fun β : Noise ↦ fun j ↦ centerMap (β j))=law := by
    rw [Measure.pi_map_pi (fun _ ↦ centerMap.continuous.measurable.aemeasurable)]
    simp only [←bridgeLaw_center,law]
  exact (show MeasurePreserving (fun β : Noise ↦ fun j ↦ centerMap (β j)) _ law from ⟨hm,he⟩).comp rawNoise_preserving

lemma lifted_coord_le (ζ : EuclideanPath) (a b s q : Time) (i : Fin 3) :
    |ζ i (intervalTime a b s)-ζ i (intervalTime a b q)|≤liftedDiameter a b ζ := by
  have hsq : (ζ i (intervalTime a b s)-ζ i (intervalTime a b q))^2≤
      ∑j,(ζ j (intervalTime a b s)-ζ j (intervalTime a b q))^2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (ζ j (intervalTime a b s)-ζ j (intervalTime a b q))) (Finset.mem_univ i)
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at h
  exact h.trans ((le_abs_self _).trans
    (ContinuousMap.norm_coe_le_norm (liftedDiameterMap a b ζ) (s,q)))

lemma centeredNoise_eval (w : CoordinatePaths 1) (j : Fin 3) (s : Time) :
    centeredNoise w j s=w (0,j) s-(s:ℝ)*w (0,j) 1 := by simp [centeredNoise,rawNoise]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def rawPath (t : ℝ) (y : Point) (w : CoordinatePaths 1) : EuclideanPath := fun j ↦
  ⟨fun s ↦ y j+Real.sqrt (2*t)*w (0,j) s,by fun_prop⟩
lemma rawPath_lift (L : Length) (t : ℝ) (y : Point) (w : CoordinatePaths 1) :
    IsPathLift (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))) (rawPath t y w) := by
  intro j s
  change ((y j+Real.sqrt (2*t)*w (0,j) s:ℝ):AddCircle L.val)=_
  simp only [AddCircle.coe_add,freeTrajectory,ContinuousMap.coe_mk]

lemma mesh_time_dist {n : ℕ} (j : Fin n) (s q : Time) :
    |(meshTime j s:ℝ)-(meshTime j q:ℝ)|≤1/(n:ℝ) := by
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  change |((j:ℝ)+(s:ℝ))/(n:ℝ)-((j:ℝ)+(q:ℝ))/(n:ℝ)|≤_
  rw [←sub_div,show (j:ℝ)+(s:ℝ)-((j:ℝ)+(q:ℝ))=(s:ℝ)-(q:ℝ) by ring,abs_div,abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  exact abs_le.mpr ⟨by linarith [s.property.1,q.property.2],by linarith [s.property.2,q.property.1]⟩

lemma centered_leg_mesh_coord {n : ℕ} (j : Fin n) {t r C B : ℝ} (hr : 0<r)
    (y u : Point) (w : CoordinatePaths 1) (hdis : ‖u-y‖≤C) (hw : ∀i,‖w (0,i)‖≤B)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ)≤r) (i : Fin 3) (s q : Time) :
    |leg t y u (centeredNoise w) (meshTime j s) i-leg t y u (centeredNoise w) (meshTime j q) i|≤
      liftedDiameter 0 1 (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩)+r := by
  by_cases htime : s = q
  · rw [htime, sub_self, abs_zero]
    exact add_nonneg (norm_nonneg _) hr.le
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  have hbase := lifted_coord_le (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩) 0 1 s q i
  have hi : |u i-y i-Real.sqrt (2*t)*w (0,i) 1|≤C+Real.sqrt (2*t)*B := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply add_le_add ((norm_le_pi_norm (u-y) i).trans hdis)
    exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm _ 1).trans (hw i)) (Real.sqrt_nonneg _)
  have hinc := mul_le_mul (mesh_time_dist j s q) hi (abs_nonneg _) (by positivity : 0≤1/(n:ℝ))
  have he : 1/(n:ℝ)*(C+Real.sqrt (2*t)*B)=(C+Real.sqrt (2*t)*B)/(n:ℝ) := by ring
  rw [he] at hinc
  have hs : intervalTime 0 1 s=s := by apply Subtype.ext; simp [intervalTime]
  have hq : intervalTime 0 1 q=q := by apply Subtype.ext; simp [intervalTime]
  simp only [hs,hq,ContinuousMap.comp_apply,ContinuousMap.coe_mk,rawPath] at hbase
  have hel : leg t y u (centeredNoise w) (meshTime j s) i-leg t y u (centeredNoise w) (meshTime j q) i=
    ((y i+Real.sqrt (2*t)*w (0,i) (meshTime j s))-(y i+Real.sqrt (2*t)*w (0,i) (meshTime j q)))+
    ((meshTime j s:ℝ)-(meshTime j q:ℝ))*(u i-y i-Real.sqrt (2*t)*w (0,i) 1) := by
    simp only [leg,ContinuousMap.coe_mk,centeredNoise_eval,mean]
    ring
  rw [hel]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact add_le_add hbase (hinc.trans hdrift)

lemma centered_leg_mesh_diameter {n : ℕ} (j : Fin n) {t r C B : ℝ} (hr : 0<r)
    (y u : Point) (w : CoordinatePaths 1) (hdis : ‖u-y‖≤C) (hw : ∀i,‖w (0,i)‖≤B)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ)≤r) :
    liftedDiameter 0 1 (fun k ↦ (pathCoordinates (leg t y u (centeredNoise w)) k).comp ⟨meshTime j,meshTime_continuous j⟩)/r≤
      3*(1+liftedDiameter 0 1 (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩)/r) := by
  apply (div_le_iff₀ hr).mpr
  have hh := liftedDiameter_coord_le
    (fun k ↦ (pathCoordinates (leg t y u (centeredNoise w)) k).comp ⟨meshTime j,meshTime_continuous j⟩) 0 1
    (by unfold liftedDiameter; positivity : 0≤liftedDiameter 0 1 (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩)+r)
    (fun i s q ↦ centered_leg_mesh_coord j hr y u w hdis hw hdrift i (intervalTime 0 1 s) (intervalTime 0 1 q))
  exact hh.trans_eq (by field_simp; ring)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def legCost {n : ℕ} (t r : ℝ) (y u : Point) (j : Fin n) (β : Noise) : ℝ :=
  (1+liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r)^3

def bridgeMeanCost : ℝ := 2744*(1+3072*normCubeMean)
lemma bridgeMeanCost_pos : 0<bridgeMeanCost := by unfold bridgeMeanCost; have := normCubeMean_nonneg; positivity

lemma legCost_bound {n : ℕ} (j : Fin n) {t r C : ℝ} (hr : 0<r)
    (y u : Point) (β : Noise) (hC : 0≤C) (hdis : ‖u-y‖≤C) (hdrift : C/(n:ℝ)≤r) :
    legCost t r y u j β≤2744*(1+(incrementFluctuation t r (meshTime j 0) (meshRemainder j) β)^3) := by
  have h := leg_mesh_diameter j (t:=t) hr y u β hC hdis hdrift
  have hf := incrementFluctuation_nonneg (t:=t) hr.le (meshTime j 0) (meshRemainder j) β
  have hd : 0≤liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r := div_nonneg (norm_nonneg _) hr.le
  have hp := pow_le_pow_left₀ (by linarith : 0≤1+liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r) (show 1+liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r≤7*(1+incrementFluctuation t r (meshTime j 0) (meshRemainder j) β) by linarith) 3
  have hh := loose_add_pow (by norm_num : (0:ℝ)≤1) hf 3
  simp only [one_pow] at hh
  calc
    _ ≤ (7*(1+incrementFluctuation t r (meshTime j 0) (meshRemainder j) β))^3 := hp
    _ = 343*(1+incrementFluctuation t r (meshTime j 0) (meshRemainder j) β)^3 := by ring
    _ ≤ _ := by nlinarith

lemma legCost_moment {n : ℕ} (j : Fin n) {t r C : ℝ} (ht : 0≤t) (hr : 0<r)
    (y u : Point) (hC : 0≤C) (hdis : ‖u-y‖≤C) (hdrift : C/(n:ℝ)≤r)
    (hscale : t/(n:ℝ)≤r^2) :
    ∫⁻β,ENNReal.ofReal (legCost t r y u j β) ∂law≤ENNReal.ofReal bridgeMeanCost := by
  let f := incrementFluctuation t r (meshTime j 0) (meshRemainder j)
  have hi : Integrable (fun β ↦ (f β)^3) law := by
    unfold f incrementFluctuation
    simp only [mul_pow]
    have hh := (incrementSize_memLp_power (meshTime j 0) (meshRemainder j) 3).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
    simp only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg _ _ _)] at hh
    exact hh.const_mul _
  have hm := incrementFluctuation_mean ht hr (meshTime j 0) (meshRemainder j) (by rw [mul_assoc,mesh_remaining]; simpa [div_eq_mul_inv] using hscale)
  calc
    _ ≤ ∫⁻β,ENNReal.ofReal (2744*(1+(f β)^3)) ∂law := lintegral_mono (fun β ↦ ENNReal.ofReal_le_ofReal (legCost_bound j hr y u β hC hdis hdrift))
    _ = ENNReal.ofReal (2744*(1+∫β,(f β)^3 ∂law)) := by
      have hh : Integrable (fun β ↦ 2744*(1+(f β)^3)) law := ((integrable_const 1).add hi).const_mul _
      rw [←ofReal_integral_eq_lintegral_ofReal hh (ae_of_all _ (fun β ↦ by have := incrementFluctuation_nonneg (t:=t) hr.le (meshTime j 0) (meshRemainder j) β; dsimp only [f]; positivity))]
      congr 1
      rw [integral_const_mul,integral_add (integrable_const _) hi,integral_const,probReal_univ,one_smul]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [bridgeMeanCost]; linarith)

end HardSphere.Bridge

end
end

end

end OAI
