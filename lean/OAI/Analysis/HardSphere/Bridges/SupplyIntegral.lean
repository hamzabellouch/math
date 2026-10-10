import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSuccess

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance
attribute [local instance] Classical.propDecidable

def SuccessExcept {L : Length} {N : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin N → ConfigurationPath 1 L) (i : Fin N) : Set C(Time,Point) :=
  {f | TrialCutoff L n r R C w S v f ∧ ∀j,j≠i → ¬TrialCollision r (ω j) f}

lemma successExcept_measurable {L : Length} {N : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin N → ConfigurationPath 1 L) (i : Fin N) :
    MeasurableSet (SuccessExcept n r R C S w v ω i) := by
  have h : MeasurableSet {f | ∀j,j≠i → ¬TrialCollision r (ω j) f} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ (trialCollision_closed r (ω j)).measurableSet.compl
  exact (trialCutoff_measurable L n r R C w S v).inter h

lemma trial_no_collision_far {L : Length} {n : ℕ} {r R C S : ℝ} {w : Time} {v : Point}
    {f : C(Time,Point)} (hf : TrialCutoff L n r R C w S v f) (hr : r≤1)
    (ω : ConfigurationPath 1 L) (hω : ∀s,12<torusDistance L (ω s 0) (projectPoint L v)) :
    ¬TrialCollision r ω f := by
  rintro ⟨s,hs⟩
  have htri := torusDistance_triangle' L (ω s 0) (projectPoint L (f s)) (projectPoint L v)
  have hd := (hf.2 s).2
  rw [torusDistance_comm L (ω s 0) (projectPoint L (f s))] at htri
  linarith [hω s]

lemma failure_except_le {L : Length} {N : ℕ} (n : ℕ) (t r R C S : ℝ)
    (w : Time) (y z v u : Point) (ω : Fin N → ConfigurationPath 1 L) (i : Fin N)
    (J : Finset (Fin N)) (hfar : ∀j,j∉J → ∀f,TrialCutoff L n r R C w S v f → ¬TrialCollision r (ω j) f) :
    trialKernel t y z u (SuccessExcept n r R C S w v ω i)ᶜ≤
      trialKernel t y z u {f | ¬TrialCutoff L n r R C w S v f}+
      ∑j∈J, if j=i then 0 else trialKernel t y z u {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r (ω j) f} := by
  let E := fun j ↦ if j=i then (∅ : Set C(Time,Point)) else {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r (ω j) f}
  have hsub : (SuccessExcept n r R C S w v ω i)ᶜ⊆
      {f | ¬TrialCutoff L n r R C w S v f} ∪ ⋃j∈J,E j := by
    intro f hf
    by_cases hc : TrialCutoff L n r R C w S v f
    · right
      have hh : ¬∀j,j≠i → ¬TrialCollision r (ω j) f := fun h ↦ hf ⟨hc,h⟩
      push Not at hh
      obtain ⟨j,hji,hj⟩ := hh
      have hJ : j∈J := by by_contra hn; exact hfar j hn f hc hj
      exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hJ,by simp [E,hji,hc,hj]⟩⟩
    · exact Or.inl hc
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  have h := measure_biUnion_finset_le J E (μ:=trialKernel t y z u)
  convert h using 1
  congr 1
  funext index
  by_cases hji : index=i <;> simp [E,hji]

lemma failure_integral_sum {L : Length} {N m : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L) (label : Fin m → Fin N)
    (J : Finset (Fin N)) {B : Set Point} (hB : MeasurableSet B) (hBvol : volume B≤1)
    (hfar : ∀j,j∉J → ∀f,TrialCutoff L n r R C w S v f → ¬TrialCollision r (ω j) f)
    (δ ζ : ℝ≥0∞)
    (hcut : ∀i u,u∈B → trialKernel t (y i) (z i) u {f | ¬TrialCutoff L n r R C w S v f}≤δ)
    (hhit : ∀j∈J, (∑i∈Finset.univ.filter (fun i ↦ j≠label i),
      ((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R C S (y i) (z i) v B w (ω j)))≤ζ) :
    (∑i,∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      (m:ℝ≥0∞)*δ+(J.card:ℝ≥0∞)*ζ := by
  classical
  let H := fun i j ↦ ((volume.restrict B).prod (law.prod law))
      (trialCutoffHit n t r R C S (y i) (z i) v B w (ω j))
  have hi (i : Fin m) : (∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      δ+∑j∈J,if j=label i then 0 else H i j := by
    apply (lintegral_mono fun u ↦ failure_except_le n t r R C S w (y i) (z i) v u ω (label i) J hfar).trans
    have hcm : MeasurableSet {f | ¬TrialCutoff L n r R C w S v f} := (trialCutoff_measurable L n r R C w S v).compl
    rw [lintegral_add_left ((trialKernel t (y i) (z i)).measurable_coe hcm)]
    apply add_le_add
    · calc
        _ ≤ ∫⁻_ in B,δ := lintegral_mono_ae (by filter_upwards [ae_restrict_mem hB] with u hu using hcut i u hu)
        _ = δ*volume B := by simp
        _ ≤ δ := by simpa using mul_le_mul_right hBvol δ
    · rw [lintegral_finsetSum' J]
      · apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j=label i
        · simp [hji]
        · simp only [hji,ite_false]
          exact le_of_eq (trialCutoffHit_integral n t r R C S (y i) (z i) v hB w (ω j))
      · intro j hj
        by_cases hji : j=label i
        · simp only [hji,ite_true]; exact measurable_const.aemeasurable
        · simp only [hji,ite_false]
          exact ((trialKernel t (y i) (z i)).measurable_coe
            ((trialCutoff_measurable L n r R C w S v).inter (trialCollision_closed r (ω j)).measurableSet)).aemeasurable
  apply (Finset.sum_le_sum (fun i _ ↦ hi i)).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_comm]
  apply add_le_add le_rfl
  calc
    _ = ∑j∈J,∑i∈Finset.univ.filter (fun i ↦ j≠label i),H i j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hji : j=label i <;> simp [hji]
    _ ≤ ∑_j∈J,ζ := Finset.sum_le_sum (fun j hj ↦ hhit j hj)
    _ = _ := by simp [nsmul_eq_mul]

lemma physical_failure_sum {L : Length} {N m n : ℕ} (hn : 0<n)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
    (label : Fin m → Fin N) (J : Finset (Fin N))
    {t r ε h R C S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hC : 0≤C) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : ∀j∈J,Regular (n+n) r R C (prefixTime midpointTime w) S (ω j))
    (hsmall : r*R≤1) (hτr : t/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ)≤r)
    {B : Set Point} (hB : MeasurableSet B) (hBvol : volume B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (y i)) (ω j 0 0))
    (hz : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (z i)) (ω j 1 0))
    (hfar : ∀j,j∉J → ∀s,12<torusDistance L (ω j s 0) (projectPoint L v))
    (δ : ℝ≥0∞)
    (hcut : ∀i u,u∈B → trialKernel t (y i) (z i) u {f | ¬TrialCutoff L n r R C w S v f}≤δ) :
    (∑i,∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      (m:ℝ≥0∞)*δ+(J.card:ℝ≥0∞)*(2*ENNReal.ofReal
        (hitConstant*(8*C*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2)))) := by
  refine failure_integral_sum n t r R C S w y z v ω label J hB hBvol
    (fun j hj f hf ↦ trial_no_collision_far hf hr1 (ω j) (hfar j hj)) δ _ hcut ?_
  intro j hj
  apply physical_trial_collision_subset hn (Finset.univ.filter (fun i ↦ j≠label i)) y z v (ω j) w
    hL ht hr hr1 hε hR hC hh hw hsepY hsepZ (hreg j hj) hsmall hτr hnscale hwindow hlarge hdrift
    hB hBvol hBv hBY hBZ
  · exact fun i hi ↦ hy j hj i (Finset.mem_filter.mp hi).2
  · exact fun i hi ↦ hz j hj i (Finset.mem_filter.mp hi).2

end HardSphere.Bridge

end
end

end

end OAI
