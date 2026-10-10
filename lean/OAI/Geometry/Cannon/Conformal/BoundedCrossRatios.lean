import Mathlib
import OAI.Geometry.Cannon.Conformal.WeakQSPartialsLocally
import OAI.Geometry.Cannon.Beltrami.Increment

namespace OAI

section
section
section
section
section
section
noncomputable section
namespace CannonMetricQC
open MeasureTheory CannonBeltrami CannonOrientation
open scoped ComplexConjugate

lemma weakQS_ae_complexLinear_holomorphic (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f H)
    (hl : ∀ᵐ x : ℂ, ∃ a : ℂ, ∀ z, fderiv ℝ (f : ℂ → ℂ) x z=a*z) :
    Differentiable ℂ (f : ℂ → ℂ) := by
  have hb : ∀ᵐ x : ℂ, partialBar f x=0 := by
    filter_upwards [hl] with x hx
    obtain ⟨a,ha⟩ := hx
    unfold partialBar
    rw [ha,ha,mul_one]
    have he : Complex.I*(a*Complex.I)= -a := by
      calc
        _ = a*(Complex.I*Complex.I) := by ring
        _ = -a := by simp
    rw [he]; simp
  apply weak_partialBar_zero_holomorphic f.continuous
  intro φ hφ
  rw [(weakQS_partial_integration_by_parts f hH hf φ hφ).2]
  have he : (∫ z, partialBar f z*φ z)=0 := by
    calc
      _ = ∫ z : ℂ, (0:ℂ) := integral_congr_ae (hb.mono (fun _ hh => by rw [hh,zero_mul]))
      _ = 0 := integral_zero _ _
  rw [he,neg_zero]

theorem weakQS_ae_conformal_rigidity (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f H)
    (hc : ∀ᵐ x : ℂ, IsConformalMap (fderiv ℝ (f : ℂ → ℂ) x)) :
    Differentiable ℂ (f : ℂ → ℂ) ∨ Differentiable ℂ (fun z => conj (f z)) := by
  have hd := weakQS_ae_differentiable f hH hf
  rcases conformal_differential_orientation f.continuous f.injective with hp | hn
  · left
    apply weakQS_ae_complexLinear_holomorphic f hH hf
    filter_upwards [hd,hc] with x hx hcx
    obtain ⟨a,-,ha⟩ := hp x hx hcx
    exact ⟨a,ha⟩
  · right
    let F : ℂ ≃ₜ ℂ := f.trans Complex.conjCLE.toHomeomorph
    have hF : WeakQS F H := by
      intro x y z hxyz
      simpa only [F,Homeomorph.trans_apply,ContinuousLinearEquiv.coe_toHomeomorph,
        Complex.conjCLE_apply,Complex.dist_conj_conj] using hf x y z hxyz
    have hl : ∀ᵐ x : ℂ, ∃ a : ℂ, ∀ z, fderiv ℝ (F : ℂ → ℂ) x z=a*z := by
      filter_upwards [hd,hc] with x hx hcx
      obtain ⟨a,-,ha⟩ := hn x hx hcx
      have he : fderiv ℝ (F : ℂ → ℂ) x=
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (f : ℂ → ℂ) x) :=
        (Complex.conjCLE.hasFDerivAt.comp x hx.hasFDerivAt).fderiv
      refine ⟨conj a,fun z => ?_⟩
      rw [he]
      change conj (fderiv ℝ (f : ℂ → ℂ) x z)=conj a*z
      rw [ha,map_mul,starRingEnd_self_apply]
    exact weakQS_ae_complexLinear_holomorphic F hH hF hl
end CannonMetricQC

end
end
noncomputable section
namespace CannonMetricQC
open MeasureTheory CannonConformal
open scoped ComplexConjugate

lemma holomorphic_weakQS_inverse (f : ℂ ≃ₜ ℂ) {J : ℝ}
    (hJ : 0 < J) (hi : WeakQS f.symm J) (hf : Differentiable ℂ (f : ℂ → ℂ)) :
    Differentiable ℂ (f.symm : ℂ → ℂ) := by
  apply weakQS_ae_complexLinear_holomorphic f.symm hJ hi
  filter_upwards [weakQS_ae_differentiable f.symm hJ hi] with y hy
  let L := fderiv ℂ (f : ℂ → ℂ) (f.symm y)
  let B := fderiv ℝ (f.symm : ℂ → ℂ) y
  have hc := ((hf (f.symm y)).hasFDerivAt.restrictScalars ℝ).comp y hy.hasFDerivAt
  have hid : (f : ℂ → ℂ) ∘ (f.symm : ℂ → ℂ)=id := by funext z; simp
  rw [hid] at hc
  have he (z : ℂ) : L (B z)=z := congrArg (fun A : ℂ →L[ℝ] ℂ => A z)
    (hc.unique (hasFDerivAt_id y))
  have hl (v : ℂ) : L v=v*L 1 := by simpa using L.map_smul v (1:ℂ)
  have hp (z : ℂ) : L 1*B z=z := by
    calc
      L 1*B z = B z*L 1 := mul_comm _ _
      _ = L (B z) := (hl _).symm
      _ = z := he z
  have hn : L 1 ≠ 0 := by intro hz; have hh := hp 1; rw [hz,zero_mul] at hh; exact zero_ne_one hh
  refine ⟨(L 1)⁻¹,fun z => ?_⟩
  calc
    B z = (L 1)⁻¹*(L 1*B z) := by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
    _ = (L 1)⁻¹*z := by rw [hp]

lemma WeakQS.post_conj (f : ℂ ≃ₜ ℂ) {H : ℝ} (hf : WeakQS f H) :
    WeakQS (f.trans Complex.conjCLE.toHomeomorph) H := by
  intro x y z hh
  simpa only [Homeomorph.trans_apply,ContinuousLinearEquiv.coe_toHomeomorph,
    Complex.conjCLE_apply,Complex.dist_conj_conj] using hf x y z hh

lemma WeakQS.pre_conj (f : ℂ ≃ₜ ℂ) {H : ℝ} (hf : WeakQS f H) :
    WeakQS (Complex.conjCLE.toHomeomorph.trans f) H := by
  intro x y z hh
  exact hf (conj x) (conj y) (conj z) (by simpa only [Complex.dist_conj_conj] using hh)

theorem weakQS_ae_conformal_affine_or_anti (f : ℂ ≃ₜ ℂ) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hf : WeakQS f H) (hi : WeakQS f.symm J)
    (hc : ∀ᵐ x : ℂ, IsConformalMap (fderiv ℝ (f : ℂ → ℂ) x)) :
    (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z=a*z+b) ∨
    (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z=a*conj z+b) := by
  rcases weakQS_ae_conformal_rigidity f hH hf hc with hp | hn
  · exact Or.inl (biholomorphic_affine f hp (holomorphic_weakQS_inverse f hJ hi hp))
  · let F : ℂ ≃ₜ ℂ := f.trans Complex.conjCLE.toHomeomorph
    have hFi : WeakQS F.symm J := hi.pre_conj f.symm
    obtain ⟨a,b,ha,he⟩ := biholomorphic_affine F hn (holomorphic_weakQS_inverse F hJ hFi hn)
    right
    refine ⟨conj a,conj b,by simpa using ha,?_⟩
    intro z
    have hh := congrArg (starRingEnd ℂ) (he z)
    simpa only [F,Homeomorph.trans_apply,ContinuousLinearEquiv.coe_toHomeomorph,
      Complex.conjCLE_apply,starRingEnd_self_apply,map_add,map_mul] using hh
end CannonMetricQC

end
end
section
section
noncomputable section
namespace CannonMetricQC
open Metric CannonQM

lemma WeakQS.dyadic {f : ℂ → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : WeakQS f H)
    (n : ℕ) (x y z : ℂ) (h : dist x y ≤ 2^n*dist x z) :
    dist (f x) (f y) ≤ H*(H+1)^n*dist (f x) (f z) := by
  induction n generalizing y with
  | zero => simpa using hf x y z (by simpa using h)
  | succ n ihn =>
    let u := midpoint ℝ x y
    have hxu : dist x u=dist x y/2 := by simp [u,dist_left_midpoint,div_eq_mul_inv,mul_comm]
    have hux : dist u x=dist x y/2 := by rw [dist_comm,hxu]
    have huy : dist u y=dist x y/2 := by simp [u,dist_midpoint_right,div_eq_mul_inv,mul_comm]
    have h1 := ihn u (by rw [hxu]; rw [pow_succ] at h; linarith)
    have h2 := hf u y x (by rw [huy,hux])
    rw [dist_comm (f u) (f x)] at h2
    have h3 := dist_triangle (f x) (f u) (f y)
    have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ H+1 by positivity)
    rw [pow_succ]
    nlinarith

lemma WeakQS.bounded_ratios {f : ℂ → ℂ} {H : ℝ} (hH : 0 < H) (hf : WeakQS f H)
    (R : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ x y z : ℂ, dist x y ≤ R*dist x z →
      dist (f x) (f y) ≤ C*dist (f x) (f z) := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1:ℝ) < 2)
  refine ⟨H*(H+1)^n,by positivity,fun x y z h => hf.dyadic hH.le n x y z ?_⟩
  exact h.trans (mul_le_mul_of_nonneg_right hn.le dist_nonneg)

theorem WeakQS.crossRatio_bound (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H)
    (T : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ x y z w : ℂ, Distinct x y z w →
      (crossRatio x y z w : ℝ) ≤ T →
      (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤ C := by
  obtain ⟨B,hB,hb⟩ := hf.bounded_ratios hH (2*max T 1+3)
  refine ⟨B^2,sq_pos_of_pos hB,fun x y z w hh hp => ?_⟩
  have hden : 0 < dist x w*dist y z := mul_pos (dist_pos.mpr hh.2.2.1)
    (dist_pos.mpr hh.2.2.2.1)
  have hprod : dist x y*dist z w ≤ max T 1*(dist x w*dist y z) := by
    apply (div_le_iff₀ hden).mp
    exact hp.trans (le_max_left _ _)
  have hfh := hh.map f.injective
  have hfden : 0 < dist (f x) (f w)*dist (f y) (f z) :=
    mul_pos (dist_pos.mpr hfh.2.2.1) (dist_pos.mpr hfh.2.2.2.1)
  change dist (f x) (f y)*dist (f z) (f w)/(dist (f x) (f w)*dist (f y) (f z)) ≤ B^2
  apply (div_le_iff₀ hfden).mpr
  rcases crossRatio_pair_bounds x y z w hh (le_max_right _ _) hprod with h | h
  · have h1 := hb x y w h.1
    have h2 := hb z w y (by simpa only [dist_comm] using h.2)
    rw [dist_comm (f z) (f y)] at h2
    nlinarith [mul_le_mul h1 h2 dist_nonneg (by positivity : 0 ≤ B*dist (f x) (f w))]
  · have h1 := hb y x z (by simpa only [dist_comm] using h.1)
    have h2 := hb w z x (by simpa only [dist_comm] using h.2)
    rw [dist_comm (f y) (f x)] at h1
    rw [dist_comm (f w) (f z),dist_comm (f w) (f x)] at h2
    nlinarith [mul_le_mul h1 h2 dist_nonneg (by positivity : 0 ≤ B*dist (f y) (f z))]

end CannonMetricQC

end
end
noncomputable section
namespace CannonQM
open Set Metric Filter Bornology Topology

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

def BoundedCrossRatios (f : X → Y) : Prop :=
  ∀ T : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x y z w : X, Distinct x y z w →
    (crossRatio x y z w : ℝ) ≤ T → (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤ C

lemma BoundedCrossRatios.comp {f : X → Y} {g : Y → Z}
    (hg : BoundedCrossRatios g) (hf : BoundedCrossRatios f) (hi : Function.Injective f) :
    BoundedCrossRatios (g ∘ f) := by
  intro T
  obtain ⟨B,hB,hb⟩ := hf T
  obtain ⟨C,hC,hc⟩ := hg B
  exact ⟨C,hC,fun x y z w hh hp => hc _ _ _ _ (hh.map hi) (hb _ _ _ _ hh hp)⟩

lemma Controlled.boundedCrossRatios {f : X → Y} {η : Distortion} (hf : Controlled f η) :
    BoundedCrossRatios f := by
  intro T
  refine ⟨(η T.toNNReal:ℝ)+1,by positivity,?_⟩
  intro x y z w hh hp
  have ht : crossRatio x y z w ≤ T.toNNReal := by
    exact_mod_cast hp.trans (Real.le_coe_toNNReal T)
  have hc := (hf x y z w hh).trans (η.monotone ht)
  have hc' := NNReal.coe_le_coe.mpr hc
  linarith

lemma isOpen_distinct_quad : IsOpen {p : Fin 4 → X | Distinct (p 0) (p 1) (p 2) (p 3)} := by
  exact (isOpen_ne_fun (continuous_apply 0) (continuous_apply 1)).inter
    ((isOpen_ne_fun (continuous_apply 0) (continuous_apply 2)).inter
    ((isOpen_ne_fun (continuous_apply 0) (continuous_apply 3)).inter
    ((isOpen_ne_fun (continuous_apply 1) (continuous_apply 2)).inter
    ((isOpen_ne_fun (continuous_apply 1) (continuous_apply 3)).inter
      (isOpen_ne_fun (continuous_apply 2) (continuous_apply 3))))))

lemma boundedCrossRatios_dense {α : Type*} (e : α → X) (he : DenseRange e)
    (f : X → Y) (hf : Continuous f) (hi : Function.Injective f)
    (h : ∀ T : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ p : Fin 4 → α,
      Distinct (e (p 0)) (e (p 1)) (e (p 2)) (e (p 3)) →
      (crossRatio (e (p 0)) (e (p 1)) (e (p 2)) (e (p 3)) : ℝ) ≤ T →
      (crossRatio (f (e (p 0))) (f (e (p 1))) (f (e (p 2))) (f (e (p 3))) : ℝ) ≤ C) :
    BoundedCrossRatios f := by
  intro T
  obtain ⟨C,hC,hc⟩ := h (T+1)
  refine ⟨C,hC,?_⟩
  intro x y z w hh hp
  by_contra hn
  have hn' : C < (crossRatio (f x) (f y) (f z) (f w) : ℝ) := lt_of_not_ge hn
  let p : Fin 4 → X := ![x,y,z,w]
  let a : (Fin 4 → X) → ℝ := fun q => dist (q 0) (q 1)*dist (q 2) (q 3)
  let b : (Fin 4 → X) → ℝ := fun q => dist (q 0) (q 3)*dist (q 1) (q 2)
  let c : (Fin 4 → X) → ℝ := fun q => dist (f (q 0)) (f (q 1))*dist (f (q 2)) (f (q 3))
  let d : (Fin 4 → X) → ℝ := fun q => dist (f (q 0)) (f (q 3))*dist (f (q 1)) (f (q 2))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hc' : Continuous c := by dsimp [c]; fun_prop
  have hd : Continuous d := by dsimp [d]; fun_prop
  let U : Set (Fin 4 → X) := {q | Distinct (q 0) (q 1) (q 2) (q 3)} ∩
    {q | a q < (T+1)*b q} ∩ {q | C*d q < c q}
  have hU : IsOpen U := (isOpen_distinct_quad.inter (isOpen_lt ha (continuous_const.mul hb))).inter
    (isOpen_lt (continuous_const.mul hd) hc')
  have hden : 0 < dist x w*dist y z := mul_pos (dist_pos.mpr hh.2.2.1)
    (dist_pos.mpr hh.2.2.2.1)
  have hfh := hh.map hi
  have hfden : 0 < dist (f x) (f w)*dist (f y) (f z) := mul_pos
    (dist_pos.mpr hfh.2.2.1) (dist_pos.mpr hfh.2.2.2.1)
  have hpU : p ∈ U := by
    refine ⟨⟨hh,?_⟩,?_⟩
    · have hhh := (div_lt_iff₀ hden).mp (lt_of_le_of_lt hp (by linarith : T < T+1))
      exact hhh
    · exact (lt_div_iff₀ hfden).mp hn'
  have hde : DenseRange (fun q : Fin 4 → α => fun i => e (q i)) := DenseRange.piMap (fun _ => he)
  obtain ⟨q,hq⟩ := hde.exists_mem_open hU ⟨p,hpU⟩
  have hhq := hq.1.1
  have hdq : 0 < dist (e (q 0)) (e (q 3))*dist (e (q 1)) (e (q 2)) :=
    mul_pos (dist_pos.mpr hhq.2.2.1) (dist_pos.mpr hhq.2.2.2.1)
  have hFq := hhq.map hi
  have hdfq : 0 < dist (f (e (q 0))) (f (e (q 3)))*dist (f (e (q 1))) (f (e (q 2))) :=
    mul_pos (dist_pos.mpr hFq.2.2.1) (dist_pos.mpr hFq.2.2.2.1)
  have hcrq : (crossRatio (e (q 0)) (e (q 1)) (e (q 2)) (e (q 3)) : ℝ) ≤ T+1 :=
    ((div_lt_iff₀ hdq).mpr hq.1.2).le
  have hbound := hc q hhq hcrq
  have hviol : C < (crossRatio (f (e (q 0))) (f (e (q 1))) (f (e (q 2))) (f (e (q 3))) : ℝ) :=
    (lt_div_iff₀ hdfq).mpr hq.2
  exact not_lt_of_ge hbound hviol

end CannonQM

namespace CannonMobius
open CannonQM CannonMetricQC Set
open scoped OnePoint

theorem weakQS_sphere_boundedCrossRatios (F : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hF : WeakQS F H) : BoundedCrossRatios F.onePointCongr := by
  apply boundedCrossRatios_dense (fun z : ℂ => (z:Sphere)) OnePoint.denseRange_coe
    F.onePointCongr F.onePointCongr.continuous F.onePointCongr.injective
  intro T
  obtain ⟨C,hC,hc⟩ := hF.crossRatio_bound F hH T
  refine ⟨C,hC,fun p hh hp => ?_⟩
  have hhp : Distinct (p 0) (p 1) (p 2) (p 3) := by
    rcases hh with ⟨h1,h2,h3,h4,h5,h6⟩
    exact ⟨fun he => h1 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h2 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h3 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h4 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h5 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h6 (congrArg (fun z : ℂ => (z:Sphere)) he)⟩
  have hpp : (crossRatio (p 0) (p 1) (p 2) (p 3) : ℝ) ≤ T := by simpa only [coe_crossRatio] using hp
  change (crossRatio ((F (p 0):ℂ):Sphere) ((F (p 1):ℂ):Sphere) ((F (p 2):ℂ):Sphere) ((F (p 3):ℂ):Sphere) : ℝ) ≤ C
  simpa only [coe_crossRatio] using hc _ _ _ _ hhp hpp

lemma boundedCrossRatios_restriction (f : Sphere ≃ₜ Sphere) (hi : f ∞=∞)
    (hf : BoundedCrossRatios f) : BoundedCrossRatios (finiteRestriction f hi) := by
  intro T
  obtain ⟨C,hC,hc⟩ := hf T
  refine ⟨C,hC,fun x y z w hh hp => ?_⟩
  have he (u : ℂ) : f (u:Sphere)=((finiteRestriction f hi u:ℂ):Sphere) :=
    (coe_coordinate (coe_map_ne_infty f hi u)).symm
  have hh' := hh.map (OnePoint.coe_injective (X:=ℂ))
  have h := hc (x:Sphere) (y:Sphere) (z:Sphere) (w:Sphere) hh' (by simpa only [coe_crossRatio] using hp)
  simpa only [he,coe_crossRatio] using h

end CannonMobius

end
end
end
end
end
end

end OAI
