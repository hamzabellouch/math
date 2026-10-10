import Mathlib
import OAI.Geometry.NearbyLagrangian.HamiltonianFlow
import OAI.Geometry.NearbyLagrangian.CotangentModel

namespace OAI

/-! Reversal, flattening and uniform bounds for compact Hamiltonian isotopies. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian
open scoped Manifold ContDiff Topology
open Set Function ContinuousLinearMap

lemma antisymmetric_CLM_neg_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (D : V →L[ℝ] V →L[ℝ] ℝ) (u v : V) :
    D (A (-u)) (A v) - D (A v) (A (-u)) = -(D (A u) (A v) - D (A v) (A u)) := by
  simp only [map_neg, neg_apply]
  ring

lemma symplecticForm_neg_left {n : ℕ} (z : Cotangent n)
    (u v : TangentSpace (cotangentModel n) z) :
    symplecticForm z (-u) v = -symplecticForm z u v := by
  exact antisymmetric_CLM_neg_left (V:=CotangentVector n) _ _ u v

def reverseIsotopy {n : ℕ} (φ : ℝ → CotangentDiffeomorph n) (t : ℝ) :
    CotangentDiffeomorph n := (φ 1).symm.trans (φ (1-t))

def reverseHamiltonian {n : ℕ} (H : ℝ → Cotangent n → ℝ) (t : ℝ) : Cotangent n → ℝ :=
  fun z => -H (1-t) z

lemma reverseTime_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 1-t ∈ Icc (0:ℝ) 1 :=
  ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma reverseTimeDerivative {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => 1-s) (Icc (0:ℝ) 1) t =
      -ContinuousLinearMap.id ℝ ℝ := by
  rw [mfderivWithin_eq_fderivWithin]
  have h1 : HasFDerivAt (fun s : ℝ => 1-s) (-ContinuousLinearMap.id ℝ ℝ) t :=
    (hasFDerivAt_id t).const_sub 1
  exact h1.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc (by norm_num) t ht)

section Curve
variable {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
  [TopologicalSpace M] [ChartedSpace H M]
lemma reverseCurveDerivative {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ,ℝ) I ∞ c (Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (mfderivWithin 𝓘(ℝ,ℝ) I (fun s => c (1-s)) (Icc (0:ℝ) 1) t 1 : V) =
      -(mfderivWithin 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) (1-t) 1) := by
  have hu := (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1) t ht)
  have hrev : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => 1-s) :=
    contMDiff_const.sub contMDiff_id
  have hr := hrev.mdifferentiableWithinAt (s:=Icc (0:ℝ) 1) (x:=t) (by simp)
  have hd := mfderivWithin_comp (I:=𝓘(ℝ,ℝ)) (I':=𝓘(ℝ,ℝ)) (I'':=I) t
    ((hc (1-t) (reverseTime_mem ht)).mdifferentiableWithinAt (by simp)) hr
    (fun s hs => reverseTime_mem hs) hu.uniqueMDiffWithinAt
  change ((mfderivWithin 𝓘(ℝ,ℝ) I (c ∘ (fun s : ℝ => 1-s)) (Icc (0:ℝ) 1) t) 1) = _
  rw [hd,reverseTimeDerivative ht]
  let A : ℝ →L[ℝ] V := mfderivWithin 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) (1-t)
  change A (-1) = -(A 1)
  exact map_neg A 1
lemma scalarDerivative_neg (f : M → ℝ) (x : M) (v : V) :
    mfderiv I 𝓘(ℝ,ℝ) (-f) x v = -(mfderiv I 𝓘(ℝ,ℝ) f x v) := by
  rw [mfderiv_neg]
  rfl
end Curve

lemma reverseIsotopy_velocity {n : ℕ} {φ : ℝ → CotangentDiffeomorph n}
    (hφ : ContMDiffOn (𝓘(ℝ,ℝ).prod (cotangentModel n)) (cotangentModel n) ∞
      (fun tz : ℝ × Cotangent n => φ tz.1 tz.2) (Icc (0:ℝ) 1 ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (z : Cotangent n) :
    (mfderivWithin 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => reverseIsotopy φ s z)
      (Icc (0:ℝ) 1) t 1) =
      -(mfderivWithin 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => φ s ((φ 1).symm z))
        (Icc (0:ℝ) 1) (1-t) 1) := by
  have hc : ContMDiffOn 𝓘(ℝ,ℝ) (cotangentModel n) ∞
      (fun s => φ s ((φ 1).symm z)) (Icc (0:ℝ) 1) :=
    hφ.comp ((contMDiff_id.prodMk contMDiff_const).contMDiffOn)
      (fun s hs => ⟨hs,mem_univ _⟩)
  exact reverseCurveDerivative (cotangentModel n) hc ht

theorem IsCompactHamiltonianIsotopy.reverse {n : ℕ}
    {H : ℝ → Cotangent n → ℝ} {φ : ℝ → CotangentDiffeomorph n}
    (h : IsCompactHamiltonianIsotopy H φ) :
    IsCompactHamiltonianIsotopy (reverseHamiltonian H) (reverseIsotopy φ) := by
  rcases h with ⟨hH,hφ,⟨K,hK,hKs⟩,h0,heq⟩
  have hT : ContMDiff (𝓘(ℝ,ℝ).prod (cotangentModel n))
      (𝓘(ℝ,ℝ).prod (cotangentModel n)) ∞
      (fun tz : ℝ × Cotangent n => (1-tz.1,tz.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hT' : ContMDiff (𝓘(ℝ,ℝ).prod (cotangentModel n))
      (𝓘(ℝ,ℝ).prod (cotangentModel n)) ∞
      (fun tz : ℝ × Cotangent n => (1-tz.1,(φ 1).symm tz.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk ((φ 1).symm.contMDiff.comp contMDiff_snd)
  refine ⟨?_,?_,⟨K,hK,?_⟩,?_,?_⟩
  · exact (hH.comp hT.contMDiffOn (fun tz htz => ⟨reverseTime_mem htz.1,mem_univ _⟩)).neg
  · exact hφ.comp hT'.contMDiffOn (fun tz htz => ⟨reverseTime_mem htz.1,mem_univ _⟩)
  · intro t ht z hz
    exact hKs (1-t) (reverseTime_mem ht) (by simpa [reverseHamiltonian] using hz)
  · intro z
    change φ (1-0) ((φ 1).symm z) = z
    simp
  · intro t ht z v
    change CotangentVector n at v
    rw [reverseIsotopy_velocity hφ ht z]
    change symplecticForm (φ (1-t) ((φ 1).symm z))
      (-(mfderivWithin 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => φ s ((φ 1).symm z))
        (Icc (0:ℝ) 1) (1-t) 1)) v = _
    erw [symplecticForm_neg_left]
    erw [heq (1-t) (reverseTime_mem ht)]
    change -(-(mfderiv (cotangentModel n) 𝓘(ℝ,ℝ) (H (1-t)) _ v)) =
      -(mfderiv (cotangentModel n) 𝓘(ℝ,ℝ) (-H (1-t)) _ v)
    exact (congrArg (fun r : ℝ => -r)
      (scalarDerivative_neg (cotangentModel n) (H (1-t))
        (φ (1-t) ((φ 1).symm z)) v)).symm

theorem reverseIsotopy_range_endpoint {n : ℕ} {φ : ℝ → CotangentDiffeomorph n}
    (h0 : ∀ z, φ 0 z = z) {i : Base n → Cotangent n}
    (hr : range (fun q : Base n => φ 1 (zeroSection q)) = range i) :
    range (fun q => reverseIsotopy φ 1 (i q)) = range (zeroSection (n:=n)) := by
  have he : (fun z => reverseIsotopy φ 1 z) = (fun z => (φ 1).symm z) := by
    funext z
    change φ (1-1) ((φ 1).symm z) = _
    simpa using h0 ((φ 1).symm z)
  simp_rw [congrFun he]
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    have hq : i q ∈ range (fun q : Base n => φ 1 (zeroSection q)) := hr.symm ▸ mem_range_self q
    rcases hq with ⟨q',heq⟩
    refine ⟨q',?_⟩
    change zeroSection q' = (φ 1).symm (i q)
    change φ 1 (zeroSection q') = i q at heq
    rw [← heq]
    exact ((φ 1).symm_apply_apply (zeroSection q')).symm
  · rintro ⟨q,rfl⟩
    have hq : φ 1 (zeroSection q) ∈ range i := hr ▸ mem_range_self q
    rcases hq with ⟨q',heq⟩
    exact ⟨q',by change (φ 1).symm (i q') = zeroSection q; rw [heq]; exact (φ 1).symm_apply_apply (zeroSection q)⟩

end NearbyLagrangian

namespace NearbyLagrangian
open scoped Manifold ContDiff Topology
open Set Function ContinuousLinearMap Transport

lemma antisymmetric_CLM_smul_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (D : V →L[ℝ] V →L[ℝ] ℝ) (r : ℝ) (u v : V) :
    D (A (r • u)) (A v) - D (A v) (A (r • u)) =
      r * (D (A u) (A v) - D (A v) (A u)) := by
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

lemma symplecticForm_smul_left {n : ℕ} (z : Cotangent n) (r : ℝ)
    (u v : TangentSpace (cotangentModel n) z) :
    symplecticForm z (r • u) v = r * symplecticForm z u v :=
  antisymmetric_CLM_smul_left (V:=CotangentVector n) _ _ r u v

section Curve
variable {V A M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] (I : ModelWithCorners ℝ V A)
  [TopologicalSpace M] [ChartedSpace A M]

lemma smoothCurveDerivative {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ,ℝ) I ∞ c (Icc (0:ℝ) 1)) (t : ℝ) :
    (mfderiv 𝓘(ℝ,ℝ) I (c ∘ Real.smoothTransition) t 1 : V) =
      deriv Real.smoothTransition t •
        (mfderivWithin 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) (Real.smoothTransition t) 1) := by
  have hτ : MDifferentiableWithinAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) Real.smoothTransition univ t :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).contMDiff.mdifferentiableWithinAt (by simp)
  have hd := mfderivWithin_comp (I:=𝓘(ℝ,ℝ)) (I':=𝓘(ℝ,ℝ)) (I'':=I) t
    ((hc _ (smoothTime_mem t)).mdifferentiableWithinAt (by simp)) hτ
    (fun s _ => smoothTime_mem s) (uniqueMDiffWithinAt_univ (I:=𝓘(ℝ,ℝ)) (x:=t))
  rw [mfderivWithin_univ,mfderivWithin_univ,mfderiv_eq_fderiv] at hd
  rw [hd]
  change (mfderivWithin 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) (Real.smoothTransition t))
    (fderiv ℝ Real.smoothTransition t 1) = _
  rw [fderiv_apply_one_eq_deriv]
  let L : ℝ →L[ℝ] V := mfderivWithin 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) (Real.smoothTransition t)
  change L (deriv Real.smoothTransition t) = deriv Real.smoothTransition t • L 1
  simpa only [smul_eq_mul,mul_one] using L.map_smul (deriv Real.smoothTransition t) (1:ℝ)
lemma scalarDerivative_const_mul {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f x) (r : ℝ) (v : V) :
    mfderiv I 𝓘(ℝ,ℝ) (fun y => r * f y) x v = r • (mfderiv I 𝓘(ℝ,ℝ) f x v : ℝ) := by
  change mfderiv I 𝓘(ℝ,ℝ) (r • f) x v = _
  rw [const_smul_mfderiv hf r]
  rfl

lemma timeSlice_mdifferentiable {H : ℝ → M → ℝ}
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun tz : ℝ × M => H tz.1 tz.2) (Icc (0:ℝ) 1 ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : M) : MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) x :=
  (hH.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
    (fun _ => ⟨ht,mem_univ _⟩)).mdifferentiableAt (by simp)
end Curve

def flattenIsotopy {n : ℕ} (φ : ℝ → CotangentDiffeomorph n) (t : ℝ) :
    CotangentDiffeomorph n := φ (Real.smoothTransition t)

def flattenHamiltonian {n : ℕ} (H : ℝ → Cotangent n → ℝ) (t : ℝ) (z : Cotangent n) : ℝ :=
  deriv Real.smoothTransition t * H (Real.smoothTransition t) z

lemma contMDiff_flattenIsotopy {n : ℕ} {φ : ℝ → CotangentDiffeomorph n}
    (hφ : ContMDiffOn (𝓘(ℝ,ℝ).prod (cotangentModel n)) (cotangentModel n) ∞
      (fun tz : ℝ × Cotangent n => φ tz.1 tz.2) (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContMDiff (𝓘(ℝ,ℝ).prod (cotangentModel n)) (cotangentModel n) ∞
      (fun tz : ℝ × Cotangent n => flattenIsotopy φ tz.1 tz.2) :=
  hφ.comp_contMDiff
    ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
    (fun z => ⟨smoothTime_mem z.1,mem_univ _⟩)

lemma contMDiff_flattenHamiltonian {n : ℕ} {H : ℝ → Cotangent n → ℝ}
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod (cotangentModel n)) 𝓘(ℝ,ℝ) ∞
      (fun tz : ℝ × Cotangent n => H tz.1 tz.2) (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContMDiff (𝓘(ℝ,ℝ).prod (cotangentModel n)) 𝓘(ℝ,ℝ) ∞
      (fun tz : ℝ × Cotangent n => flattenHamiltonian H tz.1 tz.2) := by
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (hd.contMDiff.comp contMDiff_fst).mul
    (hH.comp_contMDiff
      ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
      (fun z => ⟨smoothTime_mem z.1,mem_univ _⟩))

lemma flattenIsotopy_velocity {n : ℕ} {φ : ℝ → CotangentDiffeomorph n}
    (hφ : ContMDiffOn (𝓘(ℝ,ℝ).prod (cotangentModel n)) (cotangentModel n) ∞
      (fun tz : ℝ × Cotangent n => φ tz.1 tz.2) (Icc (0:ℝ) 1 ×ˢ univ)) (t : ℝ) (z : Cotangent n) :
    (mfderiv 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => flattenIsotopy φ s z) t 1 : CotangentVector n) =
      deriv Real.smoothTransition t •
        (mfderivWithin 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => φ s z)
          (Icc (0:ℝ) 1) (Real.smoothTransition t) 1) := by
  have hc : ContMDiffOn 𝓘(ℝ,ℝ) (cotangentModel n) ∞
      (fun s => φ s z) (Icc (0:ℝ) 1) :=
    hφ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs => ⟨hs,mem_univ _⟩)
  exact smoothCurveDerivative (cotangentModel n) hc t

theorem IsCompactHamiltonianIsotopy.flatten_equation {n : ℕ}
    {H : ℝ → Cotangent n → ℝ} {φ : ℝ → CotangentDiffeomorph n}
    (h : IsCompactHamiltonianIsotopy H φ) (t : ℝ) (z : Cotangent n)
    (v : TangentSpace (cotangentModel n) (flattenIsotopy φ t z)) :
    symplecticForm (flattenIsotopy φ t z)
      (mfderiv 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => flattenIsotopy φ s z) t 1) v =
      -mfderiv (cotangentModel n) 𝓘(ℝ,ℝ) (flattenHamiltonian H t) (flattenIsotopy φ t z) v := by
  rcases h with ⟨hH,hφ,hK,h0,heq⟩
  change CotangentVector n at v
  rw [flattenIsotopy_velocity hφ t z]
  change symplecticForm (φ (Real.smoothTransition t) z)
    (deriv Real.smoothTransition t •
      (mfderivWithin 𝓘(ℝ,ℝ) (cotangentModel n) (fun s => φ s z)
        (Icc (0:ℝ) 1) (Real.smoothTransition t) 1)) v = _
  erw [symplecticForm_smul_left,heq _ (smoothTime_mem t)]
  change deriv Real.smoothTransition t •
    (-(mfderiv (cotangentModel n) 𝓘(ℝ,ℝ) (H (Real.smoothTransition t)) _ v : ℝ)) =
      -(mfderiv (cotangentModel n) 𝓘(ℝ,ℝ)
        (fun x => deriv Real.smoothTransition t * H (Real.smoothTransition t) x) _ v)
  rw [scalarDerivative_const_mul (cotangentModel n)
    (timeSlice_mdifferentiable (cotangentModel n) hH (smoothTime_mem t) _)]
  exact smul_neg _ _

end NearbyLagrangian

namespace NearbyLagrangian
open scoped Manifold ContDiff Topology
open Set Function Transport

lemma flattenIsotopy_zero {n : ℕ} (φ : ℝ → CotangentDiffeomorph n) :
    flattenIsotopy φ 0 = φ 0 := by
  simp only [flattenIsotopy,Real.smoothTransition.zero]

lemma flattenIsotopy_one {n : ℕ} (φ : ℝ → CotangentDiffeomorph n) :
    flattenIsotopy φ 1 = φ 1 := by
  simp only [flattenIsotopy,Real.smoothTransition.one]

theorem IsCompactHamiltonianIsotopy.flatten {n : ℕ}
    {H : ℝ → Cotangent n → ℝ} {φ : ℝ → CotangentDiffeomorph n}
    (h : IsCompactHamiltonianIsotopy H φ) :
    IsCompactHamiltonianIsotopy (flattenHamiltonian H) (flattenIsotopy φ) := by
  refine ⟨(contMDiff_flattenHamiltonian h.1).contMDiffOn,
    (contMDiff_flattenIsotopy h.2.1).contMDiffOn,?_,?_,?_⟩
  · obtain ⟨K,hK,hS⟩ := h.2.2.1
    refine ⟨K,hK,fun t _ z hz => hS _ (smoothTime_mem t) ?_⟩
    exact (mul_ne_zero_iff.mp hz).2
  · intro z
    rw [flattenIsotopy_zero]
    exact h.2.2.2.1 z
  · intro t ht z v
    have hc : MDifferentiableAt 𝓘(ℝ,ℝ) (cotangentModel n)
        (fun s => flattenIsotopy φ s z) t :=
      ((contMDiff_flattenIsotopy h.2.1).comp
        (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
    rw [mfderivWithin_eq_mfderiv
      ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht).uniqueMDiffWithinAt) hc]
    exact h.flatten_equation t z v

end NearbyLagrangian

namespace NearbyLagrangian
open scoped Manifold ContDiff Topology
open Set Function

lemma compact_support_param_bound {T Z : Type*} [TopologicalSpace T] [TopologicalSpace Z]
    {J : Set T} {K : Set Z} (hJ : IsCompact J) (hK : IsCompact K) {H : T → Z → ℝ}
    (hc : ContinuousOn (fun tz : T × Z => H tz.1 tz.2) (J ×ˢ univ))
    (hs : ∀ t ∈ J, support (H t) ⊆ K) :
    ∃ A > (0:ℝ), ∀ t ∈ J, ∀ z, |H t z| ≤ A := by
  have hb := ((hJ.prod hK).image_of_continuousOn (hc.mono (prod_mono_right (subset_univ K)))).isBounded
  obtain ⟨A,hA,hb⟩ := hb.exists_pos_norm_le
  refine ⟨A,hA,?_⟩
  intro t ht z
  by_cases hz : z ∈ K
  · simpa only [Real.norm_eq_abs] using hb (H t z) (⟨(t,z),⟨ht,hz⟩,rfl⟩)
  · have he : H t z = 0 := by
      by_contra he
      exact hz (hs t ht he)
    simp only [he,abs_zero]
    exact hA.le

theorem IsCompactHamiltonianIsotopy.uniform_bound {n : ℕ}
    {H : ℝ → Cotangent n → ℝ} {φ : ℝ → CotangentDiffeomorph n}
    (h : IsCompactHamiltonianIsotopy H φ) :
    ∃ A > (0:ℝ), ∀ t ∈ Icc (0:ℝ) 1, ∀ z, |H t z| ≤ A := by
  obtain ⟨K,hK,hKs⟩ := h.2.2.1
  exact compact_support_param_bound isCompact_Icc hK h.1.continuousOn hKs
end NearbyLagrangian

end

end OAI
