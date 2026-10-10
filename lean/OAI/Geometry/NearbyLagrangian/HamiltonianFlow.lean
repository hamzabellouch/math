import Mathlib
import OAI.Geometry.NearbyLagrangian.GeneratingAction
import OAI.Geometry.NearbyLagrangian.Evolution

namespace OAI

/-! Flat time changes and compact Hamiltonian trajectories. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open Set Filter
open scoped ContDiff Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smoothTime_mem (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩

lemma contDiff_flat_time {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContDiff ℝ ∞ (fun z : ℝ × E => f (Real.smoothTransition z.1,z.2)) :=
  hf.comp_contDiff ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
    (fun z => ⟨smoothTime_mem z.1,mem_univ _⟩)

lemma smoothTime_deriv_zero {t : ℝ} (ht : t ∉ Icc (0:ℝ) 1) :
    deriv Real.smoothTransition t = 0 := by
  have hnot : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hnot with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    simpa only [deriv_const] using he.deriv_eq

def flatTimeField (X : ℝ × E → F) (z : ℝ × E) : F :=
  deriv Real.smoothTransition z.1 • X (Real.smoothTransition z.1,z.2)

lemma contDiff_flatTimeField {X : ℝ × E → F}
    (hX : ContDiffOn ℝ ∞ X (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContDiff ℝ ∞ (flatTimeField X) := by
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (hd.comp contDiff_fst).smul (contDiff_flat_time hX)

omit [NormedSpace ℝ E] in

lemma compactSupport_flatTimeField {X : ℝ × E → F} {K : Set E} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => X (t,x)) ⊆ K) :
    HasCompactSupport (flatTimeField X) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod hK)
  intro z hz
  change flatTimeField X z ≠ 0 at hz
  have ht : z.1 ∈ Icc (0:ℝ) 1 := by
    by_contra hn
    exact hz (by rw [flatTimeField,smoothTime_deriv_zero hn,zero_smul])
  refine ⟨ht,hs (Real.smoothTransition z.1) (smoothTime_mem _) ?_⟩
  change X (Real.smoothTransition z.1,z.2) ≠ 0
  intro h
  exact hz (by rw [flatTimeField,h,smul_zero])

lemma flatTime_solution {X : ℝ × E → E} {y : ℝ → E}
    (hy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt y (X (t,y t)) (Icc (0:ℝ) 1) t)
    (t : ℝ) :
    HasDerivAt (fun u => y (Real.smoothTransition u))
      (flatTimeField X (t,y (Real.smoothTransition t))) t := by
  exact (hy _ (smoothTime_mem t)).scomp_hasDerivAt t
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
      (by simp) t).hasDerivAt smoothTime_mem

lemma compact_map_bounds {f : E → F} (hs : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) :
    ∃ L K : ℝ≥0, (∀ x, ‖f x‖ ≤ L) ∧ LipschitzWith K f := by
  obtain ⟨L,hL⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv one_ne_zero)
  let L' : ℝ≥0 := ⟨max L 0,le_max_right _ _⟩
  let K' : ℝ≥0 := ⟨max K 0,le_max_right _ _⟩
  refine ⟨L',K',fun x => (hL x).trans (le_max_left _ _),?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
  intro x
  exact_mod_cast (hK x).trans (le_max_left K 0)

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def symplecticGradient (L : (E × E) →L[ℝ] ℝ) : E × E :=
  ((toDual ℝ E).symm (L.comp (inr ℝ E E)),
    -(toDual ℝ E).symm (L.comp (inl ℝ E E)))

lemma symplecticGradient_zero : symplecticGradient (0 : (E × E) →L[ℝ] ℝ) = 0 := by
  simp only [symplecticGradient,zero_comp,map_zero,neg_zero,Prod.mk_zero_zero]

lemma symplecticGradient_identity (L : (E × E) →L[ℝ] ℝ) (w : E × E) :
    inner ℝ (symplecticGradient L).2 w.1 - inner ℝ w.2 (symplecticGradient L).1 = -L w := by
  simp only [symplecticGradient]
  rw [inner_neg_left,real_inner_comm ((toDual ℝ E).symm (L.comp (inr ℝ E E))) w.2,toDual_symm_apply,toDual_symm_apply]
  simp only [comp_apply,inl_apply,inr_apply]
  have hs : L w = L (w.1,0)+L (0,w.2) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [hs]
  ring

lemma contDiff_symplecticGradient : ContDiff ℝ ∞ (@symplecticGradient E _ _ _) := by
  exact (((toDual ℝ E).symm.contDiff.comp
    (contDiff_id.clm_comp contDiff_const))).prodMk
    (((toDual ℝ E).symm.contDiff.comp
      (contDiff_id.clm_comp contDiff_const)).neg)

def phaseDifferential (H : ℝ × (E × E) → ℝ) (z : ℝ × (E × E)) : (E × E) →L[ℝ] ℝ :=
  fderiv ℝ (fun x => H (z.1,x)) z.2

def hamiltonianField (H : ℝ × (E × E) → ℝ) (z : ℝ × (E × E)) : E × E :=
  symplecticGradient (phaseDifferential H z)

omit [CompleteSpace E] in
lemma phaseDifferential_eq {H : ℝ × (E × E) → ℝ} (hH : Differentiable ℝ H)
    (z : ℝ × (E × E)) :
    phaseDifferential H z = (fderiv ℝ H z).comp (inr ℝ ℝ (E × E)) :=
  ((hH z).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv

lemma contDiff_hamiltonianField {H : ℝ × (E × E) → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamiltonianField H) := by
  have he : phaseDifferential H = fun z => (fderiv ℝ H z).comp (inr ℝ ℝ (E × E)) :=
    funext (phaseDifferential_eq (hH.differentiable (by simp)))
  change ContDiff ℝ ∞ (symplecticGradient ∘ phaseDifferential H)
  rw [he]
  exact contDiff_symplecticGradient.comp ((hH.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const)

lemma hamiltonianField_identity (H : ℝ × (E × E) → ℝ) (z : ℝ × (E × E)) (w : E × E) :
    inner ℝ (hamiltonianField H z).2 w.1 - inner ℝ w.2 (hamiltonianField H z).1 =
      -phaseDifferential H z w := symplecticGradient_identity _ _

lemma hamiltonianField_support {H : ℝ × (E × E) → ℝ} {K : Set (E × E)}
    (hK : IsClosed K) (hs : ∀ t x, x ∉ K → H (t,x) = 0) (t : ℝ) :
    Function.support (fun x => hamiltonianField H (t,x)) ⊆ K := by
  intro x hx
  by_contra hn
  have he : (fun y => H (t,y)) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hn] with y hy
    exact hs t y hy
  apply hx
  change symplecticGradient (fderiv ℝ (fun y => H (t,y)) x) = 0
  rw [he.fderiv_eq]
  change symplecticGradient (fderiv ℝ (Function.const (E × E) (0:ℝ)) x) = 0
  rw [fderiv_const,Pi.zero_apply,symplecticGradient_zero]

lemma compactSupport_hamiltonianField {H : ℝ × (E × E) → ℝ}
    (hH : ContDiff ℝ ∞ H) (hs : HasCompactSupport H) : HasCompactSupport (hamiltonianField H) := by
  apply (hs.fderiv ℝ).mono
  intro z hz
  change hamiltonianField H z ≠ 0 at hz
  change fderiv ℝ H z ≠ 0
  intro h
  apply hz
  rw [hamiltonianField,phaseDifferential_eq (hH.differentiable (by simp)),h,zero_comp,
    symplecticGradient_zero]

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symplecticGradient_smul (c : ℝ) (L : (E × E) →L[ℝ] ℝ) :
    symplecticGradient (c • L) = c • symplecticGradient L := by
  simp only [symplecticGradient,smul_comp,map_smul,smul_neg,Prod.smul_mk]

omit [CompleteSpace E] in
lemma contDiff_hamiltonian_slice {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) : ContDiff ℝ ∞ (fun x => H (t,x)) :=
  hH.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht,mem_univ _⟩)

lemma flatHamiltonian_field {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ)) :
    hamiltonianField (flatTimeField H) = flatTimeField (hamiltonianField H) := by
  funext z
  dsimp only [hamiltonianField,phaseDifferential,flatTimeField]
  exact (congrArg symplecticGradient (fderiv_const_smul
    ((contDiff_hamiltonian_slice hH (smoothTime_mem z.1)).differentiable (by simp) z.2)
    (deriv Real.smoothTransition z.1))).trans (symplecticGradient_smul _ _)

lemma flatHamiltonian_support {H : ℝ × (E × E) → ℝ} {S : Set (E × E)}
    (hS : IsClosed S)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S) (t : ℝ) :
    Function.support (fun x => hamiltonianField (flatTimeField H) (t,x)) ⊆ S := by
  apply hamiltonianField_support hS
  intro u x hx
  have hz : H (Real.smoothTransition u,x) = 0 := by
    by_contra hn
    exact hx (hs _ (smoothTime_mem u) hn)
  simp only [flatTimeField,hz,smul_zero]

lemma flatHamiltonian_regular {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    {S : Set (E × E)} (hS : IsCompact S)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S) :
    ContDiff ℝ ∞ (hamiltonianField (flatTimeField H)) ∧
      HasCompactSupport (hamiltonianField (flatTimeField H)) :=
  ⟨contDiff_hamiltonianField (contDiff_flatTimeField hH),
    compactSupport_hamiltonianField (contDiff_flatTimeField hH)
      (compactSupport_flatTimeField hS hs)⟩

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace SmoothFlow
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def hamiltonianTrajectory {H : ℝ × (E × E) → ℝ}
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField H))) (s : ℝ)
    (z : ℝ × (E × E)) : E × E := evolution φ ((s,z.2),z.1)

lemma contDiff_hamiltonianTrajectory {H : ℝ × (E × E) → ℝ}
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField H)))
    (hH : ContDiff ℝ ∞ H) {K : ℝ≥0} (hK : LipschitzWith K (hamiltonianField H)) (s : ℝ) :
    ContDiff ℝ ∞ (hamiltonianTrajectory φ s) :=
  (contDiff_evolution φ (contDiff_hamiltonianField hH) hK).comp
    ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)

lemma hamiltonianTrajectory_initial {H : ℝ × (E × E) → ℝ}
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField H))) (s : ℝ) (x : E × E) :
    hamiltonianTrajectory φ s (s,x) = x := evolution_initial φ s x

lemma hamiltonianTrajectory_velocity {H : ℝ × (E × E) → ℝ}
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField H)))
    (hH : ContDiff ℝ ∞ H) {K : ℝ≥0} (hK : LipschitzWith K (hamiltonianField H))
    (s t : ℝ) (x : E × E) :
    flowVelocity (hamiltonianTrajectory φ s) (t,x) =
      hamiltonianField H (t,hamiltonianTrajectory φ s (t,x)) := by
  have hd := (((contDiff_hamiltonianTrajectory φ hH hK s).differentiable (by simp)
    (t,x)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt
  exact hd.unique (evolution_derivative φ s x t)

lemma hamiltonianTrajectory_identity {H : ℝ × (E × E) → ℝ}
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField H)))
    (hH : ContDiff ℝ ∞ H) {K : ℝ≥0} (hK : LipschitzWith K (hamiltonianField H))
    (s t : ℝ) (x w : E × E) :
    inner ℝ (flowVelocity (hamiltonianTrajectory φ s) (t,x)).2 w.1 -
      inner ℝ w.2 (flowVelocity (hamiltonianTrajectory φ s) (t,x)).1 =
      -fderiv ℝ H (t,hamiltonianTrajectory φ s (t,x)) (0,w) := by
  rw [hamiltonianTrajectory_velocity φ hH hK]
  rw [hamiltonianField_identity,phaseDifferential_eq (hH.differentiable (by simp))]
  rfl

theorem exists_flat_hamiltonian_evolution {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    {S : Set (E × E)} (hS : IsCompact S)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S) :
    ∃ (K : ℝ≥0) (φ : ODE.CompleteFlow (timeLift (hamiltonianField (flatTimeField H)))),
      LipschitzWith K (hamiltonianField (flatTimeField H)) ∧
      ContDiff ℝ ∞ (evolution φ) ∧
      ∀ s t, Function.support (fun x => evolution φ ((s,x),t)-x) ⊆ S := by
  obtain ⟨hf,hc⟩ := flatHamiltonian_regular hH hS hs
  obtain ⟨L,K,hL,hK⟩ := compact_map_bounds hc (hf.of_le (by simp))
  obtain ⟨φ,hφ⟩ := exists_smooth_evolution hf hL hK
  exact ⟨K,φ,hK,hφ,fun s t => evolution_support φ hK
    (flatHamiltonian_support hS.isClosed hs) s t⟩

end NearbyLagrangian.Transport

end

end OAI
