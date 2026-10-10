import Mathlib
import OAI.Geometry.BallPacking.Hamiltonian.LiftedCompact

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

def firstClock (t : ℝ) : ℝ := Real.smoothTransition (3*t)
def secondClock (t : ℝ) : ℝ := Real.smoothTransition (3*t-2)

@[fun_prop] theorem firstClock_smooth : ContDiff ℝ ∞ firstClock := by
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
@[fun_prop] theorem secondClock_smooth : ContDiff ℝ ∞ secondClock := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

@[simp] theorem firstClock_zero : firstClock 0 = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)
@[simp] theorem secondClock_zero : secondClock 0 = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)
@[simp] theorem firstClock_one : firstClock 1 = 1 := by
  exact Real.smoothTransition.one_of_one_le (by norm_num)
@[simp] theorem secondClock_one : secondClock 1 = 1 := by
  exact Real.smoothTransition.one_of_one_le (by norm_num)

theorem secondClock_locally_zero {t : ℝ} (ht : t < 2/3) :
    secondClock =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  change s < 2/3 at hs
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem firstClock_locally_one {t : ℝ} (ht : 1/3 < t) :
    firstClock =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  change 1/3 < s at hs
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem secondClock_deriv_zero {t : ℝ} (ht : t < 2/3) : deriv secondClock t = 0 :=
  ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq (secondClock_locally_zero ht)).deriv

theorem firstClock_deriv_zero {t : ℝ} (ht : 1/3 < t) : deriv firstClock t = 0 :=
  ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq (firstClock_locally_one ht)).deriv

theorem firstClock_deriv_compact : HasCompactSupport (deriv firstClock) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro t ht
  have hor : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hor with ht | ht
  · have he : firstClock =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      change s < 0 at hs
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    exact ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he).deriv
  · exact firstClock_deriv_zero (by linarith)

theorem secondClock_deriv_compact : HasCompactSupport (deriv secondClock) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro t ht
  have hor : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hor with ht | ht
  · exact secondClock_deriv_zero (by linarith)
  · have he : secondClock =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      change 1 < s at hs
      exact Real.smoothTransition.one_of_one_le (by linarith)
    exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}
namespace CompactHamiltonianIsotopy

def concatMap (Φ Ψ : CompactHamiltonianIsotopy A) (t : ℝ) : E ≃ₜ E :=
  (Ψ.map (firstClock t)).trans (Φ.map (secondClock t))

def concatHamiltonian (Φ Ψ : CompactHamiltonianIsotopy A) : ℝ × E → ℝ :=
  reparamHamiltonian Ψ.hamiltonian firstClock + reparamHamiltonian Φ.hamiltonian secondClock

theorem concatHamiltonian_smooth (Φ Ψ : CompactHamiltonianIsotopy A) :
    ContDiff ℝ ∞ (concatHamiltonian Φ Ψ) :=
  (reparamHamiltonian_smooth Ψ.hamiltonian_smooth firstClock_smooth).add
    (reparamHamiltonian_smooth Φ.hamiltonian_smooth secondClock_smooth)

theorem concatHamiltonian_compact (Φ Ψ : CompactHamiltonianIsotopy A) :
    HasCompactSupport (concatHamiltonian Φ Ψ) :=
  (reparamHamiltonian_compact Ψ.compact firstClock firstClock_deriv_compact).add
    (reparamHamiltonian_compact Φ.compact secondClock secondClock_deriv_compact)

theorem concatMap_smooth (Φ Ψ : CompactHamiltonianIsotopy A) :
    ContDiff ℝ ∞ (fun p : ℝ × E => concatMap Φ Ψ p.1 p.2) :=
  Φ.smooth.comp ((secondClock_smooth.comp contDiff_fst).prodMk
    (Ψ.smooth.comp ((firstClock_smooth.comp contDiff_fst).prodMk contDiff_snd)))

theorem concatMap_inverse_smooth (Φ Ψ : CompactHamiltonianIsotopy A) :
    ContDiff ℝ ∞ (fun p : ℝ × E => (concatMap Φ Ψ p.1).symm p.2) :=
  Ψ.inverse_smooth.comp ((firstClock_smooth.comp contDiff_fst).prodMk
    (Φ.inverse_smooth.comp ((secondClock_smooth.comp contDiff_fst).prodMk contDiff_snd)))

@[simp] theorem concatMap_zero (Φ Ψ : CompactHamiltonianIsotopy A) :
    concatMap Φ Ψ 0 = Homeomorph.refl E := by
  simp only [concatMap,firstClock_zero,secondClock_zero,Φ.zero,Ψ.zero]
  rfl

@[simp] theorem concatMap_one (Φ Ψ : CompactHamiltonianIsotopy A) (x : E) :
    concatMap Φ Ψ 1 x = Φ.map 1 (Ψ.map 1 x) := by
  simp only [concatMap,firstClock_one,secondClock_one,Homeomorph.trans_apply]

theorem concatMap_flow (Φ Ψ : CompactHamiltonianIsotopy A) (t : ℝ) (x : E) :
    HasDerivAt (fun s => concatMap Φ Ψ s x)
      (hamiltonianField A (concatHamiltonian Φ Ψ) (t,concatMap Φ Ψ t x)) t := by
  rw [concatHamiltonian,hamiltonianField_add
    (A := A) (reparamHamiltonian_smooth Ψ.hamiltonian_smooth firstClock_smooth)
    (reparamHamiltonian_smooth Φ.hamiltonian_smooth secondClock_smooth),
    hamiltonianField_reparam A Ψ.hamiltonian_smooth firstClock_smooth,
    hamiltonianField_reparam A Φ.hamiltonian_smooth secondClock_smooth]
  by_cases ht : t ≤ 1/2
  · have ht' : t < 2/3 := by linarith
    have he : (fun s => concatMap Φ Ψ s x) =ᶠ[𝓝 t]
        (fun s => Ψ.map (firstClock s) x) := by
      filter_upwards [secondClock_locally_zero ht'] with s hs
      simp only [concatMap,Homeomorph.trans_apply,hs,Φ.zero,Homeomorph.refl_apply,id_eq]
    rw [secondClock_deriv_zero ht',zero_smul,add_zero,he.eq_of_nhds]
    exact ((Ψ.flow (firstClock t) x).scomp t
      ((firstClock_smooth.differentiable (by simp) t).hasDerivAt)).congr_of_eventuallyEq he
  · have ht' : 1/3 < t := by linarith
    have he : (fun s => concatMap Φ Ψ s x) =ᶠ[𝓝 t]
        (fun s => Φ.map (secondClock s) (Ψ.map 1 x)) := by
      filter_upwards [firstClock_locally_one ht'] with s hs
      simp only [concatMap,Homeomorph.trans_apply,hs]
    rw [firstClock_deriv_zero ht',zero_smul,zero_add,he.eq_of_nhds]
    exact ((Φ.flow (secondClock t) (Ψ.map 1 x)).scomp t
      ((secondClock_smooth.differentiable (by simp) t).hasDerivAt)).congr_of_eventuallyEq he

theorem concatMap_symplectic (Φ Ψ : CompactHamiltonianIsotopy A) (t : ℝ) (x v w : E) :
    A (fderiv ℝ (concatMap Φ Ψ t) x v) (fderiv ℝ (concatMap Φ Ψ t) x w) = A v w := by
  change A (fderiv ℝ ((Φ.map (secondClock t)) ∘ (Ψ.map (firstClock t))) x v)
    (fderiv ℝ ((Φ.map (secondClock t)) ∘ (Ψ.map (firstClock t))) x w) = _
  rw [fderiv_comp x ((Φ.map_smooth _).differentiable (by simp) _)
    ((Ψ.map_smooth _).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply,Φ.symplectic,Ψ.symplectic]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

def after (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    (Φ Ψ : CompactHamiltonianIsotopy A) : CompactHamiltonianIsotopy A where
  map := concatMap Φ Ψ
  smooth := concatMap_smooth Φ Ψ
  inverse_smooth := concatMap_inverse_smooth Φ Ψ
  zero := concatMap_zero Φ Ψ
  hamiltonian := concatHamiltonian Φ Ψ
  hamiltonian_smooth := concatHamiltonian_smooth Φ Ψ
  compact := concatHamiltonian_compact Φ Ψ
  flow := concatMap_flow Φ Ψ
  symplectic := concatMap_symplectic Φ Ψ
  fixed := by
    intro t x hx
    have hx' : concatMap Φ Ψ 0 x ∉ Prod.snd '' tsupport (concatHamiltonian Φ Ψ) := by
      simpa only [concatMap_zero,Homeomorph.refl_apply,id_eq] using hx
    have he := hamiltonian_trajectory_fixed hA hskew (concatHamiltonian_smooth Φ Ψ)
      (concatHamiltonian_compact Φ Ψ)
      ((concatMap_smooth Φ Ψ).continuous.comp (continuous_id.prodMk continuous_const))
      (fun t => concatMap_flow Φ Ψ t x) hx' t
    change concatMap Φ Ψ t x = concatMap Φ Ψ 0 x at he
    simpa only [concatMap_zero,Homeomorph.refl_apply,id_eq] using he

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem concatMap_preserves (Φ Ψ : CompactHamiltonianIsotopy A) {S : Set E}
    (hΦ : ∀ t x, Φ.map t x ∈ S ↔ x ∈ S) (hΨ : ∀ t x, Ψ.map t x ∈ S ↔ x ∈ S)
    (t : ℝ) (x : E) : concatMap Φ Ψ t x ∈ S ↔ x ∈ S := by
  exact (hΦ _ _).trans (hΨ _ _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem concatHamiltonian_face (Φ Ψ : CompactHamiltonianIsotopy A) (q : E → ℝ)
    {c ρ : ℝ}
    (hΦ : ∀ t x, c-q x < ρ → fderiv ℝ q x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    (hΨ : ∀ t x, c-q x < ρ → fderiv ℝ q x (hamiltonianField A Ψ.hamiltonian (t,x)) = 0)
    (t : ℝ) (x : E) (hx : c-q x < ρ) :
    fderiv ℝ q x (hamiltonianField A (concatHamiltonian Φ Ψ) (t,x)) = 0 := by
  rw [concatHamiltonian,hamiltonianField_add A
    (reparamHamiltonian_smooth Ψ.hamiltonian_smooth firstClock_smooth)
    (reparamHamiltonian_smooth Φ.hamiltonian_smooth secondClock_smooth),
    hamiltonianField_reparam A Ψ.hamiltonian_smooth firstClock_smooth,
    hamiltonianField_reparam A Φ.hamiltonian_smooth secondClock_smooth,map_add,map_smul,map_smul,
    hΦ _ _ hx,hΨ _ _ hx,smul_zero,smul_zero,zero_add]

end CompactHamiltonianIsotopy

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy
open scoped ContDiff Topology BigOperators
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def refl (A : E →L[ℝ] E →L[ℝ] ℝ) : CompactHamiltonianIsotopy A where
  map := fun _ => Homeomorph.refl E
  smooth := contDiff_snd
  inverse_smooth := contDiff_snd
  zero := rfl
  hamiltonian := 0
  hamiltonian_smooth := contDiff_const
  compact := by simp [HasCompactSupport]
  flow := by
    intro t x
    simpa only [hamiltonianField,formMoserField,spatialDifferential,
      fderiv_zero,Pi.zero_apply,ContinuousLinearMap.zero_comp,map_zero,neg_zero,
      Homeomorph.refl_apply,id_eq] using hasDerivAt_const t x
  symplectic := by intro t x v w; simp
  fixed := fun _ _ _ => rfl

end PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian Comparison
open scoped Pointwise
open MeasureTheory
section

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem exists_lifted_rearrangement_convex (j : Fin m) [Nonempty (Active b j)]
    (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c))
    (F : ConvexMaps (region b c) (convex_region b c)) {ε : ℝ} (he : 0 < ε) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _),
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (hz : z ∈ planeRegion b c), ∀ hz',
        F.val ⟨planeMoments (Φ.map 1 z),hz'⟩ ≤
          (coordOperator b c j hb F).val ⟨planeMoments z,hz⟩+ε) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  obtain ⟨f,hf⟩ := ContinuousMap.exists_extension hK.isClosed.isClosedEmbedding_subtypeVal F.val
  have heq (p : region b c) : f p.val = F.val p := congrArg (fun H : C(region b c,ℝ) => H p) hf
  have hconv : ConvexOn ℝ (region b c) f := by
    refine ⟨convex_region b c,?_⟩
    intro p hp q hq a d ha hd had
    simpa only [←heq,smul_eq_mul] using! F.property ⟨p,hp⟩ ⟨q,hq⟩ a d ha hd had
  obtain ⟨Φ,hmem,hest,hface⟩ := exists_cartesian_lifted_rearrangement b c j hb hK f hconv he
  refine ⟨Φ,hmem,?_,hface⟩
  intro z hz hz'
  have hext : f.restrict (region b c) = F.val := hf
  have hh := hest z hz
  rw [hext,heq ⟨_,hz'⟩] at hh
  exact hh

variable [∀ j, Nonempty (Active b j)]

theorem exists_successive_rearrangement (hb : ∀ ν i, 0 ≤ b ν i)
    (hK : IsCompact (region b c)) (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) {ε : ℝ} (he : 0 < ε) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _),
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (hz : z ∈ planeRegion b c), ∀ hz',
        F.val ⟨planeMoments (Φ.map 1 z),hz'⟩ ≤
          (successive b c hb js F).val ⟨planeMoments z,hz⟩+ε) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  induction js generalizing F ε with
  | nil =>
    refine ⟨CompactHamiltonianIsotopy.refl (@phaseArea (Fin m) _),?_,?_,?_⟩
    · intro t z
      rfl
    · intro z hz hz'
      change F.val ⟨planeMoments z,hz'⟩ ≤ F.val ⟨planeMoments z,hz⟩+ε
      exact le_add_of_nonneg_right he.le
    · intro ν
      refine ⟨1,zero_lt_one,fun _ _ _ => ?_⟩
      simp [CompactHamiltonianIsotopy.refl,hamiltonianField,formMoserField,spatialDifferential]
  | cons j js ih =>
    obtain ⟨Φ,hΦ,hΦest,hΦface⟩ := exists_lifted_rearrangement_convex b c j hb hK F (half_pos he)
    obtain ⟨Ψ,hΨ,hΨest,hΨface⟩ := ih (coordOperator b c j hb F) (half_pos he)
    let Γ := Φ.after phaseArea_isInvertible phaseArea_skew Ψ
    have hΓ (t : ℝ) (z : PlanePhase (Fin m)) : Γ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c :=
      Φ.concatMap_preserves Ψ hΦ hΨ t z
    refine ⟨Γ,hΓ,?_,?_⟩
    · intro z hz hz'
      have hy := (hΨ 1 z).mpr hz
      have hfirst := hΦest (Ψ.map 1 z) hy ((hΦ 1 _).mpr hy)
      have hsecond := hΨest z hz hy
      have hend : Γ.map 1 z = Φ.map 1 (Ψ.map 1 z) := Φ.concatMap_one Ψ z
      have hval : F.val ⟨planeMoments (Γ.map 1 z),hz'⟩ =
          F.val ⟨planeMoments (Φ.map 1 (Ψ.map 1 z)),(hΦ 1 _).mpr hy⟩ := by
        apply congrArg F.val
        apply Subtype.ext
        exact congrArg planeMoments hend
      rw [hval]
      change _ ≤ (successive b c hb js (coordOperator b c j hb F)).val ⟨planeMoments z,hz⟩+ε
      linarith
    · intro ν
      obtain ⟨a,ha,haf⟩ := hΦface ν
      obtain ⟨d,hd,hdf⟩ := hΨface ν
      refine ⟨min a d,lt_min ha hd,?_⟩
      intro t z hz
      exact Φ.concatHamiltonian_face Ψ (weightedMoment (b ν))
        (fun t z hz => haf t z (hz.trans_le (min_le_left _ _)))
        (fun t z hz => hdf t z (hz.trans_le (min_le_right _ _))) t z hz

end
section

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem hamiltonian_comparison (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 < c ν)
    (hcomp : IsCompact (region b c))
    (Q : ConvexMaps (region b c) (convex_region b c))
    {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a)
    (hmean : averageMap (region b c) hcomp Q.val < 0)
    (houter : ∀ p : region b c, p.val ∉ τ • region b c → Q.val p ≤ -a) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _)),
      ContDiff ℝ ∞ K ∧
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (_hz : z ∈ planeRegion b c), ∀ hz',
        K (planeMoments (Φ.map 1 z))+Q.val ⟨planeMoments (Φ.map 1 z),hz'⟩ < K (planeMoments z)) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  let : ∀ j, Nonempty (Active b j) := fun j => active_nonempty b c hb hc hcomp j
  obtain ⟨K,d,hd,hgap⟩ := analytic_gap b c hb hc hcomp Q hτ hτ1 ha hmean houter
  obtain ⟨Φ,hmem,hest,hface⟩ := exists_successive_rearrangement b c hb hcomp (List.finRange m)
    (affineStep 1 (by norm_num) Q K) (show 0 < d/4 by positivity)
  obtain ⟨k,hk,happrox⟩ := smooth_approximation (region b c) hcomp K.val (show 0 < d/4 by positivity)
  refine ⟨k,Φ,hk,hmem,?_,hface⟩
  intro z hz hz'
  have hout := happrox ⟨planeMoments (Φ.map 1 z),hz'⟩
  have hin := happrox ⟨planeMoments z,hz⟩
  rw [Real.dist_eq] at hout hin
  have ho := (abs_lt.mp hout).2
  have hi := (abs_lt.mp hin).1
  have he := hest z hz hz'
  have hg := hgap ⟨planeMoments z,hz⟩
  change (affineStep 1 (by norm_num) Q K).val ⟨planeMoments (Φ.map 1 z),hz'⟩ ≤
    (fullRearrangement b c hb (affineStep 1 (by norm_num) Q K)).val ⟨planeMoments z,hz⟩+d/4 at he
  simp only [affineStep, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, one_mul] at he hg
  linarith only [hd,ho,hi,he,hg]

end

theorem positive_hamiltonian_comparison {m N : ℕ}
    (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 < c ν)
    (hcomp : IsCompact (region b c))
    (P : Moments m → ℝ) (hP : ContinuousOn P (region b c))
    (hconc : ConcaveOn ℝ (region b c) P)
    (hmean : 0 < ∫ p in region b c, P p)
    {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a)
    (houter : ∀ p ∈ region b c, p ∉ τ • region b c → a ≤ P p) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _)),
      ContDiff ℝ ∞ K ∧
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z ∈ planeRegion b c,
        K (planeMoments (Φ.map 1 z))-P (planeMoments (Φ.map 1 z)) < K (planeMoments z)) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  let Q : ConvexMaps (region b c) (convex_region b c) :=
    ⟨⟨fun p => -P p, hP.domRestrict.neg⟩,by
      intro x y r s hr hs hrs
      change -P (r • (x : Moments m)+s • (y : Moments m)) ≤ r*(-P x)+s*(-P y)
      simpa only [Pi.neg_apply,smul_eq_mul] using
        (hconc.neg.2 x.property y.property hr hs hrs)⟩
  have he : zeroExtend (region b c) Q.val = (region b c).indicator (fun p => -P p) := by
    funext p
    by_cases hp : p ∈ region b c
    · simp only [zeroExtend,dite_eq_left hp,indicator_of_mem hp]
      rfl
    · simp [zeroExtend,hp]
  have hm : averageMap (region b c) hcomp Q.val < 0 := by
    change (volume (region b c)).toReal⁻¹ * (∫ p, zeroExtend (region b c) Q.val p) < 0
    rw [he,integral_indicator hcomp.measurableSet,integral_neg]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (volume_region_toReal_pos b c hc hcomp))
      (neg_neg_of_pos hmean)
  obtain ⟨K,Φ,hK,hmem,hgap,hface⟩ := hamiltonian_comparison b c hb hc hcomp Q
    hτ hτ1 ha hm (fun p hp => neg_le_neg (houter p p.property hp))
  refine ⟨K,Φ,hK,hmem,?_,hface⟩
  intro z hz
  have hg := hgap z hz ((hmem 1 z).2 hz)
  change K (planeMoments (Φ.map 1 z))+(-P (planeMoments (Φ.map 1 z))) < K (planeMoments z) at hg
  simpa only [sub_eq_add_neg] using hg

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function

variable {ι : Type*} [Fintype ι]

theorem isCompact_preimage_planeMoments {D : Set (ι → ℝ)} (hD : IsCompact D) :
    IsCompact (planeMoments ⁻¹' D) := by
  obtain ⟨R,hR⟩ := hD.isBounded.exists_norm_le
  have hp : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hclosed : IsClosed (planeMoments ⁻¹' D) :=
    hD.isClosed.preimage planeMoments_smooth.continuous
  apply (isCompact_closedBall (0 : PlanePhase ι) (|R|+1)).of_isClosed_subset hclosed
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ |R|+1)).2
  intro i
  have hm : planeMoments z i ≤ |R| :=
    (le_abs_self _).trans ((norm_le_pi_norm (planeMoments z) i).trans ((hR _ hz).trans (le_abs_self R)))
  have hs : (z i).1^2+(z i).2^2 ≤ planeMoments z i := by
    change (z i).1^2+(z i).2^2 ≤ Real.pi*((z i).1^2+(z i).2^2)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  apply max_le
  · nlinarith [sq_abs (z i).1,abs_nonneg (z i).1,sq_nonneg (z i).2,abs_nonneg R]
  · nlinarith [sq_abs (z i).2,abs_nonneg (z i).2,sq_nonneg (z i).1,abs_nonneg R]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff BigOperators
open Set Function
open Hamiltonian

theorem planeRegion_isCompact {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hC : IsCompact (region b c)) : IsCompact (planeRegion b c) :=
  isCompact_preimage_planeMoments hC

theorem planeRegion_nonempty {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hc : ∀ ν,0 ≤ c ν) : (planeRegion b c).Nonempty := by
  refine ⟨0,?_,⟩
  change (∀ j,0 ≤ planeMoments (0 : PlanePhase (Fin m)) j) ∧
    ∀ ν,∑ j,b ν j*planeMoments (0 : PlanePhase (Fin m)) j ≤ c ν
  refine ⟨fun j => planeMoments_nonneg _ _,fun ν => ?_⟩
  simpa [planeMoments,radialArea,radiusSq] using hc ν

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

def smoothUpperPositivePart (δ x : ℝ) : ℝ := (x+Real.sqrt (x^2+δ^2))/2

theorem smoothUpperPositivePart_smooth {δ : ℝ} (hδ : 0<δ) :
    ContDiff ℝ ∞ (smoothUpperPositivePart δ) := by
  have hpos (x : ℝ) : 0<x^2+δ^2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hδ)
  apply (contDiff_id.add ((contDiff_id.pow 2).add contDiff_const |>.sqrt (fun x => ne_of_gt (hpos x)))).div_const

theorem smoothUpperPositivePart_bounds {δ : ℝ} (hδ : 0<δ) (x : ℝ) :
    max x 0 < smoothUpperPositivePart δ x ∧
      smoothUpperPositivePart δ x - max x 0 ≤ δ/2 := by
  have hp : 0 ≤ x^2+δ^2 := add_nonneg (sq_nonneg x) (sq_nonneg δ)
  have hroot := Real.sq_sqrt hp
  have hrootpos := Real.sqrt_nonneg (x^2+δ^2)
  have habs := sq_abs x
  have hgt : |x| < Real.sqrt (x^2+δ^2) := by nlinarith [sq_pos_of_pos hδ]
  have hle : Real.sqrt (x^2+δ^2) ≤ |x|+δ := by
    nlinarith [abs_nonneg x]
  rcases le_total 0 x with hx|hx
  · rw [max_eq_left hx,abs_of_nonneg hx] at *
    dsimp [smoothUpperPositivePart]
    constructor <;> linarith
  · rw [max_eq_right hx,abs_of_nonpos hx] at *
    dsimp [smoothUpperPositivePart]
    constructor <;> linarith

theorem exists_smooth_positive_caps {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (r : ι → ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ h : ι → (κ → ℝ) → ℝ,
      (∀ i, ContDiff ℝ ∞ (h i)) ∧
      (∀ i p, max (r i-∑ j, p j) 0 < h i p) ∧
      (∀ p, 0 < (∑ i, h i p)-(∑ i, max (r i-∑ j, p j) 0) ∧
        (∑ i, h i p)-(∑ i, max (r i-∑ j, p j) 0) < ε) := by
  classical
  let N : ℝ := Fintype.card ι
  have hN : 0<N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let δ := ε/N
  have hδ : 0<δ := div_pos hε hN
  let h : ι → (κ → ℝ) → ℝ := fun i p => smoothUpperPositivePart δ (r i-∑ j, p j)
  refine ⟨h,?_,?_,?_⟩
  · intro i
    exact (smoothUpperPositivePart_smooth hδ).comp (contDiff_const.sub (by fun_prop))
  · intro i p
    exact (smoothUpperPositivePart_bounds hδ _).1
  · intro p
    rw [←Finset.sum_sub_distrib]
    have hsum : (∑ i, (h i p-max (r i-∑ j, p j) 0)) ≤ N*(δ/2) := by
      calc
        _ ≤ ∑ _i : ι, δ/2 := Finset.sum_le_sum (fun i _ => (smoothUpperPositivePart_bounds hδ _).2)
        _ = N*(δ/2) := by simp [N]
    have hc : N*(δ/2)=ε/2 := by dsimp [δ]; field_simp
    refine ⟨Finset.sum_pos (fun i _ => sub_pos.mpr (smoothUpperPositivePart_bounds hδ _).1) Finset.univ_nonempty,?_⟩
    rw [hc] at hsum
    exact hsum.trans_lt (half_lt_self hε)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
