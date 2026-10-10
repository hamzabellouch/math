import Mathlib
import OAI.Geometry.NearbyLagrangian.HamiltonianFlow

namespace OAI

/-! Compactly supported Hamiltonian evolution and its smooth motion. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

lemma mem_open_iff_of_fixed_outside (U : Set E) (e : E ≃ E)
    (hs : ∀ x ∉ U, e x = x) (x : E) : e x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    by_contra hn
    exact hn ((hs x hn) ▸ hx)
  · intro hx
    by_contra hn
    have hi := e.injective (hs (e x) hn)
    exact hn (hi.symm ▸ hx)

def restrictSupportedDiffeomorph (U : Opens E)
    (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) E E ∞)
    (hs : ∀ x ∉ (U:Set E), e x = x) : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) U U ∞ where
  toFun x := ⟨e x,(mem_open_iff_of_fixed_outside (U:Set E) e.toEquiv hs x).mpr x.property⟩
  invFun x := ⟨e.symm x,by
    apply (mem_open_iff_of_fixed_outside (U:Set E) e.toEquiv hs (e.symm x)).mp
    change e (e.symm x) ∈ (U:Set E)
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Function TopologicalSpace SmoothFlow
open scoped Manifold ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def openEvolution (U : Opens E) {X : ℝ × E → E}
    (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x)
    (s t : ℝ) : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) U U ∞ :=
  restrictSupportedDiffeomorph U (evolutionDiffeomorph φ hX hK s t) (hs s t)

lemma openEvolution_apply (U : Opens E) {X : ℝ × E → E}
    (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x)
    (s t : ℝ) (x : U) :
    (openEvolution U φ hX hK hs s t x:E) = evolution φ ((s,(x:E)),t) := rfl

lemma contMDiff_openEvolution (U : Opens E) {X : ℝ × E → E}
    (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x) (s : ℝ) :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun z : ℝ × U => openEvolution U φ hX hK hs s z.1 z.2) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  have hd := (contDiff_evolution φ hX hK).contMDiff
  have hi : ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,(ℝ × E) × ℝ) ∞
      (fun z : ℝ × U => ((s,(z.2:E)),z.1)) := by
    apply (contMDiff_prod_module_iff _).mpr
    refine ⟨?_,contMDiff_fst⟩
    apply (contMDiff_prod_module_iff _).mpr
    exact ⟨contMDiff_const,contMDiff_subtype_val.comp contMDiff_snd⟩
  exact hd.comp hi

variable {V A M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]

def chartEvolution (U : Opens E) (e : Diffeomorph I 𝓘(ℝ,E) M U ∞)
    {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x)
    (s t : ℝ) : Diffeomorph I I M M ∞ :=
  (e.trans (openEvolution U φ hX hK hs s t)).trans e.symm

lemma chartEvolution_identity (U : Opens E) (e : Diffeomorph I 𝓘(ℝ,E) M U ∞)
    {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x)
    (s t : ℝ) (x : M) :
    (e (chartEvolution U e φ hX hK hs s t x):E) = evolution φ ((s,(e x:E)),t) := by
  change (e (e.symm (openEvolution U φ hX hK hs s t (e x))):E) = _
  rw [e.apply_symm_apply]
  rfl

lemma chartEvolution_initial (U : Opens E) (e : Diffeomorph I 𝓘(ℝ,E) M U ∞)
    {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x)
    (s : ℝ) (x : M) : chartEvolution U e φ hX hK hs s s x = x := by
  apply e.injective
  apply Subtype.val_injective
  change (e (chartEvolution U e φ hX hK hs s s x):E) = (e x:E)
  rw [chartEvolution_identity,evolution_initial]

lemma contMDiff_chartEvolution (U : Opens E) (e : Diffeomorph I 𝓘(ℝ,E) M U ∞)
    {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X)) (hX : ContDiff ℝ ∞ X)
    {K : ℝ≥0} (hK : LipschitzWith K X)
    (hs : ∀ s t x, x ∉ (U:Set E) → evolution φ ((s,x),t) = x) (s : ℝ) :
    ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞
      (fun z : ℝ × M => chartEvolution U e φ hX hK hs s z.1 z.2) :=
  e.symm.contMDiff.comp ((contMDiff_openEvolution U φ hX hK hs s).comp
    (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)))

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace SmoothFlow
open scoped ContDiff Topology NNReal Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_compact_hamiltonian_evolution {H : ℝ × (E × E) → ℝ}
    (hH : ContDiff ℝ ∞ H) (hs : HasCompactSupport H)
    {S : Set (E × E)} (hS : IsClosed S)
    (hsp : ∀ t, Function.support (fun x => H (t,x)) ⊆ S) :
    ∃ (K : ℝ≥0) (φ : ODE.CompleteFlow (timeLift (hamiltonianField H))),
      LipschitzWith K (hamiltonianField H) ∧
      ContDiff ℝ ∞ (evolution φ) ∧
      ∀ s t, Function.support (fun x => evolution φ ((s,x),t)-x) ⊆ S := by
  have hf := contDiff_hamiltonianField hH
  have hc := compactSupport_hamiltonianField hH hs
  obtain ⟨L,K,hL,hK⟩ := compact_map_bounds hc (hf.of_le (by simp))
  obtain ⟨φ,hφ⟩ := exists_smooth_evolution hf hL hK
  refine ⟨K,φ,hK,hφ,fun s t => evolution_support φ hK ?_ s t⟩
  intro t
  apply hamiltonianField_support hS
  intro u x hx
  by_contra hn
  exact hx (hsp u hn)

lemma hamiltonian_evolution_equation {H : ℝ × (E × E) → ℝ}
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField H)))
    (s : ℝ) (x : E × E) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (v : E × E) :
    inner ℝ (fderivWithin ℝ (fun u => evolution φ ((s,x),u)) (Icc (0:ℝ) 1) t 1).2 v.1 -
      inner ℝ v.2 (fderivWithin ℝ (fun u => evolution φ ((s,x),u)) (Icc (0:ℝ) 1) t 1).1 =
        -fderiv ℝ (fun y => H (t,y)) (evolution φ ((s,x),t)) v := by
  have he := (evolution_derivative φ s x t).hasFDerivAt.hasFDerivWithinAt.fderivWithin
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht)
  rw [he,toSpanSingleton_apply_one]
  exact hamiltonianField_identity H (t,evolution φ ((s,x),t)) v

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter Function TopologicalSpace SmoothFlow
open scoped Manifold ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure SupportedHamiltonianEvolution (U : Opens (E × E)) (H : ℝ × (E × E) → ℝ) where
  bound : ℝ≥0
  flow : ODE.CompleteFlow (timeLift (hamiltonianField H))
  smooth : ContDiff ℝ ∞ H
  lipschitz : LipschitzWith bound (hamiltonianField H)
  supportSet : Set (E × E)
  compact : IsCompact supportSet
  inside : supportSet ⊆ (U:Set (E × E))
  hamiltonianSupport : ∀ t, Function.support (fun x => H (t,x)) ⊆ supportSet
  flowSupport : ∀ s t, Function.support (fun x => evolution flow ((s,x),t)-x) ⊆ supportSet

theorem exists_supportedHamiltonianEvolution (U : Opens (E × E))
    {H : ℝ × (E × E) → ℝ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {C : Set (E × E)} (hC : IsCompact C) (hCU : C ⊆ (U:Set (E × E)))
    (hs : ∀ t, Function.support (fun x => H (t,x)) ⊆ C) :
    Nonempty (SupportedHamiltonianEvolution U H) := by
  obtain ⟨K,φ,hK,_,hS⟩ := exists_compact_hamiltonian_evolution hH hc hC.isClosed hs
  exact ⟨⟨K,φ,hH,hK,C,hC,hCU,hs,hS⟩⟩

lemma SupportedHamiltonianEvolution.fixed {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (s t : ℝ) (x : E × E) (hx : x ∉ U) :
    evolution F.flow ((s,x),t) = x := by
  by_contra hn
  have hd : evolution F.flow ((s,x),t)-x ≠ 0 := sub_ne_zero.mpr hn
  exact hx (F.inside (F.flowSupport s t hd))

variable {V A M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]

def SupportedHamiltonianEvolution.motion {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (s t : ℝ) : Diffeomorph I I M M ∞ :=
  chartEvolution U e F.flow (contDiff_hamiltonianField F.smooth) F.lipschitz F.fixed s t

lemma SupportedHamiltonianEvolution.motion_identity
    {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (s t : ℝ) (x : M) :
    (e (F.motion e s t x):E × E) = evolution F.flow ((s,(e x:E × E)),t) :=
  chartEvolution_identity U e F.flow (contDiff_hamiltonianField F.smooth) F.lipschitz F.fixed s t x

lemma SupportedHamiltonianEvolution.motion_initial
    {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (s : ℝ) (x : M) : F.motion e s s x = x :=
  chartEvolution_initial U e F.flow (contDiff_hamiltonianField F.smooth) F.lipschitz F.fixed s x

lemma SupportedHamiltonianEvolution.motion_smooth
    {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (s : ℝ) : ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ (fun z : ℝ × M => F.motion e s z.1 z.2) :=
  contMDiff_chartEvolution U e F.flow (contDiff_hamiltonianField F.smooth) F.lipschitz F.fixed s

lemma contMDiff_timeSlice {f : ℝ × M → M}
    (h : ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ f) (x : M) :
    ContMDiff 𝓘(ℝ,ℝ) I ∞ (fun t => f (t,x)) := by
  exact h.comp (contMDiff_id.prodMk contMDiff_const)

lemma SupportedHamiltonianEvolution.motion_curve_smooth
    {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (s : ℝ) (x : M) : ContMDiff 𝓘(ℝ,ℝ) I ∞ (fun t => F.motion e s t x) :=
  contMDiff_timeSlice (F.motion_smooth e s) x

lemma SupportedHamiltonianEvolution.motion_equation
    {U : Opens (E × E)} {H : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution U H) (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (s : ℝ) (x : M) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (v : E × E) :
    let d : ℝ → E × E := fun u => (e (F.motion e s u x):E × E)
    inner ℝ (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).2 v.1 -
      inner ℝ v.2 (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).1 =
        -fderiv ℝ (fun y => H (t,y)) (d t) v := by
  have hd : (fun u => (e (F.motion e s u x):E × E)) =
      (fun u => evolution F.flow ((s,(e x:E × E)),u)) :=
    funext fun u => F.motion_identity e s u x
  dsimp only
  rw [hd,F.motion_identity]
  exact hamiltonian_evolution_equation F.flow s (e x:E × E) ht v

end NearbyLagrangian.Transport

end

end OAI
