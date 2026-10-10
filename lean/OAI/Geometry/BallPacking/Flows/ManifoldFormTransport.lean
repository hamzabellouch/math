import Mathlib
import OAI.Geometry.BallPacking.Flows.AnnularPathGerms

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldPullback (Φ : ℝ × M → M) (Ω : ℝ → ManifoldTwoForm E M)
    (t : ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (Ω t (Φ (t,x))).bilinearComp
    (preferredDifferential (E := E) (fun y => Φ (t,y)) x)
    (preferredDifferential (E := E) (fun y => Φ (t,y)) x)

theorem manifold_form_transport_derivative
    {Φ : ℝ × M → M} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {U : Set ℝ} (hU : IsOpen U)
    (hflow : ∀ x s, s ∈ U → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun r => Φ (r,x)) s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x)))))
    {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {t : ℝ} (ht : t ∈ U)
    (hPDE : ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ u w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y)
        (1,timeChartField V c (t,y)) u w +
      chartTwoForm (Ω t) c y (fderiv ℝ (timeChartField V c) (t,y) (0,u)) w +
      chartTwoForm (Ω t) c y u (fderiv ℝ (timeChartField V c) (t,y) (0,w)) = 0)
    (x : M) (v w : E) :
    HasDerivAt (fun s => manifoldPullback Φ Ω s x v w) 0 t := by
  let a := extChartAt 𝓘(ℝ,E) x
  let c := Φ (t,x)
  let b := extChartAt 𝓘(ℝ,E) c
  let p : ℝ × E := (t,a x)
  let H : ℝ × E → M := fun q => Φ (q.1,a.symm q.2)
  let F : ℝ × E → E := b ∘ H
  have hx : x ∈ a.source := mem_extChartAt_source x
  have hy : a x ∈ a.target := a.map_source hx
  have hcx : Φ (t,x) ∈ b.source := mem_extChartAt_source c
  have hH : H p = Φ (t,x) := by dsimp [H,p]; rw [a.left_inv hx]
  have hc : H p ∈ b.source := hH ▸ hcx
  have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm (a x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hy)
  have hHs : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ H p :=
    hΦ.contMDiffAt.comp p (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt))
  have hFc : ContDiffAt ℝ ∞ F p := manifoldFamily_coordinate_smoothAt hΦ hy hc
  have hbc : F p ∈ b.target := b.map_source hc
  have hn : (univ ×ˢ b.target) ∈ 𝓝 (t,F p) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hbc⟩
  have hX := ((timeChartField_contDiffOn hV c).contDiffAt hn).differentiableAt (by simp)
  have hO := ((hΩ c).contDiffAt hn).differentiableAt (by simp)
  have hflowc : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2))
      (timeChartField V c (q.1,F q)) q.1 := by
    have hneigh := hHs.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    have htime : ∀ᶠ q in 𝓝 p, q.1 ∈ U :=
      continuousAt_fst.preimage_mem_nhds (hU.mem_nhds ht)
    filter_upwards [hneigh,htime] with q hq hqt
    exact timeChartField_hasDerivAt (hflow (a.symm q.2) q.1 hqt) hq
  have hd := local_flow_form_derivative hFc hX hflowc hO (hPDE c (F p) hbc) v w
  apply hd.congr_of_eventuallyEq
  have hΦt : ContinuousAt (fun s => Φ (s,x)) t :=
    hΦ.continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [hΦt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hcx)] with s hs
  have hfs : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (s,y)) x :=
    (hΦ.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp) x
  have he := chart_spatial_pullback hfs hs (Ω s) v w
  dsimp only [F,H,p,Function.comp_apply]
  rw [a.left_inv hx]
  exact he.symm

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifold_form_transport_constant
    {Φ : ℝ × M → M} {Ω : ℝ → ManifoldTwoForm E M}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, ∀ x v w,
      HasDerivAt (fun s => manifoldPullback Φ Ω s x v w) 0 t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : M) (v w : E) :
    manifoldPullback Φ Ω t x v w = manifoldPullback Φ Ω 0 x v w := by
  have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs x v w).hasDerivWithinAt)
    (fun s hs => (by simp : ‖(0:ℝ)‖ ≤ (0:ℝ)))
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) ht
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using he



theorem local_manifold_form_transport_derivative
    {Φ : ℝ × M → M} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {U : Set ℝ} (hU : IsOpen U)
    (hflow : ∀ x s, s ∈ U → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun r => Φ (r,x)) s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x)))))
    {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {t : ℝ} (ht : t ∈ U)
    (x : M)
    (hPDE : ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target →
      (extChartAt 𝓘(ℝ,E) c).symm y=Φ (t,x) → ∀ u w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y)
        (1,timeChartField V c (t,y)) u w +
      chartTwoForm (Ω t) c y (fderiv ℝ (timeChartField V c) (t,y) (0,u)) w +
      chartTwoForm (Ω t) c y u (fderiv ℝ (timeChartField V c) (t,y) (0,w)) = 0)
    (v w : E) :
    HasDerivAt (fun s => manifoldPullback Φ Ω s x v w) 0 t := by
  let a := extChartAt 𝓘(ℝ,E) x
  let c := Φ (t,x)
  let b := extChartAt 𝓘(ℝ,E) c
  let p : ℝ × E := (t,a x)
  let H : ℝ × E → M := fun q => Φ (q.1,a.symm q.2)
  let F : ℝ × E → E := b ∘ H
  have hx : x ∈ a.source := mem_extChartAt_source x
  have hy : a x ∈ a.target := a.map_source hx
  have hcx : Φ (t,x) ∈ b.source := mem_extChartAt_source c
  have hH : H p = Φ (t,x) := by dsimp [H,p]; rw [a.left_inv hx]
  have hc : H p ∈ b.source := hH ▸ hcx
  have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm (a x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hy)
  have hHs : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ H p :=
    hΦ.contMDiffAt.comp p (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt))
  have hFc : ContDiffAt ℝ ∞ F p := manifoldFamily_coordinate_smoothAt hΦ hy hc
  have hbc : F p ∈ b.target := b.map_source hc
  have hn : (univ ×ˢ b.target) ∈ 𝓝 (t,F p) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hbc⟩
  have hX := ((timeChartField_contDiffOn hV c).contDiffAt hn).differentiableAt (by simp)
  have hO := ((hΩ c).contDiffAt hn).differentiableAt (by simp)
  have hflowc : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2))
      (timeChartField V c (q.1,F q)) q.1 := by
    have hneigh := hHs.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    have htime : ∀ᶠ q in 𝓝 p, q.1 ∈ U :=
      continuousAt_fst.preimage_mem_nhds (hU.mem_nhds ht)
    filter_upwards [hneigh,htime] with q hq hqt
    exact timeChartField_hasDerivAt (hflow (a.symm q.2) q.1 hqt) hq
  have hd := local_flow_form_derivative hFc hX hflowc hO (hPDE c (F p) hbc ((b.left_inv hc).trans hH)) v w
  apply hd.congr_of_eventuallyEq
  have hΦt : ContinuousAt (fun s => Φ (s,x)) t :=
    hΦ.continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [hΦt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hcx)] with s hs
  have hfs : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (s,y)) x :=
    (hΦ.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp) x
  have he := chart_spatial_pullback hfs hs (Ω s) v w
  dsimp only [F,H,p,Function.comp_apply]
  rw [a.left_inv hx]
  exact he.symm


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem manifoldMoserField_moment_tangent
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {p : ℝ × M} (hinv : (Ω p.1 p.2).IsInvertible)
    (hskew : ∀ u v, Ω p.1 p.2 u v = -Ω p.1 p.2 v u)
    (L : E →L[ℝ] ℝ) (Z : E) (hface : Ω p.1 p.2 Z = -L)
    (hhor : α p.1 p.2 Z=0) : L (manifoldMoserField Ω α p)=0 := by
  let v : E := manifoldMoserField Ω α p
  change L v = 0
  have hs : Ω p.1 p.2 v = -α p.1 p.2 := by
    simp only [v,manifoldMoserField,map_neg,hinv.self_apply_inverse]
  have hh := congrArg (fun A : E →L[ℝ] ℝ => A Z) hs
  have hz := congrArg (fun A : E →L[ℝ] ℝ => A v) hface
  simp only [neg_apply,hhor,neg_zero] at hh
  simp only [neg_apply] at hz
  rw [hskew] at hh
  linarith


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def chartField (v : (x : M) → TangentSpace 𝓘(ℝ,E) x) (x : M) (y : E) : E :=
  let z := (extChartAt 𝓘(ℝ,E) x).symm y
  tangentCoordChange 𝓘(ℝ,E) z x z (v z)

theorem chartField_smoothOn {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ContDiffOn ℝ ∞ (chartField v x) (extChartAt 𝓘(ℝ,E) x).target := by
  have h := (contMDiff_iff.mp hv).2 x (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hh := h.snd
  change ContDiffOn ℝ ∞ (chartField v x) _ at hh
  apply hh.mono
  intro y hy
  refine ⟨hy,?_⟩
  simp only [Set.mem_preimage, extChartAt_source, TangentBundle.mem_chart_source_iff]
  simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,E) x).map_target hy

theorem chartCurve_hasMFDerivAt {v : (z : M) → TangentSpace 𝓘(ℝ,E) z}
    (x : M) {f : ℝ → E} {t : ℝ}
    (hf : f t ∈ (extChartAt 𝓘(ℝ,E) x).target)
    (hd : HasDerivAt f (chartField v x (f t)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) x).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt 𝓘(ℝ,E) x).symm (f t)))) := by
  change M → E at v
  let z : M := (extChartAt 𝓘(ℝ,E) x).symm (f t)
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) x).source := (extChartAt 𝓘(ℝ,E) x).map_target hf
  have hz' := mem_extChartAt_source (I := 𝓘(ℝ,E)) z
  have hd' : HasDerivAt f (tangentCoordChange 𝓘(ℝ,E) z x z (v z)) t := hd
  refine ⟨(continuousAt_extChartAt_symm'' hf).comp hd.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps,hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt 𝓘(ℝ,E) z ∘ (extChartAt 𝓘(ℝ,E) x).symm) ∘ f) (v z) t
  rw [←tangentCoordChange_self (I := 𝓘(ℝ,E)) (x := z) (z := z) (v := v z) hz',
    ←tangentCoordChange_comp (x := x) ⟨⟨hz',hz⟩,hz'⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hd'
  apply HasFDerivWithinAt.hasFDerivAt (s := range 𝓘(ℝ,E)) _ (by simp)
  rw [←(extChartAt 𝓘(ℝ,E) x).right_inv hf]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hz,hz'⟩


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_bounded_trajectory {X : E → E} {L : ℝ≥0}
    (hL : LipschitzWith L X) {B : ℝ≥0} (hB : ∀ x, ‖X x‖ ≤ B) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (X (γ t)) t := by
  have hex (a : ℝ≥0) : ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Icc (-(a:ℝ)) a, HasDerivWithinAt γ (X (γ t)) (Icc (-(a:ℝ)) a) t := by
    let t₀ : Icc (-(a:ℝ)) a := ⟨0, neg_nonpos.mpr a.coe_nonneg, a.coe_nonneg⟩
    have hp : IsPicardLindelof (fun _ : ℝ => X) t₀ x (B*a) 0 B L := {
      lipschitzOnWith := fun _ _ => hL.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ y _ => hB y
      mul_max_le := by simp [t₀] }
    exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose u hu0 hud using hex
  have heq {a b : ℝ≥0} (hab : a ≤ b) : EqOn (u a) (u b) (Ioo (-(a:ℝ)) a) := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha' : (0:ℝ) < a := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
      apply ODE_solution_unique_of_mem_Ioo
        (s := fun _ => univ) (fun _ _ => hL.lipschitzOnWith)
        (t₀ := 0) ⟨by linarith,ha'⟩
        (fun t ht => ⟨(hud a t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),mem_univ _⟩)
      · intro t ht
        have ht' : t ∈ Ioo (-(b:ℝ)) b := by
          have hab' : (a:ℝ) ≤ b := hab
          constructor <;> linarith [ht.1,ht.2]
        exact ⟨(hud b t (Ioo_subset_Icc_self ht')).hasDerivAt
          (Icc_mem_nhds ht'.1 ht'.2),mem_univ _⟩
      · rw [hu0 a,hu0 b]
  let γ : ℝ → E := fun t => u (‖t‖₊+1) t
  have hmatch {a : ℝ≥0} : EqOn γ (u a) (Ioo (-(a:ℝ)) a) := by
    intro t ht
    have ht' : t ∈ Ioo (-((‖t‖₊+1:ℝ≥0):ℝ)) (‖t‖₊+1:ℝ≥0) := by
      simp only [NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs]
      exact abs_lt.mp (lt_add_one |t|)
    rcases le_total (‖t‖₊+1) a with h | h
    · exact heq h ht'
    · exact (heq h ht).symm
  refine ⟨γ,?_,?_⟩
  · change u (‖(0:ℝ)‖₊+1) 0 = x
    exact hu0 _
  · intro t
    let a : ℝ≥0 := ‖t‖₊+1
    have ht : t ∈ Ioo (-(a:ℝ)) a := by
      simpa only [a,NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs,mem_Ioo]
        using abs_lt.mp (lt_add_one |t|)
    have he : γ =ᶠ[𝓝 t] u a := Filter.eventually_of_mem
      (isOpen_Ioo.mem_nhds ht) (fun s hs => hmatch hs)
    have hd := (hud a t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [he.eq_of_nhds]
    exact hd.congr_of_eventuallyEq he


end

section
open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem stepEndpoint_eq_trajectory {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖*L < 1) {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) :
    stepEndpoint X hX h (γ 0) = γ h := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  let u : C(Time,E) := ⟨fun s => γ (h*(s:ℝ)),
    hγc.comp (continuous_const.mul continuous_subtype_val)⟩
  have hu0 : u ⟨0,by simp⟩ = γ 0 := by simp [u]
  have hud (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (extendPath u) (h • X (extendPath u s)) s := by
    have he : extendPath u =ᶠ[𝓝 s] (fun t => γ (h*t)) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
      exact extendPath_coe u ⟨t,ht⟩
    have hd := (hγ (h*s)).scomp s (hasDerivAt_const_mul h)
    rw [he.eq_of_nhds]
    exact hd.congr_of_eventuallyEq he
  have he := fixedStep_eq_solution X hX hh u (γ 0) hu0 hud
  have he' := congrArg (fun v : C(Time,E) => v ⟨1,by simp⟩) he
  simpa only [stepEndpoint,u,ContinuousMap.coe_mk,mul_one] using he'

def shortFlow {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (p : ℝ × E) : E :=
  stepEndpoint X hX p.1 p.2

theorem shortFlow_zero {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (x : E) :
    shortFlow X hX (0,x) = x := by
  have he := fixedStep_equation X hX (h := 0) (by simp) x
  simp only [zero_smul,add_zero] at he
  change fixedStep X hX 0 x ⟨1,by simp⟩ = x
  rw [he]
  rfl

variable [FiniteDimensional ℝ E]

theorem shortFlow_smoothOn {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) :
    ContDiffOn ℝ ∞ (shortFlow X hX) {p : ℝ × E | ‖p.1‖*(L:ℝ) < 1} := by
  have hc := (localPath_smooth X hX hXs).comp
    (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => hp)
  exact (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).contDiff.comp_contDiffOn hc

omit [FiniteDimensional ℝ E] in

theorem shortFlow_derivative {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXc : HasCompactSupport X) {t : ℝ} (ht : ‖t‖*(L:ℝ) < 1) (x : E) :
    HasDerivAt (fun s => shortFlow X hX (s,x)) (X (shortFlow X hX (t,x))) t := by
  obtain ⟨B,hB⟩ := X.continuous.bounded_above_of_compact_support hXc
  have hB0 : 0 ≤ B := (norm_nonneg (X x)).trans (hB x)
  obtain ⟨γ,hγ0,hγd⟩ := exists_global_bounded_trajectory hX (B := ⟨B,hB0⟩) hB x
  have hopen : IsOpen {s : ℝ | ‖s‖*(L:ℝ) < 1} :=
    isOpen_lt (continuous_id.norm.mul continuous_const) continuous_const
  have he : (fun s => shortFlow X hX (s,x)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    change stepEndpoint X hX s x = γ s
    rw [←hγ0]
    exact stepEndpoint_eq_trajectory X hX hs hγd
  rw [he.eq_of_nhds]
  exact (hγd t).congr_of_eventuallyEq he


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_local_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ∃ (ε : ℝ) (U : Set E) (Φ : ℝ × E → M),
      0 < ε ∧ IsOpen U ∧ extChartAt 𝓘(ℝ,E) x x ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      ContMDiffOn 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ Φ (Ioo (-ε) ε ×ˢ U) ∧
      (∀ y ∈ U, Φ (0,y) = (extChartAt 𝓘(ℝ,E) x).symm y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (fun t => Φ (t,y)) v (Ioo (-ε) ε)) := by
  let c := extChartAt 𝓘(ℝ,E) x x
  have hc : c ∈ (extChartAt 𝓘(ℝ,E) x).target := mem_extChartAt_target x
  have hT := isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x
  obtain ⟨χ,_,_,_,_,_,hXs,hXc,hEq⟩ := exists_smooth_compact_extension
    (isCompact_singleton (x := c)) hT (singleton_subset_iff.mpr hc) (chartField_smoothOn hv x)
  let X : C(E,E) := ⟨fun y => χ y • chartField v x y,hXs.continuous⟩
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  have heq : ∀ᶠ y in 𝓝 c, X y = chartField v x y := by
    simpa only [nhdsSet_singleton,X,ContinuousMap.coe_mk] using hEq
  have hnb : {y | X y = chartField v x y ∧ y ∈ (extChartAt 𝓘(ℝ,E) x).target} ∈ 𝓝 c :=
    heq.and (hT.mem_nhds hc)
  obtain ⟨V,hVsub,hVo,hcV⟩ := mem_nhds_iff.mp hnb
  let D : Set (ℝ × E) := {p | ‖p.1‖*(L:ℝ) < 1}
  have hDo : IsOpen D := isOpen_lt (continuous_fst.norm.mul continuous_const) continuous_const
  have hcD : ((0,c) : ℝ × E) ∈ D := by simp [D]
  have hflowc : ContinuousAt (shortFlow X hL) (0,c) :=
    ((shortFlow_smoothOn X hL hXs).contDiffAt (hDo.mem_nhds hcD)).continuousAt
  have hpV : (shortFlow X hL) ⁻¹' V ∈ 𝓝 ((0,c) : ℝ × E) := by
    apply hflowc.preimage_mem_nhds
    rw [shortFlow_zero]
    exact hVo.mem_nhds hcV
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hDo.mem_nhds hcD) hpV)
  let U : Set E := Metric.ball c δ
  have hroom {t : ℝ} (ht : t ∈ Ioo (-δ) δ) {y : E} (hy : y ∈ U) :
      (t,y) ∈ D ∧ shortFlow X hL (t,y) ∈ V := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by simpa only [dist_zero_right,Real.norm_eq_abs] using (abs_lt.mpr ht),hy⟩
  have hUtarget : U ⊆ (extChartAt 𝓘(ℝ,E) x).target := by
    intro y hy
    have hm := (hroom (t := 0) ⟨by linarith,hδ⟩ hy).2
    rw [shortFlow_zero] at hm
    exact (hVsub hm).2
  let Φ : ℝ × E → M := (extChartAt 𝓘(ℝ,E) x).symm ∘ shortFlow X hL
  refine ⟨δ,U,Φ,hδ,Metric.isOpen_ball,Metric.mem_ball_self hδ,hUtarget,?_,?_,?_⟩
  · apply (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) x).comp
      ((shortFlow_smoothOn X hL hXs).mono (fun p hp => (hroom hp.1 hp.2).1)).contMDiffOn
    intro p hp
    exact (hVsub (hroom hp.1 hp.2).2).2
  · intro y _
    change (extChartAt 𝓘(ℝ,E) x).symm (shortFlow X hL (0,y)) = _
    rw [shortFlow_zero]
  · intro y hy t ht
    have hm := hroom ht hy
    have hd := shortFlow_derivative X hL hXc hm.1 y
    rw [(hVsub hm.2).1] at hd
    exact (chartCurve_hasMFDerivAt x (hVsub hm.2).2 hd).hasMFDerivWithinAt

theorem exists_smooth_local_manifold_family
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ∃ (ε : ℝ) (W : Set M) (Ψ : ℝ × M → M),
      0 < ε ∧ IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  obtain ⟨ε,U,Φ,hε,hU,hxU,_,hΦ,hΦ0,hΦd⟩ := exists_smooth_local_manifold_flow hv x
  let e := extChartAt 𝓘(ℝ,E) x
  let W : Set M := e.source ∩ e ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) hU
  have hxW : x ∈ W := ⟨mem_extChartAt_source x,hxU⟩
  let Ψ : ℝ × M → M := fun p => Φ (p.1,e p.2)
  refine ⟨ε,W,Ψ,hε,hW,hxW,?_,?_,?_⟩
  · have hc : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M => e p.2) (Ioo (-ε) ε ×ˢ W) :=
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := x)).comp contMDiff_snd.contMDiffOn
        (fun p hp => by
          change p.2 ∈ (chartAt E x).source
          simpa only [e,extChartAt_source] using hp.2.1)
    exact hΦ.comp (contMDiff_fst.contMDiffOn.prodMk_space hc) (fun _ hp => ⟨hp.1,hp.2.2⟩)
  · intro y hy
    exact (hΦ0 (e y) hy.2).trans (e.left_inv hy.1)
  · intro y hy
    exact hΦd (e y) hy.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_uniform_smooth_manifold_families
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M, ∃ (W : Set M) (Ψ : ℝ × M → M),
      IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  classical
  choose ε W Ψ hε hW hxW hΨs hΨ0 hΨd using exists_smooth_local_manifold_family hv
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW (fun x _ => mem_iUnion.mpr ⟨x,hxW x⟩)
  have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, δ ≤ ε x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ,hδ,hδs⟩ := ih
      refine ⟨min (ε a) δ,lt_min (hε a) hδ,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδs x hx)
  obtain ⟨δ,hδ,hδs⟩ := hsmall
  refine ⟨δ,hδ,fun x => ?_⟩
  by_cases hx : x ∈ K
  · obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs hx)
    have hI : Ioo (-δ) δ ⊆ Ioo (-ε a) (ε a) :=
      Ioo_subset_Ioo (neg_le_neg (hδs a ha)) (hδs a ha)
    exact ⟨W a,Ψ a,hW a,hxa,(hΨs a).mono (prod_mono hI Subset.rfl),
      hΨ0 a,fun y hy => (hΨd a y hy).mono hI⟩
  · exact ⟨Kᶜ,Prod.snd,hK.isClosed.isOpen_compl,hx,contMDiff_snd.contMDiffOn,
      fun _ _ => rfl,fun y hy => (isMIntegralCurve_const (hvK y hy)).isMIntegralCurveOn _⟩

theorem exists_global_compact_manifold_trajectory
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε,hε,h⟩ := exists_uniform_smooth_manifold_families hv hK hvK
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hv.of_le (by simp)) hε _ x
  intro y
  obtain ⟨W,Ψ,_,hy,_,hΨ0,hΨd⟩ := h y
  exact ⟨fun t => Ψ (t,y),hΨ0 y hy,hΨd y hy⟩



end PackingSufficiencySupport.Hamiltonian
end

end OAI
