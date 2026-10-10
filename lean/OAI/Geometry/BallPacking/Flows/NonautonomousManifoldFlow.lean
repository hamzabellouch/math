import Mathlib
import OAI.Geometry.BallPacking.Flows.FlowSmoothExtension

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_nonautonomous_manifold_flow
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x)) = x ∧ Φ (t,Ψ (t,x)) = x) ∧
      (∀ x t, t ∈ Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x))))) ∧
      (∀ x, (∀ s, V (s,x) = 0) → ∀ t, Φ (t,x) = x) := by
  obtain ⟨χ,G,hχ,hχ1,hGs,hG0,hGa,hGd,hclock⟩ := exists_compact_time_lift hV
  let Φ : ℝ × M → M := fun p => (G (p.1,(0,p.2))).2
  let Ψ : ℝ × M → M := fun p => (G (-p.1,p)).2
  have hΦs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ :=
    contMDiff_snd.comp (hGs.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd)))
  have hneg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => -p.1) :=
    contDiff_neg.contMDiff.comp contMDiff_fst
  have hΨs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ :=
    contMDiff_snd.comp (hGs.comp (hneg.prodMk contMDiff_id))
  have hΦclock (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) (x : M) : G (t,(0,x)) = (t,Φ (t,x)) := by
    apply Prod.ext
    · simpa only [zero_add] using hclock 0 (by norm_num) x t ht
    · rfl
  refine ⟨Φ,Ψ,hΦs,hΨs,?_,?_,?_,?_⟩
  · intro x
    exact congrArg Prod.snd (hG0 (0,x))
  · intro t ht x
    have ht' : t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    have hmt : -t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    constructor
    · change (G (-t,(t,Φ (t,x)))).2 = x
      rw [←hΦclock t ht' x,←hGa,neg_add_cancel,hG0]
    · have hΨclock : G (-t,(t,x)) = (0,Ψ (t,x)) := by
        apply Prod.ext
        · simpa only [add_neg_cancel] using hclock t ht x (-t) hmt
        · rfl
      change (G (t,(0,Ψ (t,x)))).2 = x
      rw [←hΨclock,←hGa,add_neg_cancel,hG0]
  · intro x t ht
    have hd := timeLiftField_spatial_derivative (hGd (0,x) t)
    have hh : χ t = 1 := hχ1 t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [hΦclock t ht x] at hd
    simpa only [hh,one_smul] using hd
  · intro x hx t
    exact timeLift_spatial_stationary hχ hV hx (hGd (0,x)) (hG0 (0,x)) t

def nonautonomousSlice (Φ Ψ : ℝ × M → M)
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ)
    (t : ℝ) (hinv : ∀ x, Ψ (t,Φ (t,x)) = x ∧ Φ (t,Ψ (t,x)) = x) :
    M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M where
  toFun x := Φ (t,x)
  invFun x := Ψ (t,x)
  left_inv x := (hinv x).1
  right_inv x := (hinv x).2
  contMDiff_toFun := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := hΨ.comp (contMDiff_const.prodMk contMDiff_id)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_spatially_compact_nonautonomous_flow
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hVK : ∀ s x, x ∉ K → V (s,x)=0) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x)) = x ∧ Φ (t,Ψ (t,x)) = x) ∧
      (∀ x t, t ∈ Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x))))) ∧
      (∀ x, (∀ s, V (s,x) = 0) → ∀ t, Φ (t,x) = x) := by
  obtain ⟨χ,G,hχ,hχ1,hGs,hG0,hGa,hGd,hclock⟩ := exists_spatially_compact_time_lift hV hK hVK
  let Φ : ℝ × M → M := fun p => (G (p.1,(0,p.2))).2
  let Ψ : ℝ × M → M := fun p => (G (-p.1,p)).2
  have hΦs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ :=
    contMDiff_snd.comp (hGs.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd)))
  have hneg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => -p.1) :=
    contDiff_neg.contMDiff.comp contMDiff_fst
  have hΨs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ :=
    contMDiff_snd.comp (hGs.comp (hneg.prodMk contMDiff_id))
  have hΦclock (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) (x : M) : G (t,(0,x)) = (t,Φ (t,x)) := by
    apply Prod.ext
    · simpa only [zero_add] using hclock 0 (by norm_num) x t ht
    · rfl
  refine ⟨Φ,Ψ,hΦs,hΨs,?_,?_,?_,?_⟩
  · intro x
    exact congrArg Prod.snd (hG0 (0,x))
  · intro t ht x
    have ht' : t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    have hmt : -t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    constructor
    · change (G (-t,(t,Φ (t,x)))).2 = x
      rw [←hΦclock t ht' x,←hGa,neg_add_cancel,hG0]
    · have hΨclock : G (-t,(t,x)) = (0,Ψ (t,x)) := by
        apply Prod.ext
        · simpa only [add_neg_cancel] using hclock t ht x (-t) hmt
        · rfl
      change (G (t,(0,Ψ (t,x)))).2 = x
      rw [←hΨclock,←hGa,add_neg_cancel,hG0]
  · intro x t ht
    have hd := timeLiftField_spatial_derivative (hGd (0,x) t)
    have hh : χ t = 1 := hχ1 t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [hΦclock t ht x] at hd
    simpa only [hh,one_smul] using hd
  · intro x hx t
    exact timeLift_spatial_stationary hχ hV hx (hGd (0,x)) (hG0 (0,x)) t

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open Set

theorem constant_above_on_convex {s : Set ℝ} (hs : Convex ℝ s)
    {f : ℝ → ℝ} (hf : ContinuousOn f s) {a t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hzero : ∀ t ∈ s, a < f t → HasDerivWithinAt f 0 s t)
    (h₀ : a < f t₀) : ∀ t ∈ s, f t = f t₀ := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.isPreconnected
  let T : Set s := {t | f t = f t₀}
  have hfc : Continuous (fun t : s => f t) := hf.domRestrict
  have hc : IsClosed T := isClosed_eq hfc continuous_const
  have ho : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hft : a < f t := by rw [ht]; exact h₀
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const hfc).mem_nhds hft)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds t hr)
    intro u hu
    let U : Set ℝ := s ∩ Metric.ball (t : ℝ) r
    have hUc : Convex ℝ U := hs.inter (convex_ball (t:ℝ) r)
    have hUd (v : ℝ) (hv : v ∈ U) : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) U v := by
      have habove : a < f v := hball (show (⟨v,hv.1⟩ : s) ∈ Metric.ball t r from hv.2)
      simpa using (hzero v hv.1 habove).hasFDerivWithinAt.mono inter_subset_left
    have htU : (t : ℝ) ∈ U := ⟨t.property,Metric.mem_ball_self hr⟩
    have huU : (u : ℝ) ∈ U := ⟨u.property,hu⟩
    have hb := hUc.norm_image_sub_le_of_norm_hasFDerivWithin_le hUd
      (fun v hv => by simp : ∀ v ∈ U, ‖(0 : ℝ →L[ℝ] ℝ)‖ ≤ (0:ℝ)) htU huU
    have he : f u = f t := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hb))
    exact he.trans ht
  have he : T = univ := (show IsClopen T from ⟨hc,ho⟩).eq_univ ⟨⟨t₀,ht₀⟩,rfl⟩
  intro t ht
  exact (show (⟨t,ht⟩ : s) ∈ T from he.symm ▸ mem_univ _)

theorem sublevel_iff_of_zero_in_collar {s : Set ℝ} (hs : Convex ℝ s)
    {f : ℝ → ℝ} (hf : ContinuousOn f s) {a c t u : ℝ} (hac : a < c)
    (ht : t ∈ s) (hu : u ∈ s)
    (hzero : ∀ r ∈ s, a < f r → HasDerivWithinAt f 0 s r) :
    f t ≤ c ↔ f u ≤ c := by
  have hdir (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) (h : f t ≤ c) : f u ≤ c := by
    by_contra hn
    have hc : c < f u := lt_of_not_ge hn
    have he := constant_above_on_convex hs hf hu hzero (hac.trans hc) t ht
    linarith
  exact ⟨hdir t u ht hu,hdir u t hu ht⟩

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifold_flow_sublevels_iff
    {Φ : ℝ × M → M} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hΦ0 : ∀ x, Φ (0,x)=x)
    (hODE : ∀ x t, t ∈ Icc (0:ℝ) 1 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))))
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i<c i)
    (htan : ∀ i t x, a i<μ i x → mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) x (V (t,x))=0)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : M) :
    (∀ i, μ i (Φ (t,x))≤c i) ↔ (∀ i, μ i x≤c i) := by
  have he (i : ι) : μ i (Φ (t,x))≤c i ↔ μ i x≤c i := by
    have hz (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (ha : a i<μ i (Φ (s,x))) :
        HasDerivWithinAt (fun r => μ i (Φ (r,x))) 0 (Icc (0:ℝ) 1) s := by
      have hd := ((hμ i).mdifferentiable (by simp) (Φ (s,x))).hasMFDerivAt.comp s
        (hODE x s hs)
      have heq : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) (Φ (s,x))).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x))))=(0 : ℝ →L[ℝ] ℝ) := by
        ext
        simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
          map_smul,htan i s (Φ (s,x)) ha,smul_zero]
        rfl
      have hd' : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
          (fun r => μ i (Φ (r,x))) s 0 := hd.congr_mfderiv heq
      exact (hasDerivAt_iff_hasFDerivAt.mpr
        (by simpa using! hasMFDerivAt_iff_hasFDerivAt.mp hd')).hasDerivWithinAt
    have hc : ContinuousOn (fun r => μ i (Φ (r,x))) (Icc (0:ℝ) 1) :=
      ((hμ i).continuous.comp (hΦ.continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
    simpa only [hΦ0] using sublevel_iff_of_zero_in_collar (convex_Icc (0:ℝ) 1)
      hc (hac i) ht (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) hz
  exact forall_congr' he

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifold_flow_image_sublevels
    {Φ Ψ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ)
    (t : ℝ) (hinv : ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x)
    {D : Set M} (hD : ∀ x, Φ (t,x) ∈ D ↔ x ∈ D) :
    (fun x => Φ (t,x)) '' D=D ∧
      (fun x => Φ (t,x)) '' interior D=interior D := by
  let f := nonautonomousSlice Φ Ψ hΦ hΨ t hinv
  have he : (fun x => Φ (t,x)) '' D=D := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; exact (hD x).mpr hx
    · intro hy
      exact ⟨Ψ (t,y),(hD _).mp (by simpa only [(hinv y).2] using hy),(hinv y).2⟩
  refine ⟨he,?_⟩
  change f.toHomeomorph '' interior D=interior D
  rw [f.toHomeomorph.image_interior]
  exact congrArg interior he

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifold_relative_sublevel_moser
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i<c i)
    (hD : IsCompact {x | ∀ i, μ i x≤c i})
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x≤c i} ⊆ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (hskew : ∀ p ∈ U, ∀ v w, Ω p.1 p.2 v w = -Ω p.1 p.2 w v)
    (hclosed : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ,E) b).target →
      (t,(extChartAt 𝓘(ℝ,E) b).symm y) ∈ U → ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (0,w) u v = 0)
    (htime : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ,E) b).target →
      (t,(extChartAt 𝓘(ℝ,E) b).symm y) ∈ U → ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t,y) (0,w) v)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
      α p.1 p.2=0 ∨
      (Ω p.1 p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        α p.1 p.2 (Z i p.2)=0)) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → Φ (t,x)=x) ∧
      (∀ x, (∀ t, α t x=0) → ∀ t, Φ (t,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        (fun x => Φ (t,x)) '' {x | ∀ i, μ i x≤c i}={x | ∀ i, μ i x≤c i} ∧
        (fun x => Φ (t,x)) '' interior {x | ∀ i, μ i x≤c i}=interior {x | ∀ i, μ i x≤c i}) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (∀ i, μ i x≤c i) → ∀ v w,
        manifoldPullback Φ Ω t x v w=Ω 0 x v w) := by
  obtain ⟨V,hV,hVe,hVz,⟨C,hC,hVC⟩,hVtan⟩ := exists_joint_localized_manifold_moser_field
    hΩ hα (isCompact_Icc.prod hD) hU hDU hinv
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hODE,hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hC hVC
  have htangent (i : ι) (t : ℝ) (x : M) (hx : a i<μ i x) :
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) x (V (t,x))=0 := by
    apply hVtan
    intro hp
    rcases hface i (t,x) hp hx with hz | ⟨hm,hh⟩
    · simp only [manifoldMoserField,hz,map_zero,neg_zero]
      exact (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) x).map_zero
    · exact manifoldMoserField_moment_tangent (hinv (t,x) hp) (hskew (t,x) hp)
        _ (Z i x) hm hh
  have hiff (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : M) :
      (∀ i, μ i (Φ (t,x))≤c i) ↔ (∀ i, μ i x≤c i) := by
    apply manifold_flow_sublevels_iff hΦ hΦ0 _ μ hμ a c hac htangent t ht x
    intro y s hs
    exact hODE y s ⟨by linarith [hs.1],by linarith [hs.2]⟩
  refine ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,⟨C,hC,?_⟩,?_,?_,?_⟩
  · intro t x hx
    exact hfix x (fun s => hVC s x hx) t
  · intro x hx t
    exact hfix x (fun s => hVz (s,x) (hx s)) t
  · intro t ht
    exact manifold_flow_image_sublevels hΦ hΨ t (hΦinv t ht) (hiff t ht)
  · intro t ht x hx v w
    have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
        HasDerivAt (fun r => manifoldPullback Φ Ω r x v w) 0 s := by
      apply local_manifold_form_transport_derivative hΦ hV isOpen_Ioo hODE hΩ
        (show s ∈ Ioo (-2:ℝ) 2 by constructor <;> linarith [hs.1,hs.2]) x
      intro b y hy he
      have hpK : (s,(extChartAt 𝓘(ℝ,E) b).symm y) ∈
          Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x≤c i} :=
        ⟨hs,by rw [he]; exact (hiff s hs x).mpr hx⟩
      have hpU := hDU hpK
      have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) b).target) ∈ 𝓝 (s,y) :=
        (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b)).mem_nhds ⟨mem_univ _,hy⟩
      apply joint_manifold_moser_PDE hV hU hy hpU hinv
        (hVe.filter_mono (nhds_le_nhdsSet hpK)) ((hΩ b).contDiffAt hn)
        ((hα b).contDiffAt hn) _ (hclosed s b y hy hpU) (htime s b y hy hpU)
      intro u z
      exact hskew _ hpU _ _
    have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (fun s hs => (by simp : ‖(0:ℝ)‖ ≤ (0:ℝ)))
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) ht
    have hconst : manifoldPullback Φ Ω t x v w=manifoldPullback Φ Ω 0 x v w := by
      simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using he
    rw [hconst]
    have hid : (fun y => Φ (0,y))=id := funext hΦ0
    have hDifferential : preferredDifferential (E := E) (fun y => Φ (0,y)) x=
        ContinuousLinearMap.id ℝ E := by
      change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (0,y)) x=_
      rw [hid]
      exact mfderiv_id
    rw [manifoldPullback,hDifferential]
    simp only [hΦ0,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

theorem manifold_exact_sublevel_moser
    {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i<c i)
    (hD : IsCompact {x | ∀ i, μ i x≤c i})
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x≤c i} ⊆ U)
    (hinv : ∀ p ∈ U, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
      (∀ t, Γ t p.2=Γ 0 p.2) ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        ∀ t, Γ t p.2 (Z i p.2)=Γ 0 p.2 (Z i p.2))) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → Φ (t,x)=x) ∧
      (∀ x, (∀ t, Γ t x=Γ 0 x) → ∀ t, Φ (t,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        (fun x => Φ (t,x)) '' {x | ∀ i, μ i x≤c i}={x | ∀ i, μ i x≤c i} ∧
        (fun x => Φ (t,x)) '' interior {x | ∀ i, μ i x≤c i}=interior {x | ∀ i, μ i x≤c i}) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (∀ i, μ i x≤c i) → ∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
          manifoldExteriorOneForm (Γ 0) x v w) := by
  have hf : ∀ i p, p ∈ U → a i<μ i p.2 →
      manifoldTimePrimitive Γ p.1 p.2=0 ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        manifoldTimePrimitive Γ p.1 p.2 (Z i p.2)=0) := by
    intro i p hp ha
    rcases hface i p hp ha with hz | ⟨hm,hz⟩
    · exact Or.inl (manifoldTimePrimitive_stationary hz p.1)
    · exact Or.inr ⟨hm,manifoldTimePrimitive_eval_constant hΓ hz p.1⟩
  have hΩ := manifoldExteriorOneForm_path_smooth hΓ
  have hα := manifoldTimePrimitive_smooth hΓ
  have hc := manifoldExteriorOneForm_path_closed hΓ
  have ht := manifoldExteriorOneForm_path_time hΓ
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hC,hfix,hpres,hpull⟩ := manifold_relative_sublevel_moser
    (Ω := fun s => manifoldExteriorOneForm (Γ s)) (α := manifoldTimePrimitive Γ)
    hΩ hα μ hμ a c hac hD hU hDU hinv
    (fun p _ v w => manifoldExteriorOneForm_skew (Γ p.1) p.2 v w)
    (fun t b y hy _ u v w => hc t b y hy u v w)
    (fun t b y hy _ v w => ht t b y hy v w) Z hf
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hC,?_,hpres,hpull⟩
  intro x hx t
  exact hfix x (fun s => manifoldTimePrimitive_stationary hx s) t

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def PreservesTwoFormOn (e : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M)
    (Ω₀ Ω₁ : ManifoldTwoForm E M) (D : Set M) : Prop :=
  ∀ x ∈ D, ∀ v w, Ω₁ (e x)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e x v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e x w) = Ω₀ x v w

namespace PreservesTwoFormOn
variable {e f : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M}
  {Ω₀ Ω₁ Ω₂ : ManifoldTwoForm E M} {D : Set M}

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem trans (he : PreservesTwoFormOn e Ω₀ Ω₁ D)
    (hf : PreservesTwoFormOn f Ω₁ Ω₂ D) (hmap : MapsTo e D D) :
    PreservesTwoFormOn (e.trans f) Ω₀ Ω₂ D := by
  intro x hx v w
  have hd := mfderiv_comp x (f.contMDiff.mdifferentiable (by simp) (e x))
    (e.contMDiff.mdifferentiable (by simp) x)
  change Ω₂ (f (e x)) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f ∘ e) x v)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f ∘ e) x w) = _
  rw [hd]
  exact (hf (e x) (hmap hx) _ _).trans (he x hx v w)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem symm (he : PreservesTwoFormOn e Ω₀ Ω₁ D) (hD : e '' D = D) :
    PreservesTwoFormOn e.symm Ω₁ Ω₀ D := by
  intro y hy v w
  have hx : e.symm y ∈ D := by
    obtain ⟨x,hx,hxy⟩ := hD.symm ▸ hy
    simpa only [←hxy,e.symm_apply_apply] using hx
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (e.symm y))
    (e.symm.contMDiff.mdifferentiable (by simp) y)
  have heq : (e : M → M) ∘ e.symm = id := by funext z; exact e.apply_symm_apply z
  rw [heq,mfderiv_id] at hd
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hd.symm
  have hw := congrArg (fun L : E →L[ℝ] E => L w) hd.symm
  have h := he (e.symm y) hx (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y v)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y w)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e (e.symm y) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y v)=v at hv
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e (e.symm y) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y w)=w at hw
  rw [hv,hw,e.apply_symm_apply] at h
  exact h.symm

end PreservesTwoFormOn

variable [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem manifold_exact_moser_endpoint
    {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i<c i)
    (hD : IsCompact {x | ∀ i, μ i x≤c i})
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x≤c i} ⊆ U)
    (hinv : ∀ p ∈ U, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
      (∀ t, Γ t p.2=Γ 0 p.2) ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        ∀ t, Γ t p.2 (Z i p.2)=Γ 0 p.2 (Z i p.2))) :
    ∃ e : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M,
      e '' {x | ∀ i, μ i x≤c i}={x | ∀ i, μ i x≤c i} ∧
      e '' interior {x | ∀ i, μ i x≤c i}=interior {x | ∀ i, μ i x≤c i} ∧
      PreservesTwoFormOn e (manifoldExteriorOneForm (Γ 0)) (manifoldExteriorOneForm (Γ 1))
        {x | ∀ i, μ i x≤c i} ∧
      (∃ C : Set M, IsCompact C ∧ ∀ x, x ∉ C → e x=x) ∧
      (∀ x, (∀ t, Γ t x=Γ 0 x) → e x=x) := by
  obtain ⟨Φ,Ψ,hΦ,hΨ,_,hi,hC,hfix,hpres,hpull⟩ :=
    manifold_exact_sublevel_moser hΓ μ hμ a c hac hD hU hDU hinv Z hface
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  let e : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M :=
    { toFun := fun x => Φ (1,x)
      invFun := fun x => Ψ (1,x)
      left_inv := fun x => (hi 1 h1 x).1
      right_inv := fun x => (hi 1 h1 x).2
      contMDiff_toFun := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hΨ.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨e,(hpres 1 h1).1,(hpres 1 h1).2,?_,?_,?_⟩
  · intro x hx v w
    exact hpull 1 h1 x hx v w
  · obtain ⟨C,hc,h⟩ := hC
    exact ⟨C,hc,fun x hx => h 1 x hx⟩
  · intro x hx
    exact hfix x hx 1

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def FormNeighborhoodEmbedding (K : Set N) (σ : ManifoldTwoForm F N)
    (Ω : ManifoldTwoForm E M) (f : N → M) : Prop :=
  ∃ U : Set N, IsOpen U ∧ K ⊆ U ∧ ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ v w, Ω (f x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) f x v) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) f x w) = σ x v w

theorem FormNeighborhoodEmbedding.transport
    {K : Set N} {σ : ManifoldTwoForm F N} {Ω₀ Ω₁ : ManifoldTwoForm E M}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω₁ f)
    {D : Set M} (he : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M)
    (hform : PreservesTwoFormOn he Ω₁ Ω₀ D) (himage : MapsTo f K (interior D)) :
    FormNeighborhoodEmbedding K σ Ω₀ (he ∘ f) := by
  obtain ⟨U,hU,hKU,hs,hfemb,hσ⟩ := hf
  let W := U ∩ f ⁻¹' interior D
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU isOpen_interior
  have hWU : W ⊆ U := inter_subset_left
  refine ⟨W,hW,fun x hx => ⟨hKU hx,himage hx⟩,
    he.contMDiff.comp_contMDiffOn (hs.mono hWU),?_,?_⟩
  · exact he.toHomeomorph.isEmbedding.comp (hfemb.comp (Topology.IsEmbedding.inclusion hWU))
  · intro x hx v w
    have hd := mfderiv_comp x (he.contMDiff.mdifferentiable (by simp) (f x))
      ((hs.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))
    rw [hd]
    exact (hform (f x) (interior_subset hx.2) _ _).trans (hσ x hx.1 v w)

theorem transport_form_packing {ι : Type*} (K : ι → Set N)
    (σ : ManifoldTwoForm F N) (Ω₀ Ω₁ : ManifoldTwoForm E M) {D : Set M}
    (e : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M)
    (hform : PreservesTwoFormOn e Ω₀ Ω₁ D)
    (hD : e '' D=D) (hInt : e '' interior D=interior D)
    (f : ι → N → M) (hf : ∀ i, FormNeighborhoodEmbedding (K i) σ Ω₁ (f i))
    (himage : ∀ i, MapsTo (f i) (K i) (interior D))
    (hdis : Pairwise (fun i j => Disjoint (f i '' K i) (f j '' K j))) :
    (∀ i, FormNeighborhoodEmbedding (K i) σ Ω₀ (e.symm ∘ f i)) ∧
    (∀ i, MapsTo (e.symm ∘ f i) (K i) (interior D)) ∧
    Pairwise (fun i j => Disjoint ((e.symm ∘ f i) '' K i) ((e.symm ∘ f j) '' K j)) := by
  refine ⟨fun i => (hf i).transport e.symm (hform.symm hD) (himage i),?_,?_⟩
  · intro i x hx
    obtain ⟨y,hy,hyx⟩ := hInt.symm ▸ himage i hx
    simpa only [Function.comp_apply,←hyx,e.symm_apply_apply] using hy
  · intro i j hij
    rw [Set.image_comp,Set.image_comp]
    exact (hdis hij).image (e.symm.injective.injOn (s := Set.univ)) (subset_univ _) (subset_univ _)

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

theorem FormNeighborhoodEmbedding.postcompose {K : Set N}
    {σ : ManifoldTwoForm F N} {Ω₀ : ManifoldTwoForm E M} {Ω₁ : ManifoldTwoForm G P}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω₀ f)
    {T : Set M} (hT : IsOpen T) {g : M → P}
    (hg : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g T)
    (hemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hform : ∀ x ∈ T, ∀ v w, Ω₁ (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x w) = Ω₀ x v w)
    (him : MapsTo f K T) : FormNeighborhoodEmbedding K σ Ω₁ (g ∘ f) := by
  obtain ⟨U,hU,hKU,hs,he,hσ⟩ := hf
  let W := U ∩ f ⁻¹' T
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU hT
  have hWU : W ⊆ U := inter_subset_left
  have hWT : MapsTo f W T := inter_subset_right
  refine ⟨W,hW,fun x hx => ⟨hKU hx,him hx⟩,hg.comp (hs.mono hWU) hWT,?_,?_⟩
  · have he' := (he.comp (Topology.IsEmbedding.inclusion hWU)).codRestrict T
      (fun x : W => show f x.val ∈ T from x.property.2)
    exact hemb.comp he'
  · intro x hx v w
    have hd := mfderiv_comp x ((hg.contMDiffAt (hT.mem_nhds hx.2)).mdifferentiableAt (by simp))
      ((hs.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))
    rw [hd]
    exact (hform (f x) hx.2 _ _).trans (hσ x hx.1 v w)

theorem postcompose_form_packing {ι : Type*} (K : ι → Set N)
    (σ : ManifoldTwoForm F N) (Ω₀ : ManifoldTwoForm E M) (Ω₁ : ManifoldTwoForm G P)
    {T : Set M} (hT : IsOpen T) (g : M → P)
    (hg : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g T)
    (hemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hform : ∀ x ∈ T, ∀ v w, Ω₁ (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x w) = Ω₀ x v w)
    (f : ι → N → M) (hf : ∀ i, FormNeighborhoodEmbedding (K i) σ Ω₀ (f i))
    (him : ∀ i, MapsTo (f i) (K i) T)
    (hd : Pairwise (fun i j => Disjoint (f i '' K i) (f j '' K j))) :
    (∀ i, FormNeighborhoodEmbedding (K i) σ Ω₁ (g ∘ f i)) ∧
      Pairwise (fun i j => Disjoint ((g ∘ f i) '' K i) ((g ∘ f j) '' K j)) := by
  refine ⟨fun i => (hf i).postcompose hT hg hemb hform (him i),?_⟩
  have hinj : InjOn g T := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) heq)
  intro i j hij
  rw [Set.image_comp,Set.image_comp]
  exact (hd hij).image hinj (image_subset_iff.mpr (him i)) (image_subset_iff.mpr (him j))

end

def successorStandardForm (m : ℕ) : Ambient (m+1) →L[ℝ] Ambient (m+1) →L[ℝ] ℝ :=
  (productForm (phaseArea (ι := Fin m))).bilinearComp (complexSplitPhase m).toContinuousLinearMap (complexSplitPhase m).toContinuousLinearMap

@[simp] theorem successorStandardForm_apply (m : ℕ) (v w : Ambient (m+1)) :
    successorStandardForm m v w = standardForm v w := complexSplitPhase_form m v w

 theorem isBallEmbedding_iff_formNeighborhoodEmbedding {m : ℕ} {r : ℝ}
    {f : Ambient (m+1) → Ambient (m+1)} :
    IsBallEmbedding r f ↔ FormNeighborhoodEmbedding (closedBall (m+1) r)
      (fun _ => successorStandardForm m) (fun _ => successorStandardForm m) f := by
  constructor
  · rintro ⟨U,hU,hBU,hs,he,hform⟩
    refine ⟨U,hU,hBU,hs.contMDiffOn,he,?_⟩
    intro x hx v w
    rw [mfderiv_eq_fderiv]
    change successorStandardForm m (fderiv ℝ f x v) (fderiv ℝ f x w) = successorStandardForm m v w
    erw [successorStandardForm_apply, successorStandardForm_apply]
    exact hform x hx v w
  · rintro ⟨U,hU,hBU,hs,he,hform⟩
    refine ⟨U,hU,hBU,hs.contDiffOn,he,?_⟩
    intro x hx v w
    have hh := hform x hx v w
    rw [mfderiv_eq_fderiv] at hh
    change successorStandardForm m (fderiv ℝ f x v) (fderiv ℝ f x w) = successorStandardForm m v w at hh
    erw [successorStandardForm_apply, successorStandardForm_apply] at hh
    exact hh

end PackingSufficiencySupport.Hamiltonian
end

end OAI
