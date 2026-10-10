import Mathlib
import OAI.Geometry.BallPacking.Flows.ManifoldFormTransport

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem flow_smooth_of_uniform_local
    (F : ℝ × M → M) (hzero : ∀ x, F (0,x) = x)
    (hadd : ∀ s t x, F (s+t,x) = F (s,F (t,x)))
    {ε : ℝ} (hε : 0 < ε)
    (hs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F := by
  have hshort (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : M) :
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (t,x) :=
    hs.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
  have hmultiple (n : ℕ) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : M) :
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M => F ((n:ℝ)*p.1,p.2)) (t,x) := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,hzero] using
        (contMDiffAt_snd : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Prod.snd (t,x))
    | succ n ih =>
      have h := (hshort t ht (F ((n:ℝ)*t,x))).comp (t,x) (contMDiffAt_fst.prodMk ih)
      have he : (fun p : ℝ × M => F (((n+1:ℕ):ℝ)*p.1,p.2)) =
          (fun p : ℝ × M => F (p.1,F ((n:ℝ)*p.1,p.2))) := by
        funext p
        rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm,hadd]
      rw [he]
      exact h
  intro p
  obtain ⟨n,hn⟩ := exists_nat_gt (max (|p.1|/ε) 1)
  have hn0 : (0:ℝ) < n := lt_trans (by norm_num) ((le_max_right _ _).trans_lt hn)
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have ht : p.1/(n:ℝ) ∈ Ioo (-ε) ε := by
    apply abs_lt.mp
    rw [abs_div,abs_of_pos hn0,div_lt_iff₀ hn0]
    have hb := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hn)
    simpa only [mul_comm] using hb
  have hc : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞
      (fun q : ℝ × M => (q.1/(n:ℝ),q.2)) :=
    ((contDiff_id.div_const (n:ℝ)).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have h := (hmultiple n (p.1/n) ht p.2).comp p hc.contMDiffAt
  have hcancel (r : ℝ) : (n:ℝ)*(r/(n:ℝ)) = r := by field_simp
  simpa only [Function.comp_def,hcancel] using h


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_global_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) :
    ∃ F : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F ∧
      (∀ x, F (0,x) = x) ∧
      (∀ s t x, F (s+t,x) = F (s,F (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => F (t,x)) v) ∧
      (∀ x, v x = 0 → ∀ t, F (t,x) = x) := by
  classical
  choose γ hγ0 hγd using exists_global_compact_manifold_trajectory hv hK hvK
  let F : ℝ × M → M := fun p => γ p.2 p.1
  have hF0 (x : M) : F (0,x) = x := hγ0 x
  have hFd (x : M) : IsMIntegralCurve (fun t => F (t,x)) v := hγd x
  have hv1 : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) := hv.of_le (by simp)
  have hFa (s t : ℝ) (x : M) : F (s+t,x) = F (s,F (t,x)) := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
      ((hFd x).comp_add t) (hFd (F (t,x))) (by simp only [Function.comp_apply,zero_add,hF0])
    exact congrFun he s
  obtain ⟨ε,hε,hfamilies⟩ := exists_uniform_smooth_manifold_families hv hK hvK
  have hFs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ) := by
    intro p hp
    obtain ⟨W,Ψ,hW,hpW,hΨs,hΨ0,hΨd⟩ := hfamilies p.2
    have heq : EqOn F Ψ (Ioo (-ε) ε ×ˢ W) := by
      intro q hq
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨neg_lt_zero.mpr hε,hε⟩ hv1 ((hFd q.2).isMIntegralCurveOn _)
        (hΨd q.2 hq.2) ((hF0 q.2).trans (hΨ0 q.2 hq.2).symm) hq.1
    have hnb : Ioo (-ε) ε ×ˢ W ∈ 𝓝 p := (isOpen_Ioo.prod hW).mem_nhds ⟨hp.1,hpW⟩
    exact ((hΨs.contMDiffAt hnb).congr_of_eventuallyEq
      (Filter.mem_of_superset hnb heq)).contMDiffWithinAt
  refine ⟨F,flow_smooth_of_uniform_local F hF0 hFa hε hFs,hF0,hFa,hFd,?_⟩
  intro x hx t
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
    (hFd x) (isMIntegralCurve_const hx) (hF0 x)
  exact congrFun he t



omit [FiniteDimensional ℝ E] in

theorem exists_smooth_global_manifold_flow_of_uniform_families
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {ε : ℝ} (hε : 0 < ε)
    (hfamilies : ∀ x : M, ∃ (W : Set M) (Ψ : ℝ × M → M),
      IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε))) :
    ∃ F : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F ∧
      (∀ x, F (0,x) = x) ∧
      (∀ s t x, F (s+t,x) = F (s,F (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => F (t,x)) v) ∧
      (∀ x, v x = 0 → ∀ t, F (t,x) = x) := by
  classical
  have hex (x : M) : ∃ γ : ℝ → M, γ 0=x ∧ IsMIntegralCurve γ v := by
    apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hv.of_le (by simp)) hε _ x
    intro y
    obtain ⟨W,Ψ,_,hy,_,hΨ0,hΨd⟩ := hfamilies y
    exact ⟨fun t => Ψ (t,y),hΨ0 y hy,hΨd y hy⟩
  choose γ hγ0 hγd using hex
  let F : ℝ × M → M := fun p => γ p.2 p.1
  have hF0 (x : M) : F (0,x) = x := hγ0 x
  have hFd (x : M) : IsMIntegralCurve (fun t => F (t,x)) v := hγd x
  have hv1 : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) := hv.of_le (by simp)
  have hFa (s t : ℝ) (x : M) : F (s+t,x) = F (s,F (t,x)) := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
      ((hFd x).comp_add t) (hFd (F (t,x))) (by simp only [Function.comp_apply,zero_add,hF0])
    exact congrFun he s
  have hFs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ) := by
    intro p hp
    obtain ⟨W,Ψ,hW,hpW,hΨs,hΨ0,hΨd⟩ := hfamilies p.2
    have heq : EqOn F Ψ (Ioo (-ε) ε ×ˢ W) := by
      intro q hq
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨neg_lt_zero.mpr hε,hε⟩ hv1 ((hFd q.2).isMIntegralCurveOn _)
        (hΨd q.2 hq.2) ((hF0 q.2).trans (hΨ0 q.2 hq.2).symm) hq.1
    have hnb : Ioo (-ε) ε ×ˢ W ∈ 𝓝 p := (isOpen_Ioo.prod hW).mem_nhds ⟨hp.1,hpW⟩
    exact ((hΨs.contMDiffAt hnb).congr_of_eventuallyEq
      (Filter.mem_of_superset hnb heq)).contMDiffWithinAt
  refine ⟨F,flow_smooth_of_uniform_local F hF0 hFa hε hFs,hF0,hFa,hFd,?_⟩
  intro x hx t
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
    (hFd x) (isMIntegralCurve_const hx) (hF0 x)
  exact congrFun he t



theorem exists_uniform_smooth_manifold_families_of_background
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (B : ℝ × M → M)
    (hB : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ B)
    (hB0 : ∀ x, B (0,x)=x)
    (hBd : ∀ x, x ∉ K → IsMIntegralCurve (fun t => B (t,x)) v) :
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
  · exact ⟨Kᶜ,B,hK.isClosed.isOpen_compl,hx,hB.contMDiffOn,
      fun y _ => hB0 y,fun y hy => (hBd y hy).isMIntegralCurveOn _⟩


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem exists_smooth_scalar_clock_flow {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∃ C : ℝ × ℝ → ℝ, ContDiff ℝ ∞ C ∧ (∀ a, C (0,a)=a) ∧
      (∀ a t, HasDerivAt (fun s => C (s,a)) (χ (C (t,a))) t) ∧
      (∀ a, χ a=0 → ∀ t, C (t,a)=a) := by
  have hv : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ)).tangent ∞
      (fun a => (⟨a,χ a⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hχ
  obtain ⟨C,hC,hC0,_,hCd,hCfix⟩ := exists_smooth_global_manifold_flow hv hχc
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
  refine ⟨C,?_,hC0,?_,hCfix⟩
  · rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hC
    exact contMDiff_iff_contDiff.mp hC
  · intro a t
    have hd := hasMFDerivAt_iff_hasFDerivAt.mp (hCd a t)
    rw [hasDerivAt_iff_hasFDerivAt]
    exact hd


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def timeLiftField (χ : ℝ → ℝ) (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2)
    (p : ℝ × M) : TangentSpace ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) p :=
  χ p.1 • ((1:ℝ),V p)

theorem timeLiftField_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).tangent) ∞
      (fun p => (⟨p,timeLiftField χ V p⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (ℝ × M))) := by
  have hc : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ)).tangent ∞
      (fun p : ℝ × M => (⟨p.1,(1:ℝ)⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) := by
    have hp : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ)).tangent ∞
        (fun r : ℝ => (⟨r,(1:ℝ)⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact hp.comp contMDiff_fst
  have hu : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).tangent) ∞
      (fun p : ℝ × M => (⟨p,((1:ℝ),V p)⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (ℝ × M))) :=
    contMDiff_equivTangentBundleProd_symm.comp (hc.prodMk hV)
  exact (hχ.contMDiff.comp contMDiff_fst).smul_section hu

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem timeLiftField_clock_derivative {χ : ℝ → ℝ}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → ℝ × M} {t : ℝ}
    (hd : HasMFDerivAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeLiftField χ V (γ t)))) :
    HasDerivAt (fun s => (γ s).1) (χ (γ t).1) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply ((hasMFDerivAt_fst (γ t)).comp t hd).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change a * (χ (γ t).1 * 1) = a * χ (γ t).1
  rw [mul_one]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem timeLiftField_spatial_derivative {χ : ℝ → ℝ}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → ℝ × M} {t : ℝ}
    (hd : HasMFDerivAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeLiftField χ V (γ t)))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (χ (γ t).1 • V (γ t))) := by
  apply ((hasMFDerivAt_snd (γ t)).comp t hd).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem timeLift_constant_spatial_curve {χ : ℝ → ℝ}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {x : M} (hx : ∀ s, V (s,x) = 0) {γ : ℝ → ℝ}
    (hγ : ∀ t, HasDerivAt γ (χ (γ t)) t) :
    IsMIntegralCurve (fun t => (γ t,x)) (timeLiftField χ V) := by
  intro t
  have hc : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun _ : ℝ => x) t 0 :=
    hasMFDerivAt_const (x := t) x
  have hr : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (χ (γ t))) := (hγ t).hasFDerivAt.hasMFDerivAt
  have hd := hr.prodMk hc
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change (a * χ (γ t),0) = (a * (χ (γ t) * 1),a • (χ (γ t) • V (γ t,x)))
  rw [hx,mul_one,smul_zero,smul_zero]

variable [T2Space M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem timeLift_spatial_stationary {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {a : ℝ} {x : M} (hx : ∀ s, V (s,x) = 0)
    {γ : ℝ → ℝ × M} (hγ : IsMIntegralCurve γ (timeLiftField χ V))
    (h0 : γ 0 = (a,x)) (t : ℝ) : (γ t).2 = x := by
  have hd := timeLift_constant_spatial_curve hx (fun s => timeLiftField_clock_derivative (hγ s))
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    ((timeLiftField_smooth hχ hV).of_le (by simp)) hγ hd (by rw [h0])
  exact congrArg Prod.snd (congrFun he t)


end

section
open scoped Topology NNReal
open Set Function

theorem scalar_clock_eq {χ : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L χ)
    (hχ : ∀ s ∈ Icc (-3:ℝ) 3, χ s = 1)
    {γ : ℝ → ℝ} (hd : ∀ t, HasDerivAt γ (χ (γ t)) t)
    {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (h0 : γ 0 = a) :
    EqOn γ (fun t => a+t) (Ioo (-2:ℝ) 2) := by
  apply ODE_solution_unique_of_mem_Ioo
    (s := fun _ => univ) (fun _ _ => hL.lipschitzOnWith)
    (t₀ := 0) (by constructor <;> norm_num)
    (fun t _ => ⟨hd t,mem_univ _⟩)
  · intro t ht
    have hm : a+t ∈ Icc (-3:ℝ) 3 := by constructor <;> linarith [ha.1,ha.2,ht.1,ht.2]
    rw [hχ _ hm]
    exact ⟨by simpa only [Function.id_def] using (hasDerivAt_id t).const_add a,mem_univ _⟩
  · simpa only [add_zero] using h0


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_spatially_compact_time_lift
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hVK : ∀ s x, x ∉ K → V (s,x)=0) :
    ∃ (χ : ℝ → ℝ) (G : ℝ × (ℝ × M) → ℝ × M),
      ContDiff ℝ ∞ χ ∧ (∀ s ∈ Icc (-3:ℝ) 3, χ s = 1) ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
        ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ G ∧
      (∀ p, G (0,p) = p) ∧
      (∀ s t p, G (s+t,p) = G (s,G (t,p))) ∧
      (∀ p, IsMIntegralCurve (fun t => G (t,p)) (timeLiftField χ V)) ∧
      (∀ a ∈ Icc (0:ℝ) 1, ∀ x t, t ∈ Ioo (-2:ℝ) 2 → (G (t,(a,x))).1 = a+t) := by
  obtain ⟨χ,hχ,hχc,_,hχone,_⟩ := exists_smooth_cutoff (isCompact_Icc (a := (-3:ℝ)) (b := 3))
    isOpen_univ (subset_univ _)
  have hχ1 : ∀ s ∈ Icc (-3:ℝ) 3, χ s = 1 := hχone.self_of_nhdsSet
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ (by simp)
  have hprod : IsManifold ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ (ℝ × M) := inferInstance
  let instProd : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  have : IsManifold 𝓘(ℝ,ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hprod
  have hv : ContMDiff 𝓘(ℝ,ℝ × E) (𝓘(ℝ,ℝ × E)).tangent ∞
      (fun p => (⟨p,timeLiftField χ V p⟩ : TangentBundle 𝓘(ℝ,ℝ × E) (ℝ × M))) := by
    simpa only [modelWithCornersSelf_prod,instProd] using! timeLiftField_smooth hχ hV
  obtain ⟨C,hC,hC0,hCd,hCfix⟩ := exists_smooth_scalar_clock_flow hχ hχc
  let B : ℝ × (ℝ × M) → ℝ × M := fun p => (C (p.1,p.2.1),p.2.2)
  have hCm : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ C := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact hC.contMDiff
  have hBm : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
      ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ B :=
    (hCm.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  have hB0 (p : ℝ × M) : B (0,p)=p := by dsimp [B]; rw [hC0]
  have hBd (p : ℝ × M) (hp : p ∉ tsupport χ ×ˢ K) :
      IsMIntegralCurve (fun t => B (t,p)) (timeLiftField χ V) := by
    by_cases hx : p.2 ∈ K
    · have ha : p.1 ∉ tsupport χ := fun ht => hp ⟨ht,hx⟩
      have hz : χ p.1=0 := image_eq_zero_of_notMem_tsupport ha
      have he : (fun t => B (t,p))=(fun _ => p) := by
        funext t
        dsimp [B]
        rw [hCfix p.1 hz t]
      rw [he]
      apply isMIntegralCurve_const
      rw [timeLiftField,hz,zero_smul]
      rfl
    · exact timeLift_constant_spatial_curve (fun s => hVK s p.2 hx) (hCd p.1)
  have hBs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ × E)) 𝓘(ℝ,ℝ × E) ∞ B := by
    simpa only [modelWithCornersSelf_prod,instProd] using hBm
  have hBd' (p : ℝ × M) (hp : p ∉ tsupport χ ×ˢ K) :
      IsMIntegralCurve (I := 𝓘(ℝ,ℝ × E)) (fun t => B (t,p)) (timeLiftField χ V) := by
    intro t
    have hderiv := hBd p hp t
    simp only [HasMFDerivAt,modelWithCornersSelf_prod] at hderiv ⊢
    refine ⟨hderiv.1,?_⟩
    convert hderiv.2 using 1
    rfl
  obtain ⟨ε,hε,hfamilies⟩ := exists_uniform_smooth_manifold_families_of_background
    hv (hχc.prod hK) B hBs hB0 hBd'
  obtain ⟨G,hGs,hG0,hGa,hGd,_⟩ := exists_smooth_global_manifold_flow_of_uniform_families
    hv hε hfamilies
  have hGs' : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
      ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ G := by
    simpa only [modelWithCornersSelf_prod,instProd] using hGs
  have hGd' : ∀ p, IsMIntegralCurve (fun t => G (t,p)) (timeLiftField χ V) := by
    intro p t
    have hderiv := hGd p t
    simp only [HasMFDerivAt,modelWithCornersSelf_prod] at hderiv ⊢
    refine ⟨hderiv.1,?_⟩
    convert hderiv.2 using 1
    rfl
  refine ⟨χ,G,hχ,hχ1,hGs',hG0,hGa,hGd',?_⟩
  intro a ha x t ht
  exact scalar_clock_eq hL hχ1 (fun s => timeLiftField_clock_derivative (hGd' (a,x) s)) ha
    (congrArg Prod.fst (hG0 (a,x))) ht


end

open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_compact_time_lift
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ∃ (χ : ℝ → ℝ) (G : ℝ × (ℝ × M) → ℝ × M),
      ContDiff ℝ ∞ χ ∧ (∀ s ∈ Icc (-3:ℝ) 3, χ s = 1) ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
        ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ G ∧
      (∀ p, G (0,p) = p) ∧
      (∀ s t p, G (s+t,p) = G (s,G (t,p))) ∧
      (∀ p, IsMIntegralCurve (fun t => G (t,p)) (timeLiftField χ V)) ∧
      (∀ a ∈ Icc (0:ℝ) 1, ∀ x t, t ∈ Ioo (-2:ℝ) 2 → (G (t,(a,x))).1 = a+t) := by
  obtain ⟨χ,hχ,hχc,_,hχone,_⟩ := exists_smooth_cutoff (isCompact_Icc (a := (-3:ℝ)) (b := 3))
    isOpen_univ (subset_univ _)
  have hχ1 : ∀ s ∈ Icc (-3:ℝ) 3, χ s = 1 := hχone.self_of_nhdsSet
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ (by simp)
  have hprod : IsManifold ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ (ℝ × M) := inferInstance
  let instProd : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  have : IsManifold 𝓘(ℝ,ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hprod
  have hv : ContMDiff 𝓘(ℝ,ℝ × E) (𝓘(ℝ,ℝ × E)).tangent ∞
      (fun p => (⟨p,timeLiftField χ V p⟩ : TangentBundle 𝓘(ℝ,ℝ × E) (ℝ × M))) := by
    simpa only [modelWithCornersSelf_prod,instProd] using! timeLiftField_smooth hχ hV
  have hvK (p : ℝ × M) (hp : p ∉ tsupport χ ×ˢ (univ : Set M)) : timeLiftField χ V p = 0 := by
    have hp' : p.1 ∉ tsupport χ := fun h => hp ⟨h,mem_univ _⟩
    rw [timeLiftField,image_eq_zero_of_notMem_tsupport hp',zero_smul]
    rfl
  obtain ⟨G,hGs,hG0,hGa,hGd,_⟩ := exists_smooth_global_manifold_flow hv
    (hχc.prod (isCompact_univ : IsCompact (univ : Set M))) hvK
  have hGs' : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
      ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ G := by
    simpa only [modelWithCornersSelf_prod,instProd] using hGs
  have hGd' : ∀ p, IsMIntegralCurve (fun t => G (t,p)) (timeLiftField χ V) := by
    intro p t
    have hderiv := hGd p t
    simp only [HasMFDerivAt,modelWithCornersSelf_prod] at hderiv ⊢
    refine ⟨hderiv.1,?_⟩
    convert hderiv.2 using 1
    rfl
  refine ⟨χ,G,hχ,hχ1,hGs',hG0,hGa,hGd',?_⟩
  intro a ha x t ht
  exact scalar_clock_eq hL hχ1 (fun s => timeLiftField_clock_derivative (hGd' (a,x) s)) ha
    (congrArg Prod.fst (hG0 (a,x))) ht



end PackingSufficiencySupport.Hamiltonian
end

end OAI
