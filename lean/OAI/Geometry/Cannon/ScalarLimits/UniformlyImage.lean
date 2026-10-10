import Mathlib
import OAI.Geometry.Cannon.Energy.Plane
import OAI.Geometry.Cannon.Boundary.BoundaryPuncturedPathConnected
import OAI.Geometry.Cannon.ScalarLimits.Exhaustion
import OAI.Geometry.Cannon.Energy.MeshTransportBound
import OAI.Geometry.Cannon.ScalarLimits.NormalizedLevelsEscape
import OAI.Geometry.Cannon.Energy.AffineRangeBounded

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology
open Set Metric Filter Topology

namespace CannonComparison

open Set Metric Filter Topology CannonPacking CannonApprox CannonVariation CannonDiagonal

lemma uniformly_on_image {X Y : Type*} (g : Y → X) (F : ℕ → X → ℝ)
    (W : X → ℝ) (K : Set Y) (h : TendstoUniformlyOn F W atTop (g '' K)) :
    TendstoUniformlyOn (fun n => F n ∘ g) (W ∘ g) atTop K :=
  (h.comp g).mono (fun _ hx => mem_image_of_mem _ hx)

theorem fixed_transform_comparison {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (Q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f : ℕ → X → ℝ) (W : X → ℝ) (b : X)
    (hW : ContinuousOn W ({b}ᶜ : Set X))
    (hfbounded : ∀ n, BddAbove (range (f n)) ∧ BddBelow (range (f n)))
    (hfcont : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hflim : ∀ K : Set X, IsCompact K → b ∉ K → TendstoUniformlyOn f W atTop K)
    (hfe : ∀ K : Set X, IsCompact K → b ∉ K → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (f n) K) atTop (𝓝 0))
    (hlevels : EscapingLevelsAlong f W b)
    (g : X ≃ₜ X) (H B : ℝ) (hH : 0 < H) (hB : 0 < B)
    (hg : ∀ x y, dist (g x) (g y) ≤ H*dist x y)
    (hginv : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y)
    (hgb : g b ≠ b) (z : X) (hzb : z ≠ b) (hzgb : z ≠ g b)
    (hz : NonconstantAt W z) : W (g.symm z) = W (g.symm b) := by
  have hpre (K : Set X) (hbK : g b ∉ K) : b ∉ g.symm '' K := by
    rintro ⟨y,hy,heq⟩
    have heq' : y = g b := by simpa only [g.apply_symm_apply] using congrArg g heq
    exact hbK (heq' ▸ hy)
  have hV : ContinuousOn (W ∘ g.symm) ({g b}ᶜ : Set X) := by
    apply hW.comp g.symm.continuous.continuousOn
    intro y hy heq
    change y ≠ g b at hy
    exact hy (by simpa only [g.apply_symm_apply] using congrArg g heq)
  have hwcont : ∀ K : Set X, IsCompact K → g b ∉ K →
      ∀ᶠ n in atTop, ContinuousOn (f n ∘ g.symm) K := by
    intro K hK hbK
    filter_upwards [hfcont (g.symm '' K) (hK.image g.symm.continuous) (hpre K hbK)] with n hn
    exact hn.comp g.symm.continuous.continuousOn (fun y hy => mem_image_of_mem _ hy)
  exact comparison_across_punctures ι p r hr hrlim hpnet f (fun n => f n ∘ g.symm)
    W (W ∘ g.symm) b (g b) hgb.symm hW hV hfcont hwcont hflim
    (fun K hK hbK => uniformly_on_image g.symm f W K
      (hflim _ (hK.image g.symm.continuous) (hpre K hbK)))
    (fun K hK hbK => hfe K hK hbK 2 (by norm_num))
    (fun K hK hbK => transported_mesh_energy_tendsto Q CP H B hpack hCP hH hB g hg hginv
      ι p r hr hrlim hpsep hpnet f hfbounded b hfe K hK hbK 2 (by norm_num))
    hlevels z hzb hzgb hz

end CannonComparison

namespace CannonComparison

open Set Metric Filter Topology CannonPacking CannonApprox CannonVariation CannonDiagonal CannonMagnification

theorem magnified_transform_comparison {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (Q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (hpnet : ∀ n y, ∃ i, dist (p n i) y ≤ r n)
    (Ω : Set X) (hΩ : IsOpen Ω) (U : X → ℝ) (H : ℕ → X → ℝ)
    (hHrange : ∀ n y, H n y ∈ Icc (0:ℝ) 1)
    (hHcont : ∀ n, ContinuousOn (H n) Ω)
    (hHlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H U atTop K)
    (d₁ : ℝ) (hd₁ : 0 < d₁)
    (hlevels : ∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ d₁ ≤ diam A ∧
        (∀ y ∈ A, H n y = τ) ∧
        ∀ v w : X, ∀ γ : Path v w, range γ ⊆ Ω → H n v < τ → τ < H n w →
          (A ∩ range γ).Nonempty)
    (h : ℕ → X ≃ₜ X) (x : ℕ → X) (z₀ b : X) (q : ℕ → ℝ)
    (C L d₀ : ℝ) (hC : 0 ≤ C) (hd₀ : 0 < d₀)
    (hq : ∀ n, 0 < q n) (hqlim : Tendsto q atTop (𝓝 0))
    (hexp : ∀ n, Expansion (h n) (x n) (q n) C L)
    (hz₀ : ∀ n, d₀ ≤ dist (x n) z₀) (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hb : Tendsto (fun n => h n z₀) atTop (𝓝 b))
    (c sig : ℕ → ℝ) (hsig : ∀ n, 0 < sig n) (W : X → ℝ)
    (hW : ContinuousOn W ({b}ᶜ : Set X))
    (hpre : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ n in atTop, (h n).symm '' K ⊆ Ω)
    (hFlim : ∀ K : Set X, IsCompact K → b ∉ K →
      TendstoUniformlyOn (fun n z => (U ((h n).symm z)-c n)/sig n) W atTop K)
    (hE : ∀ i K, IsCompact K → K ⊆ (h i) '' Ω → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (H n ∘ (h i).symm) K) atTop (𝓝 0)) :
    ∀ (g : X ≃ₜ X) (A B : ℝ), 0 < A → 0 < B →
      (∀ y z, dist (g y) (g z) ≤ A*dist y z) →
      (∀ y z, dist (g.symm y) (g.symm z) ≤ B*dist y z) →
      g b ≠ b → ∀ z, z ≠ b → z ≠ g b → NonconstantAt W z →
        W (g.symm z) = W (g.symm b) := by
  let S : ℕ → Set X := fun i => h i '' Ω
  let F : ℕ → X → ℝ := fun i z => (U ((h i).symm z)-c i)/sig i
  let G : ℕ → ℕ → X → ℝ := fun i n z => (H n ((h i).symm z)-c i)/sig i
  have hHbounded (n : ℕ) : BddAbove (range (H n)) ∧ BddBelow (range (H n)) := by
    constructor
    · exact ⟨1,by rintro _ ⟨z,rfl⟩; exact (hHrange n z).2⟩
    · exact ⟨0,by rintro _ ⟨z,rfl⟩; exact (hHrange n z).1⟩
  have hcompbounded (i n : ℕ) : BddAbove (range (H n ∘ (h i).symm)) ∧
      BddBelow (range (H n ∘ (h i).symm)) :=
    ⟨(hHbounded n).1.range_comp_right _,(hHbounded n).2.range_comp_right _⟩
  have hGbounded (i n : ℕ) : BddAbove (range (G i n)) ∧ BddBelow (range (G i n)) :=
    affine_range_bounded _ (hcompbounded i n).1 (hcompbounded i n).2 (c i) (sig i) (hsig i)
  have hpreimage (i : ℕ) (K : Set X) (hK : K ⊆ S i) : (h i).symm '' K ⊆ Ω := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨w,hw,rfl⟩ := hK hz
    simpa only [(h i).symm_apply_apply] using hw
  have hdom : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ i in atTop, K ⊆ S i := by
    intro K hK hbK
    filter_upwards [hpre K hK hbK] with i hi
    intro z hz
    exact ⟨(h i).symm z,hi (mem_image_of_mem _ hz),(h i).apply_symm_apply z⟩
  have hG : ∀ i K, IsCompact K → K ⊆ S i → TendstoUniformlyOn (G i) (F i) atTop K := by
    intro i K hK hKS
    exact uniformly_affine _ _ K
      (uniformly_on_image (h i).symm H U K
        (hHlim _ (hK.image (h i).symm.continuous) (hpreimage i K hKS)))
      (c i) (sig i) (hsig i)
  have hGE : ∀ i K, IsCompact K → K ⊆ S i → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (G i n) K) atTop (𝓝 0) := by
    intro i K hK hKS J hJ
    exact meshEnergy_affine_tendsto ι p r (fun n => (hr n).le) J hJ.le
      (fun n => H n ∘ (h i).symm) (hcompbounded i) (c i) (sig i) (hsig i) K (hE i K hK hKS J hJ)
  obtain ⟨α,N,hα,hN,hlim,henergy⟩ := common_mesh_diagonal ι p r hr hrlim b S
    (fun i => (h i).isOpenMap _ hΩ) F W G hFlim hdom hG hGbounded hGE
  have hpre' : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ j in atTop, (h (α j)).symm '' K ⊆ Ω := by
    intro K hK hbK
    exact hα.tendsto_atTop.eventually (hpre K hK hbK)
  have hcont' : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ j in atTop, ContinuousOn (G (α j) (N j)) K := by
    intro K hK hbK
    filter_upwards [hpre' K hK hbK] with j hj
    exact ((hHcont (N j)).comp (h (α j)).symm.continuous.continuousOn
      (fun z hz => hj (mem_image_of_mem _ hz))).sub continuousOn_const |>.div_const _
  have hlevels' : EscapingLevelsAlong (fun j => G (α j) (N j)) W b :=
    normalized_levels_escape (fun j => H (N j)) Ω (fun j y _ => hHrange (N j) y)
      d₁ hd₁ (fun j => hlevels (N j)) (fun j => h (α j)) (x ∘ α) z₀ b (q ∘ α)
      C L d₀ hC hd₀ (fun j => hq (α j)) (hqlim.comp hα.tendsto_atTop)
      (fun j => hexp (α j)) (fun j => hz₀ (α j)) hdiam (hb.comp hα.tendsto_atTop)
      (c ∘ α) (sig ∘ α) (fun j => hsig (α j)) W hpre' hlim
  intro g A B hA hB hg hginv hgb z hzb hzgb hz
  exact fixed_transform_comparison Q CP hpack hCP (fun j => ι (N j))
    (fun j => p (N j)) (r ∘ N) (fun j => hr (N j)) (hrlim.comp hN.tendsto_atTop)
    (fun j => hpsep (N j)) (fun j => hpnet (N j)) (fun j => G (α j) (N j)) W b hW
    (fun j => hGbounded (α j) (N j)) hcont' hlim
    (fun K hK hbK J hJ => (henergy K hK hbK J hJ).1) hlevels'
    g A B hA hB hg hginv hgb z hzb hzgb hz

end CannonComparison

namespace CannonComparison

open Set Filter Topology CannonVariation

lemma nonconstantAt_pullback {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    (s : X ≃ₜ X) (z : X) (hz : NonconstantAt (F ∘ s) z) : NonconstantAt F (s z) := by
  intro he
  apply hz
  exact s.continuous.continuousAt.tendsto.eventually he

theorem all_two_transform_comparison {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (W : X → ℝ) (b : X)
    (hc : ∀ g : G, ρ g b ≠ b → ∀ z, z ≠ b → z ≠ ρ g b → NonconstantAt W z →
      W (ρ g⁻¹ z) = W (ρ g⁻¹ b)) :
    ∀ s t : G, ρ s b ≠ ρ t b → ∀ z, z ≠ ρ s b → z ≠ ρ t b →
      NonconstantAt (fun z => W (ρ s⁻¹ z)) z → W (ρ t⁻¹ z) = W (ρ t⁻¹ (ρ s b)) := by
  intro s t hst z hzs hzt hz
  have hsimp (u : X) : ρ s⁻¹ (ρ s u) = u := by
    simp only [map_inv, Homeomorph.inv_apply, Homeomorph.symm_apply_apply]
  have hsimp' (u : X) : ρ s (ρ s⁻¹ u) = u := by
    simp only [map_inv, Homeomorph.inv_apply, Homeomorph.apply_symm_apply]
  have hgb : ρ (s⁻¹*t) b ≠ b := by
    intro he
    apply hst
    have hh := congrArg (ρ s) he
    simpa only [map_mul,Homeomorph.mul_apply,hsimp'] using hh.symm
  have hzb : ρ s⁻¹ z ≠ b := by
    intro he
    apply hzs
    simpa only [hsimp'] using congrArg (ρ s) he
  have hzg : ρ s⁻¹ z ≠ ρ (s⁻¹*t) b := by
    intro he
    apply hzt
    have hh := congrArg (ρ s) he
    simpa only [map_mul,Homeomorph.mul_apply,hsimp'] using hh
  have hnc := nonconstantAt_pullback W (ρ s⁻¹) z hz
  have hh := hc (s⁻¹*t) hgb (ρ s⁻¹ z) hzb hzg hnc
  simpa only [mul_inv_rev,inv_inv,map_mul,Homeomorph.mul_apply,hsimp'] using hh

end CannonComparison

end

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonVariation CannonComparison
open CannonPacking CannonApprox CannonCrossEnergy CannonCrossEnergyLocal Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance uniformlyImageSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_holder_scalar_impossible (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D)
    (r : ℕ → ℝ), (∀ n, 0 < r n) → Tendsto r atTop (𝓝 0) →
    (∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j)) →
    (∀ n y, ∃ i, dist (p n i) y ≤ r n) →
    ∀ (Ω O P : Set (Boundary D)), IsOpen Ω → IsOpen O → Oᶜ.Nonempty →
    closure O ⊆ Ω → IsCompact P → IsConnected P → P ⊆ O →
    ∀ f : C(Ω,ℝ), (∃ u ∈ P, ∃ v ∈ P, onDomain f u ≠ onDomain f v) →
    ∀ α : ℝ, 0 < α →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α) →
    ∀ (z₀ : Boundary D) (d₀ : ℝ), 0 < d₀ → (∀ x ∈ O, d₀ ≤ dist x z₀) →
    ∀ H : ℕ → Boundary D → ℝ,
    (∀ n y, H n y ∈ Icc (0:ℝ) 1) → (∀ n, ContinuousOn (H n) Ω) →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn H (onDomain f) atTop K) →
    ∀ d₁ : ℝ, 0 < d₁ →
    (∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ A : Set (Boundary D), IsCompact A ∧ IsConnected A ∧ d₁ ≤ diam A ∧
        (∀ y ∈ A, H n y = τ) ∧
        ∀ v w : Boundary D, ∀ γ : Path v w, range γ ⊆ Ω →
          H n v < τ → τ < H n w → (A ∩ range γ).Nonempty) →
    (∀ g : G, ∀ K, IsCompact K → K ⊆ boundaryHomeomorph D ⟨δ,hδ⟩ g '' Ω →
      ∀ J : ℝ, 0 < J → Tendsto
        (fun n => meshEnergy (p n) (r n) J
          (H n ∘ (boundaryHomeomorph D ⟨δ,hδ⟩ g).symm) K) atTop (𝓝 0)) → False := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro ι hι p r hr hrlim hpsep hpnet Ω O P hΩ hO hOc hOΩ hP hPc hPO
    f hv α hα hholder z₀ d₀ hd₀ hsep H hHrange hHcont hHlim d₁ hd₁ hlevels hE
  obtain ⟨β,hβ,k,x,sig,b,W,hk,hx,hb,_hescape,hpre,hFlim,hWholder,hWvar⟩ :=
    boundary_holder_magnification D hδ φ Ω O P hΩ hO hOc hOΩ hP hPc hPO
      f hv α hα hholder z₀ d₀ hd₀ hsep
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let q : ℕ → ℝ := fun i => (a^(k i))⁻¹
  have hq : ∀ i, 0 < q i := fun i => by dsimp [q,a]; positivity
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  obtain ⟨Q,CP,_hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  have hlim : ∀ K : Set (Boundary D), IsCompact K → b ∉ K →
      TendstoUniformlyOn
        (fun i z => (onDomain f ((boundaryExpansion D hδ (x i) (k i)).symm z)-onDomain f (x i))/sig i)
        (onDomain W) atTop K := by
    intro K hK hbK
    exact uniform_onDomain _ W hFlim K hK (by intro z hz hzb; exact hbK (hzb ▸ hz))
  have hcomp := magnified_transform_comparison Q CP hpack hCP.le ι p r hr hrlim hpsep hpnet
    Ω hΩ (onDomain f) H hHrange hHcont hHlim d₁ hd₁ hlevels
    (fun i => boundaryExpansion D hδ (x i) (k i)) x z₀ b q
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))) d₀ (by positivity) hd₀
    hq hqlim (fun i => boundaryExpansion_formula D hδ (x i) (k i))
    (fun i => hsep (x i) (hx i).1) (boundaryDist_le_one D hδ) hb
    (fun i => onDomain f (x i)) sig (fun i => (hx i).2) (onDomain W)
    (continuousOn_onDomain W)
    (fun K hK hbK => by
      filter_upwards [hpre K hK hbK] with i hi
      rintro z ⟨y,hy,rfl⟩
      exact hi y hy) hlim
    (fun i K hK hKS J hJ => hE ((boundaryBasedRay D (x i)).val (k i))⁻¹ K hK hKS J hJ)
  have hall := all_two_transform_comparison (boundaryAction D ⟨δ,hδ⟩) (onDomain W) b (by
    intro g hgb z hzb hzgb hz
    exact hcomp (boundaryHomeomorph D ⟨δ,hδ⟩ g)
      (2*Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ)))
      (2*Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g⁻¹+4*δ):ℕ)))
      (by positivity) (by positivity) (boundaryTranslate_lipschitz_bound D hδ g)
      (boundaryTranslate_lipschitz_bound D hδ g⁻¹) hgb z hzb hzgb hz)
  apply boundary_second_magnification_obstruction D hδ φ b W
    (Real.log β/Real.log a) (div_pos (Real.log_pos hβ) (Real.log_pos ha)) ?_ hWvar hall
  intro K hK hKb
  let K' : Set ({b}ᶜ : Set (Boundary D)) := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
    (by simpa only [Subtype.range_coe] using hKb)
  obtain ⟨C,hC,hCh⟩ := hWholder K' hK'
  refine ⟨C,hC,?_⟩
  intro z w hz hw
  simpa only [Real.dist_eq] using hCh z hz w hw

end CannonRelease

end

end
end
end
end
end
end
end
end

end OAI
