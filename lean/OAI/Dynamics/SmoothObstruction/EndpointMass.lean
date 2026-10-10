import OAI.Dynamics.SmoothObstruction.SwitchRecovery
import OAI.Dynamics.SmoothObstruction.EndpointFrames

namespace OAI

section

open scoped BigOperators
open scoped ContDiff BigOperators
open Module
open Filter Topology
open scoped Real

namespace SmoothObstruction.SmoothScales
lemma tendsto_zero_of_square_summable {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hs : Summable (fun k => (b k)^2)) : Tendsto b atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq (hb _), Real.sqrt_zero] using h

lemma summable_B_sixteen {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hs : Summable (fun k => (b k)^2)) : Summable (fun k => (B (b k))^16) := by
  exact hs.congr (fun k => (root_sixteen (hb k)).symm)

lemma dyadic_floor (k : ℕ) :
    ((2 : ℝ)^k) ^ (-1 / 10 : ℝ) = (2 : ℝ)^(-(k : ℝ) / 10) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  congr 1
  ring
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.ExteriorStability
open RelativeProduct Asymptotics

/-- Full asymptotic conclusion in source Lemma `lem:relative-exterior`, at the
literal dyadic scales and with the literal summable chord sequence. The same
proof supplies one rate of convergence for every matrix family satisfying the
fixed displayed constants, since the bounding sequence in
`uniform_relative_small` depends only on those constants and `b`. -/
theorem relative_exterior_dyadic (d : ℕ) (_hd : 1 ≤ d) (K : ℝ) (_hK : 1 ≤ K)
    (p : ℕ) (hp : p ≤ d)
    (b : ℕ → ℝ) (hbpos : ∀ k, 0 < b k) (hbsum : Summable (fun k => (b k)^2))
    (hbfloor : ∀ k : ℕ, (2 : ℝ)^(-(k : ℝ) / 10) ≤ b k)
    (m : ℕ → ℕ)
    (A B : ℕ → ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (σ a ε : ℕ → ℝ) (C₀ C₁ C₂ C₃ : ℝ) (hC₀ : 0 < C₀) (hC₃ : 0 ≤ C₃)
    (hdata : ∀ᶠ k in atTop,
      1 ≤ m k ∧ (m k : ℝ) ≤ 2 * (2 : ℝ)^k ∧
      0 ≤ a k ∧ a k ≤ C₁ * b k * (2 : ℝ)^k ∧ |σ k| ≤ C₂ ∧
      0 ≤ ε k ∧ ε k ≤ 1 ∧
      ε k ≤ C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B (b k) * (2 : ℝ)^k) ∧
      (∀ t < m k, ‖A k t‖ ≤ K) ∧
      (∀ t < m k, ‖B k t - A k t‖ ≤ ε k) ∧
      (∀ s q : ℕ, s + q ≤ m k →
        ‖exterior p (segment (A k) s q)‖ ≤ Real.exp (σ k * q + a k))) :
    (fun k => exterior p (segment (B k) 0 (m k)) - exterior p (segment (A k) 0 (m k)))
      =o[atTop] (fun k => Real.exp (σ k * m k - C₀ * b k * (2 : ℝ)^k)) := by
  obtain ⟨C, hC, hbound⟩ := relative_exterior_core (E := EuclideanSpace ℝ (Fin d)) d K
  have hsmall : (fun k => ‖exterior p (segment (B k) 0 (m k)) -
      exterior p (segment (A k) 0 (m k))‖) =o[atTop]
      (fun k => Real.exp (σ k * m k - C₀ * b k * (2 : ℝ)^k)) := by
    apply (Asymptotics.isLittleO_iff_tendsto (fun k hk => (Real.exp_ne_zero _ hk).elim)).mpr
    apply RelativeAsymptotics.uniform_relative_small (Filter.Eventually.of_forall hbpos)
      (SmoothScales.tendsto_zero_of_square_summable (fun k => (hbpos k).le) hbsum)
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))
      (Filter.Eventually.of_forall (fun k => by simpa only [SmoothScales.dyadic_floor] using hbfloor k))
      C C₀ C₁ C₂ C₃ hC hC₀.le hC₃
    filter_upwards [hdata] with k hk
    rcases hk with ⟨_, hm, ha, hale, hσ, hε, hε₁, hεle, hA, hBA, hseg⟩
    exact ⟨ContinuousLinearMap.opNorm_nonneg _, ha, hε, hm, hale, hσ, hεle,
      hbound p hp (A k) (B k) (m k) (σ k) (a k) (ε k) hε hε₁ hA hBA hseg⟩
  apply Asymptotics.isLittleO_iff.mpr
  intro c hc
  filter_upwards [hsmall.bound hc] with k hk
  simp only [Real.norm_eq_abs] at hk ⊢
  exact (le_abs_self _).trans hk
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.RelativeAsymptotics
open Filter Topology

/-- Exterior relative errors absorb every fixed exponential gauge cost.
The multiplicative nonlinear error remains the authentic envelope times
its exponential, not a dimension- or bin-dependent replacement. -/
theorem weighted_envelope_tendsto {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (C C₁ C₂ C₃ A K : ℝ) :
    Tendsto (fun k => A*Real.exp (K*b k*n k)*
      (envelope C 0 C₁ C₂ C₃ (b k) (n k)*
        Real.exp (envelope C 0 C₁ C₂ C₃ (b k) (n k)))) l (𝓝 0) := by
  have hv (J : ℝ) : Tendsto (fun k => envelope C J C₁ C₂ C₃ (b k) (n k)) l (𝓝 0) := by
    simpa only [envelope,mul_zero] using
      (SmoothScales.decisive_decay hbpos hb hn hfloor (2*C₁+J)).const_mul
        (2*C*C₃*Real.exp C₂)
  have hh := ((hv K).mul ((Real.continuous_exp.tendsto 0).comp (hv 0))).const_mul A
  simp only [Real.exp_zero,mul_one,mul_zero] at hh
  apply hh.congr
  intro k
  dsimp only [envelope,Function.comp_apply]
  rw [show -(3/2:ℝ)*SmoothScales.B (b k)*n k+(2*C₁+K)*b k*n k=
    K*b k*n k+(-(3/2:ℝ)*SmoothScales.B (b k)*n k+(2*C₁+0)*b k*n k) by ring,
    Real.exp_add]
  ring

/-- Literal leading-minor relative perturbation parameter tends to zero. -/
theorem common_relative_budget {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (C Crel C₁ C₂ C₃ D W : ℝ) (p : ℕ) :
    Tendsto (fun k => 2*((C*(Real.exp (D*b k*n k))^p)^2*(C*2^p))*C*
      (envelope Crel 0 C₁ C₂ C₃ (b k) (n k)*
        Real.exp (envelope Crel 0 C₁ C₂ C₃ (b k) (n k)))*W) l (𝓝 0) := by
  apply (weighted_envelope_tendsto hbpos hb hn hfloor Crel C₁ C₂ C₃
    (2*C^4*2^p*W) ((2*p:ℕ)*D)).congr
  intro k
  have he : Real.exp (((2*p:ℕ):ℝ)*D*b k*n k)=(Real.exp (D*b k*n k))^(2*p) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simp only [Nat.mul_comm 2 p,pow_mul]
  ring
end SmoothObstruction.RelativeAsymptotics

namespace SmoothObstruction.EndpointBudget
open Filter Topology
noncomputable def leading (C K : ℝ) (p : ℕ) : ℝ := (C*(Real.exp K)^p)^2*(C*2^p)
noncomputable def normCost (C K N : ℝ) (p : ℕ) : ℝ := C*(C^2*(Real.exp K)^(2*p)*N)
noncomputable def mixedCost (C K N V : ℝ) (p : ℕ) : ℝ := C*(C*(Real.exp K)^p)^2*N*V
noncomputable def relative (C Crel C₁ C₂ C₃ D V b n : ℝ) (p : ℕ) : ℝ :=
  2*leading C (D*b*n) p*C*
    (RelativeAsymptotics.envelope Crel 0 C₁ C₂ C₃ b n*
      Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ C₂ C₃ b n))*V
noncomputable def graph (C D N V W b n δ : ℝ) (p : ℕ) : ℝ :=
  2*leading C (D*b*n) p*
    (mixedCost C (D*b*n) N V p*Real.exp (-2*b^(1/2:ℝ)*n)+normCost C (D*b*n) N p*W*δ)

/-- One eventual scalar budget works at ALL ranks, before choosing any
starting cell, endpoint label, good gauge, or input frame. -/
theorem all_ranks {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) (C Crel C₁ C₂ C₃ D c : ℝ) (hc : 0<c)
    (F N V W β : Fin (d+1) → ℝ)
    (hF : ∀ p,0≤F p) (hN : ∀ p,0≤N p) (hV : ∀ p,0≤V p)
    (hW : ∀ p,0≤W p) (hβ : ∀ p,0<β p)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    ∀ᶠ k in l,∀ p : Fin (d+1),
      (F p*δ k)*(1+leading C (D*b k*n k) p.val*normCost C (D*b k*n k) (N p) p.val)≤1/2 ∧
      relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val≤1/100 ∧
      (graph C D (N p) (V p) (W p) (b k) (n k) (δ k) p.val+
        relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val)/
        (1-relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val)≤β p := by
  apply Filter.eventually_all.mpr
  intro p
  have hf := SmoothScales.common_frame_budget (C:=C) hbpos hb hn hfloor hc (hF p) (hN p) D p.val hδ
  have hr := RelativeAsymptotics.common_relative_budget hbpos hb hn hfloor C Crel C₁ C₂ C₃ D (V p) p.val
  have hg := SmoothScales.common_graph_budget (C:=C) hbpos hb hn hfloor hc (hN p) (hV p) (hW p) D p.val hδ
  change Tendsto (fun k => relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val) l (𝓝 0) at hr
  change Tendsto (fun k => graph C D (N p) (V p) (W p) (b k) (n k) (δ k) p.val) l (𝓝 0) at hg
  filter_upwards [hf,hr.eventually_le_const (by norm_num : (0:ℝ)<1/100),
    (SmoothScales.perturbed_graph_decay hg hr).eventually_le_const (hβ p)] with k hk hrk hgk
  exact ⟨hk,hrk,hgk⟩
end SmoothObstruction.EndpointBudget

end

section

namespace SmoothObstruction.AtlasCores
open Set Filter Topology
variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Fintype ι]

/-- A finite closed atlas selector can only approach charts whose compact
carrier contains the limiting point. It need not be a continuous selector. -/
theorem closed_selector_germ (K : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (q : Y → ι) (hq : ∀ y,y∈K (q y)) (y : Y) :
    ∀ᶠ z in 𝓝 y,y∈K (q z) := by
  have hall : ∀ i,∀ᶠ z in 𝓝 y,q z=i → y∈K i := by
    intro i
    by_cases hy : y∈K i
    · exact Eventually.of_forall (fun _ _ => hy)
    · filter_upwards [(hK i).isOpen_compl.mem_nhds hy] with z hz he
      exact (hz (he ▸ hq z)).elim
  filter_upwards [Filter.eventually_all.mpr hall] with z hz
  exact hz (q z) rfl

/-- Local analytic branches may be checked simultaneously in finitely many
possible chart codes, without adding those codes to any global partition. -/
theorem eventually_selected (K : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (q : Y → ι) (hq : ∀ y,y∈K (q y)) (f : X → Y) (x : X)
    (hf : ContinuousAt f x) (V : ι → Set X)
    (hV : ∀ i,f x∈K i → V i∈𝓝 x) :
    ∀ᶠ u in 𝓝 x,u∈V (q (f u)) := by
  have hcodes := hf.eventually (closed_selector_germ K hK q hq (f x))
  have hall : ∀ i,∀ᶠ u in 𝓝 x,f x∈K i → u∈V i := by
    intro i
    by_cases hi : f x∈K i
    · filter_upwards [hV i hi] with u hu using fun _ => hu
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [hcodes,Filter.eventually_all.mpr hall] with u hu hv
  exact hv (q (f u)) hu
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.AtlasCores
open Set Filter Topology
variable {X Y E ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [Fintype ι]

/-- A smooth local branch in all possible old charts satisfies the selected
canonical tube relation on a whole relative neighborhood. No regularity of
the finite chart selector is asserted and no intermediate chart pattern is
recorded in the partition. -/
theorem selected_tube_germ (K U : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (hU : ∀ i,IsOpen (U i)) (hKU : ∀ i,K i⊆U i)
    (q : Y → ι) (hq : ∀ y,y∈K (q y))
    (φ : ι → Y → E) (hφ : ∀ i,ContinuousOn (φ i) (U i))
    (f g : X → Y) (x : X) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (δ : ℝ) (hbase : ∀ i,f x∈K i →
      g x∈U i ∧ ‖φ i (g x)-φ i (f x)‖<δ) :
    ∀ᶠ u in 𝓝 x,g u∈U (q (f u)) ∧
      ‖φ (q (f u)) (g u)-φ (q (f u)) (f u)‖≤δ := by
  apply eventually_selected K hK q hq f x hf
    (fun i => {u | g u∈U i ∧ ‖φ i (g u)-φ i (f u)‖≤δ})
  intro i hi
  have hgf := hbase i hi
  have hcf : ContinuousAt (fun u => φ i (f u)) x :=
    ((hφ i).continuousAt ((hU i).mem_nhds (hKU i hi))).comp hf
  have hcg : ContinuousAt (fun u => φ i (g u)) x :=
    ((hφ i).continuousAt ((hU i).mem_nhds hgf.1)).comp hg
  filter_upwards [hg.eventually ((hU i).mem_nhds hgf.1),
    (hcg.sub hcf).norm.eventually (gt_mem_nhds hgf.2)] with u hu hv
  exact ⟨hu,hv.le⟩

/-- Finitely many positive and negative iterate charts may be handled at
once. The number of cases affects only a local neighborhood, never the
number of partition labels or an error/mass bound. -/
theorem selected_path_tube_germ {T : Type*} [Finite T]
    (K U : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (hU : ∀ i,IsOpen (U i)) (hKU : ∀ i,K i⊆U i)
    (q : Y → ι) (hq : ∀ y,y∈K (q y))
    (φ : ι → Y → E) (hφ : ∀ i,ContinuousOn (φ i) (U i))
    (f g : T → X → Y) (x : X)
    (hf : ∀ t,ContinuousAt (f t) x) (hg : ∀ t,ContinuousAt (g t) x)
    (δ : ℝ) (hbase : ∀ t i,f t x∈K i →
      g t x∈U i ∧ ‖φ i (g t x)-φ i (f t x)‖<δ) :
    ∀ᶠ u in 𝓝 x,∀ t,g t u∈U (q (f t u)) ∧
      ‖φ (q (f t u)) (g t u)-φ (q (f t u)) (f t u)‖≤δ := by
  exact Filter.eventually_all.mpr (fun t => selected_tube_germ K U hK hU hKU
    q hq φ hφ (f t) (g t) x (hf t) (hg t) δ (hbase t))
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A genuine sharp orbit tube persists in all selected old charts along a
continuous local branch. Intermediate chart selectors need not be locally
constant; their finite compact cores suffice. -/
theorem actual_selected_tube_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧
      ∀ {X T : Type*} [TopologicalSpace X] [Finite T]
        (c : M → ι) (_ : ∀ z,z∈K (c z))
        (f g : T → X → M) (x : X) (ρ δ : ℝ),
        (∀ t,ContinuousAt (f t) x) → (∀ t,ContinuousAt (g t) x) →
        0≤ρ → ρ≤r → C*ρ<δ →
        (∀ t,closedBall ((extChartAt I (a (c (f t x)))) (f t x)) ρ⊆interior (range I)) →
        (∀ t,g t x∈(extChartAt I (a (c (f t x)))).source ∧
          ‖(extChartAt I (a (c (f t x)))) (g t x)-
            (extChartAt I (a (c (f t x)))) (f t x)‖≤ρ) →
        ∀ᶠ u in 𝓝 x,∀ t,g t u∈(extChartAt I (a (c (f t u)))).source ∧
          ‖(extChartAt I (a (c (f t u)))) (g t u)-
            (extChartAt I (a (c (f t u)))) (f t u)‖≤δ := by
  obtain ⟨r,C,hr,hC,ht⟩ := uniform_chart_transfer I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro X T _ _ c hc f g x ρ δ hf hg hρ hρr hδ hsafe hbase
  apply AtlasCores.selected_path_tube_germ K
    (fun i => (extChartAt I (a i)).source) (fun i => (hK i).isClosed)
    (fun i => by simpa only [extChartAt_source] using (chartAt H (a i)).open_source)
    (fun i => by simpa only [extChartAt_source] using hKU i)
    c hc (fun i => extChartAt I (a i)) (fun i => continuousOn_extChartAt (I := I) (a i))
    f g x hf hg δ
  intro t i hi
  obtain ⟨hs,hb⟩ := ht (c (f t x)) i (f t x) (g t x) ρ (hc _) hi hρ hρr (hsafe t)
    (by simpa only [extChartAt_source] using (hbase t).1) (hbase t).2
  exact ⟨by simpa only [extChartAt_source] using hs,
    lt_of_le_of_lt (hb.trans (mul_le_mul_of_nonneg_left (hbase t).2 (by linarith))) hδ⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Actual orbit tubes persist locally under continuous input and output
branches without continuity of the atlas selector. -/
theorem original_tube_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧
      ∀ {X : Type*} [TopologicalSpace X] (S : Diffeomorph I I M M ∞)
        (c : M → ι) (_ : ∀ z,z∈K (c z))
        (f g : X → M) (x : X) (n : ℕ) (ρ δ : ℝ),
        ContinuousAt f x → ContinuousAt g x →
        0≤ρ → ρ≤r → C*ρ<δ →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] (f x))))) (S^[t.val] (f x))) ρ
          ⊆interior (range I)) →
        originalTube I S a c (n:=n) ρ (f x) (g x) →
        ∀ᶠ u in 𝓝 x,originalTube I S a c (n:=n) δ (f u) (g u) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := actual_selected_tube_germ I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro X _ S c hc f g x n ρ δ hf hg hρ hρr hδ hsafe hbase
  have hh := hgerm c hc (fun t : Fin (n+1) => S^[t.val] ∘ f)
    (fun t : Fin (n+1) => S^[t.val] ∘ g) x ρ δ
    (fun t => (S.continuous.iterate t.val).continuousAt.comp hf)
    (fun t => (S.continuous.iterate t.val).continuousAt.comp hg)
    hρ hρr hδ hsafe (fun t => ⟨by simpa only [extChartAt_source,Function.comp_apply] using (hbase t).1,(hbase t).2⟩)
  simpa only [originalTube,Function.comp_apply,extChartAt_source] using hh
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The authentic smooth local pair branch agrees with the canonical switch
on a relative neighborhood of the retained set. No regularity of good gauge
witnesses or intermediate chart labels enters this assertion. -/
theorem original_pair_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧
      ∀ {X J A : Type*} [TopologicalSpace X]
        (S : Diffeomorph I I M M ∞) (c : M → ι) (_ : ∀ z,z∈K (c z))
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
        (n : ℕ) (ρ δ : ℝ) (Φ : M×M → M×M)
        (e Ψ : X → M×M) (x : X),
        ContinuousAt e x → ContinuousAt Ψ x → 0≤ρ → ρ≤r → C*ρ<δ →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] (e x).1)))) (S^[t.val] (e x).1)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] (e x).1)))) (S.symm^[t.val] (e x).1)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] (e x).2)))) (S^[t.val] (e x).2)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] (e x).2)))) (S.symm^[t.val] (e x).2)) ρ⊆interior (range I)) →
        originalTube I S a c (n:=n) ρ (e x).1 (Ψ x).1 →
        originalTube I S.symm a c (n:=n) ρ (e x).2 (Ψ x).1 →
        originalTube I S a c (n:=n) ρ (e x).2 (Ψ x).2 →
        originalTube I S.symm a c (n:=n) ρ (e x).1 (Ψ x).2 →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z →
            z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ᶠ t in 𝓝 x,
          originalEndpoint I S a c (n:=n) (Wf (P (e t).1,P (S^[n] (e t).1))) (e t).1 (Ψ t).1 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).2,P (S.symm^[n] (e t).2))) (e t).2 (Ψ t).1 ∧
          originalEndpoint I S a c (n:=n) (Wf (P (e t).2,P (S^[n] (e t).2))) (e t).2 (Ψ t).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).1,P (S.symm^[n] (e t).1))) (e t).1 (Ψ t).2) →
        ∀ᶠ t in 𝓝 x,(e t).1∈R → (e t).2∈R → L (e t).1=L (e t).2 → Ψ t=Φ (e t) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := original_tube_germ I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro X J A _ S c hc P L R Wf Wb n ρ δ Φ e Ψ x he hΨ hρ hρr hδ
    hsafe h1 h2 h3 h4 huniq hsecond heq
  have ht1 := hgerm S c hc (fun t => (e t).1) (fun t => (Ψ t).1) x n ρ δ
    he.fst hΨ.fst hρ hρr hδ (fun t => (hsafe t).1) h1
  have ht2 := hgerm S.symm c hc (fun t => (e t).2) (fun t => (Ψ t).1) x n ρ δ
    he.snd hΨ.fst hρ hρr hδ (fun t => (hsafe t).2.2.2) h2
  have ht3 := hgerm S c hc (fun t => (e t).2) (fun t => (Ψ t).2) x n ρ δ
    he.snd hΨ.snd hρ hρr hδ (fun t => (hsafe t).2.2.1) h3
  have ht4 := hgerm S.symm c hc (fun t => (e t).1) (fun t => (Ψ t).2) x n ρ δ
    he.fst hΨ.snd hρ hρr hδ (fun t => (hsafe t).2.1) h4
  filter_upwards [ht1,ht2,ht3,ht4,heq] with t h1t h2t h3t h4t ht
  intro hu hv hL
  apply Prod.ext
  · exact huniq _ hu _ hv hL _ h1t h2t ht.1 ht.2.1
  · obtain ⟨h1',h2',h3',h4'⟩ := hsecond _ hu _ hv hL
    exact (huniq _ hv _ hu hL.symm _ h3t h4t ht.2.2.1 ht.2.2.2).trans
      (huniq _ hv _ hu hL.symm _ h1' h2' h3' h4').symm
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ChartDensity
open Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Measurable total chart extensions agree with the authentic inverse chart
on a neighborhood of every interior coordinate point. -/
lemma inverse_germ (a : M) (u : E₀) (hu : u∈(extChartAt I a).target)
    (hi : u∈interior (range I)) :
    ContinuousAt (extChartAt I a).symm u ∧
    ∀ᶠ v in 𝓝 u,inverse I a v=(extChartAt I a).symm v ∧
      coordinates I a ((extChartAt I a).symm v)=v := by
  have ht := extChartAt_target_mem_nhdsWithin_of_mem hu
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hi)] at ht
  refine ⟨(continuousOn_extChartAt_symm a u hu).continuousAt ht,?_⟩
  filter_upwards [ht] with v hv
  refine ⟨inverse_eq I a v hv,?_⟩
  rw [coordinates_eq I a _ ((extChartAt I a).map_target hv)]
  exact (extChartAt I a).right_inv hv

lemma pair_inverse_germ (a : M) (u : E₀×E₀)
    (h₁ : u.1∈(extChartAt I a).target) (h₂ : u.2∈(extChartAt I a).target)
    (i₁ : u.1∈interior (range I)) (i₂ : u.2∈interior (range I)) :
    let r₀ := Prod.map (extChartAt I a).symm (extChartAt I a).symm
    let r := Prod.map (inverse I a) (inverse I a)
    let e := Prod.map (coordinates I a) (coordinates I a)
    ContinuousAt r₀ u ∧ ∀ᶠ v in 𝓝 u,r v=r₀ v ∧ e (r₀ v)=v := by
  intro r₀ r e
  obtain ⟨hc₁,hg₁⟩ := inverse_germ I a u.1 h₁ i₁
  obtain ⟨hc₂,hg₂⟩ := inverse_germ I a u.2 h₂ i₂
  refine ⟨(hc₁.comp continuousAt_fst).prodMk (hc₂.comp continuousAt_snd),?_⟩
  filter_upwards [continuousAt_fst.eventually hg₁,continuousAt_snd.eventually hg₂] with v hv₁ hv₂
  exact ⟨Prod.ext hv₁.1 hv₂.1,Prod.ext hv₁.2 hv₂.2⟩

/-- Physical agreement on retained inputs gives the exact coordinate germ
required for change of variables, despite arbitrary chart extensions away
from their sources. Only the original retained set is used. -/
theorem retained_pair_germ (a : M) (G : Set (M×M)) (Φ : M×M → M×M)
    (Ψ : E₀×E₀ → E₀×E₀) (u : E₀×E₀) (hΨ : ContinuousAt Ψ u)
    (hu₁ : u.1∈(extChartAt I a).target) (hu₂ : u.2∈(extChartAt I a).target)
    (iu₁ : u.1∈interior (range I)) (iu₂ : u.2∈interior (range I))
    (hv₁ : (Ψ u).1∈(extChartAt I a).target) (hv₂ : (Ψ u).2∈(extChartAt I a).target)
    (iv₁ : (Ψ u).1∈interior (range I)) (iv₂ : (Ψ u).2∈interior (range I))
    (hag : let r₀ := Prod.map (extChartAt I a).symm (extChartAt I a).symm
      ∀ᶠ v in 𝓝 u,r₀ v∈G → r₀ (Ψ v)=Φ (r₀ v)) :
    let e := Prod.map (coordinates I a) (coordinates I a)
    let r := Prod.map (inverse I a) (inverse I a)
    Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e r G] u] (e ∘ Φ ∘ r) := by
  intro e r
  let r₀ := Prod.map (extChartAt I a).symm (extChartAt I a).symm
  have hinput := (pair_inverse_germ I a u hu₁ hu₂ iu₁ iu₂).2
  have hout := hΨ.eventually ((pair_inverse_germ I a (Ψ u) hv₁ hv₂ iv₁ iv₂).2)
  have hall : ∀ᶠ v in 𝓝 u,v∈ChartDomination.coordinateSet e r G → Ψ v=(e ∘ Φ ∘ r) v := by
    filter_upwards [hinput,hout,hag] with v hv hv' hag'
    intro hvG
    have hrv : r v=r₀ v := hv.1
    have hg : r₀ v∈G := by rw [←hrv]; exact hvG.1
    have heq : r₀ (Ψ v)=Φ (r₀ v) := hag' hg
    change Ψ v=e (Φ (r v))
    rw [hrv,←heq]
    exact hv'.2.symm
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with v hv hvG
  exact hv hvG
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι A : Type*}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Endpoint rows in a fixed old chart are exactly the canonical projected
equation when the ORIGINAL endpoint label is retained. -/
lemma original_endpoint_iff_coordinates (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) (P : M → A)
    (hPc : ∀ x y,P x=P y → c x=c y) (W : A×A → Submodule ℝ E₀)
    (a₀ x : M) (n : ℕ) (u v : E₀)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W (P x,P (S^[n] x)))
    (hz : ∀ z∈W (P x,P (S^[n] x)),∀ j∉r,b.repr z j=0)
    (hP₀ : P ((extChartAt I a₀).symm u)=P x)
    (hP₁ : P (S^[n] ((extChartAt I a₀).symm u))=P (S^[n] x)) :
    originalEndpoint I S a c (n:=n)
      (W (P ((extChartAt I a₀).symm u),P (S^[n] ((extChartAt I a₀).symm u))))
      ((extChartAt I a₀).symm u) ((extChartAt I a₀).symm v) ↔
    EndpointFrame.coordinates b r
      ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) v)=
    EndpointFrame.coordinates b r
      ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) u) := by
  rw [originalEndpoint,hP₀,hP₁,hPc _ _ hP₁]
  exact (EndpointFrame.coordinates_eq_iff _ b r hr hz _ _).symm

lemma inverse_continuousAt_interior (a : M) (u : E₀)
    (hu : u∈(extChartAt I a).target) (hi : u∈interior (range I)) :
    ContinuousAt (extChartAt I a).symm u := by
  have ht := extChartAt_target_mem_nhdsWithin_of_mem hu
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hi)] at ht
  exact (continuousOn_extChartAt_symm a u hu).continuousAt ht

/-- The four original endpoint equations of a smooth pair branch follow
from the four IFT row equations, using only the OLD starting and endpoint
labels. No intermediate orbit label is frozen or added to the cell. -/
theorem original_equations_germ {q : ℕ}
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι) (P : M → A)
    (hPc : ∀ x y,P x=P y → c x=c y)
    (Wf Wb : A×A → Submodule ℝ E₀) (a₀ x y : M) (n : ℕ)
    (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E₀)
    (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
    (hb₀ : ∀ j∈r₀,b₀ j∈Wf (P x,P (S^[n] x)))
    (hz₀ : ∀ z∈Wf (P x,P (S^[n] x)),∀ j∉r₀,b₀.repr z j=0)
    (hb₁ : ∀ j∈r₁,b₁ j∈Wf (P y,P (S^[n] y)))
    (hz₁ : ∀ z∈Wf (P y,P (S^[n] y)),∀ j∉r₁,b₁.repr z j=0)
    (hc₀ : ∀ j∈s₀,c₀ j∈Wb (P x,P (S.symm^[n] x)))
    (hv₀ : ∀ z∈Wb (P x,P (S.symm^[n] x)),∀ j∉s₀,c₀.repr z j=0)
    (hc₁ : ∀ j∈s₁,c₁ j∈Wb (P y,P (S.symm^[n] y)))
    (hv₁ : ∀ z∈Wb (P y,P (S.symm^[n] y)),∀ j∉s₁,c₁.repr z j=0)
    (Ψ : E₀×E₀ → E₀×E₀) (u : E₀×E₀)
    (hlabels : ∀ᶠ t in 𝓝 u,
      P ((extChartAt I a₀).symm t.1)=P x ∧
      P ((extChartAt I a₀).symm t.2)=P y ∧
      P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
      P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y))
    (heq : ∀ᶠ t in 𝓝 u,
      EndpointFrame.coordinates b₀ r₀ ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) (Ψ t).1)=
        EndpointFrame.coordinates b₀ r₀ ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) t.1) ∧
      EndpointFrame.coordinates b₁ r₁ ((extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm) (Ψ t).2)=
        EndpointFrame.coordinates b₁ r₁ ((extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm) t.2) ∧
      EndpointFrame.coordinates c₀ s₀ ((extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) (Ψ t).2)=
        EndpointFrame.coordinates c₀ s₀ ((extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) t.1) ∧
      EndpointFrame.coordinates c₁ s₁ ((extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) (Ψ t).1)=
        EndpointFrame.coordinates c₁ s₁ ((extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) t.2)) :
    let e := Prod.map (extChartAt I a₀).symm (extChartAt I a₀).symm
    ∀ᶠ t in 𝓝 u,
      originalEndpoint I S a c (n:=n) (Wf (P (e t).1,P (S^[n] (e t).1))) (e t).1 (e (Ψ t)).1 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).2,P (S.symm^[n] (e t).2))) (e t).2 (e (Ψ t)).1 ∧
      originalEndpoint I S a c (n:=n) (Wf (P (e t).2,P (S^[n] (e t).2))) (e t).2 (e (Ψ t)).2 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).1,P (S.symm^[n] (e t).1))) (e t).1 (e (Ψ t)).2 := by
  intro e
  filter_upwards [hlabels,heq] with t ht he
  exact ⟨(original_endpoint_iff_coordinates I S a c P hPc Wf a₀ x n t.1 (Ψ t).1 b₀ r₀ hb₀ hz₀ ht.1 ht.2.2.1).mpr he.1,
    (original_endpoint_iff_coordinates I S.symm a c P hPc Wb a₀ y n t.2 (Ψ t).1 c₁ s₁ hc₁ hv₁ ht.2.1 ht.2.2.2.2.2).mpr he.2.2.2,
    (original_endpoint_iff_coordinates I S a c P hPc Wf a₀ y n t.2 (Ψ t).2 b₁ r₁ hb₁ hz₁ ht.2.1 ht.2.2.2.1).mpr he.2.1,
    (original_endpoint_iff_coordinates I S.symm a c P hPc Wb a₀ x n t.1 (Ψ t).2 c₀ s₀ hc₀ hv₀ ht.1 ht.2.2.2.2.1).mpr he.2.2.1⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p q : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The authentic eight endpoint minors give the local Jacobian germ of the
ORIGINAL measurable switch. Rank-zero blocks are included. The agreement is
relative to retained original inputs, not an extension or a different law. -/
theorem controlled_original_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0<r ∧ 1≤C ∧ 0<β ∧
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ≤r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        let Z := (extChartAt I a₀) z
        let W := (extChartAt I a₀) w
        let f₀ := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm
        let f₁ := extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm
        let g₀ := extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm
        let g₁ := extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
          (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E₀)
          (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
          (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
          (∀ j∈r₀,b₀ j∈Wf (P x,P (S^[n] x))) →
          (∀ v∈Wf (P x,P (S^[n] x)),∀ j∉r₀,b₀.repr v j=0) →
          (∀ j∈r₁,b₁ j∈Wf (P y,P (S^[n] y))) →
          (∀ v∈Wf (P y,P (S^[n] y)),∀ j∉r₁,b₁.repr v j=0) →
          (∀ j∈s₀,c₀ j∈Wb (P x,P (S.symm^[n] x))) →
          (∀ v∈Wb (P x,P (S.symm^[n] x)),∀ j∉s₀,c₀.repr v j=0) →
          (∀ j∈s₁,c₁ j∈Wb (P y,P (S.symm^[n] y))) →
          (∀ v∈Wb (P y,P (S.symm^[n] y)),∀ j∉s₁,c₁.repr v j=0) →
          GoodEndpoint β b₀ r₀ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₀ X A₀ →
          GoodEndpoint β b₀ r₀ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₀ Z A₀ →
          GoodEndpoint β b₁ r₁ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₁ Y A₁ →
          GoodEndpoint β b₁ r₁ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₁ W A₁ →
          GoodEndpoint β c₀ s₀ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₀ X D₀ →
          GoodEndpoint β c₀ s₀ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₀ W D₀ →
          GoodEndpoint β c₁ s₁ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₁ Y D₁ →
          GoodEndpoint β c₁ s₁ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₁ Z D₁ →
          coordinates b₀ r₀ (f₀ Z)=coordinates b₀ r₀ (f₀ X) →
          coordinates b₁ r₁ (f₁ W)=coordinates b₁ r₁ (f₁ Y) →
          coordinates c₀ s₀ (g₀ W)=coordinates c₀ s₀ (g₀ X) →
          coordinates c₁ s₁ (g₁ Z)=coordinates c₁ s₁ (g₁ Y) →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := original_pair_germ I hclosed a K hK hKU
  obtain ⟨β,hβ,hbranch⟩ := four_endpoint_branch (d:=d) (p:=p) (q:=q)
  refine ⟨r,C,β,hr,hC,hβ,?_⟩
  intro A J S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    z w ht1 ht2 ht3 ht4 a₀ X Y Z W f₀ f₁ g₀ g₁ U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ A₀ A₁ D₀ D₁
    hb₀ hz₀ hb₁ hz₁ hc₀ hv₀ hc₁ hv₁ hxF hzF hyF hwF hxB hwB hyB hzB he₀ he₁ he₂ he₃ hlabels e s
  obtain ⟨Ψ,hΨ,hcd,hlo,_,heq⟩ := hbranch U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁
    f₀ f₁ g₀ g₁ X Y Z W A₀ A₁ D₀ D₁ hxF hzF hyF hwF hxB hwB hyB hzB he₀ he₁ he₂ he₃
  let r₀' := Prod.map (extChartAt I a₀).symm (extChartAt I a₀).symm
  have hsrcx : x∈(extChartAt I a₀).source := by simpa only [extChartAt_source] using hKU _ (hc x)
  have hsrcy : y∈(extChartAt I a₀).source := by
    dsimp only [a₀]; rw [hcxy]; simpa only [extChartAt_source] using hKU _ (hc y)
  have hsrcz : z∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht1 0).1
  have hsrcw : w∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht4 0).1
  have hx : r₀' (X,Y)=(x,y) := Prod.ext ((extChartAt I a₀).left_inv hsrcx) ((extChartAt I a₀).left_inv hsrcy)
  have hz : r₀' (Ψ (X,Y))=(z,w) := by
    rw [hΨ]; exact Prod.ext ((extChartAt I a₀).left_inv hsrcz) ((extChartAt I a₀).left_inv hsrcw)
  have hXi : X∈interior (range I) := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply] using (hsafe 0).1 (mem_closedBall_self hρ)
  have hYi : Y∈interior (range I) := by
    dsimp only [Y,a₀]; rw [hcxy]
    simpa only [Fin.val_zero,Function.iterate_zero_apply] using (hsafe 0).2.2.1 (mem_closedBall_self hρ)
  have hZi : Z∈interior (range I) := by
    apply (hsafe 0).1
    exact mem_closedBall.mpr (by simpa only [Fin.val_zero,Function.iterate_zero_apply,dist_eq_norm] using (ht1 0).2)
  have hWi : W∈interior (range I) := by
    apply (hsafe 0).2.1
    exact mem_closedBall.mpr (by simpa only [Fin.val_zero,Function.iterate_zero_apply,dist_eq_norm] using (ht4 0).2)
  have hct := (ChartDensity.pair_inverse_germ I a₀ (X,Y)
    ((extChartAt I a₀).map_source hsrcx) ((extChartAt I a₀).map_source hsrcy) hXi hYi).1
  have hco : ContinuousAt r₀' (Z,W) := (ChartDensity.pair_inverse_germ I a₀ (Z,W)
    ((extChartAt I a₀).map_source hsrcz) ((extChartAt I a₀).map_source hsrcw) hZi hWi).1
  have hctΨ : ContinuousAt (r₀' ∘ Ψ) (X,Y) := (hΨ ▸ hco).comp hcd.continuousAt
  have heq' := original_equations_germ I S a c P hPc Wf Wb a₀ x y n b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁
    hb₀ hz₀ hb₁ hz₁ hc₀ hv₀ hc₁ hv₁ Ψ (X,Y) hlabels heq
  have hag := hgerm S c hc P L R Wf Wb n ρ δ Φ r₀' (r₀' ∘ Ψ) (X,Y)
    hct hctΨ hρ hρr hρδ (by simpa only [hx] using hsafe)
    (by simpa only [Function.comp_apply,hx,hz] using ht1)
    (by simpa only [Function.comp_apply,hx,hz] using ht2)
    (by simpa only [Function.comp_apply,hx,hz] using ht3)
    (by simpa only [Function.comp_apply,hx,hz] using ht4) huniq hsecond heq'
  refine ⟨Ψ,(hcd.differentiableAt (by simp)).hasFDerivAt,hlo,?_⟩
  apply ChartDensity.retained_pair_germ I a₀ G Φ Ψ (X,Y) hcd.continuousAt
    ((extChartAt I a₀).map_source hsrcx) ((extChartAt I a₀).map_source hsrcy) hXi hYi
  · simpa only [hΨ] using (extChartAt I a₀).map_source hsrcz
  · simpa only [hΨ] using (extChartAt I a₀).map_source hsrcw
  · simpa only [hΨ] using hZi
  · simpa only [hΨ] using hWi
  · filter_upwards [hag] with t ht
    intro htG
    exact ht (hG _ htG).1 (hG _ htG).2.1 (hG _ htG).2.2
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The original orbit-tube endpoint minor, now with the actual bilateral
finite-time gauge. This is uniform in every starting bin and every rank. -/
theorem gauge_endpoint_minor (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ Crel C₁ : ℝ,0<r ∧ 1≤K₀ ∧ 0≤Crel ∧ 0≤C₁ ∧
      ∀ {p q : ℕ} (c : M → ι) (x y : M) (n : ℕ) (b R C δ β γ g : ℝ)
        (A : BilateralGauge I S a c n (Dg*(b*n)) R x)
        (T : Finset (Fin d)) (_ : T.card=p),
        (∀ z,z∈L (c z)) → 0≤b → 1≤b*n → 0≤R → 0≤g → 0≤C → 0≤δ →
        (∀ j∈T,γ+g≤A.lam j) → (∀ j∉T,A.lam j≤γ-g) →
        let ρ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        K₀*ρ≤1 → ρ≤r → originalTube I S a c (n:=n) ρ x y →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I)) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior p B‖≤C*(max 1 ‖B‖)^p) →
        ∀ (W G Gslow : Submodule ℝ E₀),Module.finrank ℝ W=p →
        (‖(A.forwardSpace I S a c n T).starProjection-W.starProjection‖≤1/2) →
        (‖(A.forwardSpace I S a c 0 T).starProjection-G.starProjection‖≤δ) →
        (‖(A.forwardSpace I S a c 0 Tᶜ).starProjection-Gslow.starProjection‖≤δ) →
        ∀ (bE : OrthonormalBasis (Fin d) ℝ E₀) (rE : powersetCard (Fin d) p),
        (∀ j∈rE,bE j∈W) → (∀ v∈W,∀ j∉rE,bE.repr v j=0) →
        ∀ (v : Fin p → E₀) (z : Fin q → E₀),Orthonormal ℝ v →
        (∀ i,v i∈G) → (∀ j,z j∈Gslow) → (∀ j,‖z j‖≤1) →
        let K := Dg*(b*n)
        let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
        let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p) : ℝ))
        let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p) : ℝ)*‖continuousWedge (E := E₀) p‖
        let ζ := RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n *
          Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n)
        let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
        let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := E₀) p*δ)
        (frameWedgeConstant (E := E₀) p*δ)*(1+L₀*N₀)≤1/2 →
        ε≤1/100 → (θ+ε)/(1-ε)≤β →
        let F := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm
        GoodEndpoint β bE rE v z F ((extChartAt I (a (c x))) y)
          (endpointMatrix bE p rE (fderiv ℝ F ((extChartAt I (a (c x))) x)) v) := by
  obtain ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,hh⟩ := actual_endpoint_minor I hclosed S a L hL hLU Dg hDg
  refine ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,?_⟩
  intro p q c x y n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hfast hslow ρ hρ hρr ht hs
  apply hh c x y n A.UF A.VF A.lam T hTp γ g (Dg*(b*n)) b n R C δ β hc hb
    (Nat.cast_nonneg n) hbn hR hg (by positivity) le_rfl (by nlinarith [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]) hC hδ
    (fun t => (A.invF t).1) (fun t => (A.invF t).2) A.stepF A.rate_bound hfast hslow
    (fun t ht => (A.normF t ht).1) (fun t ht => (A.normF t ht).2) hρ hρr
    (fun t htn => by simpa only [extChartAt_source] using (ht ⟨t,by omega⟩).1) (fun t htn => (ht ⟨t,by omega⟩).2)
    (fun t htn => hs ⟨t,by omega⟩)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.EndpointBudget
open Set EndpointFrame ExteriorStability
/-- Literal three errors entering the actual endpoint-minor theorem. -/
def admissible (d p : ℕ) (Dg R C K₀ Crel C₁ b n g δ β : ℝ) : Prop :=
  let K := Dg*(b*n)
  let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
  let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p) : ℝ))
  let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p) : ℝ)*‖continuousWedge (E := EuclideanSpace ℝ (Fin d)) p‖
  let ζ := RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n *
    Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n)
  let ε := 2*L₀*C*ζ*‖continuousWedge (E := EuclideanSpace ℝ (Fin d)) p‖
  let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := EuclideanSpace ℝ (Fin d)) p*δ)
  (frameWedgeConstant (E := EuclideanSpace ℝ (Fin d)) p*δ)*(1+L₀*N₀)≤1/2 ∧
    ε≤1/100 ∧ (θ+ε)/(1-ε)≤β
end SmoothObstruction.EndpointBudget

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- One authentic frame and one original leading matrix control the whole
old-chart orbit tube. Neither the frame nor the normalization is reselected
at the perturbed point. -/
theorem gauge_endpoint_family (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ Crel C₁ : ℝ,0<r ∧ 1≤K₀ ∧ 0≤Crel ∧ 0≤C₁ ∧
      ∀ {p q : ℕ} (c : M → ι) (x : M) (n : ℕ) (b R C δ β γ g : ℝ)
        (A : BilateralGauge I S a c n (Dg*(b*n)) R x)
        (T : Finset (Fin d)) (_ : T.card=p),
        (∀ z,z∈L (c z)) → 0≤b → 1≤b*n → 0≤R → 0≤g → 0≤C → 0≤δ →
        (∀ j∈T,γ+g≤A.lam j) → (∀ j∉T,A.lam j≤γ-g) →
        let ρ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        K₀*ρ≤1 → ρ≤r →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I)) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior p B‖≤C*(max 1 ‖B‖)^p) →
        ∀ (W G Gslow : Submodule ℝ E₀),Module.finrank ℝ W=p →
        (‖(A.forwardSpace I S a c n T).starProjection-W.starProjection‖≤1/2) →
        (‖(A.forwardSpace I S a c 0 T).starProjection-G.starProjection‖≤δ) →
        (‖(A.forwardSpace I S a c 0 Tᶜ).starProjection-Gslow.starProjection‖≤δ) →
        ∀ (u : OrthonormalBasis (Fin p) ℝ G) (v : OrthonormalBasis (Fin q) ℝ Gslow),
        EndpointBudget.admissible d p Dg R C K₀ Crel C₁ b n g δ β →
        ∃ (bE : OrthonormalBasis (Fin d) ℝ E₀) (rE : powersetCard (Fin d) p)
          (D : Matrix (Fin p) (Fin p) ℝ),
          (∀ j∈rE,bE j∈W) ∧ (∀ v∈W,∀ j∉rE,bE.repr v j=0) ∧
          ∀ y,originalTube I S a c (n:=n) ρ x y →
            let F := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm
            GoodEndpoint β bE rE (fun i => (u i:E₀)) (fun i => (v i:E₀)) F
              ((extChartAt I (a (c x))) y) D := by
  obtain ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,hm⟩ := gauge_endpoint_minor I hclosed S a L hL hLU Dg hDg
  refine ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,?_⟩
  intro p q c x n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hf hs ρ hρ hρr hsafe hpoly
    W G Gslow hdim hend hstart hstartSlow u v hbud
  obtain ⟨bE,rE,hrE,_,hzero⟩ := EndpointFrame.exists_frame W hdim
  let F := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm
  let D := endpointMatrix bE p rE (fderiv ℝ F ((extChartAt I (a (c x))) x)) (fun i => (u i:E₀))
  refine ⟨bE,rE,D,hrE,hzero,?_⟩
  intro y hy
  have hu : Orthonormal ℝ (fun i => (u i:E₀)) := u.orthonormal.comp_linearIsometry G.subtypeₗᵢ
  have hvnorm (i : Fin q) : ‖(v i:E₀)‖≤1 := by
    change ‖v i‖≤1
    exact le_of_eq (v.norm_eq_one i)
  exact hm c x y n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hf hs hρ hρr hy hsafe
    hpoly W G Gslow hdim hend hstart hstartSlow bE rE hrE hzero
    (fun i => (u i:E₀)) (fun i => (v i:E₀)) hu (fun i => (u i).property)
    (fun i => (v i).property) hvnorm hbud.1 hbud.2.1 hbud.2.2

omit [IsManifold I ∞ M] [Fintype ι] in
lemma originalTube_self (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {ρ : ℝ} (hρ : 0≤ρ) (x : M)
    (hsrc : ∀ z,z∈(chartAt H (a (c z))).source) : originalTube I S a c (n:=n) ρ x x := by
  intro t
  exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hρ⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p q : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

def OriginalEndpointControl (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    (n : ℕ) (ρ β : ℝ) (W : Submodule ℝ E₀) (u : Fin p → E₀) (v : Fin q → E₀) (x : M) : Prop :=
  ∃ (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (D : Matrix (Fin p) (Fin p) ℝ),
    (∀ j∈r,b j∈W) ∧ (∀ z∈W,∀ j∉r,b.repr z j=0) ∧
    ∀ y,originalTube I S a c (n:=n) ρ x y →
      GoodEndpoint β b r u v
        (extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm)
        ((extChartAt I (a (c x))) y) D

omit [IsManifold I ∞ M] [Fintype ι] in
lemma originalEndpoint_coordinates (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) (n : ℕ) (a₀ x z : M) (W : Submodule ℝ E₀)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hz : ∀ z∈W,∀ j∉r,b.repr z j=0)
    (hx : x∈(extChartAt I a₀).source) (hzt : z∈(extChartAt I a₀).source)
    (he : originalEndpoint I S a c (n:=n) W x z) :
    coordinates b r ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm)
      ((extChartAt I a₀) z))=
    coordinates b r ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm)
      ((extChartAt I a₀) x)) := by
  simp only [Function.comp_apply,(extChartAt I a₀).left_inv hx,(extChartAt I a₀).left_inv hzt]
  exact (EndpointFrame.coordinates_eq_iff W b r hr hz _ _).mpr he

/-- Fixed old-chart endpoint families give the actual retained-set relative germ. -/
theorem family_original_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0<r ∧ 1≤C ∧ 0<β ∧
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ≤r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
          OriginalEndpointControl I S a c n ρ β (Wf (P x,P (S^[n] x))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) x →
          OriginalEndpointControl I S a c n ρ β (Wf (P y,P (S^[n] y))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) y →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P x,P (S.symm^[n] x))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) x →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P y,P (S.symm^[n] y))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) y →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  obtain ⟨r,C,β,hr,hC,hβ,hh⟩ := controlled_original_germ (p:=p) (q:=q) I hclosed a K hK hKU
  refine ⟨r,C,β,hr,hC,hβ,?_⟩
  intro A J S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    z w ht1 ht2 ht3 ht4 a₀ X Y U V h u v hf₀ hf₁ hb₀ hb₁ he₀ he₁ he₂ he₃ hlabels e s
  obtain ⟨b₀,r₀,A₀,hbF₀,hzF₀,hmF₀⟩ := hf₀
  obtain ⟨b₁,r₁,A₁,hbF₁,hzF₁,hmF₁⟩ := hf₁
  obtain ⟨c₀,s₀,D₀,hbB₀,hzB₀,hmB₀⟩ := hb₀
  obtain ⟨c₁,s₁,D₁,hbB₁,hzB₁,hmB₁⟩ := hb₁
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hc x)
  have hx : x∈(extChartAt I a₀).source := by simpa only [extChartAt_source] using hsrc x
  have hy : y∈(extChartAt I a₀).source := by dsimp only [a₀]; rw [hcxy]; simpa only [extChartAt_source] using hsrc y
  have hz : z∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht1 0).1
  have hw : w∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht4 0).1
  have hfx := hmF₀ x (originalTube_self I S a c hρ x hsrc)
  have hfy := hmF₁ y (originalTube_self I S a c hρ y hsrc)
  have hbx := hmB₀ x (originalTube_self I S.symm a c hρ x hsrc)
  have hby := hmB₁ y (originalTube_self I S.symm a c hρ y hsrc)
  have hfw := hmF₁ w ht3
  have hbz := hmB₁ z ht2
  rw [←hcxy] at hfy hby hfw hbz
  exact hh S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    ht1 ht2 ht3 ht4 U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ A₀ A₁ D₀ D₁
    hbF₀ hzF₀ hbF₁ hzF₁ hbB₀ hzB₀ hbB₁ hzB₁
    hfx (hmF₀ z ht1) hfy hfw hbx (hmB₀ w ht4) hby hbz
    (originalEndpoint_coordinates I S a c n a₀ x z _ b₀ r₀ hbF₀ hzF₀ hx hz he₀)
    (originalEndpoint_coordinates I S a c n a₀ y w _ b₁ r₁ hbF₁ hzF₁ hy hw he₁)
    (originalEndpoint_coordinates I S.symm a c n a₀ x w _ c₀ s₀ hbB₀ hzB₀ hx hw he₂)
    (originalEndpoint_coordinates I S.symm a c n a₀ y z _ c₁ s₁ hbB₁ hzB₁ hy hz he₃) hlabels
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction
lemma finite_positive_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i,0<f i) :
    ∃ b : ℝ,0<b ∧ ∀ i,b≤f i := by
  classical
  by_cases h : Nonempty ι
  · let := h
    refine ⟨Finset.univ.inf' Finset.univ_nonempty f,?_,?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hf i)
    · intro i; exact Finset.inf'_le _ (Finset.mem_univ i)
  · exact ⟨1,by norm_num,fun i => (h ⟨i⟩).elim⟩
end SmoothObstruction

end

end OAI
