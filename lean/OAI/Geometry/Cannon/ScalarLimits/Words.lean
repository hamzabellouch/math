import Mathlib
import OAI.Geometry.Cannon.Flows.State
import OAI.Geometry.Cannon.Boundary.ThinQuadrilateral

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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance boundaryStabilizerWordsSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_stabilizer_linear (b : Boundary D) :
    ∃ C : ℕ, ∀ (F : Finset G) (t : ℕ),
      (∀ g ∈ F, boundaryTranslate D hthin g b = b) →
      (∀ g ∈ F, D.graph.dist 1 g ≤ t) → F.card ≤ C*(t+1) := by
  classical
  obtain ⟨δ,hδ⟩ := hthin
  let B := (CannonGraph.finite_graph_ball D.connected
    (CannonGraph.finite_cayley_neighbors D.generators) 1 (2*δ)).toFinset
  refine ⟨(4*δ+2)*B.card, ?_⟩
  induction b using Quotient.inductionOn with
  | h r =>
    intro F t hF ht
    have hfix : ∀ q ∈ F, ∃ C : ℕ, ∀ n, D.graph.dist (q*r.val n) (r.val n) ≤ C := by
      intro q hq
      have he : Quotient.mk' (translateRay D ⟨δ,hδ⟩ q r) = (Quotient.mk' r : Boundary D) :=
        hF q hq
      have he' : Asymptotic D (translateRay D ⟨δ,hδ⟩ q r).val r.val := Quotient.exact he
      exact Asymptotic.trans D (Asymptotic.symm D (translateRay_spec D ⟨δ,hδ⟩ q r)) he'
    have hcard := CannonGraph.asymptotic_translate_card_bound D.connected
      D.dist_mul_left hδ r.val r.property.1 r.property.2 B
      (fun x hx => by simpa [B] using hx) F t ht hfix
    calc
      F.card ≤ (2*t+4*δ+2)*B.card := hcard
      _ ≤ ((4*δ+2)*(t+1))*B.card := Nat.mul_le_mul_right _ (by nlinarith)
      _ = ((4*δ+2)*B.card)*(t+1) := by ring

end CannonRelease

namespace CannonStabilizer

open Set

private def words {G : Type*} [Group G] [DecidableEq G] (a b : G) : ℕ → Finset G
  | 0 => {1}
  | n+1 => (words a b n).image (a*·) ∪ (words a b n).image (b*·)

private lemma words_preserve {G X : Type*} [Group G] [DecidableEq G]
    [MulAction G X] (a b : G) (T : Set X)
    (ha : ∀ x ∈ T, a • x ∈ T) (hb : ∀ x ∈ T, b • x ∈ T) :
    ∀ n g, g ∈ words a b n → ∀ x ∈ T, g • x ∈ T := by
  intro n
  induction n with
  | zero =>
    intro g hg x hx
    have : g = 1 := by simpa [words] using hg
    simpa [this] using hx
  | succ n ih =>
    intro g hg x hx
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
      simpa only [mul_smul] using ha (v • x) (ih v hv x hx)
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
      simpa only [mul_smul] using hb (v • x) (ih v hv x hx)

private lemma words_card {G X : Type*} [Group G] [DecidableEq G]
    [MulAction G X] (a b : G) (T U V : Set X) (hne : T.Nonempty)
    (hUT : U ⊆ T) (hVT : V ⊆ T) (hdis : Disjoint U V)
    (ha : ∀ x ∈ T, a • x ∈ U) (hb : ∀ x ∈ T, b • x ∈ V) :
    ∀ n, (words a b n).card = 2^n := by
  have hap : ∀ x ∈ T, a • x ∈ T := fun x hx => hUT (ha x hx)
  have hbp : ∀ x ∈ T, b • x ∈ T := fun x hx => hVT (hb x hx)
  intro n
  induction n with
  | zero => simp [words]
  | succ n ih =>
    have hd : Disjoint ((words a b n).image (a*·)) ((words a b n).image (b*·)) := by
      apply Finset.disjoint_left.mpr
      intro g hga hgb
      obtain ⟨u,hu,he₁⟩ := Finset.mem_image.mp hga
      obtain ⟨v,hv,he₂⟩ := Finset.mem_image.mp hgb
      obtain ⟨x,hx⟩ := hne
      have ha' : g • x ∈ U := by
        rw [← he₁,mul_smul]
        exact ha _ (words_preserve a b T hap hbp n u hu x hx)
      have hb' : g • x ∈ V := by
        rw [← he₂,mul_smul]
        exact hb _ (words_preserve a b T hap hbp n v hv x hx)
      exact Set.disjoint_left.mp hdis ha' hb'
    rw [words,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun x y h => mul_left_cancel h),
      Finset.card_image_of_injective _ (fun x y h => mul_left_cancel h),ih,pow_succ]
    omega

private lemma words_mem {G : Type*} [Group G] [DecidableEq G]
    (E : Subgroup G) (a b : G) (ha : a ∈ E) (hb : b ∈ E) :
    ∀ n g, g ∈ words a b n → g ∈ E := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have : g = 1 := Finset.mem_singleton.mp hg
    subst g
    exact E.one_mem
  | succ n ih =>
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      exact E.mul_mem ha (ih u hu)
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      exact E.mul_mem hb (ih u hu)

private lemma words_length {G : Type*} [Group G] [DecidableEq G]
    (len : G → ℕ) (h₁ : len 1 = 0)
    (hsub : ∀ g h, len (g*h) ≤ len g + len h) (a b : G) :
    ∀ n g, g ∈ words a b n → len g ≤ n * (len a + len b) := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have : g = 1 := by simpa [words] using hg
    simp [this,h₁]
  | succ n ih =>
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      have := ih u hu
      have := hsub a u
      rw [Nat.succ_mul]
      omega
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      have := ih u hu
      have := hsub b u
      rw [Nat.succ_mul]
      omega

lemma exists_exponential_gt_linear (C L : ℕ) : ∃ n : ℕ, C*(n*L+1) < 2^n := by
  let k := C*(L+1)+1
  refine ⟨2*k, ?_⟩
  have hpow := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
  have hk : C*L+1 ≤ k := by dsimp [k]; nlinarith
  have hC : C ≤ k := by dsimp [k]; nlinarith
  have hm := Nat.mul_le_mul_left (2*k) hk
  have hkpos : 0 < k := by dsimp [k]; positivity
  nlinarith

theorem no_disjoint_contractions {G X : Type*} [Group G] [MulAction G X]
    (E : Subgroup G) (len : G → ℕ) (h₁ : len 1 = 0)
    (hsub : ∀ g h, len (g*h) ≤ len g + len h)
    (C : ℕ) (hlinear : ∀ (F : Finset G) (t : ℕ),
      (∀ g ∈ F, g ∈ E) → (∀ g ∈ F, len g ≤ t) → F.card ≤ C*(t+1))
    (a b : G) (haE : a ∈ E) (hbE : b ∈ E)
    (T U V : Set X) (hne : T.Nonempty) (hUT : U ⊆ T) (hVT : V ⊆ T)
    (hdis : Disjoint U V) (ha : ∀ x ∈ T, a • x ∈ U)
    (hb : ∀ x ∈ T, b • x ∈ V) : False := by
  classical
  obtain ⟨n,hn⟩ := exists_exponential_gt_linear C (len a+len b)
  have hc := hlinear (words a b n) (n*(len a+len b))
    (words_mem E a b haE hbE n) (words_length len h₁ hsub a b n)
  rw [words_card a b T U V hne hUT hVT hdis ha hb n] at hc
  omega

def ContractingDirection {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace X] (E : Subgroup G) (b x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∀ V : Set X, IsOpen V → b ∈ V →
    ∃ g ∈ E, MapsTo (g • ·) Vᶜ U

theorem contracting_direction_unique {G X : Type*} [Group G] [MulAction G X]
    [MetricSpace X] (E : Subgroup G) (len : G → ℕ) (h₁ : len 1 = 0)
    (hsub : ∀ g h, len (g*h) ≤ len g + len h)
    (C : ℕ) (hlinear : ∀ (F : Finset G) (t : ℕ),
      (∀ g ∈ F, g ∈ E) → (∀ g ∈ F, len g ≤ t) → F.card ≤ C*(t+1))
    {b x y : X} (hxb : x ≠ b) (hyb : y ≠ b)
    (hx : ContractingDirection E b x) (hy : ContractingDirection E b y) : x = y := by
  by_contra hxy
  let r := min (dist x y) (min (dist x b) (dist y b)) / 3
  have hr : 0 < r := div_pos (lt_min (dist_pos.mpr hxy)
    (lt_min (dist_pos.mpr hxb) (dist_pos.mpr hyb))) (by norm_num)
  have hxy' : r+r ≤ dist x y := by
    have := min_le_left (dist x y) (min (dist x b) (dist y b))
    dsimp [r] at *
    linarith
  have hxb' : r+r ≤ dist x b := by
    have := (min_le_right (dist x y) (min (dist x b) (dist y b))).trans
      (min_le_left (dist x b) (dist y b))
    dsimp [r] at *
    linarith
  have hyb' : r+r ≤ dist y b := by
    have := (min_le_right (dist x y) (min (dist x b) (dist y b))).trans
      (min_le_right (dist x b) (dist y b))
    dsimp [r] at *
    linarith
  obtain ⟨g,hg,hgc⟩ := hx (Metric.ball x r) Metric.isOpen_ball
    (Metric.mem_ball_self hr) (Metric.ball b r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨h,hh,hhc⟩ := hy (Metric.ball y r) Metric.isOpen_ball
    (Metric.mem_ball_self hr) (Metric.ball b r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hUT : Metric.ball x r ⊆ (Metric.ball b r)ᶜ :=
    (Metric.ball_disjoint_ball hxb').subset_compl_right
  have hVT : Metric.ball y r ⊆ (Metric.ball b r)ᶜ :=
    (Metric.ball_disjoint_ball hyb').subset_compl_right
  exact no_disjoint_contractions E len h₁ hsub C hlinear g h hg hh
    (Metric.ball b r)ᶜ (Metric.ball x r) (Metric.ball y r)
    ⟨x,hUT (Metric.mem_ball_self hr)⟩ hUT hVT
    (Metric.ball_disjoint_ball hxy') (fun z hz => hgc hz) (fun z hz => hhc hz)

end CannonStabilizer

namespace CannonStabilizer

open CannonMagnification

@[instance_reducible] def homAction {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) : MulAction G X where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [map_one]; rfl
  mul_smul g h x := by change ρ (g*h) x = ρ g (ρ h x); rw [map_mul]; rfl

theorem contracting_direction_of_fixed_puncture
    {G X : Type*} [Group G] [MetricSpace X]
    (ρ : G →* (X ≃ₜ X)) (b y : X) (v₀ : G) (v : ℕ → G)
    (x : ℕ → X) (r : ℕ → ℝ) (C L : ℝ)
    (hdiam : ∀ z w : X, dist z w ≤ 1)
    (hC : 0 ≤ C) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hxlim : Tendsto x atTop (𝓝 y)) (hyb : y ≠ b)
    (hexp : ∀ i, Expansion (ρ ((v i)⁻¹)) (x i) (r i) C L)
    (hp : ∀ i, ρ ((v i)⁻¹) b = ρ (v₀⁻¹) b) :
    let _ : MulAction G X := homAction ρ
    ContractingDirection (MulAction.stabilizer G b) b y := by
  let _ : MulAction G X := homAction ρ
  dsimp only [ContractingDirection]
  intro U hU hyU V hV hbV
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU y hyU
  let p := ρ (v₀⁻¹) b
  have h₀ : ρ v₀ p = b := by
    dsimp [p]
    change ((ρ v₀)*(ρ (v₀⁻¹))) b = b
    rw [← map_mul,mul_inv_cancel,map_one]
    rfl
  have hpre : IsOpen ((ρ v₀) ⁻¹' V) := hV.preimage (ρ v₀).continuous
  obtain ⟨e,he,hepre⟩ := Metric.isOpen_iff.mp hpre p (by simpa [h₀] using hbV)
  have hsep : ∀ z ∉ V, e ≤ dist (ρ (v₀⁻¹) z) p := by
    intro z hz
    by_contra hez
    have hmem := hepre (show ρ (v₀⁻¹) z ∈ ball p e by exact lt_of_not_ge hez)
    have hid : ρ v₀ (ρ (v₀⁻¹) z) = z := by
      change ((ρ v₀)*(ρ (v₀⁻¹))) z = z
      rw [← map_mul,mul_inv_cancel,map_one]
      rfl
    exact hz (by simpa only [Set.mem_preimage,hid] using hmem)
  let d := dist y b / 2
  have hd : 0 < d := div_pos (dist_pos.mpr hyb) (by norm_num)
  have hdlim : Tendsto (fun i => dist (x i) b) atTop (𝓝 (dist y b)) :=
    hxlim.dist tendsto_const_nhds
  have hdlate : ∀ᶠ i in atTop, d ≤ dist (x i) b :=
    (hdlim.eventually (eventually_gt_nhds (show d < dist y b by dsimp [d]; linarith [dist_pos.mpr hyb]))).mono
      (fun _ hi => hi.le)
  have hxlate : ∀ᶠ i in atTop, dist (x i) y < ε/2 :=
    hxlim.eventually (Metric.ball_mem_nhds y (by positivity))
  have hrlim' : Tendsto (fun i => (C/(e*d))*r i) atTop (𝓝 0) := by
    simpa using hrlim.const_mul (C/(e*d))
  have hrlate : ∀ᶠ i in atTop, (C/(e*d))*r i < ε/2 :=
    hrlim'.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨i,hiD,hiX,hiR⟩ := (hdlate.and (hxlate.and hrlate)).exists
  refine ⟨v i * v₀⁻¹, ?_, ?_⟩
  · change ρ (v i * v₀⁻¹) b = b
    rw [map_mul]
    change ρ (v i) (ρ (v₀⁻¹) b) = b
    rw [← hp i]
    change ((ρ (v i))*(ρ ((v i)⁻¹))) b = b
    rw [← map_mul,mul_inv_cancel,map_one]
    rfl
  · intro z hz
    apply hεU
    have hnear := preimage_distance_bound (ρ ((v i)⁻¹)) (x i) b
      (ρ (v₀⁻¹) z) (r i) C L e d (hr i) hC he hd (hexp i) hdiam hiD
      (by rw [hp i]; exact hsep z hz)
    have hinv : (ρ ((v i)⁻¹)).symm (ρ (v₀⁻¹) z) = ρ (v i * v₀⁻¹) z := by
      rw [map_inv,map_mul]
      rfl
    rw [hinv] at hnear
    change dist (ρ (v i * v₀⁻¹) z) y < ε
    have ht := dist_triangle (ρ (v i * v₀⁻¹) z) (x i) y
    rw [dist_comm (ρ (v i * v₀⁻¹) z) (x i)] at ht
    linarith

end CannonStabilizer

namespace CannonStabilizer

open CannonMagnification

theorem puncture_fibers_finite {G X : Type*} [Group G] [MetricSpace X]
    (ρ : G →* (X ≃ₜ X)) (b : X) (v : ℕ → G) (x : ℕ → X) (r : ℕ → ℝ)
    (C L : ℝ) (hdiam : ∀ z w : X, dist z w ≤ 1)
    (hC : 0 ≤ C) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hexp : ∀ i, Expansion (ρ ((v i)⁻¹)) (x i) (r i) C L)
    (K : Set X) (hK : IsCompact K) (hxK : ∀ i, x i ∈ K) (hbK : b ∉ K)
    (hgood : let _ : MulAction G X := homAction ρ
      ∀ y ∈ K, ¬ ContractingDirection (MulAction.stabilizer G b) b y) :
    ∀ p : X, {i | ρ ((v i)⁻¹) b = p}.Finite := by
  let _ : MulAction G X := homAction ρ
  intro p
  by_contra hfin
  have hinf : Set.Infinite {i | ρ ((v i)⁻¹) b = p} := hfin
  obtain ⟨s,hs,hsp⟩ := extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hinf)
  obtain ⟨y,hy,t,ht,hyLim⟩ := hK.tendsto_subseq (fun i => hxK (s i))
  have hp : ∀ i, ρ ((v (s (t i)))⁻¹) b = ρ ((v (s (t 0)))⁻¹) b :=
    fun i => (hsp (t i)).trans (hsp (t 0)).symm
  have hyb : y ≠ b := fun h => hbK (h ▸ hy)
  have hc := contracting_direction_of_fixed_puncture ρ b y (v (s (t 0)))
    (fun i => v (s (t i))) (fun i => x (s (t i))) (fun i => r (s (t i)))
    C L hdiam hC (fun i => hr (s (t i)))
    (hrlim.comp (hs.comp ht).tendsto_atTop) hyLim hyb (fun i => hexp (s (t i))) hp
  exact hgood y hy hc

theorem injective_subsequence_of_finite_fibers {X : Type*} (p : ℕ → X)
    (hfib : ∀ x : X, {i | p i = x}.Finite) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ Function.Injective (p ∘ s) := by
  classical
  have hRange : (range p).Infinite := by
    intro hfin
    have hU : (univ : Set ℕ).Finite := Set.Finite.of_finite_fibers p
      (by simpa using hfin) (by intro x _; exact (hfib x).subset (by intro i hi; exact hi.2))
    exact Set.infinite_univ hU
  let e := hRange.natEmbedding (range p)
  have hp : ∀ i : ℕ, ∃ n : ℕ, p n = (e i).val := fun i => (e i).property
  choose f hf using hp
  have hpf : Function.Injective (p ∘ f) := by
    intro i j h
    apply e.injective
    apply Subtype.ext
    exact (hf i).symm.trans (h.trans (hf j))
  have hfij : Function.Injective f := fun i j h => hpf (congrArg p h)
  obtain ⟨s,hs,hfs⟩ := strictMono_subseq_of_tendsto_atTop hfij.nat_tendsto_atTop
  exact ⟨f ∘ s,hfs,hpf.comp hs.injective⟩

end CannonStabilizer

open Set unitInterval

namespace CannonVariation

open Filter Topology Metric

def NonconstantAt {X : Type*} [TopologicalSpace X] (F : X → ℝ) (x : X) : Prop :=
  ¬ ∀ᶠ y in 𝓝 x, F y = F x

theorem path_meets_variation {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    {x y : X} (p : Path x y) (hxy : F x ≠ F y) :
    ∃ z ∈ range p, NonconstantAt F z := by
  by_contra h
  push Not at h
  have hlc : IsLocallyConstant (fun t : I => F (p t)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro t
    have ht : ∀ᶠ z in 𝓝 (p t), F z = F (p t) := not_not.mp (h (p t) (mem_range_self t))
    exact p.continuous.continuousAt.tendsto.eventually ht
  have he := hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ (0 : I)) (mem_univ (1 : I))
  exact hxy (by simpa using he)

lemma nonconstantAt_normalize {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    (A sig : ℝ) (hsig : sig ≠ 0) (x : X) :
    NonconstantAt (fun z => (F z - A) / sig) x ↔ NonconstantAt F x := by
  simp only [NonconstantAt, div_left_inj' hsig, sub_left_inj]

theorem value_subpath {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    {x y : X} (p : Path x y) (hF : ContinuousOn F (range p))
    (a b : ℝ) (hab : a < b) (hxa : F x ≤ a) (hby : b ≤ F y) :
    ∃ v w : X, ∃ q : Path v w, range q ⊆ range p ∧ F v = a ∧ F w = b ∧
      ∀ z ∈ range q, F z ∈ Icc a b := by
  have hc : Continuous (fun t => F (p t)) := hF.comp_continuous p.continuous (fun t => mem_range_self t)
  obtain ⟨s,t,hst,hs,ht,hbt⟩ := CannonAnnular.radial_subinterval
    (fun t => F (p t)) hc a b hab (by simpa using hxa) (by simpa using hby)
  refine ⟨p s,p t,p.subpath s t,?_,hs,ht,?_⟩
  · rw [Path.range_subpath_of_le _ _ _ hst.le]
    exact image_subset_range _ _
  · intro z hz
    rw [Path.range_subpath_of_le _ _ _ hst.le] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    exact hbt u hu

end CannonVariation

end
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
