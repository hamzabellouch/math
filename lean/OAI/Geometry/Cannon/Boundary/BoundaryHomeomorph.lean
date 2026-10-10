import Mathlib
import OAI.Geometry.Cannon.Boundary.Thin

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) (hthin : D.ThinTriangles)
local instance : Setoid (BasedRay D) := raySetoid D

include hthin in
lemma translated_relation_closed (g : G) :
    IsClosed {p : BasedRay D × BasedRay D |
      Asymptotic D p.2.val (fun n => g*p.1.val n)} := by
  obtain ⟨δ,hδ⟩ := hthin
  have he : {p : BasedRay D × BasedRay D |
      Asymptotic D p.2.val (fun n => g*p.1.val n)} =
      ⋂ n : ℕ, {p | D.graph.dist (p.2.val n) (g*p.1.val n) ≤ 3*D.graph.dist 1 g + 4*δ} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hp
      have hh := CannonGraph.asymptotic_rays_different_bases_uniform D.connected
        (CannonGraph.finite_cayley_neighbors D.generators) hδ p.2.val
        (fun n => g*p.1.val n) p.2.property.2
        (fun i j => (D.dist_mul_left g _ _).trans (p.1.property.2 i j)) hp
      simpa only [p.1.property.1, p.2.property.1, mul_one, CayleyData.graph] using hh
    · intro hp
      exact ⟨_,hp⟩
  rw [he]
  apply isClosed_iInter
  intro n
  have h₁ : Continuous (fun p : BasedRay D × BasedRay D => p.2.val n) :=
    (continuous_apply n).comp (continuous_subtype_val.comp continuous_snd)
  have h₂ : Continuous (fun p : BasedRay D × BasedRay D => g*p.1.val n) :=
    (continuous_of_discreteTopology : Continuous (fun x : G => g*x)).comp
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst))
  exact (isClosed_discrete {k : ℕ | k ≤ 3*D.graph.dist 1 g + 4*δ}).preimage
    ((continuous_of_discreteTopology : Continuous (fun p : G × G => D.graph.dist p.1 p.2)).comp
      (h₁.prodMk h₂))

lemma boundaryTranslate_graph_closed (g : G) :
    IsClosed {p : Boundary D × Boundary D | boundaryTranslate D hthin g p.1 = p.2} := by
  let _ : T2Space (Boundary D) := boundary_t2Space D hthin
  let _ : T2Space (Quotient (raySetoid D)) := boundary_t2Space D hthin
  let _ : T2Space (Quotient (inferInstance : Setoid (BasedRay D))) := boundary_t2Space D hthin
  have he : {p : Boundary D × Boundary D | boundaryTranslate D hthin g p.1 = p.2} =
      Prod.map (Quotient.mk' : BasedRay D → Boundary D) Quotient.mk' ''
      {p : BasedRay D × BasedRay D | Asymptotic D p.2.val (fun n => g*p.1.val n)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨r,hr⟩ := Quotient.mk'_surjective p.1
      obtain ⟨s,hs⟩ := Quotient.mk'_surjective p.2
      have hq : (raySetoid D).r (translateRay D hthin g r) s := by
        apply Quotient.exact
        change boundaryTranslate D hthin g (Quotient.mk' r) = Quotient.mk' s
        rw [hr, hs]
        exact hp
      refine ⟨(r,s),?_,Prod.ext hr hs⟩
      exact Asymptotic.trans D (Asymptotic.symm D hq) (translateRay_spec D hthin g r)
    · rintro ⟨⟨r,s⟩,hrs,rfl⟩
      exact Quotient.sound (Asymptotic.trans D (translateRay_spec D hthin g r)
        (Asymptotic.symm D hrs))
  rw [he]
  exact ((translated_relation_closed D hthin g).isCompact.image
    (continuous_quotient_mk'.prodMap continuous_quotient_mk')).isClosed

lemma boundaryTranslate_continuous (g : G) : Continuous (boundaryTranslate D hthin g) := by
  apply continuous_iff_isClosed.mpr
  intro F hF
  have he : boundaryTranslate D hthin g ⁻¹' F =
      Prod.fst '' ({p : Boundary D × Boundary D | boundaryTranslate D hthin g p.1 = p.2} ∩
        (Set.univ ×ˢ F)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x,boundaryTranslate D hthin g x),⟨rfl,trivial,hx⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,⟨hxy,_,hy⟩,rfl⟩
      change boundaryTranslate D hthin g x ∈ F
      change boundaryTranslate D hthin g x = y at hxy
      rwa [hxy]
  rw [he]
  exact isClosedMap_fst_of_compactSpace _
    ((boundaryTranslate_graph_closed D hthin g).inter (isClosed_univ.prod hF))

def boundaryHomeomorph (g : G) : Boundary D ≃ₜ Boundary D where
  toFun := boundaryTranslate D hthin g
  invFun := boundaryTranslate D hthin g⁻¹
  left_inv x := by
    rw [← boundaryTranslate_mul, inv_mul_cancel, boundaryTranslate_one]
  right_inv x := by
    rw [← boundaryTranslate_mul, mul_inv_cancel, boundaryTranslate_one]
  continuous_toFun := boundaryTranslate_continuous D hthin g
  continuous_invFun := boundaryTranslate_continuous D hthin g⁻¹

def boundaryAction : G →* (Boundary D ≃ₜ Boundary D) where
  toFun := boundaryHomeomorph D hthin
  map_one' := by
    ext x
    exact boundaryTranslate_one D hthin x
  map_mul' g h := by
    ext x
    exact boundaryTranslate_mul D hthin g h x

end CannonRelease
namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def product2 (o x y : V) : ℕ := G.dist o x + G.dist o y - G.dist x y

lemma product2_add_dist (hG : G.Connected) (o x y : V) :
    product2 (G := G) o x y + G.dist x y = G.dist o x + G.dist o y := by
  apply Nat.sub_add_cancel
  have := @Connected.dist_triangle _ G x o y hG
  rwa [SimpleGraph.dist_comm (u := x) (v := o)] at this

lemma product2_le_twice_left (hG : G.Connected) (o x y : V) :
    product2 (G := G) o x y ≤ 2*G.dist o x := by
  have h := product2_add_dist hG o x y
  have h' := @Connected.dist_triangle _ G o x y hG
  omega

lemma product2_comm (o x y : V) : product2 (G := G) o x y = product2 (G := G) o y x := by
  simp only [product2, SimpleGraph.dist_comm (u := x) (v := y), Nat.add_comm]

lemma product2_le_twice_right (hG : G.Connected) (o x y : V) :
    product2 (G := G) o x y ≤ 2*G.dist o y := by
  rw [product2_comm]
  exact product2_le_twice_left hG o y x

theorem product2_hyperbolic (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (o x y z : V) :
    min (product2 (G := G) o x y) (product2 (G := G) o y z) ≤
      product2 (G := G) o x z + 8*δ+6 := by
  let m := min (product2 (G := G) o x y) (product2 (G := G) o y z)
  by_cases hm : m ≤ 2*δ+2
  · change m ≤ _
    omega
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist o x
  obtain ⟨q,hq⟩ := hG.exists_walk_length_eq_dist o y
  obtain ⟨r,hr⟩ := hG.exists_walk_length_eq_dist o z
  let k := m/2-δ-1
  have hm₁ : m ≤ product2 (G := G) o x y := min_le_left _ _
  have hm₂ : m ≤ product2 (G := G) o y z := min_le_right _ _
  have hk : 2*k+2*δ < m := by dsimp [k]; omega
  have hkp : k ≤ p.length := by
    have := product2_le_twice_left hG o x y
    dsimp [k]; omega
  have hkq : k ≤ q.length := by
    have := product2_le_twice_right hG o x y
    dsimp [k]; omega
  have hkr : k ≤ r.length := by
    have := product2_le_twice_right hG o y z
    dsimp [k]; omega
  have hxy := product2_add_dist hG o x y
  have hyz := product2_add_dist hG o y z
  have h₁ := fellow_travel_below_product hG hthin p q hp hq hkp hkq (by omega)
  have h₂ := fellow_travel_below_product hG hthin q r hq hr hkq hkr (by omega)
  have hpx := getVert_end_dist hG p hp hkp
  have hrz := getVert_end_dist hG r hr hkr
  have h₃ := @Connected.dist_triangle _ G (p.getVert k) (q.getVert k) (r.getVert k) hG
  have h₄ := @Connected.dist_triangle _ G x (p.getVert k) (r.getVert k) hG
  have h₅ := @Connected.dist_triangle _ G x (r.getVert k) z hG
  rw [SimpleGraph.dist_comm (u := x) (v := p.getVert k)] at h₄
  have hxz := product2_add_dist hG o x z
  change m ≤ _
  dsimp [k] at *
  omega

lemma product2_ray_mono (hG : G.Connected) (r s : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j) (h₀ : r 0 = s 0) :
    Monotone (fun n => product2 (G := G) (r 0) (r n) (s n)) := by
  intro i j hij
  have h₁ := @Connected.dist_triangle _ G (r j) (r i) (s i) hG
  have h₂ := @Connected.dist_triangle _ G (r j) (s i) (s j) hG
  rw [hr] at h₁
  rw [hs] at h₂
  have hi := product2_add_dist hG (r 0) (r i) (s i)
  have hj := product2_add_dist hG (r 0) (r j) (s j)
  have hi₀ : G.dist (r 0) (s i) = i := by
    simpa only [h₀, Nat.dist_zero_left] using hs 0 i
  have hj₀ : G.dist (r 0) (s j) = j := by
    simpa only [h₀, Nat.dist_zero_left] using hs 0 j
  rw [hr, hi₀] at hi
  rw [hr, hj₀] at hj
  simp only [Nat.dist_zero_left, Nat.dist_eq_sub_of_le hij,
    Nat.dist_eq_sub_of_le_right hij] at *
  omega

end CannonGraph

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

abbrev Ray (G : SimpleGraph V) (o : V) :=
  {r : ℕ → V // r 0 = o ∧ ∀ i j, G.dist (r i) (r j) = Nat.dist i j}

noncomputable def decay (ε : ℝ) (r s : Ray G o) (n : ℕ) : ℝ≥0 :=
  ⟨Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val n) (s.val n))), (Real.exp_pos _).le⟩

noncomputable def preDist (ε : ℝ) (r s : Ray G o) : ℝ≥0 := ⨅ n : ℕ, decay ε r s n

lemma preDist_le_decay (ε : ℝ) (r s : Ray G o) (n : ℕ) :
    preDist ε r s ≤ decay ε r s n := ciInf_le (OrderBot.bddBelow _) n

lemma decay_comm (ε : ℝ) (r s : Ray G o) (n : ℕ) : decay ε r s n = decay ε s r n := by
  apply NNReal.coe_injective
  change Real.exp _ = Real.exp _
  rw [CannonGraph.product2_comm (o := o) (x := r.val n) (y := s.val n)]

lemma preDist_comm (ε : ℝ) (r s : Ray G o) : preDist ε r s = preDist ε s r := by
  simp only [preDist, decay_comm ε r s]

lemma decay_antitone (hG : G.Connected) {ε : ℝ} (hε : 0 ≤ ε) (r s : Ray G o) :
    Antitone (decay ε r s) := by
  intro i j hij
  change Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val j) (s.val j))) ≤
    Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val i) (s.val i)))
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hε)
  have h := CannonGraph.product2_ray_mono hG r.val s.val r.property.2 s.property.2
    (r.property.1.trans s.property.1.symm) hij
  rw [r.property.1] at h
  exact_mod_cast h

lemma product2_self (r : Ray G o) (n : ℕ) :
    CannonGraph.product2 (G := G) o (r.val n) (r.val n) = 2*n := by
  have hr := r.property.2 0 n
  rw [r.property.1] at hr
  simp only [CannonGraph.product2, SimpleGraph.dist_self, Nat.sub_zero, hr, Nat.dist_zero_left]
  omega

lemma preDist_self {ε : ℝ} (hε : 0 < ε) (r : Ray G o) : preDist ε r r = 0 := by
  apply NNReal.coe_injective
  let f : ℕ → ℝ := fun n => Real.exp (-(2*ε) * (n : ℝ))
  have ht : Tendsto f atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop (by positivity : 0 < 2*ε)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hb : ∀ n, (preDist ε r r : ℝ) ≤ f n := by
    intro n
    have h := preDist_le_decay ε r r n
    change (preDist ε r r : ℝ) ≤ Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val n) (r.val n))) at h
    rw [product2_self, Nat.cast_mul, Nat.cast_ofNat] at h
    simpa only [f, neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using h
  have hh : (preDist ε r r : ℝ) ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hb)
  exact le_antisymm hh (NNReal.coe_nonneg _)

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma exp_neg_mul_min {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    Real.exp (-ε * min a b) = max (Real.exp (-ε*a)) (Real.exp (-ε*b)) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hε))
  · rw [min_eq_right h, max_eq_right]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hε))

lemma product2_four (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    (o x₁ x₂ x₃ x₄ : V) :
    min (CannonGraph.product2 (G := G) o x₁ x₂)
      (min (CannonGraph.product2 (G := G) o x₂ x₃) (CannonGraph.product2 (G := G) o x₃ x₄)) ≤
      CannonGraph.product2 (G := G) o x₁ x₄ + 2*(8*δ+6) := by
  have h₁ := CannonGraph.product2_hyperbolic hG hthin o x₁ x₂ x₄
  have h₂ := CannonGraph.product2_hyperbolic hG hthin o x₂ x₃ x₄
  omega

lemma decay_four (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : Real.exp (ε * (2*(8*δ+6) : ℕ)) ≤ 2)
    (r₁ r₂ r₃ r₄ : Ray G o) (n : ℕ) :
    decay ε r₁ r₄ n ≤ 2 * max (decay ε r₁ r₂ n) (max (decay ε r₂ r₃ n) (decay ε r₃ r₄ n)) := by
  let p₁₂ : ℝ := CannonGraph.product2 (G := G) o (r₁.val n) (r₂.val n)
  let p₂₃ : ℝ := CannonGraph.product2 (G := G) o (r₂.val n) (r₃.val n)
  let p₃₄ : ℝ := CannonGraph.product2 (G := G) o (r₃.val n) (r₄.val n)
  let p₁₄ : ℝ := CannonGraph.product2 (G := G) o (r₁.val n) (r₄.val n)
  have hp : min p₁₂ (min p₂₃ p₃₄) ≤ p₁₄ + (2*(8*δ+6) : ℕ) := by
    dsimp [p₁₂, p₂₃, p₃₄, p₁₄]
    exact_mod_cast product2_four hG hthin o (r₁.val n) (r₂.val n) (r₃.val n) (r₄.val n)
  have hh : -ε*p₁₄ ≤ ε*(2*(8*δ+6) : ℕ) + -ε * min p₁₂ (min p₂₃ p₃₄) := by
    nlinarith
  have hh' := Real.exp_le_exp.mpr hh
  rw [Real.exp_add, exp_neg_mul_min hε, exp_neg_mul_min hε] at hh'
  exact hh'.trans (mul_le_mul_of_nonneg_right hsmall (by positivity))

lemma tendsto_decay (hG : G.Connected) {ε : ℝ} (hε : 0 ≤ ε) (r s : Ray G o) :
    Tendsto (decay ε r s) atTop (𝓝 (preDist ε r s)) :=
  tendsto_atTop_ciInf (decay_antitone hG hε r s) (OrderBot.bddBelow _)

lemma preDist_four (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : Real.exp (ε * (2*(8*δ+6) : ℕ)) ≤ 2)
    (r₁ r₂ r₃ r₄ : Ray G o) :
    preDist ε r₁ r₄ ≤ 2 * max (preDist ε r₁ r₂) (max (preDist ε r₂ r₃) (preDist ε r₃ r₄)) := by
  apply le_of_tendsto_of_tendsto (tendsto_decay hG hε r₁ r₄)
    (((tendsto_decay hG hε r₁ r₂).max ((tendsto_decay hG hε r₂ r₃).max
      (tendsto_decay hG hε r₃ r₄))).const_mul 2)
  exact Filter.Eventually.of_forall (decay_four hG hthin hε hsmall r₁ r₂ r₃ r₄)

noncomputable def visualExponent (δ : ℕ) : ℝ := Real.log 2 / (2*(8*δ+6) : ℕ)

lemma visualExponent_pos (δ : ℕ) : 0 < visualExponent δ := by
  unfold visualExponent
  apply div_pos (Real.log_pos (by norm_num))
  positivity

lemma visualExponent_small (δ : ℕ) : Real.exp (visualExponent δ * (2*(8*δ+6) : ℕ)) ≤ 2 := by
  have h : ((2*(8*δ+6) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [visualExponent, div_mul_cancel₀ _ h, Real.exp_log (by norm_num : (0:ℝ)<2)]

@[instance_reducible]
noncomputable def rayPseudoMetric (δ : ℕ) : PseudoMetricSpace (Ray G o) :=
  PseudoMetricSpace.ofPreNNDist (preDist (visualExponent δ))
    (preDist_self (visualExponent_pos δ)) (preDist_comm (visualExponent δ))

lemma visual_distance_le (δ : ℕ) (r s : Ray G o) :
    @dist _ (rayPseudoMetric (G := G) (o := o) δ).toDist r s ≤ preDist (visualExponent δ) r s :=
  PseudoMetricSpace.dist_ofPreNNDist_le _ _ _ _ _

lemma preDist_le_twice_visual_distance (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    (r s : Ray G o) :
    (preDist (visualExponent δ) r s : ℝ) ≤ 2 * @dist _ (rayPseudoMetric δ).toDist r s :=
  PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _
    (preDist_four hG hthin (visualExponent_pos δ).le (visualExponent_small δ)) _ _

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology CannonGraph
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_ray_sum (hG : G.Connected) (r s : Ray G o) (n : ℕ) :
    product2 (G := G) o (r.val n) (s.val n) + G.dist (r.val n) (s.val n) = 2*n := by
  have hr := r.property.2 0 n
  have hs := s.property.2 0 n
  rw [r.property.1, Nat.dist_zero_left] at hr
  rw [s.property.1, Nat.dist_zero_left] at hs
  simpa only [hr, hs, two_mul] using product2_add_dist hG o (r.val n) (s.val n)

lemma product2_le_of_separated (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : Ray G o) {k : ℕ} (hsep : 2*δ < G.dist (r.val k) (s.val k)) (n : ℕ) :
    product2 (G := G) o (r.val n) (s.val n) ≤ 2*k+2*δ := by
  by_cases hk : k ≤ n
  · by_contra hn
    let p := raySegment r.val r.property.2 n
    let q := (raySegment s.val s.property.2 n).copy
      (s.property.1.trans r.property.1.symm) rfl
    have hp : p.length = G.dist (r.val 0) (r.val n) := by
      simp [p, r.property.2, Nat.dist]
    have hq : q.length = G.dist (r.val 0) (s.val n) := by
      have h := s.property.2 0 n
      rw [s.property.1] at h
      simpa [q, r.property.1, Nat.dist] using h.symm
    have hkp : k ≤ p.length := by simpa [p] using hk
    have hkq : k ≤ q.length := by simpa [q] using hk
    have hsum := product2_ray_sum hG r s n
    have hnear := fellow_travel_below_product hG hthin p q hp hq hkp hkq (by
      rw [r.property.2, r.property.1]
      have hs := s.property.2 0 n
      rw [s.property.1, Nat.dist_zero_left] at hs
      rw [hs, Nat.dist_zero_left]
      omega)
    have hnear' : G.dist (r.val k) (s.val k) ≤ 2*δ := by
      simpa only [p, q, Walk.getVert_copy, raySegment_getVert _ _ hk] using hnear
    omega
  · have hp := product2_le_twice_left hG o (r.val n) (s.val n)
    have hr := r.property.2 0 n
    rw [r.property.1, Nat.dist_zero_left] at hr
    rw [hr] at hp
    omega

lemma preDist_pos_of_separated (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {ε : ℝ} (hε : 0 ≤ ε) (r s : Ray G o) {k : ℕ}
    (hsep : 2*δ < G.dist (r.val k) (s.val k)) : 0 < preDist ε r s := by
  let a : ℝ≥0 := ⟨Real.exp (-ε*(2*k+2*δ : ℕ)), (Real.exp_pos _).le⟩
  have ha : 0 < a := Real.exp_pos _
  refine ha.trans_le (le_ciInf fun n => ?_)
  change Real.exp _ ≤ Real.exp _
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hε)
  exact_mod_cast product2_le_of_separated hG hthin r s hsep n

lemma tendsto_exp_linear {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.exp (-(2*ε)*(n:ℝ))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
    (Filter.Tendsto.const_mul_atTop (by positivity : 0 < 2*ε)
      (tendsto_natCast_atTop_atTop (R := ℝ)))

lemma preDist_zero_of_bounded (hG : G.Connected) {ε : ℝ} (hε : 0 < ε)
    (r s : Ray G o) (hbounded : ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C) :
    preDist ε r s = 0 := by
  obtain ⟨C,hC⟩ := hbounded
  apply NNReal.coe_injective
  have hb : ∀ n : ℕ, (preDist ε r s : ℝ) ≤ Real.exp (ε*C) * Real.exp (-(2*ε)*(n:ℝ)) := by
    intro n
    have hp := product2_ray_sum hG r s n
    have hpn : (product2 (G := G) o (r.val n) (s.val n) : ℝ) + (C : ℝ) ≥ 2*(n:ℝ) := by
      exact_mod_cast (show 2*n ≤ product2 (G := G) o (r.val n) (s.val n)+C by have := hC n; omega)
    have hh : -ε*(product2 (G := G) o (r.val n) (s.val n) : ℝ) ≤ ε*C + -(2*ε)*(n:ℝ) := by
      nlinarith
    have hle : (preDist ε r s : ℝ) ≤ (decay ε r s n : ℝ) := preDist_le_decay ε r s n
    exact hle.trans (by
      change Real.exp _ ≤ _
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hh)
  have ht := Filter.Tendsto.const_mul (Real.exp (ε*C)) (tendsto_exp_linear hε)
  simp only [mul_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (Filter.Eventually.of_forall hb)) (NNReal.coe_nonneg _)

theorem preDist_zero_iff_bounded (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {ε : ℝ} (hε : 0 < ε) (r s : Ray G o) :
    preDist ε r s = 0 ↔ ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C := by
  constructor
  · intro h
    refine ⟨2*δ,fun n => ?_⟩
    by_contra hn
    have hp := preDist_pos_of_separated hG hthin hε.le r s (Nat.lt_of_not_ge hn)
    rw [h] at hp
    exact (lt_irrefl _ hp)
  · exact preDist_zero_of_bounded hG hε r s

theorem visual_distance_zero_iff_bounded (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : Ray G o) :
    @dist _ (rayPseudoMetric δ).toDist r s = 0 ↔
      ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C := by
  rw [← preDist_zero_iff_bounded hG hthin (visualExponent_pos δ) r s]
  constructor
  · intro h
    have hp := preDist_le_twice_visual_distance hG hthin r s
    rw [h, mul_zero] at hp
    exact NNReal.coe_eq_zero.mp (le_antisymm hp (NNReal.coe_nonneg _))
  · intro h
    have hp := visual_distance_le δ r s
    rw [h, NNReal.coe_zero] at hp
    let := rayPseudoMetric (G := G) (o := o) δ
    exact le_antisymm hp dist_nonneg

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology CannonGraph
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

def raySetoid (hG : G.Connected) (o : V) : Setoid (Ray G o) where
  r r s := ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C
  iseqv := by
    constructor
    · intro r
      exact ⟨0,fun n => by simp⟩
    · rintro r s ⟨C,hC⟩
      exact ⟨C,fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩
    · rintro r s t ⟨C,hC⟩ ⟨E,hE⟩
      exact ⟨C+E,fun n => (@Connected.dist_triangle _ G (r.val n) (s.val n) (t.val n) hG).trans
        (Nat.add_le_add (hC n) (hE n))⟩

def MetricBoundary (G : SimpleGraph V) (o : V) (hG : G.Connected) := ULift.{0} (Quotient (raySetoid hG o))

noncomputable def boundaryDist (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (x y : MetricBoundary G o hG) : ℝ :=
  Quotient.liftOn₂ x.down y.down (fun r s => @dist _ (rayPseudoMetric δ).toDist r s) (by
    intro r₁ s₁ r₂ s₂ hr hs
    let := rayPseudoMetric (G := G) (o := o) δ
    have hr₀ := (visual_distance_zero_iff_bounded hG hthin r₁ r₂).mpr hr
    have hs₀ := (visual_distance_zero_iff_bounded hG hthin s₁ s₂).mpr hs
    change dist r₁ s₁ = dist r₂ s₂
    rw [dist_comm r₁ s₁, PseudoMetricSpace.dist_eq_of_dist_zero s₁ hr₀,
      dist_comm s₁ r₂, PseudoMetricSpace.dist_eq_of_dist_zero r₂ hs₀])

@[instance_reducible]
noncomputable def boundaryMetricSpace (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ) :
    MetricSpace (MetricBoundary G o hG) where
  dist := boundaryDist hG hthin
  dist_self x := by
    obtain ⟨x⟩ := x
    induction x using Quotient.inductionOn with | h r =>
      exact @dist_self _ (rayPseudoMetric δ) r
  dist_comm x y := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    induction x,y using Quotient.inductionOn₂ with | h r s =>
      exact @dist_comm _ (rayPseudoMetric δ) r s
  dist_triangle x y z := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨z⟩ := z
    induction x,y,z using Quotient.inductionOn₃ with | h r s t =>
      exact @dist_triangle _ (rayPseudoMetric δ) r s t
  eq_of_dist_eq_zero := by
    intro x y h
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    induction x,y using Quotient.inductionOn₂ with | h r s =>
      exact congrArg ULift.up (Quotient.sound ((visual_distance_zero_iff_bounded hG hthin r s).mp h))

lemma boundary_dist_mk (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ) (r s : Ray G o) :
    @dist _ (boundaryMetricSpace hG hthin).toDist (ULift.up (Quotient.mk'' r)) (ULift.up (Quotient.mk'' s)) =
      @dist _ (rayPseudoMetric δ).toDist r s := rfl

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology CannonGraph
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma decay_of_agree (ε : ℝ) (r s : Ray G o) {n : ℕ} (h : r.val n = s.val n) :
    (decay ε r s n : ℝ) = Real.exp (-(2*ε)*(n:ℝ)) := by
  change Real.exp _ = _
  rw [← h, product2_self, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  ring

lemma continuous_boundary_mk [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ) :
    @Continuous (Ray G o) (MetricBoundary G o hG) inferInstance
      (boundaryMetricSpace (o := o) hG hthin).toUniformSpace.toTopologicalSpace (fun r => ULift.up (Quotient.mk'' r)) := by
  let := boundaryMetricSpace (o := o) hG hthin
  apply continuous_iff_continuousAt.mpr
  intro r
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_exp_linear (visualExponent_pos δ)).eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  have hc : Continuous (fun s : Ray G o => s.val n) :=
    (continuous_apply n).comp continuous_subtype_val
  have hopen : IsOpen {s : Ray G o | s.val n = r.val n} :=
    (isOpen_discrete {r.val n}).preimage hc
  filter_upwards [hopen.mem_nhds (show r.val n = r.val n from rfl)] with s hs
  change @dist _ (rayPseudoMetric δ).toDist s r < ε
  have hle : (preDist (visualExponent δ) s r : ℝ) ≤ (decay (visualExponent δ) s r n : ℝ) :=
    preDist_le_decay _ _ _ _
  exact ((visual_distance_le δ s r).trans hle).trans_lt ((decay_of_agree _ s r hs) ▸ hn)

noncomputable def quotientVisualHomeomorph [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite) {δ : ℕ} (hthin : Thin G δ) :
    @Homeomorph (Quotient (raySetoid hG o)) (MetricBoundary G o hG) inferInstance
      (boundaryMetricSpace (o := o) hG hthin).toUniformSpace.toTopologicalSpace := by
  let := boundaryMetricSpace (o := o) hG hthin
  let : CompactSpace (Ray G o) := isCompact_iff_compactSpace.mp (compact_ray_space hG hfin o)
  let e : Quotient (raySetoid hG o) ≃ MetricBoundary G o hG := Equiv.ulift.symm
  have hc : Continuous e := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_boundary_mk hG hthin
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

end CannonVisual

namespace CannonRelease
open CannonGraph CannonVisual

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

@[instance_reducible]
noncomputable def visualMetricSpace : MetricSpace (Boundary D) := by
  let _ : MetricSpace (CannonVisual.MetricBoundary D.graph 1 D.connected) :=
    CannonVisual.boundaryMetricSpace (o := (1:G)) D.connected hδ
  let e : Boundary D ≃ₜ CannonVisual.MetricBoundary D.graph 1 D.connected :=
    CannonVisual.quotientVisualHomeomorph D.connected
      (finite_cayley_neighbors D.generators) hδ
  exact e.isEmbedding.comapMetricSpace e

lemma visualMetric_dist_ray (r s : BasedRay D) :
    @dist _ (visualMetricSpace D hδ).toDist (Quotient.mk' r) (Quotient.mk' s) =
      @dist _ (CannonVisual.rayPseudoMetric δ).toDist r s := rfl

lemma visualMetric_comparison (r s : BasedRay D) :
    @dist _ (visualMetricSpace D hδ).toDist (Quotient.mk' r) (Quotient.mk' s) ≤
        (preDist (visualExponent δ) r s : ℝ) ∧
      (preDist (visualExponent δ) r s : ℝ) ≤
        2 * @dist _ (visualMetricSpace D hδ).toDist (Quotient.mk' r) (Quotient.mk' s) :=
  ⟨visual_distance_le δ r s, preDist_le_twice_visual_distance D.connected hδ r s⟩

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma translateRay_uniform (g : G) (r : BasedRay D) (n : ℕ) :
    D.graph.dist ((translateRay D ⟨δ,hδ⟩ g r).val n) (g*r.val n) ≤
      3*D.graph.dist 1 g+4*δ := by
  have h := asymptotic_rays_different_bases_uniform D.connected
    (finite_cayley_neighbors D.generators) hδ
    (translateRay D ⟨δ,hδ⟩ g r).val (fun n => g*r.val n)
    (translateRay D ⟨δ,hδ⟩ g r).property.2
    (fun i j => (D.dist_mul_left g _ _).trans (r.property.2 i j))
    (translateRay_spec D ⟨δ,hδ⟩ g r) n
  simpa only [(translateRay D ⟨δ,hδ⟩ g r).property.1, r.property.1, mul_one, CayleyData.graph] using h

lemma translated_product2_bound (g : G) (r s : BasedRay D) (n : ℕ) :
    product2 (G := D.graph) 1 (r.val n) (s.val n) ≤
      product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g r).val n)
        ((translateRay D ⟨δ,hδ⟩ g s).val n) + 2*(3*D.graph.dist 1 g+4*δ) := by
  let r' := translateRay D ⟨δ,hδ⟩ g r
  let s' := translateRay D ⟨δ,hδ⟩ g s
  have hp := product2_ray_sum D.connected r s n
  have hp' := product2_ray_sum D.connected r' s' n
  have ht₁ := @SimpleGraph.Connected.dist_triangle _ D.graph (r'.val n) (g*r.val n) (s'.val n) D.connected
  have ht₂ := @SimpleGraph.Connected.dist_triangle _ D.graph (g*r.val n) (g*s.val n) (s'.val n) D.connected
  rw [D.dist_mul_left g, SimpleGraph.dist_comm (u := g*s.val n) (v := s'.val n)] at ht₂
  have hr := translateRay_uniform D hδ g r n
  have hs := translateRay_uniform D hδ g s n
  change D.graph.dist (r'.val n) (g*r.val n) ≤ _ at hr
  change D.graph.dist (s'.val n) (g*s.val n) ≤ _ at hs
  change _ ≤ product2 (G := D.graph) 1 (r'.val n) (s'.val n) + _
  dsimp only [CayleyData.graph] at *
  omega

lemma translated_preDist_le (g : G) (r s : BasedRay D) :
    (preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g r)
      (translateRay D ⟨δ,hδ⟩ g s) : ℝ) ≤
    Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ)) *
      (preDist (visualExponent δ) r s : ℝ) := by
  let r' := translateRay D ⟨δ,hδ⟩ g r
  let s' := translateRay D ⟨δ,hδ⟩ g s
  apply le_of_tendsto_of_tendsto
    (NNReal.continuous_coe.tendsto _ |>.comp (tendsto_decay D.connected (visualExponent_pos δ).le r' s'))
    ((NNReal.continuous_coe.tendsto _ |>.comp
      (tendsto_decay D.connected (visualExponent_pos δ).le r s)).const_mul _)
  apply Filter.Eventually.of_forall
  intro n
  change Real.exp _ ≤ Real.exp _ * Real.exp _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : (product2 (G := D.graph) 1 (r.val n) (s.val n) : ℝ) ≤
      (product2 (G := D.graph) 1 (r'.val n) (s'.val n) : ℝ) +
        (2*(3*D.graph.dist 1 g+4*δ) : ℕ) := by
    exact_mod_cast translated_product2_bound D hδ g r s n
  have he := visualExponent_pos δ
  change -visualExponent δ * _ ≤ _ + -visualExponent δ * _
  dsimp only [CayleyData.graph] at *
  nlinarith

lemma boundaryTranslate_lipschitz_bound (g : G) (x y : Boundary D) :
    @dist _ (visualMetricSpace D hδ).toDist (boundaryTranslate D ⟨δ,hδ⟩ g x)
      (boundaryTranslate D ⟨δ,hδ⟩ g y) ≤
      (2*Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ))) *
        @dist _ (visualMetricSpace D hδ).toDist x y := by
  induction x,y using Quotient.inductionOn₂ with
  | h r s =>
    have h₁ := (visualMetric_comparison D hδ (translateRay D ⟨δ,hδ⟩ g r)
      (translateRay D ⟨δ,hδ⟩ g s)).1
    have h₂ := translated_preDist_le D hδ g r s
    have h₃ := (visualMetric_comparison D hδ r s).2
    have h₄ := mul_le_mul_of_nonneg_left h₃
      (Real.exp_pos (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ))).le
    exact (h₁.trans h₂).trans (h₄.trans_eq (by
      dsimp only [Quotient.mk', CayleyData.graph, Thin]
      ring))

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
