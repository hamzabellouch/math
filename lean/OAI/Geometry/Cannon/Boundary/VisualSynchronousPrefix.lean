import Mathlib
import OAI.Geometry.Cannon.Boundary.WordBall

namespace OAI

section
section
section
noncomputable section
section
section
open Set Topology

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance visualSynchronousPrefixSetoid : Setoid (BasedRay D) := raySetoid D

theorem visual_synchronous_prefix (C : ℝ) (_hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ (r s : BasedRay D) (j : ℕ),
      boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) ≤ C*visualScale δ j →
      D.graph.dist (r.val j) (s.val j) ≤ B := by
  have hε := visualExponent_pos δ
  have hexp : Tendsto (fun n : ℕ => Real.exp (visualExponent δ*(n:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  obtain ⟨A,hA⟩ := (hexp.eventually (eventually_gt_atTop (2*C))).exists
  refine ⟨2*(A+(8*δ+6))+4*δ+2,fun r s j hj => ?_⟩
  have hc := (visualMetric_comparison D hδ r s).2
  have hp : (preDist (visualExponent δ) r s : ℝ) <
      Real.exp (visualExponent δ*(A:ℝ)-2*visualExponent δ*j) := by
    calc
      _ ≤ 2*boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) := hc
      _ ≤ 2*(C*visualScale δ j) := mul_le_mul_of_nonneg_left hj (by norm_num)
      _ < Real.exp (visualExponent δ*(A:ℝ))*visualScale δ j := by
        nlinarith only [mul_lt_mul_of_pos_right hA (visualScale_pos δ j)]
      _ = _ := by rw [visualScale,← Real.exp_add]; congr 1; push_cast; ring
  have hlim : Tendsto (fun n => (decay (visualExponent δ) r s n : ℝ)) atTop
      (𝓝 (preDist (visualExponent δ) r s : ℝ)) :=
    NNReal.continuous_coe.tendsto _ |>.comp
      (tendsto_decay D.connected hε.le r s)
  obtain ⟨n,hn,hdec⟩ := ((eventually_ge_atTop j).and (hlim.eventually_lt_const hp)).exists
  change Real.exp (-visualExponent δ*(product2 (G:=D.graph) 1 (r.val n) (s.val n):ℝ)) < _ at hdec
  have hprod : 2*j ≤ product2 (G:=D.graph) 1 (r.val n) (s.val n)+A := by
    have he := Real.exp_lt_exp.mp hdec
    have he' : (2*j:ℕ) ≤ product2 (G:=D.graph) 1 (r.val n) (s.val n)+A := by
      have hh : ((2*j:ℕ):ℝ) ≤ ((product2 (G:=D.graph) 1 (r.val n) (s.val n)+A:ℕ):ℝ) := by
        push_cast
        nlinarith only [he,hε]
      exact_mod_cast hh
    exact he'
  have hpref := (product2_prefix D.connected hδ r s hn).2
  have hr : D.graph.dist 1 (r.val j) = j := by
    simpa only [r.property.1,Nat.dist_zero_left] using r.property.2 0 j
  dsimp only [CayleyData.graph] at *
  have hv := vertex_close_to_ray D.connected hδ s (r.val j) n (A+(8*δ+6))
    (by simpa only [hr] using hn) (by rw [hr]; omega)
  simpa only [hr] using hv

theorem separated_ray_products {e : ℝ} (he : 0 < e) :
    ∃ C : ℕ, ∀ (r s : BasedRay D),
      e ≤ boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) →
      ∀ n, product2 (G:=D.graph) 1 (r.val n) (s.val n) ≤ C := by
  have hε := visualExponent_pos δ
  have ht : Tendsto (fun n : ℕ => Real.exp (-visualExponent δ*(n:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul,Function.comp_def] using tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  obtain ⟨C,hC⟩ := (ht.eventually_lt_const he).exists
  refine ⟨C,fun r s hsep n => ?_⟩
  have hc := (visualMetric_comparison D hδ r s).1
  have hd := preDist_le_decay (visualExponent δ) r s n
  have hd' : (preDist (visualExponent δ) r s : ℝ) ≤
      Real.exp (-visualExponent δ*(product2 (G:=D.graph) 1 (r.val n) (s.val n):ℝ)) := hd
  by_contra hn
  have hCN : (C:ℝ) ≤ product2 (G:=D.graph) 1 (r.val n) (s.val n) := by exact_mod_cast (lt_of_not_ge hn).le
  have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hCN (neg_nonpos.mpr hε.le))
  exact (not_lt_of_ge (hsep.trans (hc.trans hd'))) (hm.trans_lt hC)

theorem inverse_puncture_prefix {e : ℝ} (he : 0 < e) :
    ∃ B : ℕ, ∀ (r z : BasedRay D) (k : ℕ),
      e ≤ boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' z) →
      D.graph.dist (r.val k)⁻¹
        ((translateRay D ⟨δ,hδ⟩ (r.val k)⁻¹ z).val k) ≤ B := by
  obtain ⟨C,hC⟩ := separated_ray_products D hδ he
  refine ⟨2*(C+(8*δ+6))+4*δ+2,fun r z k hz => ?_⟩
  let g := (r.val k)⁻¹
  let p := translateRay D ⟨δ,hδ⟩ g z
  have hk : D.graph.dist 1 (r.val k) = k := by
    simpa only [r.property.1,Nat.dist_zero_left] using r.property.2 0 k
  have hg : D.graph.dist 1 g = k := by
    have hh := D.dist_mul_left g (r.val k) 1
    simpa [g,SimpleGraph.dist_comm,hk] using hh
  obtain ⟨n,hn,hbig⟩ := ((eventually_ge_atTop k).and
    (translated_mixed_product_large D hδ g z (2*D.graph.dist 1 g))).exists
  have hrepl := product2_replace_one D.connected hδ 1 g (g*z.val n) (p.val n) hbig
  have hpref := (product2_prefix D.connected hδ r z hn).1
  have hbound := hC r z hz n
  have hcomp := product2_complement D.connected 1 (r.val k) (z.val n)
  have hmul : product2 (G:=D.graph) 1 g (g*z.val n) =
      product2 (G:=D.graph) (r.val k) 1 (z.val n) := by
    have hh := product2_mul D g (r.val k) 1 (z.val n)
    simpa [g] using hh
  change product2 (G:=D.graph) (r.val k) 1 (z.val n) +
    product2 (G:=D.graph) 1 (r.val k) (z.val n) = 2*D.graph.dist 1 (r.val k) at hcomp
  rw [hk,← hmul] at hcomp
  dsimp only [CayleyData.graph] at *
  have hprod : 2*D.graph.dist 1 g ≤ product2 (G:=D.graph) 1 g (p.val n)+(C+(8*δ+6)) := by
    dsimp only [CayleyData.graph]
    rw [hg]
    omega
  have hh := vertex_close_to_ray D.connected hδ p g n (C+(8*δ+6)) (hg ▸ hn) hprod
  simpa only [hg] using hh

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance visualSynchronousGraphBallSetoid : Setoid (BasedRay D) := raySetoid D

local instance visualSynchronousGraphBallDecidable : ∀ p : Prop, Decidable p :=
  Classical.propDecidable

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma uniform_graph_ball_card (B : ℕ) :
    ∃ N : ℕ, ∀ (x : G) (S : Finset G),
      (∀ y ∈ S, D.graph.dist x y ≤ B) → S.card ≤ N := by
  classical
  let T := (finite_graph_ball D.connected (finite_cayley_neighbors D.generators) 1 B).toFinset
  refine ⟨T.card,fun x S hS => ?_⟩
  apply card_le_card_of_injOn (fun y => x⁻¹*y) ?_ (by intro a _ b _ hab; exact mul_left_cancel hab)
  intro y hy
  change x⁻¹*y ∈ (finite_graph_ball D.connected (finite_cayley_neighbors D.generators) 1 B).toFinset
  rw [Set.Finite.mem_toFinset]
  have hh := D.dist_mul_left x 1 (x⁻¹*y)
  simp only [mul_one,mul_inv_cancel_left] at hh
  change D.graph.dist 1 (x⁻¹*y) ≤ B
  rw [← hh]
  exact hS y hy

theorem vertex_assignment_multiplicity {H : ℝ} (hH : 0 < H) :
    ∃ N : ℕ, ∀ {ι : Type*} (S : Finset ι) (r : ι → BasedRay D) (k : ℕ),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*visualScale δ k ≤
        boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' (r j))) →
      ∀ v : G, (S.filter (fun i => (r i).val k = v)).card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  obtain ⟨N,hN⟩ := relative_packing_bound D hδ hH
  refine ⟨N,fun {ι} S r k hsep v => ?_⟩
  let T := S.filter (fun i => (r i).val k = v)
  by_cases hT : T.Nonempty
  · obtain ⟨i,hi⟩ := hT
    let x : ι → Boundary D := fun j => Quotient.mk' (r j)
    have hinj : Set.InjOn x (T : Set ι) := by
      intro j hj j' hj' heq
      by_contra hne
      have hh := hsep j (mem_filter.mp hj).1 j' (mem_filter.mp hj').1 hne
      change H*visualScale δ k ≤ dist (x j) (x j') at hh
      rw [heq,dist_self] at hh
      exact (not_le_of_gt (mul_pos hH (visualScale_pos δ k))) hh
    have hh := hN (x i) (visualScale δ k) (visualScale_pos δ k)
      (by rw [visualScale]; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (visualExponent_pos δ).le) (Nat.cast_nonneg _)) (T.image x) (by
        intro y hy
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
        exact boundaryDist_le_of_prefix D hδ (r i) (r j)
          ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)) (by
        intro y hy y' hy' hne
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
        obtain ⟨j',hj',rfl⟩ := mem_image.mp hy'
        exact hsep j (mem_filter.mp hj).1 j' (mem_filter.mp hj').1
          (fun he => hne (congrArg x he)))
    rwa [card_image_of_injOn hinj] at hh
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

theorem puncture_ball_multiplicity {e H C : ℝ} (he : 0 < e) (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ {ι : Type*} (S : Finset ι) (r : ι → BasedRay D) (z : BasedRay D) (k : ℕ),
      (∀ i ∈ S, e ≤ boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' z)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*visualScale δ k ≤
        boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' (r j))) →
      ∀ b : Boundary D, (S.filter (fun i => boundaryDist D hδ
        (boundaryTranslate D ⟨δ,hδ⟩ ((r i).val k)⁻¹ (Quotient.mk' z)) b ≤ C*visualScale δ k)).card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  obtain ⟨B,hB⟩ := inverse_puncture_prefix D hδ he
  obtain ⟨B',hB'⟩ := visual_synchronous_prefix D hδ (2*C) (by positivity)
  obtain ⟨Ng,hNg⟩ := uniform_graph_ball_card D (B+B')
  obtain ⟨Nv,hNv⟩ := vertex_assignment_multiplicity D hδ hH
  refine ⟨Nv*Ng,fun {ι} S r z k hsep hcent b => ?_⟩
  let p : ι → BasedRay D := fun i => translateRay D ⟨δ,hδ⟩ ((r i).val k)⁻¹ z
  let T := S.filter (fun i => boundaryDist D hδ (Quotient.mk' (p i)) b ≤ C*visualScale δ k)
  change T.card ≤ Nv*Ng
  by_cases hT : T.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hT
    have hnear (i : ι) (hi : i ∈ T) :
        D.graph.dist ((r i).val k)⁻¹ ((p i₀).val k) ≤ B+B' := by
      have h₁ := hB (r i) z k (hsep i (mem_filter.mp hi).1)
      have hpd : boundaryDist D hδ (Quotient.mk' (p i)) (Quotient.mk' (p i₀)) ≤
          (2*C)*visualScale δ k := by
        have hh := @dist_triangle (Boundary D) _ (Quotient.mk' (p i)) b (Quotient.mk' (p i₀))
        rw [@dist_comm (Boundary D) _ b (Quotient.mk' (p i₀))] at hh
        change boundaryDist D hδ (Quotient.mk' (p i)) (Quotient.mk' (p i₀)) ≤
          boundaryDist D hδ (Quotient.mk' (p i)) b + boundaryDist D hδ (Quotient.mk' (p i₀)) b at hh
        linarith only [hh,(mem_filter.mp hi).2,(mem_filter.mp hi₀).2]
      have h₂ := hB' (p i) (p i₀) k hpd
      have ht := @SimpleGraph.Connected.dist_triangle _ D.graph
        ((r i).val k)⁻¹ ((p i).val k) ((p i₀).val k) D.connected
      exact ht.trans (Nat.add_le_add h₁ h₂)
    have hcard := hNg ((p i₀).val k) (T.image (fun i => ((r i).val k)⁻¹)) (by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      rw [SimpleGraph.dist_comm]
      exact hnear i hi)
    have hfib : ∀ v ∈ T.image (fun i => ((r i).val k)⁻¹),
        (T.filter (fun i => ((r i).val k)⁻¹ = v)).card ≤ Nv := by
      intro v _
      have hh := hNv T r k (fun i hi j hj hij => hcent i (mem_filter.mp hi).1
        j (mem_filter.mp hj).1 hij) v⁻¹
      simpa only [inv_eq_iff_eq_inv] using hh
    exact (card_le_mul_card_image T Nv hfib).trans (Nat.mul_le_mul_left Nv hcard)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

end CannonRelease

namespace CannonGraph

open SimpleGraph CannonVisual

variable {V : Type*} {Γ : SimpleGraph V} {o : V}

lemma prefix_of_near_ray (hΓ : Γ.Connected) {δ : ℕ} (hδ : Thin Γ δ)
    (p : Ray Γ o) (v w : V) (k l B : ℕ) (hl : l ≤ k)
    (_hv : Γ.dist o v = k) (hw : Γ.dist o w = l)
    (hwv : Γ.dist w v = k-l) (hvp : Γ.dist v (p.val k) ≤ B) :
    Γ.dist w (p.val l) ≤ 2*B+4*δ+2 := by
  have hp : Γ.dist o (p.val k) = k := by
    simpa only [p.property.1,Nat.dist_zero_left] using p.property.2 0 k
  have ht := @Connected.dist_triangle _ Γ w v (p.val k) hΓ
  have hprod := product2_add_dist hΓ o w (p.val k)
  have hlarge : 2*Γ.dist o w ≤ product2 (G:=Γ) o w (p.val k)+B := by
    rw [hwv] at ht
    rw [hw,hp] at hprod
    rw [hw]
    omega
  have hh := vertex_close_to_ray hΓ hδ p w k B (by simpa only [hw] using hl) hlarge
  simpa only [hw] using hh

end CannonGraph

namespace CannonRelease

open CannonGraph CannonVisual Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance visualSynchronousInverseRaySetoid : Setoid (BasedRay D) := raySetoid D

local instance visualSynchronousInverseRayDecidable : ∀ p : Prop, Decidable p :=
  Classical.propDecidable

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma inverse_ray_prefix (r : BasedRay D) {k l : ℕ} (hl : l ≤ k) :
    D.graph.dist 1 ((r.val k)⁻¹*r.val (k-l)) = l ∧
    D.graph.dist ((r.val k)⁻¹*r.val (k-l)) (r.val k)⁻¹ = k-l := by
  have h₁ := D.dist_mul_left (r.val k) 1 ((r.val k)⁻¹*r.val (k-l))
  have h₂ := D.dist_mul_left (r.val k) ((r.val k)⁻¹*r.val (k-l)) (r.val k)⁻¹
  simp only [mul_one,mul_inv_cancel_left,mul_inv_cancel] at h₁ h₂
  have hkk := r.property.2 k (k-l)
  have hk₀ := r.property.2 (k-l) 0
  rw [r.property.1,Nat.dist_zero_right] at hk₀
  dsimp only [CayleyData.graph] at h₁ h₂ hkk hk₀ ⊢
  constructor
  · rw [← h₁,hkk,Nat.dist_eq_sub_of_le_right (Nat.sub_le _ _)]
    omega
  · rw [← h₂,hk₀]

theorem near_puncture_descendant_count {e H C : ℝ}
    (he : 0 < e) (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ {ι : Type*} (S : Finset ι) (r : ι → BasedRay D)
      (z a b : BasedRay D) (k l : ℕ), l ≤ k →
      (∀ i ∈ S, e ≤ boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' z)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*visualScale δ k ≤
        boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' (r j))) →
      (∀ i ∈ S, boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' a) ≤
        C*visualScale δ (k-l)) →
      (∀ i ∈ S, boundaryDist D hδ
        (boundaryTranslate D ⟨δ,hδ⟩ ((r i).val k)⁻¹ (Quotient.mk' z))
        (Quotient.mk' b) ≤ visualScale δ l) →
      S.card ≤ N := by
  classical
  obtain ⟨B,hB⟩ := inverse_puncture_prefix D hδ he
  obtain ⟨B₁,hB₁⟩ := visual_synchronous_prefix D hδ 1 (by norm_num)
  obtain ⟨B₂,hB₂⟩ := visual_synchronous_prefix D hδ C hC
  obtain ⟨N₁,hN₁⟩ := uniform_graph_ball_card D (2*B+4*δ+2+B₁)
  obtain ⟨N₂,hN₂⟩ := uniform_graph_ball_card D B₂
  obtain ⟨Nv,hNv⟩ := vertex_assignment_multiplicity D hδ hH
  refine ⟨Nv*(N₁*N₂),fun {ι} S r z a b k l hl hsep hcent hanc hpunc => ?_⟩
  let u : ι → G := fun i => (r i).val (k-l)
  let w : ι → G := fun i => ((r i).val k)⁻¹*u i
  let p : ι → BasedRay D := fun i => translateRay D ⟨δ,hδ⟩ ((r i).val k)⁻¹ z
  have hw (i : ι) (hi : i ∈ S) :
      D.graph.dist (w i) (b.val l) ≤ 2*B+4*δ+2+B₁ := by
    have hg : D.graph.dist 1 ((r i).val k)⁻¹ = k := by
      have hh := D.dist_mul_left ((r i).val k) 1 ((r i).val k)⁻¹
      have hk := (r i).property.2 k 0
      rw [(r i).property.1,Nat.dist_zero_right] at hk
      simpa only [mul_one,mul_inv_cancel,hk] using hh.symm
    have hpre := inverse_ray_prefix D (r i) hl
    have hnear := hB (r i) z k (hsep i hi)
    have hh := prefix_of_near_ray D.connected hδ (p i) ((r i).val k)⁻¹ (w i)
      k l B hl hg hpre.1 hpre.2 hnear
    have hpi := hpunc i hi
    have heq : boundaryTranslate D ⟨δ,hδ⟩ ((r i).val k)⁻¹ (Quotient.mk' z) =
        Quotient.mk' (p i) := rfl
    rw [heq] at hpi
    have hsync := hB₁ (p i) b l (by simpa only [one_mul] using hpi)
    exact (@SimpleGraph.Connected.dist_triangle _ D.graph (w i) ((p i).val l) (b.val l)
      D.connected).trans (Nat.add_le_add hh hsync)
  have hu (i : ι) (hi : i ∈ S) : D.graph.dist (u i) (a.val (k-l)) ≤ B₂ :=
    hB₂ (r i) a (k-l) (hanc i hi)
  have hwcard : (S.image w).card ≤ N₁ := hN₁ (b.val l) (S.image w) (by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    rw [SimpleGraph.dist_comm]
    exact hw i hi)
  have hucard : (S.image u).card ≤ N₂ := hN₂ (a.val (k-l)) (S.image u) (by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    rw [SimpleGraph.dist_comm]
    exact hu i hi)
  let f : ι → G × G := fun i => (w i,u i)
  have hfcard : (S.image f).card ≤ N₁*N₂ := by
    have hsub : S.image f ⊆ (S.image w) ×ˢ (S.image u) := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact mem_product.mpr ⟨mem_image.mpr ⟨i,hi,rfl⟩,mem_image.mpr ⟨i,hi,rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (by rw [card_product]; exact Nat.mul_le_mul hwcard hucard)
  have hfib : ∀ y ∈ S.image f, (S.filter (fun i => f i = y)).card ≤ Nv := by
    intro y _
    apply (Finset.card_le_card (show S.filter (fun i => f i = y) ⊆
      S.filter (fun i => (r i).val k = y.2*y.1⁻¹) from ?_)).trans (hNv S r k hcent _)
    intro i hi
    obtain ⟨hi,heq⟩ := mem_filter.mp hi
    have hw := congrArg Prod.fst heq
    have hu := congrArg Prod.snd heq
    change w i = y.1 at hw
    change u i = y.2 at hu
    refine mem_filter.mpr ⟨hi,?_⟩
    rw [← hw,← hu]
    simp only [w,mul_inv_rev,inv_inv,mul_inv_cancel_left]
  exact (card_le_mul_card_image S Nv hfib).trans (Nat.mul_le_mul_left Nv hfcard)

end CannonRelease

end

end
end
end
end
end

end OAI
