import Mathlib
import OAI.Geometry.Cannon.Boundary.ImageAwayPuncture
import OAI.Geometry.Cannon.PlaneTopology.Plane

namespace OAI

section
section
section
section
section
namespace CannonPaths
lemma expansion_image_small {R C s e d q : ℝ}
    (hR : 0<R) (hC : 0<C) (_hs : 0<s) (hsR : s ≤ R)
    (he : 0<e) (hq : 0≤q) (hd : d<(e/C)*s)
    (hexp : q*R*max R d ≤ C*R*d) : q<e := by
  have hc : q*max R d ≤ C*d := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hexp]
  have hm := mul_le_mul_of_nonneg_left (le_max_left R d) hq
  have hd' : C*d<e*s := by
    rw [div_mul_eq_mul_div] at hd
    have hh := (lt_div_iff₀ hC).mp hd
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsR he.le
  exact (mul_lt_mul_iff_right₀ hR).mp (by linarith)
end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths CannonRegularDisk Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

theorem boundary_controlled_regular_disks (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ c : ℝ, 0<c ∧ c≤1 ∧ ∀ (x : Boundary D) (s : ℝ), 0<s → s≤1 →
      ∃ U : Set (Boundary D), IsRegularDisk U ∧ ball x (c*s) ⊆ U ∧ closure U ⊆ ball x s := by
  let _ := visualMetricSpace D hδ
  dsimp only
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 1≤A := Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hAp : 0<A := zero_lt_one.trans_le hA
  obtain ⟨e,he,hdisks⟩ := uniform_regular_disk_neighborhoods φ
    (show 0<1/(2*(B*A)) by positivity)
  let c := min 1 (e/C)
  have hc : 0<c := lt_min zero_lt_one (div_pos he hC)
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro x s hs hsone
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs hsone
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
  obtain ⟨V,hV,hinner,houter⟩ := hdisks (f (Quotient.mk' r : Boundary D))
  have hcomm (z w : Boundary D) : boundaryDist D hδ z w = boundaryDist D hδ w z := dist_comm z w
  have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)=0 := dist_self _
  refine ⟨f ⁻¹' V,hV.preimage f,?_,?_⟩
  · intro y hy
    apply hinner
    have hy' : boundaryDist D hδ (Quotient.mk' r) y < c*s := by
      change boundaryDist D hδ y (Quotient.mk' r) < c*s at hy
      exact (hcomm (Quotient.mk' r) y).trans_lt hy
    have hy'' : boundaryDist D hδ (Quotient.mk' r) y < (e/C)*s :=
      hy'.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le)
    have hh := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).1
    change boundaryDist D hδ (f (Quotient.mk' r)) (f y)*
      max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r))*
      max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y) ≤
      C*visualScale δ k*boundaryDist D hδ (Quotient.mk' r) y at hh
    rw [hself,max_eq_left (visualScale_pos δ k).le] at hh
    have hsmall := expansion_image_small (visualScale_pos δ k) hC hs hk he dist_nonneg hy'' hh
    change boundaryDist D hδ (f y) (f (Quotient.mk' r)) < e
    rwa [hcomm]
  · intro y hy
    have hy' : f y ∈ closure V := by rwa [←f.preimage_closure] at hy
    have him : boundaryDist D hδ (f (Quotient.mk' r)) (f y)<1/(2*(B*A)) := by
      have hh := houter hy'
      change boundaryDist D hδ (f y) (f (Quotient.mk' r)) < 1/(2*(B*A)) at hh
      rwa [hcomm] at hh
    have hd : boundaryDist D hδ (Quotient.mk' r) y<s := by
      by_contra hn
      have hh := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).2
      change visualScale δ k*boundaryDist D hδ (Quotient.mk' r) y ≤
        B*(boundaryDist D hδ (f (Quotient.mk' r)) (f y)*
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r))*
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y)) at hh
      rw [hself,max_eq_left (visualScale_pos δ k).le] at hh
      have hfar := expansion_endpoint_clearance (visualScale_pos δ k) hB hA hs
        dist_nonneg (le_of_not_gt hn) hk' hh
      have hhalf : 1/(2*(B*A))<1/(B*A) := by
        apply one_div_lt_one_div_of_lt (mul_pos hB hAp)
        nlinarith [mul_pos hB hAp]
      exact (hfar.trans_lt him).not_ge hhalf.le
    change boundaryDist D hδ y (Quotient.mk' r) < s
    exact (hcomm y (Quotient.mk' r)).trans_lt hd

end CannonRelease

end
section
noncomputable section

noncomputable section
open Set Topology

noncomputable section

namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G)

variable (hthin : D.ThinTriangles)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) (hthin : D.ThinTriangles)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonMetric
open Set Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma compact_packing_bound {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, ∀ s : Finset X, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → e ≤ dist x y) → s.card ≤ N := by
  classical
  obtain ⟨t,_,ht,hcover⟩ := (isCompact_univ : IsCompact (univ : Set X)).finite_cover_balls (show 0 < e/3 by positivity)
  let T := ht.toFinset
  have hT (x : X) : ∃ y ∈ T, dist x y < e/3 := by
    have := hcover (mem_univ x)
    obtain ⟨y,hy⟩ := mem_iUnion.mp this
    obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
    exact ⟨y,ht.mem_toFinset.mpr hyt,hxy⟩
  choose f hf hf' using hT
  refine ⟨T.card,fun s hs => ?_⟩
  let F : ↥s → ↥T := fun x => ⟨f x,hf x⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    by_contra hn
    have h := dist_triangle x.val (f x.val) y.val
    have hh : f x.val = f y.val := congrArg Subtype.val hxy
    rw [hh,dist_comm (f y.val) y.val] at h
    have h₁ := hf' x.val
    have h₂ := hf' y.val
    rw [hh] at h₁
    have h₃ := hs x.val x.property y.val y.property hn
    linarith
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hinj

end CannonMetric

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma finite_triple_translates (r s : BasedRay D) (hrs : ¬ (raySetoid D).r r s)
    {e : ℝ} (he : 0 < e) :
    {g : G | ∃ x y z : Boundary D,
      e ≤ boundaryDist D hδ x y ∧ e ≤ boundaryDist D hδ x z ∧ e ≤ boundaryDist D hδ y z ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g z) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z)}.Finite := by
  obtain ⟨N,hN⟩ := proper_triple_word_bound D hδ r s hrs he
  have hfin := finite_graph_ball D.connected (finite_cayley_neighbors D.generators) 1 N
  apply (hfin.preimage (f := fun g : G => g⁻¹) inv_injective.injOn).subset
  rintro g ⟨x,y,z,hxy,hxz,hyz,hgxy,hgxz,hgyz⟩
  exact hN g x y z hxy hxz hyz hgxy hgxz hgyz

lemma visual_ball_expansion (r : BasedRay D) (k : ℕ) (y z : Boundary D)
    (hy : boundaryDist D hδ (Quotient.mk' r) y ≤ visualScale δ k)
    (hz : boundaryDist D hδ (Quotient.mk' r) z ≤ visualScale δ k) :
    let E := boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ y)
      (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ z)
    E*visualScale δ k ≤ (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))*boundaryDist D hδ y z ∧
      boundaryDist D hδ y z ≤ (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*E*visualScale δ k := by
  have hh := visual_expansion_ray D hδ r k y z
  change _ ∧ _ at hh
  change _ ∧ _
  have hR := visualScale_pos δ k
  rw [max_eq_left hy,max_eq_left hz] at hh
  constructor
  · apply (mul_le_mul_iff_left₀ hR).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.1
  · apply (mul_le_mul_iff_right₀ hR).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.2

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

theorem relative_packing_bound {q : ℝ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (x : Boundary D) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ s : Finset (Boundary D),
      (∀ y ∈ s, boundaryDist D hδ x y ≤ r) →
      (∀ y ∈ s, ∀ z ∈ s, y ≠ z → q*r ≤ boundaryDist D hδ y z) → s.card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  let L := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 0 < A := Real.exp_pos _
  have he : 0 < q/(L*A) := div_pos hq (mul_pos hL hA)
  obtain ⟨N,hN⟩ := CannonMetric.compact_packing_bound (X := Boundary D) he
  refine ⟨N,fun x t ht ht₁ s hs hsep => ?_⟩
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ ht ht₁
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹
  have hinj : Function.Injective f := (boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹).injective
  have himage := hN (s.image f) (by
    intro y hy z hz hyz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have huv : u ≠ v := fun heq => hyz (congrArg f heq)
    have hh := (visual_ball_expansion D hδ r k u v ((hs u hu).trans hk) ((hs v hv).trans hk)).2
    change boundaryDist D hδ u v ≤ L*boundaryDist D hδ (f u) (f v)*visualScale δ k at hh
    have hn : 0 ≤ boundaryDist D hδ (f u) (f v) := dist_nonneg
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hk' (mul_nonneg hL.le hn))
    have hh'' := hsep u hu v hv huv
    have hc : q ≤ L*boundaryDist D hδ (f u) (f v)*A := by
      apply (mul_le_mul_iff_left₀ ht).mp
      calc
        q*t ≤ boundaryDist D hδ u v := hh''
        _ ≤ L*boundaryDist D hδ (f u) (f v)*(A*t) := hh'
        _ = L*boundaryDist D hδ (f u) (f v)*A*t := by ring
    apply (div_le_iff₀ (mul_pos hL hA)).mpr
    nlinarith)
  rwa [Finset.card_image_of_injective s hinj] at himage

end CannonRelease

namespace CannonGraph
open SimpleGraph

variable {M : Type*} [Group M]

noncomputable def wordBall (S : Finset M) : ℕ → Finset M := by
  classical
  exact fun n => Nat.rec {1} (fun _ t => t.biUnion (fun x => (insert 1 S).image (x*·))) n

lemma one_mem_wordBall (S : Finset M) (n : ℕ) : 1 ∈ wordBall S n := by
  classical
  induction n with
  | zero => simp [wordBall]
  | succ n ih =>
    simp only [wordBall] at *
    exact Finset.mem_biUnion.mpr ⟨1,ih,Finset.mem_image.mpr ⟨1,Finset.mem_insert_self _ _,one_mul 1⟩⟩

lemma wordBall_step (S : Finset M) {x y : M} {n : ℕ} (hx : x ∈ wordBall S n)
    (hy : y = 1 ∨ y ∈ S) : x*y ∈ wordBall S (n+1) := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hx,Finset.mem_image.mpr ⟨y,?_,rfl⟩⟩
  exact (Finset.mem_insert).mpr hy

lemma walk_end_mem_wordBall (S : Finset M) (hs : ∀ x ∈ S, x⁻¹ ∈ S)
    {x : M} (p : (mulCayley (S : Set M)).Walk 1 x) {n : ℕ} (hp : p.length ≤ n) :
    x ∈ wordBall S n := by
  classical
  induction n generalizing x with
  | zero =>
    have he := Walk.eq_of_length_eq_zero (p := p) (show p.length = 0 by omega)
    rw [← he]
    exact one_mem_wordBall S 0
  | succ n ih =>
    by_cases hz : p.length = 0
    · have he := Walk.eq_of_length_eq_zero hz
      rw [← he]
      exact one_mem_wordBall S (n+1)
    · have hp' : p.dropLast.length ≤ n := by rw [Walk.length_dropLast]; omega
      have hprev := ih p.dropLast hp'
      have hadj := p.adj_penultimate (by simpa only [← Walk.length_eq_zero_iff] using hz)
      obtain ⟨_,g,hg,he⟩ := (mulCayley_adj' (S : Set M) p.penultimate x).mp hadj
      rcases he with he | he
      · rw [← he]
        exact wordBall_step S hprev (Or.inr hg)
      · have he' : x = p.penultimate*g⁻¹ := by rw [he]; simp
        rw [he']
        exact wordBall_step S hprev (Or.inr (hs g hg))

lemma wordBall_card (S : Finset M) (n : ℕ) : (wordBall S n).card ≤ (S.card+1)^n := by
  classical
  induction n with
  | zero => simp [wordBall]
  | succ n ih =>
    calc
      _ ≤ ∑ x ∈ wordBall S n, ((insert 1 S).image (x*·)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ wordBall S n, (S.card+1) := Finset.sum_le_sum (fun x _ =>
        (Finset.card_image_le).trans (Finset.card_insert_le _ _))
      _ = (wordBall S n).card*(S.card+1) := by simp
      _ ≤ (S.card+1)^n*(S.card+1) := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma boundaryDist_le_of_prefix (r s : BasedRay D) {n : ℕ} (h : r.val n = s.val n) :
    boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) ≤ visualScale δ n := by
  apply (visualMetric_comparison D hδ r s).1.trans
  have hh : (preDist (visualExponent δ) r s : ℝ) ≤ (decay (visualExponent δ) r s n : ℝ) :=
    preDist_le_decay _ _ _ _
  apply hh.trans_eq
  rw [decay_of_agree _ r s h]
  unfold visualScale
  congr 1
  push_cast
  ring

lemma global_prefix_packing (n : ℕ) (s : Finset (Boundary D))
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → visualScale δ n < boundaryDist D hδ x y) :
    s.card ≤ (D.generators.card+1)^n := by
  classical
  choose r hr using (fun x : Boundary D => Quotient.exists_rep x)
  have hword (x : Boundary D) : (r x).val n ∈ wordBall D.generators n := by
    obtain ⟨p,hp⟩ := D.connected.exists_walk_length_eq_dist 1 ((r x).val n)
    apply walk_end_mem_wordBall D.generators D.symmetric p
    rw [hp]
    change D.graph.dist 1 ((r x).val n) ≤ n
    have hd := (r x).property.2 0 n
    dsimp only [CayleyData.graph] at hd ⊢
    simpa only [(r x).property.1,Nat.dist_zero_left] using hd.le
  let F : ↥s → ↥(wordBall D.generators n) := fun x => ⟨(r x.val).val n,hword x.val⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    by_contra hn
    have hh := boundaryDist_le_of_prefix D hδ (r x.val) (r y.val) (congrArg Subtype.val hxy)
    dsimp only [Quotient.mk',CayleyData.graph,Thin] at hh
    rw [hr x.val,hr y.val] at hh
    exact not_lt_of_ge hh (hs x.val x.property y.val y.property hn)
  have hcard := Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hcard
  exact hcard.trans (wordBall_card D.generators n)

end CannonRelease

namespace CannonReal
lemma power_counting_bound {A B : ℝ} (hA : 1 < A) (hB : 1 ≤ B) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∃ n : ℕ, (A⁻¹)^n < x ∧ B^n ≤ B*(1/x)^Q := by
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt B hA
  let Q := m+2
  have hApos : 0 < A := zero_lt_one.trans hA
  have hBQ : B ≤ A^Q := hm.le.trans (pow_le_pow_right₀ hA.le (by dsimp [Q]; omega))
  refine ⟨Q,by dsimp [Q]; omega,fun x hx hx₁ => ?_⟩
  obtain ⟨k,hk,hy⟩ := exists_nat_pow_near_of_lt_one hx hx₁ (inv_pos.mpr hApos)
    ((inv_lt_one₀ hApos).mpr hA)
  refine ⟨k+1,hk,?_⟩
  have hAk : 0 < A^k := pow_pos hApos k
  have hAx : A^k ≤ 1/x := by
    apply (le_div_iff₀ hx).mpr
    have hh := mul_le_mul_of_nonneg_right hy hAk.le
    rw [inv_pow,inv_mul_cancel₀ hAk.ne'] at hh
    simpa only [mul_comm] using hh
  have hpow : B^k ≤ (1/x)^Q := calc
    _ ≤ (A^Q)^k := pow_le_pow_left₀ (zero_le_one.trans hB) hBQ k
    _ = (A^k)^Q := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ (1/x)^Q := pow_le_pow_left₀ hAk.le hAx Q
  rw [pow_succ]
  calc
    B^k*B ≤ (1/x)^Q*B := mul_le_mul_of_nonneg_right hpow (zero_le_one.trans hB)
    _ = _ := mul_comm _ _
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma global_polynomial_packing :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ s : Finset (Boundary D),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → e ≤ boundaryDist D hδ x y) →
      (s.card : ℝ) ≤ (D.generators.card+1)*(1/e)^Q := by
  let A := Real.exp (2*visualExponent δ)
  have hA : 1 < A := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  obtain ⟨Q,hQ,hbound⟩ := CannonReal.power_counting_bound hA
    (show (1:ℝ) ≤ (D.generators.card:ℝ)+1 by have h : (0:ℝ) ≤ D.generators.card := Nat.cast_nonneg _; linarith)
  refine ⟨Q,hQ,fun e he he₁ s hs => ?_⟩
  obtain ⟨n,hn,hBn⟩ := hbound e he he₁
  have hn' : visualScale δ n < e := by
    rw [visualScale_eq_pow]
    have hex : Real.exp (-(2*visualExponent δ)) = A⁻¹ := Real.exp_neg _
    rwa [hex]
  have hh := global_prefix_packing D hδ n s (fun x hx y hy hxy => hn'.trans_le (hs x hx y hy hxy))
  have hh' : (s.card:ℝ) ≤ (D.generators.card+1:ℝ)^n := by exact_mod_cast hh
  exact hh'.trans hBn

end CannonRelease

end
end
end
end
end
end
end
end

end OAI
