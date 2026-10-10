import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryHomeomorph

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
namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma product2_base_upper (hG : G.Connected) (o v x y : V) :
    product2 (G := G) o x y ≤ product2 (G := G) v x y + 2*G.dist o v := by
  have h₁ := product2_add_dist hG o x y
  have h₂ := product2_add_dist hG v x y
  have h₃ := @Connected.dist_triangle _ G o v x hG
  have h₄ := @Connected.dist_triangle _ G o v y hG
  omega

lemma product2_replace_endpoints (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (o a b a' b' : V)
    (ha : product2 (G := G) o a b + 2*(8*δ+6) < product2 (G := G) o a a')
    (hb : product2 (G := G) o a b + 2*(8*δ+6) < product2 (G := G) o b b') :
    product2 (G := G) o a b ≤ product2 (G := G) o a' b' + 2*(8*δ+6) ∧
    product2 (G := G) o a' b' ≤ product2 (G := G) o a b + 2*(8*δ+6) := by
  have h₁ := CannonVisual.product2_four hG hδ o a' a b b'
  have h₂ := CannonVisual.product2_four hG hδ o a a' b' b
  rw [product2_comm (o := o) (x := a') (y := a)] at h₁
  rw [product2_comm (o := o) (x := b') (y := b)] at h₂
  omega

lemma product2_base_cross (hG : G.Connected) (o v a b c d : V) :
    product2 (G := G) o a b + product2 (G := G) o c d +
      product2 (G := G) v a d + product2 (G := G) v b c =
    product2 (G := G) o a d + product2 (G := G) o b c +
      product2 (G := G) v a b + product2 (G := G) v c d := by
  have h₁ := product2_add_dist hG o a b
  have h₂ := product2_add_dist hG o c d
  have h₃ := product2_add_dist hG o a d
  have h₄ := product2_add_dist hG o b c
  have h₅ := product2_add_dist hG v a b
  have h₆ := product2_add_dist hG v c d
  have h₇ := product2_add_dist hG v a d
  have h₈ := product2_add_dist hG v b c
  omega

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma product2_mul (g o x y : G) :
    product2 (G := D.graph) (g*o) (g*x) (g*y) = product2 (G := D.graph) o x y := by
  simp only [product2, D.dist_mul_left]

omit [TopologicalSpace G] [DiscreteTopology G] in
include hδ in
lemma product2_ray_bounded {r s : BasedRay D} (h : ¬ (raySetoid D).r r s) :
    ∃ C : ℕ, ∀ n, product2 (G := D.graph) 1 (r.val n) (s.val n) ≤ C := by
  have hn : ∃ n, 2*δ < D.graph.dist (r.val n) (s.val n) := by
    by_contra hn
    push Not at hn
    exact h ⟨2*δ,hn⟩
  obtain ⟨k,hk⟩ := hn
  exact ⟨2*k+2*δ,product2_le_of_separated D.connected hδ r s hk⟩

lemma translated_mixed_product_large (g : G) (r : BasedRay D) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, C < product2 (G := D.graph) 1 (g*r.val n)
      ((translateRay D ⟨δ,hδ⟩ g r).val n) := by
  let r' := translateRay D ⟨δ,hδ⟩ g r
  filter_upwards [Filter.eventually_ge_atTop (C+4*D.graph.dist 1 g+4*δ+1)] with n hn
  have hr := translateRay_uniform D hδ g r n
  have hp := product2_add_dist D.connected 1 (g*r.val n) (r'.val n)
  have ht := @SimpleGraph.Connected.dist_triangle _ D.graph g 1 (g*r.val n) D.connected
  have hg : D.graph.dist g (g*r.val n) = n := by
    simpa only [mul_one, r.property.1, Nat.dist_zero_left] using
      (D.dist_mul_left g 1 (r.val n)).trans (by simpa only [r.property.1, Nat.dist_zero_left] using r.property.2 0 n)
  have hr' : D.graph.dist 1 (r'.val n) = n := by
    simpa only [r'.property.1, Nat.dist_zero_left] using r'.property.2 0 n
  rw [hg, SimpleGraph.dist_comm (u := g) (v := 1)] at ht
  dsimp only [CayleyData.graph] at hr' hp
  rw [hr', SimpleGraph.dist_comm (u := g*r.val n) (v := r'.val n)] at hp
  change D.graph.dist (r'.val n) (g*r.val n) ≤ _ at hr
  change C < product2 (G := D.graph) 1 (g*r.val n) (r'.val n)
  dsimp only [CayleyData.graph] at *
  omega

lemma translated_product_independent_error (g : G) (r s : BasedRay D)
    (h : ¬ (raySetoid D).r r s) :
    ∀ᶠ n : ℕ in atTop,
      product2 (G := D.graph) 1 (g*r.val n) (g*s.val n) ≤
        product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g r).val n)
          ((translateRay D ⟨δ,hδ⟩ g s).val n) + 2*(8*δ+6) ∧
      product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g r).val n)
          ((translateRay D ⟨δ,hδ⟩ g s).val n) ≤
        product2 (G := D.graph) 1 (g*r.val n) (g*s.val n) + 2*(8*δ+6) := by
  obtain ⟨C,hC⟩ := product2_ray_bounded D hδ h
  let B := C + 2*D.graph.dist 1 g + 2*(8*δ+6)
  filter_upwards [translated_mixed_product_large D hδ g r B,
    translated_mixed_product_large D hδ g s B] with n hr hs
  have hp := product2_base_upper D.connected 1 g (g*r.val n) (g*s.val n)
  have he : product2 (G := D.graph) g (g*r.val n) (g*s.val n) =
      product2 (G := D.graph) 1 (r.val n) (s.val n) := by
    simpa only [mul_one] using product2_mul D g 1 (r.val n) (s.val n)
  dsimp only [CayleyData.graph] at hp he
  rw [he] at hp
  have hbound := hC n
  dsimp only [CayleyData.graph] at hbound
  apply product2_replace_endpoints D.connected hδ
  · dsimp [B] at hr
    dsimp only [CayleyData.graph] at *
    omega
  · dsimp [B] at hs
    dsimp only [CayleyData.graph] at *
    omega

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma translated_product2_cross (g a b c d : G) :
    product2 (G := D.graph) 1 (g*a) (g*b) + product2 (G := D.graph) 1 (g*c) (g*d) +
      product2 (G := D.graph) 1 a d + product2 (G := D.graph) 1 b c =
    product2 (G := D.graph) 1 (g*a) (g*d) + product2 (G := D.graph) 1 (g*b) (g*c) +
      product2 (G := D.graph) 1 a b + product2 (G := D.graph) 1 c d := by
  have hm (x y : G) : product2 (G := D.graph) g (g*x) (g*y) = product2 (G := D.graph) 1 x y := by
    simpa only [mul_one] using product2_mul D g 1 x y
  have h := product2_base_cross D.connected 1 g (g*a) (g*b) (g*c) (g*d)
  dsimp only [CayleyData.graph] at h hm ⊢
  simpa only [hm] using h

lemma translated_preDist_crossratio (g : G) (a b c d : BasedRay D)
    (hab : ¬ (raySetoid D).r a b) (hcd : ¬ (raySetoid D).r c d)
    (had : ¬ (raySetoid D).r a d) (hbc : ¬ (raySetoid D).r b c) :
    (preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g a) (translateRay D ⟨δ,hδ⟩ g b) : ℝ) *
      preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g c) (translateRay D ⟨δ,hδ⟩ g d) *
      preDist (visualExponent δ) a d * preDist (visualExponent δ) b c ≤
    Real.exp (visualExponent δ * (8*(8*δ+6) : ℕ)) *
      ((preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g a) (translateRay D ⟨δ,hδ⟩ g d) : ℝ) *
      preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g b) (translateRay D ⟨δ,hδ⟩ g c) *
      preDist (visualExponent δ) a b * preDist (visualExponent δ) c d) := by
  let a' := translateRay D ⟨δ,hδ⟩ g a
  let b' := translateRay D ⟨δ,hδ⟩ g b
  let c' := translateRay D ⟨δ,hδ⟩ g c
  let d' := translateRay D ⟨δ,hδ⟩ g d
  have hlim (r s : BasedRay D) : Tendsto (fun n => (decay (visualExponent δ) r s n : ℝ)) atTop
      (𝓝 (preDist (visualExponent δ) r s : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_decay D.connected (visualExponent_pos δ).le r s)
  apply le_of_tendsto_of_tendsto
    ((((hlim a' b').mul (hlim c' d')).mul (hlim a d)).mul (hlim b c))
    (((((hlim a' d').mul (hlim b' c')).mul (hlim a b)).mul (hlim c d)).const_mul _)
  filter_upwards [translated_product_independent_error D hδ g a b hab,
    translated_product_independent_error D hδ g c d hcd,
    translated_product_independent_error D hδ g a d had,
    translated_product_independent_error D hδ g b c hbc] with n hab' hcd' had' hbc'
  have hident := translated_product2_cross D g (a.val n) (b.val n) (c.val n) (d.val n)
  have hsum : product2 (G := D.graph) 1 (a'.val n) (d'.val n) +
      product2 (G := D.graph) 1 (b'.val n) (c'.val n) +
      product2 (G := D.graph) 1 (a.val n) (b.val n) +
      product2 (G := D.graph) 1 (c.val n) (d.val n) ≤
    product2 (G := D.graph) 1 (a'.val n) (b'.val n) +
      product2 (G := D.graph) 1 (c'.val n) (d'.val n) +
      product2 (G := D.graph) 1 (a.val n) (d.val n) +
      product2 (G := D.graph) 1 (b.val n) (c.val n) + 8*(8*δ+6) := by
    dsimp only [a',b',c',d']
    omega
  have hsum' : (product2 (G := D.graph) 1 (a'.val n) (d'.val n) : ℝ) +
      product2 (G := D.graph) 1 (b'.val n) (c'.val n) +
      product2 (G := D.graph) 1 (a.val n) (b.val n) +
      product2 (G := D.graph) 1 (c.val n) (d.val n) ≤
    (product2 (G := D.graph) 1 (a'.val n) (b'.val n) : ℝ) +
      product2 (G := D.graph) 1 (c'.val n) (d'.val n) +
      product2 (G := D.graph) 1 (a.val n) (d.val n) +
      product2 (G := D.graph) 1 (b.val n) (c.val n) + (8*(8*δ+6) : ℕ) := by
    exact_mod_cast hsum
  change Real.exp _ * Real.exp _ * Real.exp _ * Real.exp _ ≤
    Real.exp _ * (Real.exp _ * Real.exp _ * Real.exp _ * Real.exp _)
  repeat rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := visualExponent_pos δ
  dsimp only [CayleyData.graph] at *
  nlinarith

end CannonRelease

namespace CannonReal
lemma mul_four_le {a b c d A B C D : ℝ} (ha : a ≤ A) (hb : b ≤ B)
    (hc : c ≤ C) (hd : d ≤ D) (hb₀ : 0 ≤ b) (hd₀ : 0 ≤ d)
    (hc₀ : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    a*b*c*d ≤ A*B*C*D := by
  have h₁ := mul_le_mul ha hb hb₀ hA
  have h₂ := mul_le_mul hc hd hd₀ hC
  simpa only [mul_assoc] using mul_le_mul h₁ h₂ (mul_nonneg hc₀ hd₀) (mul_nonneg hA hB)
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

theorem boundary_uniform_cross_bound (g : G) (x y z w : Boundary D)
    (hxy : x ≠ y) (hzw : z ≠ w) (hxw : x ≠ w) (hyz : y ≠ z) :
    let _ := visualMetricSpace D hδ
    (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g z) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) x w * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) y z ≤
    (16*Real.exp (visualExponent δ * (8*(8*δ+6):ℕ))) *
      ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) x y * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) z w) := by
  let _ := visualMetricSpace D hδ
  induction x,y using Quotient.inductionOn₂ with | h a b =>
    induction z,w using Quotient.inductionOn₂ with | h c d =>
      let a' := translateRay D ⟨δ,hδ⟩ g a
      let b' := translateRay D ⟨δ,hδ⟩ g b
      let c' := translateRay D ⟨δ,hδ⟩ g c
      let d' := translateRay D ⟨δ,hδ⟩ g d
      have hab : ¬ (raySetoid D).r a b := fun h => hxy (Quotient.sound h)
      have hcd : ¬ (raySetoid D).r c d := fun h => hzw (Quotient.sound h)
      have had : ¬ (raySetoid D).r a d := fun h => hxw (Quotient.sound h)
      have hbc : ¬ (raySetoid D).r b c := fun h => hyz (Quotient.sound h)
      have huv := translated_preDist_crossratio D hδ g a b c d hab hcd had hbc
      have hlow := CannonReal.mul_four_le
        (visualMetric_comparison D hδ a' b').1 (visualMetric_comparison D hδ c' d').1
        (visualMetric_comparison D hδ a d).1 (visualMetric_comparison D hδ b c).1
        dist_nonneg dist_nonneg dist_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
      have hupp := CannonReal.mul_four_le
        (visualMetric_comparison D hδ a' d').2 (visualMetric_comparison D hδ b' c').2
        (visualMetric_comparison D hδ a b).2 (visualMetric_comparison D hδ c d).2
        (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
        (mul_nonneg (by norm_num) dist_nonneg) (mul_nonneg (by norm_num) dist_nonneg)
        (mul_nonneg (by norm_num) dist_nonneg)
      have hfinal := (hlow.trans huv).trans (mul_le_mul_of_nonneg_left hupp
        (Real.exp_pos (visualExponent δ * (8*(8*δ+6):ℕ))).le)
      change (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' b' : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' c' : Boundary D) (Quotient.mk' d' : Boundary D) *
        (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' d : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' b : Boundary D) (Quotient.mk' c : Boundary D) ≤
        (16*Real.exp (visualExponent δ * (8*(8*δ+6):ℕ))) *
          ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' d' : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' b' : Boundary D) (Quotient.mk' c' : Boundary D) *
            (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' b : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' c : Boundary D) (Quotient.mk' d : Boundary D))
      exact hfinal.trans_eq (by ring)

end CannonRelease

namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_prefix (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (r s : CannonVisual.Ray G o) {k n : ℕ} (hkn : k ≤ n) :
    product2 (G := G) o (r.val k) (s.val n) ≤
      min (2*k) (product2 (G := G) o (r.val n) (s.val n)) ∧
    min (2*k) (product2 (G := G) o (r.val n) (s.val n)) ≤
      product2 (G := G) o (r.val k) (s.val n) + (8*δ+6) := by
  have hr (j : ℕ) : G.dist o (r.val j) = j := by
    simpa only [r.property.1, Nat.dist_zero_left] using r.property.2 0 j
  have hs (j : ℕ) : G.dist o (s.val j) = j := by
    simpa only [s.property.1, Nat.dist_zero_left] using s.property.2 0 j
  have h₁ := product2_add_dist hG o (r.val k) (s.val n)
  have h₂ := product2_add_dist hG o (r.val n) (s.val n)
  have ht := @Connected.dist_triangle _ G (r.val n) (r.val k) (s.val n) hG
  rw [r.property.2, Nat.dist_eq_sub_of_le_right hkn] at ht
  rw [hr, hs] at h₁ h₂
  have hup := product2_le_twice_left hG o (r.val k) (s.val n)
  rw [hr] at hup
  have hself : product2 (G := G) o (r.val k) (r.val n) = 2*k := by
    unfold product2
    rw [hr,hr,r.property.2,Nat.dist_eq_sub_of_le hkn]
    omega
  have hlow := product2_hyperbolic hG hδ o (r.val k) (r.val n) (s.val n)
  rw [hself] at hlow
  constructor <;> omega

lemma product2_base_change (hG : G.Connected) (o v y z : V) :
    product2 (G := G) v y z + product2 (G := G) o v y + product2 (G := G) o v z =
      product2 (G := G) o y z + 2*G.dist o v := by
  have h₁ := product2_add_dist hG v y z
  have h₂ := product2_add_dist hG o v y
  have h₃ := product2_add_dist hG o v z
  have h₄ := product2_add_dist hG o y z
  omega

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma expansion_product_sums (x y z : BasedRay D) (k : ℕ)
    (hyz : ¬ (raySetoid D).r y z) :
    let g := (x.val k)⁻¹
    ∀ᶠ n : ℕ in atTop,
      product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g y).val n)
        ((translateRay D ⟨δ,hδ⟩ g z).val n) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (y.val n)) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (z.val n)) ≤
          product2 (G := D.graph) 1 (y.val n) (z.val n) + 2*k + 4*(8*δ+6) ∧
      product2 (G := D.graph) 1 (y.val n) (z.val n) + 2*k ≤
        product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g y).val n)
          ((translateRay D ⟨δ,hδ⟩ g z).val n) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (y.val n)) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (z.val n)) + 2*(8*δ+6) := by
  let g := (x.val k)⁻¹
  filter_upwards [translated_product_independent_error D hδ g y z hyz,
    Filter.eventually_ge_atTop k] with n hn hkn
  have hy := product2_prefix D.connected hδ x y hkn
  have hz := product2_prefix D.connected hδ x z hkn
  have hid := product2_base_change D.connected 1 (x.val k) (y.val n) (z.val n)
  have hd : D.graph.dist 1 (x.val k) = k := by
    simpa only [x.property.1, Nat.dist_zero_left] using x.property.2 0 k
  have he : product2 (G := D.graph) 1 (g*y.val n) (g*z.val n) =
      product2 (G := D.graph) (x.val k) (y.val n) (z.val n) := by
    simpa only [g,inv_mul_cancel] using product2_mul D ((x.val k)⁻¹) (x.val k) (y.val n) (z.val n)
  dsimp only [CayleyData.graph] at *
  rw [hd] at hid
  rw [he] at hn
  dsimp only [g] at *
  constructor <;> omega

end CannonRelease

namespace CannonReal
lemma exp_neg_nat_min (ε : ℝ) (hε : 0 ≤ ε) (a b : ℕ) :
    Real.exp (-ε * (min a b : ℕ)) =
      max (Real.exp (-ε * (a : ℝ))) (Real.exp (-ε * (b : ℝ))) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_left]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hab) (neg_nonpos.mpr hε)
  · rw [min_eq_right hba, max_eq_right]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hba) (neg_nonpos.mpr hε)

lemma exp_expansion (ε : ℝ) (hε : 0 ≤ ε) (E A B C K k : ℕ)
    (h₁ : E + min (2*k) A + min (2*k) B ≤ C+2*k+4*K)
    (h₂ : C+2*k ≤ E+min (2*k) A+min (2*k) B+2*K) :
    Real.exp (-ε*(E:ℝ)) * max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(A:ℝ))) *
        max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(B:ℝ))) ≤
      Real.exp (ε*(2*K:ℕ)) * Real.exp (-ε*(2*k:ℕ)) * Real.exp (-ε*(C:ℝ)) ∧
    Real.exp (-ε*(2*k:ℕ)) * Real.exp (-ε*(C:ℝ)) ≤
      Real.exp (ε*(4*K:ℕ)) * (Real.exp (-ε*(E:ℝ)) *
        max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(A:ℝ))) *
        max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(B:ℝ)))) := by
  rw [← exp_neg_nat_min ε hε, ← exp_neg_nat_min ε hε]
  have h₁' : (E:ℝ) + (min (2*k) A : ℕ) + (min (2*k) B : ℕ) ≤
      (C:ℝ) + (2*k:ℕ) + (4*K:ℕ) := by exact_mod_cast h₁
  have h₂' : (C:ℝ)+(2*k:ℕ) ≤ (E:ℝ)+(min (2*k) A : ℕ)+(min (2*k) B : ℕ)+(2*K:ℕ) := by
    exact_mod_cast h₂
  constructor <;> repeat rw [← Real.exp_add]
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_exp.mpr
    nlinarith
end CannonReal

namespace CannonVisual
noncomputable def visualScale (δ k : ℕ) : ℝ := Real.exp (-visualExponent δ * (2*k:ℕ))
lemma visualScale_pos (δ k : ℕ) : 0 < visualScale δ k := Real.exp_pos _
end CannonVisual

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma preDist_expansion (x y z : BasedRay D) (k : ℕ)
    (hyz : ¬ (raySetoid D).r y z) :
    let g := (x.val k)⁻¹
    let R := visualScale δ k
    let E := (preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g y)
      (translateRay D ⟨δ,hδ⟩ g z) : ℝ)
    let A := max R (preDist (visualExponent δ) x y : ℝ)
    let B := max R (preDist (visualExponent δ) x z : ℝ)
    E*A*B ≤ Real.exp (visualExponent δ * (2*(8*δ+6):ℕ))*R*(preDist (visualExponent δ) y z : ℝ) ∧
    R*(preDist (visualExponent δ) y z : ℝ) ≤ Real.exp (visualExponent δ * (4*(8*δ+6):ℕ))*(E*A*B) := by
  let g := (x.val k)⁻¹
  let y' := translateRay D ⟨δ,hδ⟩ g y
  let z' := translateRay D ⟨δ,hδ⟩ g z
  have hlim (r s : BasedRay D) : Tendsto (fun n => (decay (visualExponent δ) r s n : ℝ)) atTop
      (𝓝 (preDist (visualExponent δ) r s : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_decay D.connected (visualExponent_pos δ).le r s)
  have he : ∀ᶠ n : ℕ in atTop,
      (decay (visualExponent δ) y' z' n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x y n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x z n : ℝ) ≤
      Real.exp (visualExponent δ * (2*(8*δ+6):ℕ))*visualScale δ k*(decay (visualExponent δ) y z n : ℝ) ∧
      visualScale δ k*(decay (visualExponent δ) y z n : ℝ) ≤
      Real.exp (visualExponent δ * (4*(8*δ+6):ℕ)) *
        ((decay (visualExponent δ) y' z' n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x y n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x z n : ℝ)) := by
    filter_upwards [expansion_product_sums D hδ x y z k hyz] with n hn
    exact CannonReal.exp_expansion (visualExponent δ) (visualExponent_pos δ).le _ _ _ _ _ _ hn.1 hn.2
  have hf := ((hlim y' z').mul ((tendsto_const_nhds (x := visualScale δ k)).max (hlim x y))).mul
    ((tendsto_const_nhds (x := visualScale δ k)).max (hlim x z))
  constructor
  · exact le_of_tendsto_of_tendsto hf ((hlim y z).const_mul _) (he.mono fun _ h => h.1)
  · exact le_of_tendsto_of_tendsto ((hlim y z).const_mul _) (hf.const_mul _) (he.mono fun _ h => h.2)

end CannonRelease

namespace CannonReal
lemma max_le_twice_max {R d p : ℝ} (hR : 0 ≤ R) (hp : p ≤ 2*d) :
    max R p ≤ 2*max R d := by
  apply max_le
  · have := le_max_left R d
    nlinarith
  · exact hp.trans (mul_le_mul_of_nonneg_left (le_max_right R d) (by norm_num))

lemma mul_three_le {a b c A B C : ℝ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    a*b*c ≤ A*B*C :=
  mul_le_mul (mul_le_mul ha hb hb₀ hA) hc hc₀ (mul_nonneg hA hB)
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

theorem visual_expansion_ray (r : BasedRay D) (k : ℕ) (y z : Boundary D) :
    let _ := visualMetricSpace D hδ
    let g := (r.val k)⁻¹
    let x : Boundary D := Quotient.mk' r
    let R := visualScale δ k
    let E := (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z)
    let A := max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) x y)
    let B := max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) x z)
    E*A*B ≤ (2*Real.exp (visualExponent δ * (2*(8*δ+6):ℕ)))*R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) y z ∧
      R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) y z ≤ (8*Real.exp (visualExponent δ * (4*(8*δ+6):ℕ)))*(E*A*B) := by
  let _ := visualMetricSpace D hδ
  by_cases hyz : y = z
  · subst z
    simp only [dist_self,zero_mul,mul_zero,le_refl,and_self]
  induction y,z using Quotient.inductionOn₂ with | h a b =>
    let g := (r.val k)⁻¹
    let a' := translateRay D ⟨δ,hδ⟩ g a
    let b' := translateRay D ⟨δ,hδ⟩ g b
    let R := visualScale δ k
    have hR : 0 ≤ R := (visualScale_pos δ k).le
    have hab : ¬ (raySetoid D).r a b := fun h => hyz (Quotient.sound h)
    have hh := preDist_expansion D hδ r a b k hab
    have hc (s t : BasedRay D) := visualMetric_comparison D hδ s t
    have hm (s : BasedRay D) : max R (preDist (visualExponent δ) r s : ℝ) ≤
        2*max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' s : Boundary D)) :=
      CannonReal.max_le_twice_max hR (hc r s).2
    have hn₁ : 0 ≤ max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' a : Boundary D)) := hR.trans (le_max_left _ _)
    have hn₂ : 0 ≤ max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' b : Boundary D)) := hR.trans (le_max_left _ _)
    have hp₁ : 0 ≤ max R (preDist (visualExponent δ) r a : ℝ) := hR.trans (le_max_left _ _)
    have hp₂ : 0 ≤ max R (preDist (visualExponent δ) r b : ℝ) := hR.trans (le_max_left _ _)
    have hlo := CannonReal.mul_three_le (hc a' b').1
      (max_le_max_left R (hc r a).1) (max_le_max_left R (hc r b).1)
      hn₁ hn₂ (NNReal.coe_nonneg _) hp₁
    have hup := CannonReal.mul_three_le (hc a' b').2 (hm a) (hm b)
      hp₁ hp₂ (mul_nonneg (by norm_num) dist_nonneg) (mul_nonneg (by norm_num) hn₁)
    change (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' b' : Boundary D) *
        max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' a : Boundary D)) * max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' b : Boundary D)) ≤
      (2*Real.exp (visualExponent δ * (2*(8*δ+6):ℕ)))*R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' b : Boundary D) ∧
      R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' b : Boundary D) ≤
        (8*Real.exp (visualExponent δ * (4*(8*δ+6):ℕ)))*
          ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' b' : Boundary D) *
            max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' a : Boundary D)) * max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' b : Boundary D)))
    constructor
    · have h := (hlo.trans hh.1).trans (mul_le_mul_of_nonneg_left (hc a b).2
        (mul_nonneg (Real.exp_pos _).le hR))
      exact h.trans_eq (by ring)
    · have h := (mul_le_mul_of_nonneg_left (hc a b).1 hR).trans hh.2
      exact (h.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)).trans_eq (by ring)

end CannonRelease

namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_replace_one (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (o v a b : V) (hab : 2*G.dist o v < product2 (G := G) o a b) :
    product2 (G := G) o v a ≤ product2 (G := G) o v b + (8*δ+6) ∧
    product2 (G := G) o v b ≤ product2 (G := G) o v a + (8*δ+6) := by
  have h₁ := product2_hyperbolic hG hδ o v a b
  have h₂ := product2_hyperbolic hG hδ o v b a
  rw [product2_comm (o := o) (x := b) (y := a)] at h₂
  have h₃ := product2_le_twice_left hG o v a
  have h₄ := product2_le_twice_left hG o v b
  constructor <;> omega

lemma product2_complement (hG : G.Connected) (o v a : V) :
    product2 (G := G) v o a + product2 (G := G) o v a = 2*G.dist o v := by
  have h₁ := product2_add_dist hG v o a
  have h₂ := product2_add_dist hG o v a
  rw [SimpleGraph.dist_comm (u := v) (v := o)] at h₁
  omega

lemma vertex_close_to_ray (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (s : CannonVisual.Ray G o) (v : V) (n C : ℕ)
    (hn : G.dist o v ≤ n)
    (hprod : 2*G.dist o v ≤ product2 (G := G) o v (s.val n) + C) :
    G.dist v (s.val (G.dist o v)) ≤ 2*C+4*δ+2 := by
  let w := G.dist o v
  have hs (i : ℕ) : G.dist o (s.val i) = i := by
    simpa only [s.property.1,Nat.dist_zero_left] using s.property.2 0 i
  by_cases hw : w ≤ C+δ+1
  · have h := @Connected.dist_triangle _ G v o (s.val w) hG
    rw [SimpleGraph.dist_comm (u := v) (v := o),hs] at h
    change G.dist v (s.val w) ≤ _
    dsimp [w] at *
    omega
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist o v
  let q : G.Walk o (s.val n) := (raySegment s.val s.property.2 n).copy s.property.1 rfl
  have hq : q.length = G.dist o (s.val n) := by simp only [q,Walk.length_copy,raySegment_length,hs]
  let m := w-(C+δ+1)
  have hm : m ≤ p.length := by dsimp [m,w]; omega
  have hm' : m ≤ q.length := by rw [hq,hs]; dsimp [m,w]; omega
  have had := product2_add_dist hG o v (s.val n)
  have hclose := fellow_travel_below_product hG hδ p q hp hq hm hm' (by dsimp [m,w] at *; omega)
  have hpm := getVert_end_dist hG p hp hm
  have hqm : q.getVert m = s.val m := by
    simp only [q,Walk.getVert_copy,raySegment_getVert s.val s.property.2 (show m ≤ n by dsimp [m,w]; omega)]
  rw [hqm] at hclose
  have h₁ := @Connected.dist_triangle _ G v (p.getVert m) (s.val m) hG
  have h₂ := @Connected.dist_triangle _ G v (s.val m) (s.val w) hG
  rw [SimpleGraph.dist_comm (u := v) (v := p.getVert m)] at h₁
  rw [s.property.2,Nat.dist_eq_sub_of_le (show m ≤ w by dsimp [m]; omega)] at h₂
  change G.dist v (s.val w) ≤ _
  dsimp [m,w] at *
  omega

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

include hδ in

theorem coarse_prefix_of_distinct_rays (r s : BasedRay D)
    (hrs : ¬ (raySetoid D).r r s) :
    ∃ B : ℕ, ∀ v : G, ∃ t : BasedRay D,
      D.graph.dist v (t.val (D.graph.dist 1 v)) ≤ B := by
  obtain ⟨C,hC⟩ := product2_ray_bounded D hδ hrs
  refine ⟨2*(C+2*(8*δ+6))+4*δ+2,?_⟩
  intro v
  let r' := translateRay D ⟨δ,hδ⟩ v r
  let s' := translateRay D ⟨δ,hδ⟩ v s
  have he := (translated_mixed_product_large D hδ v r (2*D.graph.dist 1 v)).and
    ((translated_mixed_product_large D hδ v s (2*D.graph.dist 1 v)).and
      (Filter.eventually_ge_atTop (D.graph.dist 1 v)))
  obtain ⟨n,hr,hs,hn⟩ := he.exists
  have hrb := product2_replace_one D.connected hδ 1 v (v*r.val n) (r'.val n) hr
  have hsb := product2_replace_one D.connected hδ 1 v (v*s.val n) (s'.val n) hs
  have hmin := product2_hyperbolic D.connected hδ v (v*r.val n) 1 (v*s.val n)
  have hp₁ := product2_complement D.connected 1 v (v*r.val n)
  have hp₂ := product2_complement D.connected 1 v (v*s.val n)
  have heq : product2 (G := D.graph) v (v*r.val n) (v*s.val n) =
      product2 (G := D.graph) 1 (r.val n) (s.val n) := by
    simpa only [mul_one] using product2_mul D v 1 (r.val n) (s.val n)
  have hb := hC n
  dsimp only [CayleyData.graph] at *
  rw [heq,product2_comm (o := v) (x := v*r.val n) (y := 1)] at hmin
  have hposs : 2*(SimpleGraph.mulCayley ↑D.generators).dist 1 v ≤
      product2 (G := D.graph) 1 v (r'.val n) + (C+2*(8*δ+6)) ∨
      2*(SimpleGraph.mulCayley ↑D.generators).dist 1 v ≤
      product2 (G := D.graph) 1 v (s'.val n) + (C+2*(8*δ+6)) := by
    dsimp only [CayleyData.graph]
    omega
  rcases hposs with hr' | hs'
  · exact ⟨r',vertex_close_to_ray D.connected hδ r' v n (C+2*(8*δ+6)) hn hr'⟩
  · exact ⟨s',vertex_close_to_ray D.connected hδ s' v n (C+2*(8*δ+6)) hn hs'⟩

end CannonRelease

namespace CannonVisual
lemma visualScale_eq_pow (δ k : ℕ) :
    visualScale δ k = (Real.exp (-(2*visualExponent δ)))^k := by
  rw [← Real.exp_nat_mul]
  unfold visualScale
  congr 1
  push_cast
  ring

lemma visualScale_near (δ : ℕ) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    ∃ k : ℕ, r ≤ visualScale δ k ∧
      visualScale δ k ≤ Real.exp (2*visualExponent δ)*r := by
  have he := visualExponent_pos δ
  have hq : Real.exp (-(2*visualExponent δ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  obtain ⟨k,hk₁,hk₂⟩ := exists_nat_pow_near_of_lt_one hr hr₁ (Real.exp_pos _) hq
  refine ⟨k,by simpa [visualScale_eq_pow] using hk₂,?_⟩
  rw [pow_succ] at hk₁
  have h := mul_lt_mul_of_pos_right hk₁ (Real.exp_pos (2*visualExponent δ))
  have hex : Real.exp (-(2*visualExponent δ))*Real.exp (2*visualExponent δ) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [mul_assoc,hex,mul_one] at h
  simpa only [visualScale_eq_pow,mul_comm] using h.le

lemma visualScale_tendsto_zero (δ : ℕ) :
    Filter.Tendsto (visualScale δ) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun k => visualScale δ k) Filter.atTop (nhds 0)
  simpa only [visualScale_eq_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (-(2*visualExponent δ))).le
    (show Real.exp (-(2*visualExponent δ)) < 1 by
      rw [Real.exp_lt_one_iff]; have := visualExponent_pos δ; linarith)
end CannonVisual

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
