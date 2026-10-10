import Mathlib
import OAI.Geometry.Cannon.Boundary.VisualScale

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
namespace CannonReal
lemma expansion_separation {R r s t q L A B C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hq : 1 ≤ q) (hL : 0 < L)
    (hrR : r ≤ R) (hRq : R ≤ q*r) (hrs : r ≤ s) (hrt : r ≤ t)
    (htri : s ≤ r+t) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h₁ : R*r ≤ L*(A*R*max R r))
    (h₂ : R*s ≤ L*(B*R*max R s))
    (h₃ : R*t ≤ L*(C*max R r*max R s)) :
    1/(2*L*q) ≤ A ∧ 1/(2*L*q) ≤ B ∧ 1/(2*L*q) ≤ C := by
  have hq₀ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hs : 0 < s := hr.trans_le hrs
  have ht : 0 < t := hr.trans_le hrt
  have hm : max R s ≤ q*s := max_le (hRq.trans (mul_le_mul_of_nonneg_left hrs hq₀.le))
    (by nlinarith)
  rw [max_eq_left hrR] at h₁ h₃
  have ha : r ≤ L*A*R := by nlinarith [hR]
  have ha' : r ≤ L*A*(q*r) := ha.trans (mul_le_mul_of_nonneg_left hRq (mul_nonneg hL.le hA))
  have hb : s ≤ L*B*max R s := by nlinarith [hR]
  have hb' : s ≤ L*B*(q*s) := hb.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg hL.le hB))
  have hc : t ≤ L*C*max R s := by nlinarith [hR]
  have hc' : t ≤ L*C*(q*s) := hc.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg hL.le hC))
  have hst : s ≤ 2*t := by linarith
  have hc'' : t ≤ L*C*(q*(2*t)) := hc'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hst hq₀.le) (mul_nonneg hL.le hC))
  have hden : 0 < 2*L*q := by positivity
  refine ⟨(div_le_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_⟩
  · have : 1 ≤ L*A*q := by nlinarith
    nlinarith
  · have : 1 ≤ L*B*q := by nlinarith
    nlinarith
  · have : 1 ≤ 2*L*C*q := by nlinarith
    nlinarith
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

noncomputable abbrev boundaryDist : Boundary D → Boundary D → ℝ :=
  @dist _ (visualMetricSpace D hδ).toDist

lemma boundaryDist_le_one (x y : Boundary D) : boundaryDist D hδ x y ≤ 1 := by
  induction x,y using Quotient.inductionOn₂ with | h r s =>
    dsimp only [boundaryDist, Quotient.mk', CayleyData.graph, Thin] at *
    apply (visualMetric_comparison D hδ r s).1.trans
    have hh := preDist_le_decay (visualExponent δ) r s 0
    have hh' : (preDist (visualExponent δ) r s : ℝ) ≤ (decay (visualExponent δ) r s 0 : ℝ) := by exact_mod_cast hh
    apply hh'.trans_eq
    simp [decay,product2,r.property.1,s.property.1]
    rfl

lemma normalize_closest (x y z : Boundary D) (hxy : x ≠ y)
    (hmin₁ : boundaryDist D hδ x y ≤ boundaryDist D hδ x z)
    (hmin₂ : boundaryDist D hδ x y ≤ boundaryDist D hδ y z) :
    ∃ g : G,
      let e := 1/(2*(8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*Real.exp (2*visualExponent δ))
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g z) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) := by
  let _ := visualMetricSpace D hδ
  have hr : 0 < boundaryDist D hδ x y := dist_pos.mpr hxy
  obtain ⟨k,hk₁,hk₂⟩ := visualScale_near δ hr (boundaryDist_le_one D hδ x y)
  obtain ⟨r,hrx⟩ := Quotient.exists_rep x
  subst x
  let g := (r.val k)⁻¹
  refine ⟨g,?_⟩
  have he₁ := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).2
  have he₂ := (visual_expansion_ray D hδ r k (Quotient.mk' r) z).2
  have he₃ := (visual_expansion_ray D hδ r k y z).2
  have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r) = 0 := dist_self _
  change visualScale δ k * boundaryDist D hδ (Quotient.mk' r) y ≤
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*
      (boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g (Quotient.mk' r))
        (boundaryTranslate D ⟨δ,hδ⟩ g y) * max (visualScale δ k)
        (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)) *
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y)) at he₁
  change visualScale δ k * boundaryDist D hδ (Quotient.mk' r) z ≤
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*
      (boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g (Quotient.mk' r))
        (boundaryTranslate D ⟨δ,hδ⟩ g z) * max (visualScale δ k)
        (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)) *
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) z)) at he₂
  rw [hself,max_eq_left (visualScale_pos δ k).le] at he₁ he₂
  exact CannonReal.expansion_separation (visualScale_pos δ k) hr
    (by rw [Real.one_le_exp_iff]; have := visualExponent_pos δ; linarith)
    (by positivity) hk₁ hk₂ hmin₁ hmin₂ (dist_triangle _ _ _)
    dist_nonneg dist_nonneg dist_nonneg he₁ he₂ he₃

end CannonRelease

namespace CannonMetric
variable {X : Type*} [MetricSpace X]
lemma two_far_from_center (p x y z : X) {e : ℝ}
    (hxy : e ≤ dist x y) (hxz : e ≤ dist x z) (hyz : e ≤ dist y z) :
    (e/2 ≤ dist p x ∧ e/2 ≤ dist p y) ∨
    (e/2 ≤ dist p x ∧ e/2 ≤ dist p z) ∨
    (e/2 ≤ dist p y ∧ e/2 ≤ dist p z) := by
  have h₁ := dist_triangle_left x y p
  have h₂ := dist_triangle_left x z p
  have h₃ := dist_triangle_left y z p
  by_cases hx : e/2 ≤ dist p x
  · by_cases hy : e/2 ≤ dist p y
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr (Or.inl ⟨hx,by linarith⟩)
  · exact Or.inr (Or.inr ⟨by linarith,by linarith⟩)
end CannonMetric

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma expansion_contraction (r : BasedRay D) (k : ℕ) (y z : Boundary D)
    {e : ℝ} (he : 0 ≤ e)
    (hy : e ≤ boundaryDist D hδ (Quotient.mk' r) y)
    (hz : e ≤ boundaryDist D hδ (Quotient.mk' r) z) :
    boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ y)
        (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ z) * (e*e) ≤
      (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))*visualScale δ k := by
  let _ := visualMetricSpace D hδ
  have h := (visual_expansion_ray D hδ r k y z).1
  have h₁ := mul_le_mul (hy.trans (le_max_right (visualScale δ k) _)) (hz.trans (le_max_right (visualScale δ k) _))
    he ((visualScale_pos δ k).le.trans (le_max_left _ _))
  have h₂ := mul_le_mul_of_nonneg_left h₁
    (show 0 ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ y)
      (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ z) from dist_nonneg)
  have h₃ := mul_le_mul_of_nonneg_left (boundaryDist_le_one D hδ y z)
    (show 0 ≤ (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))*visualScale δ k from
      mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (visualScale_pos δ k).le)
  rw [mul_one] at h₃
  exact h₂.trans (by simpa only [mul_assoc] using h.trans h₃)

lemma bounded_translate_lipschitz {B : ℕ} {g : G} (hg : D.graph.dist 1 g ≤ B)
    (x y : Boundary D) :
    boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) ≤
      (2*Real.exp (visualExponent δ*(2*(3*B+4*δ):ℕ)))*boundaryDist D hδ x y := by
  let _ := visualMetricSpace D hδ
  apply (boundaryTranslate_lipschitz_bound D hδ g x y).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (visualExponent_pos δ).le
  exact_mod_cast (show 2*(3*D.graph.dist 1 g+4*δ) ≤ 2*(3*B+4*δ) by omega)

include hδ in
lemma proper_triple_word_bound (r s : BasedRay D) (hrs : ¬ (raySetoid D).r r s)
    {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, ∀ g : G, ∀ x y z : Boundary D,
      e ≤ boundaryDist D hδ x y → e ≤ boundaryDist D hδ x z → e ≤ boundaryDist D hδ y z →
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) →
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g z) →
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) →
      D.graph.dist 1 g⁻¹ ≤ N := by
  let _ := visualMetricSpace D hδ
  obtain ⟨B,hB⟩ := coarse_prefix_of_distinct_rays D hδ r s hrs
  let M := 2*Real.exp (visualExponent δ*(2*(3*B+4*δ):ℕ))
  let U := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  have hM : 0 < M := by positivity
  have hU : 0 < U := by positivity
  have hlim := (visualScale_tendsto_zero δ).const_mul (M*U)
  have hpos : 0 < e*(e/2*(e/2)) := by positivity
  have hsmall : ∀ᶠ k in atTop, M*U*visualScale δ k < e*(e/2*(e/2)) := by
    exact (tendsto_order.1 (by simpa only [mul_zero] using hlim)).2 _ hpos
  obtain ⟨N,hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N,?_⟩
  intro g x y z hxy hxz hyz hgxy hgxz hgyz
  let k := D.graph.dist 1 g⁻¹
  obtain ⟨t,ht⟩ := hB g⁻¹
  let a := g*t.val k
  have ha : D.graph.dist 1 a ≤ B := by
    have hh := D.dist_mul_left g g⁻¹ (t.val k)
    rw [mul_inv_cancel] at hh
    exact hh.symm ▸ ht
  have hfac : a*(t.val k)⁻¹ = g := by simp only [a,mul_assoc,mul_inv_cancel,mul_one]
  have hpair (u v : Boundary D)
      (hu : e/2 ≤ boundaryDist D hδ (Quotient.mk' t) u)
      (hv : e/2 ≤ boundaryDist D hδ (Quotient.mk' t) v)
      (hguv : e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g u)
        (boundaryTranslate D ⟨δ,hδ⟩ g v)) : k ≤ N := by
    have hc := expansion_contraction D hδ t k u v (by positivity) hu hv
    have hl := bounded_translate_lipschitz D hδ ha
      (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ u) (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ v)
    rw [← boundaryTranslate_mul D ⟨δ,hδ⟩ a (t.val k)⁻¹ u,
      ← boundaryTranslate_mul D ⟨δ,hδ⟩ a (t.val k)⁻¹ v,hfac] at hl
    have hh := mul_le_mul_of_nonneg_right (hguv.trans hl)
      (show 0 ≤ e/2*(e/2) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hc hM.le
    have hh'' : e*(e/2*(e/2)) ≤ M*U*visualScale δ k := by
      calc
        e*(e/2*(e/2)) ≤ M*(boundaryDist D hδ
          (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ u)
          (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ v) * (e/2*(e/2))) := by
            simpa only [M,mul_assoc] using hh
        _ ≤ M*(U*visualScale δ k) := hh'
        _ = M*U*visualScale δ k := (mul_assoc _ _ _).symm
    by_contra hn
    exact (not_lt_of_ge hh'') (hN k (by omega))
  rcases @CannonMetric.two_far_from_center (Boundary D) (visualMetricSpace D hδ) (Quotient.mk' t : Boundary D) x y z e hxy hxz hyz with
    ⟨hx,hy⟩ | ⟨hx,hz⟩ | ⟨hy,hz⟩
  · exact hpair x y hx hy hgxy
  · exact hpair x z hx hz hgxz
  · exact hpair y z hy hz hgyz

end CannonRelease

noncomputable section
open Set Metric Topology

namespace CannonPaths
variable {X : Type*} [MetricSpace X]

lemma joined_avoid_buffer {p u v : X} {r : ℝ}
    (h : JoinedIn {z | r < dist p z} u v) :
    ∃ s > r, JoinedIn {z | s < dist p z} u v := by
  obtain ⟨t,_,ht⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set unitInterval).Nonempty)
    (continuous_const.dist h.somePath.continuous).continuousOn
  have hh : r < dist p (h.somePath t) := h.somePath_mem t
  refine ⟨(r+dist p (h.somePath t))/2,by linarith,h.somePath,fun a => ?_⟩
  have ha := ht (Set.mem_univ a)
  dsimp at ha ⊢
  linarith

variable [LocallyPathConnectedSpace X]

lemma isOpen_joined_avoid (r : ℝ) :
    IsOpen {t : X × X × X | JoinedIn {z | r < dist t.1 z} t.2.1 t.2.2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨p,u,v⟩ h
  obtain ⟨s,hrs,hs⟩ := joined_avoid_buffer h
  let V := {z : X | s < dist p z}
  have hV : IsOpen V := isOpen_lt continuous_const (continuous_const.dist continuous_id)
  have hu : u ∈ pathComponentIn V u := mem_pathComponentIn_self hs.source_mem
  have hv : v ∈ pathComponentIn V v := mem_pathComponentIn_self hs.target_mem
  refine Filter.mem_of_superset (prod_mem_nhds (ball_mem_nhds p (sub_pos.mpr hrs))
    (prod_mem_nhds ((hV.pathComponentIn u).mem_nhds hu) ((hV.pathComponentIn v).mem_nhds hv))) ?_
  rintro ⟨p',u',v'⟩ ⟨hp',hu',hv'⟩
  have hj : JoinedIn V u' v' := hu'.symm.trans (hs.trans hv')
  apply hj.mono
  intro z hz
  have ht := dist_triangle p p' z
  have hp : dist p p' < s-r := by simpa only [mem_ball,dist_comm] using hp'
  dsimp [V] at hz ⊢
  linarith

theorem uniform_avoidance [CompactSpace X]
    (hpuncture : ∀ p : X, IsPathConnected ({p}ᶜ : Set X)) {e : ℝ} (he : 0 < e) :
    ∃ r > 0, ∀ p u v : X, e ≤ dist p u → e ≤ dist p v →
      JoinedIn {z | r < dist p z} u v := by
  classical
  let K : Set (X × X × X) := {t | e ≤ dist t.1 t.2.1 ∧ e ≤ dist t.1 t.2.2}
  have hK : IsCompact K := (IsClosed.inter
    (isClosed_le continuous_const (continuous_fst.dist (continuous_fst.comp continuous_snd)))
    (isClosed_le continuous_const (continuous_fst.dist (continuous_snd.comp continuous_snd)))).isCompact
  let V : {r : ℝ // 0 < r} → Set (X × X × X) := fun r =>
    {t | JoinedIn {z | r.val < dist t.1 z} t.2.1 t.2.2}
  have hcover : K ⊆ ⋃ r, V r := by
    rintro ⟨p,u,v⟩ ⟨hu,hv⟩
    have hpu : u ∈ ({p}ᶜ : Set X) := by
      simp only [mem_compl_iff,mem_singleton_iff]
      intro h; subst u; simp at hu; linarith
    have hpv : v ∈ ({p}ᶜ : Set X) := by
      simp only [mem_compl_iff,mem_singleton_iff]
      intro h; subst v; simp at hv; linarith
    have hj := (hpuncture p).joinedIn u hpu v hpv
    have hj' : JoinedIn {z | 0 < dist p z} u v := hj.mono (by
      intro z hz
      exact dist_pos.mpr (Ne.symm hz))
    obtain ⟨r,hr,hh⟩ := joined_avoid_buffer hj'
    exact mem_iUnion.mpr ⟨⟨r,hr⟩,hh⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V (fun r => isOpen_joined_avoid r.val) hcover

  let a : ℝ := ∏ t ∈ s, min 1 t.val
  have ha : 0 < a := Finset.prod_pos (fun t _ => lt_min (by norm_num) t.property)
  refine ⟨a,ha,fun p u v hu hv => ?_⟩
  obtain ⟨b,hb⟩ := mem_iUnion.mp (hs (show (p,u,v) ∈ K from ⟨hu,hv⟩))
  obtain ⟨hb,hh⟩ := mem_iUnion.mp hb
  have hab : a ≤ b.val := (Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.singleton_subset_iff.mpr hb)
    (fun t _ => (le_min (by norm_num) t.property.le)) (fun t _ _ => min_le_left _ _)).trans ?_
  · exact hh.mono (fun z hz => lt_of_le_of_lt hab hz)
  · simp only [Finset.prod_singleton]
    exact min_le_right _ _

end CannonPaths
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
