import Mathlib
import OAI.Analysis.SymmetricDomains.DiscRelationCompactLocal

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
section IntrinsicCompactness
open Set Metric Filter
open scoped Topology Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


theorem HolomorphicOnSubset.differentiableOn_disc_comp {n m : ℕ}
    {S : Set (Affine n)} {g : S → Affine m} (hg : HolomorphicOnSubset S g)
    {f : ℂ → Affine n} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hS : MapsTo f (ball 0 1) S) :
    DifferentiableOn ℂ (fun z => if hz : f z ∈ S then g ⟨f z,hz⟩ else 0) (ball 0 1) := by
  intro z hz
  obtain ⟨W,hW,hzW,G,hG,he⟩ := hg ⟨f z,hS hz⟩
  have hfz := hf.differentiableAt (isOpen_ball.mem_nhds hz)
  have hcomp := (hG (f z) hzW).differentiableAt.comp z hfz
  apply DifferentiableAt.differentiableWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz,
    hfz.continuousAt.preimage_mem_nhds (hW.mem_nhds hzW)] with w hw hwW
  simp only [dite_eq_left (hS hw),Function.comp_apply]
  exact (he ⟨f w,hS hw⟩ hwW).symm

theorem DiscRelation.map {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    {g : S → T} (hg : HolomorphicOnSubset S (fun p => (g p).val))
    {r : ℝ} (hr : r ≤ 1) {x y : S} (h : DiscRelation S r x y) :
    DiscRelation T r (g x) (g y) := by
  classical
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  let F : ℂ → Affine m := fun z => if hz : f z ∈ S then (g ⟨f z,hz⟩).val else 0
  have hF := hg.differentiableOn_disc_comp hf hS
  have ha1 : a ∈ ball (0 : ℂ) 1 := by simpa using ha.trans_le hr
  have hb1 : b ∈ ball (0 : ℂ) 1 := by simpa using hb.trans_le hr
  refine ⟨F,hF,?_,a,b,ha,hb,?_,?_⟩
  · intro z hz
    simpa only [F,dite_eq_left (hS hz)] using (g ⟨f z,hS hz⟩).property
  · have he : (⟨f a,hS ha1⟩ : S) = x := Subtype.ext hax
    simp only [F,dite_eq_left (hS ha1),he]
  · have he : (⟨f b,hS hb1⟩ : S) = y := Subtype.ext hby
    simp only [F,dite_eq_left (hS hb1),he]

theorem DiscRelation.mono {S T : Set E} (hST : S ⊆ T) {r : ℝ} {x y : S}
    (h : DiscRelation S r x y) :
    DiscRelation T r ⟨x.val,hST x.property⟩ ⟨y.val,hST y.property⟩ := by
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  exact ⟨f,hf,hS.mono_right hST,a,b,ha,hb,hax,hby⟩

theorem discRelation_closedBall {x y : E} {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hr1 : r ≤ 1) (hxy : dist y x < ε*r/2) :
    ∃ hx : x ∈ closedBall x ε, ∃ hy : y ∈ closedBall x ε,
      DiscRelation (closedBall x ε) r ⟨x,hx⟩ ⟨y,hy⟩ := by
  let a : ℂ := (r/2 : ℝ)
  have ha : ‖a‖ = r/2 := by simp [a,hr.le]
  have ha0 : a ≠ 0 := by intro h; rw [h,_root_.norm_zero] at ha; linarith
  let v : E := a⁻¹ • (y-x)
  have hv : ‖v‖ < ε := by
    rw [norm_smul,_root_.norm_inv,ha,inv_mul_eq_div]
    apply (div_lt_iff₀ (half_pos hr)).mpr
    rw [← dist_eq_norm]
    nlinarith
  let f : ℂ → E := fun z => x + z • v
  have hf : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hmaps : MapsTo f (ball 0 1) (closedBall x ε) := by
    intro z hz
    rw [mem_ball,dist_zero_right] at hz
    rw [mem_closedBall,dist_eq_norm]
    simp only [f,add_sub_cancel_left,norm_smul]
    exact ((mul_le_mul_of_nonneg_right hz.le (norm_nonneg v)).trans_eq (one_mul _)).trans hv.le
  have hx : x ∈ closedBall x ε := mem_closedBall_self hε.le
  have hy : y ∈ closedBall x ε := by
    rw [mem_closedBall]
    have : ε*r ≤ ε := mul_le_of_le_one_right hε.le hr1
    linarith
  refine ⟨hx,hy,f,hf.differentiableOn,hmaps,0,a,by simpa using hr,by rw [ha]; linarith,?_,?_⟩
  · simp [f]
  · simp [f,v,smul_smul,ha0]

theorem open_small_disc_carrier [ProperSpace E] {S : Set E} (hS : IsOpen S)
    {x : E} (hx : x ∈ S) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set E, IsCompact K ∧ K ⊆ S ∧ ∃ hxK : x ∈ K,
      ∀ y, dist y x < δ → ∃ hy : y ∈ K,
        DiscRelation K r ⟨x,hxK⟩ ⟨y,hy⟩ := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hS x hx
  let K := closedBall x (ε/2)
  have hK : K ⊆ S := (closedBall_subset_ball (half_lt_self hε)).trans hball
  refine ⟨(ε/2)*r/2,by positivity,K,(isCompact_closedBall _ _),hK,mem_closedBall_self (by positivity),?_⟩
  intro y hy
  obtain ⟨_,hyK,hrel⟩ := discRelation_closedBall (half_pos hε) hr hr1 hy
  exact ⟨hyK,hrel⟩

theorem open_discRelation_nhds [ProperSpace E] {S : Set E} (hS : IsOpen S)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : S) :
    ∀ᶠ y in 𝓝 x, DiscRelation S r x y := by
  obtain ⟨δ,hδ,K,_hK,hKS,hxK,hrel⟩ := open_small_disc_carrier hS x.property hr hr1
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  obtain ⟨hyK,hh⟩ := hrel y.val (show dist y.val x.val < δ from hy)
  exact hh.mono hKS

open scoped Pointwise

theorem compact_relation_step {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] [MulAction G X] [ProperSMul G X]
    [ContinuousConstSMul G X] (R : X → X → Prop)
    (hR : ∀ (g : G) (x y : X), R x y → R (g • x) (g • y))
    (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)
    (hrep : ∀ x : X, ∃ k ∈ K, ∃ g : G, g • k = x)
    (hlocal : ∀ x ∈ K, ∀ y, R x y → y ∈ L)
    {C : Set X} (hC : IsCompact C) :
    ∃ M : Set X, IsCompact M ∧ ∀ x ∈ C, ∀ y, R x y → y ∈ M := by
  classical
  let A : Set G := {g | (g • K ∩ C).Nonempty}
  have hA : A.Finite := isCompact_iff_finite.mp (ProperSMul.isCompact_setOfPred_inter_nonempty hK hC)
  refine ⟨⋃ g ∈ A, g • L, hA.isCompact_biUnion (fun g _ => hL.image (continuous_const_smul g)),?_⟩
  intro x hx y hxy
  obtain ⟨k,hk,g,rfl⟩ := hrep x
  have hg : g ∈ A := ⟨g • k,⟨mem_smul_set.mpr ⟨k,hk,rfl⟩,hx⟩⟩
  have hr : R k (g⁻¹ • y) := by simpa using hR g⁻¹ (g • k) y hxy
  exact mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨hg,mem_smul_set.mpr
    ⟨g⁻¹ • y,hlocal k hk _ hr,smul_inv_smul g y⟩⟩⟩

theorem compact_images_of_local_relation {X Y I : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]
    (R : Y → Y → Prop) (hsym : ∀ x y, R x y → R y x)
    (hstep : ∀ C : Set Y, IsCompact C → ∃ M : Set Y,
      IsCompact M ∧ ∀ x ∈ C, ∀ y, R x y → y ∈ M)
    (F : I → X → Y) (l : Filter I) (x₀ : X)
    (hbase : ∃ C : Set Y, IsCompact C ∧ ∀ᶠ i in l, F i x₀ ∈ C)
    (hlocal : ∀ x, ∃ O ∈ 𝓝 x, ∀ᶠ i in l, ∀ y ∈ O, R (F i x) (F i y))
    {E : Set X} (hE : IsCompact E) :
    ∃ M : Set Y, IsCompact M ∧ ∀ᶠ i in l, ∀ x ∈ E, F i x ∈ M := by
  classical
  let P : X → Prop := fun x => ∃ C : Set Y, IsCompact C ∧ ∀ᶠ i in l, F i x ∈ C
  have hforward : ∀ x, P x → ∃ O ∈ 𝓝 x, ∃ M : Set Y,
      IsCompact M ∧ ∀ᶠ i in l, ∀ y ∈ O, F i y ∈ M := by
    intro x hx
    obtain ⟨C,hC,hxc⟩ := hx
    obtain ⟨O,hO,hrel⟩ := hlocal x
    obtain ⟨M,hM,hm⟩ := hstep C hC
    exact ⟨O,hO,M,hM,by
      filter_upwards [hxc,hrel] with i hi hri
      exact fun y hy => hm _ hi _ (hri y hy)⟩
  have hopen : IsOpen {x | P x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨O,hO,M,hM,hm⟩ := hforward x hx
    apply mem_of_superset hO
    intro y hy
    exact ⟨M,hM,hm.mono (fun _ hi => hi y hy)⟩
  have hclosed : IsClosed {x | P x} := by
    rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨O,hO,hrel⟩ := hlocal x
    apply mem_of_superset hO
    intro y hy hPy
    obtain ⟨C,hC,hc⟩ := hPy
    obtain ⟨M,hM,hm⟩ := hstep C hC
    apply hx
    refine ⟨M,hM,?_⟩
    filter_upwards [hc,hrel] with i hi hri
    exact hm _ hi _ (hsym _ _ (hri y hy))
  have hall : ∀ x, P x := by
    have he := IsClopen.eq_univ ⟨hclosed,hopen⟩ (show {x | P x}.Nonempty from ⟨x₀,hbase⟩)
    intro x
    change x ∈ {x | P x}
    rw [he]
    trivial
  choose O hO M hM hm using fun x => hforward x (hall x)
  obtain ⟨J,_,hJ⟩ := hE.elim_nhds_subcover O (fun x _ => hO x)
  refine ⟨⋃ x ∈ J, M x,J.finite_toSet.isCompact_biUnion (fun x _ => hM x),?_⟩
  have hev : ∀ᶠ i in l, ∀ x ∈ J, ∀ y ∈ O x, F i y ∈ M x := by
    exact (Filter.eventually_all_finset J).mpr (fun point _ => hm point)
  filter_upwards [hev] with i hi
  intro y hy
  obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp (hJ hy)
  exact mem_iUnion₂.mpr ⟨x,hx,hi x hx y hxy⟩

def LocallyEventuallyHolomorphic {d n : ℕ} {I : Type*}
    (S : Set (Affine d)) (U : Set (Affine n)) (F : I → S → U) (l : Filter I) : Prop :=
  ∀ x : S, ∃ W : Set (Affine d), IsOpen W ∧ x.val ∈ W ∧ ∃ hWS : W ⊆ S,
    ∀ᶠ i in l, HolomorphicOnSubset W (fun p => (F i ⟨p.val,hWS p.property⟩).val)

theorem bounded_cocompact_holomorphic_family_compact {d n : ℕ} {I Γ : Type*}
    (S : Set (Affine d)) (_hS : IsOpen S) (hconn : IsPreconnected S)
    (U : Set (Affine n)) [LocallyCompactSpace U]
    (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (F : I → S → U) (l : Filter I) (x₀ : S)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ i in l, F i x₀ ∈ C)
    (hF : LocallyEventuallyHolomorphic S U F l)
    {E : Set S} (hE : IsCompact E) :
    ∃ M : Set U, IsCompact M ∧ ∀ᶠ i in l, ∀ x ∈ E, F i x ∈ M := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  let : ContinuousConstSMul Γ U := ⟨fun γ => (hhol γ).continuous.subtype_mk _⟩
  obtain ⟨r,hr,hrsmall,L,hL,hlocal⟩ := bounded_disc_relation_compact_local hbounded hK
  have hr1 : r ≤ 1 := hrsmall.trans (by norm_num)
  have hstep : ∀ C : Set U, IsCompact C → ∃ M : Set U, IsCompact M ∧
      ∀ x ∈ C, ∀ y, DiscRelation U r x y → y ∈ M := by
    intro C hC
    exact compact_relation_step (G := Γ) (DiscRelation U r)
      (fun γ x y hxy => hxy.map (hhol γ) hr1) K L hK hL hrep hlocal hC
  apply compact_images_of_local_relation (DiscRelation U r)
    (fun _ _ hxy => discRelation_symm hxy) hstep F l x₀ hbase
    (E := E) (hE := hE)
  intro x
  obtain ⟨W,hW,hxW,hWS,hFW⟩ := hF x
  obtain ⟨δ,hδ,Q,_hQ,hQW,hxQ,hQrel⟩ := open_small_disc_carrier hW hxW hr hr1
  refine ⟨Metric.ball x δ,Metric.ball_mem_nhds x hδ,?_⟩
  filter_upwards [hFW] with i hi
  intro y hy
  obtain ⟨hyQ,hxy⟩ := hQrel y.val (show dist y.val x.val < δ from hy)
  exact (hxy.mono hQW).map (g := fun p : W => F i ⟨p.val,hWS p.property⟩) hi hr1

end IntrinsicCompactness

open Set

theorem holomorphicOnSubset_const {n m : ℕ} (S : Set (Affine n)) (c : Affine m) :
    HolomorphicOnSubset S (fun _ => c) := by
  intro p
  exact ⟨univ,isOpen_univ,mem_univ _,fun _ => c,analyticOnNhd_const,fun _ _ => rfl⟩

noncomputable def biholomorphOfSubsingleton {n m : ℕ} (S : Set (Affine n))
    (T : Set (Affine m)) [Subsingleton S] [Subsingleton T] [Nonempty S] [Nonempty T] :
    Biholomorph S T where
  toHomeomorph := {
    toFun := fun _ => Classical.choice inferInstance
    invFun := fun _ => Classical.choice inferInstance
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }
  holomorphic_toFun := holomorphicOnSubset_const S (Classical.choice (inferInstance : Nonempty T)).val
  holomorphic_invFun := holomorphicOnSubset_const T (Classical.choice (inferInstance : Nonempty S)).val

end Release061

end OAI
