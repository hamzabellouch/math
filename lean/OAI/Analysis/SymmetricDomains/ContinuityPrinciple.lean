import Mathlib
import OAI.Analysis.SymmetricDomains.DiscCompactness

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

theorem point_isBoundedSymmetricDomain :
    IsBoundedSymmetricDomain (univ : Set (Affine 0)) := by
  refine ⟨isOpen_univ,isConnected_univ,?_,?_⟩
  · exact (Set.toFinite _).isBounded
  · intro p
    refine ⟨biholomorphOfSubsingleton _ _,?_,Subsingleton.elim _ _,univ,isOpen_univ,mem_univ _,?_⟩
    · exact fun _ => Subsingleton.elim _ _
    · exact fun _ _ _ => Subsingleton.elim _ _

theorem main_point {n : ℕ} (U : Set (Affine n)) (hne : U.Nonempty)
    (hsub : U.Subsingleton) :
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D) := by
  let : Subsingleton U := (Set.subsingleton_coe U).mpr hsub
  let : Nonempty U := hne.to_subtype
  let B := biholomorphOfSubsingleton U (univ : Set (Affine 0))
  refine ⟨?_,0,univ,point_isBoundedSymmetricDomain,⟨B⟩⟩
  intro p
  exact ⟨0,U,Subset.rfl,by simp,p.property,univ,isOpen_univ,⟨B⟩⟩

theorem bounded_cocompact_holomorphic_family_limit {d n : ℕ} {I Γ : Type*}
    (S : Set (Affine d)) (hS : IsOpen S) (hconn : IsPreconnected S)
    (U : Set (Affine n)) [LocallyCompactSpace U]
    (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (F : I → S → U) (l : Filter I) [l.NeBot] (x₀ : S)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ i in l, F i x₀ ∈ C)
    (hF : LocallyEventuallyHolomorphic S U F l)
    (g : S → Affine n) (hg : ∀ x, Tendsto (fun i => (F i x).val) l (𝓝 (g x))) :
    ∀ x, g x ∈ U := by
  intro x
  obtain ⟨M,hM,hFM⟩ := bounded_cocompact_holomorphic_family_compact S hS hconn U
    hbounded hhol K hK hrep F l x₀ hbase hF (E := {x}) isCompact_singleton
  have hcl : IsClosed ((Subtype.val : U → Affine n) '' M) :=
    (hM.image continuous_subtype_val).isClosed
  have hmem := hcl.mem_of_tendsto (hg x) (hFM.mono fun i hi =>
    mem_image_of_mem Subtype.val (hi x (mem_singleton x)))
  obtain ⟨y,_hy,he⟩ := hmem
  rw [← he]
  exact y.property

theorem HolomorphicOnSubset.restrict {d n : ℕ} {S W : Set (Affine d)}
    {f : S → Affine n} (hf : HolomorphicOnSubset S f) (hWS : W ⊆ S) :
    HolomorphicOnSubset W (fun p => f ⟨p.val,hWS p.property⟩) := by
  intro p
  obtain ⟨O,hO,hpO,F,hF,he⟩ := hf ⟨p.val,hWS p.property⟩
  exact ⟨O,hO,hpO,F,hF,fun q hqO => he ⟨q.val,hWS q.property⟩ hqO⟩

theorem HolomorphicOnSubset.locallyEventually {d n : ℕ} {I : Type*}
    {S : Set (Affine d)} {U : Set (Affine n)} (hS : IsOpen S)
    {F : I → S → U} (hF : ∀ i, HolomorphicOnSubset S (fun x => (F i x).val))
    (l : Filter I) : LocallyEventuallyHolomorphic S U F l := by
  intro x
  exact ⟨S,hS,x.property,Subset.rfl,Eventually.of_forall hF⟩

theorem continuity_principle_of_interior_anchor {d n : ℕ} {X Γ : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [SequentialSpace X]
    (S Q : Set (Affine d)) (hS : IsOpen S) (hconn : IsPreconnected S)
    (hQ : IsCompact Q) (hSQ : S ⊆ Q)
    (V U : Set (Affine n)) (_hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (A : X → Q → V) (hA : Continuous (Function.uncurry A))
    (hAh : ∀ t, HolomorphicOnSubset S (fun x => (A t ⟨x.val,hSQ x.property⟩).val))
    (hanchor : ∀ t, ∃ x : S, (A t ⟨x.val,hSQ x.property⟩).val ∈ U)
    (hboundary : ∀ t (x : Q), x.val ∉ S → (A t x).val ∈ U)
    (hstart : ∃ t, ∀ x, (A t x).val ∈ U) :
    ∀ t x, (A t x).val ∈ U := by
  classical
  let T : Set X := {t | ∀ x, (A t x).val ∈ U}
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hop := hU.preimage hA
    obtain ⟨O,W,hO,_hW,htO,hQW,hOW⟩ := generalized_tube_lemma
      (s := {t}) isCompact_singleton (t := univ) isCompact_univ hop (by
        rintro ⟨u,x⟩ ⟨hu,_⟩
        rcases mem_singleton_iff.mp hu with rfl
        exact ht x)
    apply mem_of_superset (hO.mem_nhds (htO (mem_singleton t)))
    intro u hu x
    exact hOW (show (u,x) ∈ O ×ˢ W from ⟨hu,hQW (mem_univ x)⟩)
  have hclosed : IsClosed T := by
    apply IsSeqClosed.isClosed
    intro ts t hts ht
    obtain ⟨x₀,hx₀⟩ := hanchor t
    let F : ℕ → S → U := fun i x => ⟨(A (ts i) ⟨x.val,hSQ x.property⟩).val,
      hts i ⟨x.val,hSQ x.property⟩⟩
    have hlim (x : S) : Tendsto (fun i => (F i x).val) atTop
        (𝓝 (A t ⟨x.val,hSQ x.property⟩).val) :=
      (continuous_subtype_val.continuousAt.comp (hA.continuousAt.comp
        (continuous_id.prodMk continuous_const).continuousAt)).tendsto.comp ht
    have hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ i in atTop, F i x₀ ∈ C := by
      obtain ⟨C,hC,hCn⟩ := exists_compact_mem_nhds (⟨_,hx₀⟩ : U)
      have hh : Tendsto (fun i => F i x₀) atTop (𝓝 (⟨_,hx₀⟩ : U)) :=
        tendsto_subtype_rng.mpr (hlim x₀)
      exact ⟨C,hC,hh hCn⟩
    have hall := bounded_cocompact_holomorphic_family_limit S hS hconn U hbounded
      hhol K hK hrep F atTop x₀ hbase
      (HolomorphicOnSubset.locallyEventually hS (fun i => hAh (ts i)) atTop)
      (fun x => (A t ⟨x.val,hSQ x.property⟩).val) hlim
    intro x
    by_cases hx : x.val ∈ S
    · exact hall ⟨x.val,hx⟩
    · exact hboundary t x hx
  have hT : T = univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hstart
  intro t
  change t ∈ T
  rw [hT]
  trivial

theorem interior_anchor_of_boundary {d n : ℕ}
    (S Q : Set (Affine d)) (hSQ : S ⊆ Q) (hQS : Q ⊆ closure S)
    (hboundary : (Q \ S).Nonempty)
    (V U : Set (Affine n)) (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (A : Q → V) (hA : Continuous A)
    (hAb : ∀ x : Q, x.val ∉ S → (A x).val ∈ U) :
    ∃ x : S, (A ⟨x.val,hSQ x.property⟩).val ∈ U := by
  obtain ⟨b,hbQ,hbS⟩ := hboundary
  obtain ⟨f,hf,hfl⟩ := mem_closure_iff_seq_limit.mp (hQS hbQ)
  let F : ℕ → Q := fun i => ⟨f i,hSQ (hf i)⟩
  have hlim : Tendsto F atTop (𝓝 (⟨b,hbQ⟩ : Q)) := tendsto_subtype_rng.mpr hfl
  have he : ∀ᶠ i in atTop, (A (F i)).val ∈ U :=
    (hA.continuousAt.tendsto.comp hlim) (hU.mem_nhds (hAb ⟨b,hbQ⟩ hbS))
  obtain ⟨i,hi⟩ := he.exists
  exact ⟨⟨f i,hf i⟩,hi⟩

theorem bounded_cocompact_continuity_principle {d n : ℕ} {X Γ : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [SequentialSpace X]
    (S Q : Set (Affine d)) (hS : IsOpen S) (hconn : IsPreconnected S)
    (hQ : IsCompact Q) (hSQ : S ⊆ Q) (hQS : Q ⊆ closure S)
    (hbd : (Q \ S).Nonempty)
    (V U : Set (Affine n)) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (A : X → Q → V) (hA : Continuous (Function.uncurry A))
    (hAh : ∀ t, HolomorphicOnSubset S (fun x => (A t ⟨x.val,hSQ x.property⟩).val))
    (hboundary : ∀ t (x : Q), x.val ∉ S → (A t x).val ∈ U)
    (hstart : ∃ t, ∀ x, (A t x).val ∈ U) :
    ∀ t x, (A t x).val ∈ U := by
  apply continuity_principle_of_interior_anchor S Q hS hconn hQ hSQ V U hUV hU
    hbounded hhol K hK hrep A hA hAh _ hboundary hstart
  intro t
  exact interior_anchor_of_boundary S Q hSQ hQS hbd V U hU (A t)
    (hA.comp (continuous_const.prodMk continuous_id)) (hboundary t)

theorem bounded_cocompact_disc_continuity {n : ℕ} {Γ : Type*}
    (V U : Set (Affine n)) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (A : Icc (0 : ℝ) 1 → closedBall (0 : Affine 1) 1 → V)
    (hA : Continuous (Function.uncurry A))
    (hAh : ∀ t, HolomorphicOnSubset (ball (0 : Affine 1) 1)
      (fun x => (A t ⟨x.val,ball_subset_closedBall x.property⟩).val))
    (hboundary : ∀ t (x : closedBall (0 : Affine 1) 1), ‖x.val‖ = 1 → (A t x).val ∈ U)
    (hstart : ∀ x, (A ⟨0,by simp⟩ x).val ∈ U) :
    ∀ t x, (A t x).val ∈ U := by
  apply bounded_cocompact_continuity_principle (ball (0 : Affine 1) 1)
    (closedBall (0 : Affine 1) 1) isOpen_ball (convex_ball _ _).isPreconnected
    (isCompact_closedBall _ _) ball_subset_closedBall _ _ V U hUV hU
    hbounded hhol K hK hrep A hA hAh _ ⟨⟨0,by simp⟩,hstart⟩
  · rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  · refine ⟨fun _ => 1,?_,?_⟩ <;> simp
  · intro t x hx
    apply hboundary t x
    have hleft := x.property
    rw [mem_closedBall,dist_zero_right] at hleft
    rw [mem_ball,dist_zero_right,not_lt] at hx
    exact le_antisymm hleft hx

def RelationSteps {X : Type*} (R : X → X → Prop) : ℕ → X → X → Prop
  | 0, x, y => x = y
  | n+1, x, y => RelationSteps R n x y ∨ ∃ z, RelationSteps R n x z ∧ R z y

theorem compact_relation_steps {X : Type*} [TopologicalSpace X]
    (R : X → X → Prop)
    (hstep : ∀ C : Set X, IsCompact C → ∃ M : Set X,
      IsCompact M ∧ ∀ x ∈ C, ∀ y, R x y → y ∈ M)
    {C : Set X} (hC : IsCompact C) (n : ℕ) :
    ∃ M : Set X, IsCompact M ∧ ∀ x ∈ C, ∀ y, RelationSteps R n x y → y ∈ M := by
  induction n with
  | zero =>
      refine ⟨C,hC,?_⟩
      intro x hx y hxy
      exact hxy ▸ hx
  | succ _ ih =>
      obtain ⟨M,hM,hm⟩ := ih
      obtain ⟨N,hN,hn⟩ := hstep M hM
      refine ⟨M ∪ N,hM.union hN,?_⟩
      intro x hx y hxy
      rcases hxy with hy | ⟨z,hz,hzy⟩
      · exact Or.inl (hm x hx y hy)
      · exact Or.inr (hn z (hm x hx z hz) y hzy)

open Filter
open scoped Topology

theorem RelationSteps.refl {X : Type*} (R : X → X → Prop) (n : ℕ) (x : X) :
    RelationSteps R n x x := by
  induction n with
  | zero => rfl
  | succ _ ih => exact Or.inl ih

theorem RelationSteps.mono {X : Type*} {R : X → X → Prop} {m n : ℕ}
    (hmn : m ≤ n) {x y : X} (h : RelationSteps R m x y) : RelationSteps R n x y := by
  induction n,hmn using Nat.le_induction with
  | base => exact h
  | succ _ _ ih => exact Or.inl ih

end Release061

end OAI
