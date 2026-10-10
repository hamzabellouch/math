import OAI.MathematicalPhysics.Heisenberg.RegularKernels

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SlotMaximum
variable {X B : Type*}

def frameEnergy (R : X → X → Prop) (Λ : Finset X) (s : X → Finset B)
    (v : X → B → ℝ) : ℝ :=
  ∑ x∈Λ,∑ y∈Λ,if R x y then ∑ a∈s x,∑ b∈s y,(v x a-v y b)^2 else 0

lemma frameEnergy_nonneg (R : X → X → Prop) (Λ : Finset X) (s : X → Finset B)
    (v : X → B → ℝ) : 0≤frameEnergy R Λ s v := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
  · rfl

lemma test_support_subset (s : X → Finset B) (v : X → B → ℝ) (F : Finset X)
    (hvF : ∀ x,x∉F → ∀ a∈s x,v x a=0) : (test s v F hvF).support⊆F := by
  intro x hx
  by_contra hn
  have hz := zero_of_zero (s x) (v x) (hvF x hn)
  exact (Finsupp.mem_support_iff.mp hx) hz

theorem finite_frame_energy (G : SimpleGraph X) (hG : ∀ x,(G.neighborSet x).Finite)
    (R : X → X → Prop) (hR : ∀ x y,G.Adj x y → R x y)
    (Λ F : Finset X) (hF : F⊆Λ)
    (hframe : ∀ x∈F,∀ y,G.Adj x y → y∈Λ)
    (s : X → Finset B) (v : X → B → ℝ)
    (hvF : ∀ x,x∉F → ∀ a∈s x,v x a=0) :
    (∑ e∈(graphNetwork G hG).edges (test s v F hvF),
      ∑ a∈s e.fst,∑ b∈s e.snd,(v e.fst a-v e.snd b)^2) ≤ frameEnergy R Λ s v := by
  let E := (graphNetwork G hG).edges (test s v F hvF)
  let f : X×X → ℝ := fun p => if R p.1 p.2 then
    ∑ a∈s p.1,∑ b∈s p.2,(v p.1 a-v p.2 b)^2 else 0
  have he (e : G.Dart) (h : e∈E) : e.fst∈Λ ∧ e.snd∈Λ := by
    have hh := (Network.mem_edges (graphNetwork G hG) (test s v F hvF) e).mp h
    rcases hh with hh|hh
    · have hhF := test_support_subset s v F hvF hh
      exact ⟨hF hhF,hframe e.fst hhF e.snd e.adj⟩
    · have hhF := test_support_subset s v F hvF hh
      exact ⟨hframe e.snd hhF e.fst e.adj.symm,hF hhF⟩
  have hnon (p : X×X) : 0≤f p := by
    dsimp [f]
    split_ifs
    · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
    · rfl
  have hmap : E.image (fun e => e.toProd)⊆Λ×ˢΛ := by
    intro p hp
    obtain ⟨e,heE,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr (he e heE)
  calc
    _ = ∑ e∈E,f e.toProd := Finset.sum_congr rfl (fun e _ => by simp only [f,ite_eq_left (hR _ _ e.adj)])
    _ = ∑ p∈E.image (fun e => e.toProd),f p := by
      symm
      apply Finset.sum_image
      intro e _ d _ h
      exact SimpleGraph.Dart.ext e d h
    _ ≤ ∑ p∈Λ×ˢΛ,f p := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun p _ _ => hnon p)
    _ = _ := by rw [Finset.sum_product]; rfl

variable {k : ℕ}

theorem regular_frame_test (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (I V B : Type*) [Fintype I] [Fintype V]
      (K : V → I → ℝ) (x : I → ZSite k) (y : V → ZSite k)
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (R : ℕ) (s : ZSite k → Finset B)
      (slot : V → B) (v : ZSite k → B → ℝ) (Λ F : Finset (ZSite k))
      (_hvF : ∀ z,z∉F → ∀ a∈s z,v z a=0),
      F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
      (∀ j i,0≤K j i) → (∀ i,∑ j,K j i≤1) →
      (∀ z r,0≤r → ((Finset.univ.filter (fun i => dist (x i) z≤r)).card:ℝ) ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ j i,K j i≠0 → y j∉Z ∧ slot j∈s (y j)) →
      (∀ z,z∉Z → (s z).Nonempty) → (∀ z a,0≤v z a) →
      (∑ i,∑ j,goodMass K x y Z R M i j*v (y j) (slot j))^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I))*frameEnergy Step Λ s v := by
  obtain ⟨M,C,hC,htest⟩ := regular_kernel_test hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I V B _ _ K x y Z hZ R s slot v Λ F hvF hF hframe hK hm hg hs ha hv
  have hh := htest I V B K x y Z hZ R s slot v F hvF hK hm hg hs ha hv
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_frame_energy (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ) Step
    (fun _ _ h => h.1) Λ F hF (fun z hz w h => hframe z hz w h.1) s v hvF

end Heisenberg.Flow

namespace Heisenberg.Exposure
variable {V : Type*} [Fintype V]
def quietEnergy (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V) : ℝ :=
  ∑ i ∈ Finset.range n,if a i ∈ H ∧ b i ∈ H then (v.ofLp (a i)-v.ofLp (b i))^2 else 0
end Heisenberg.Exposure

namespace Heisenberg.SpatialFrame

section
variable {X B : Type*} [Fintype B]
abbrev Slots (Λ : Finset X) := Λ × B

def available (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) (x : X) : Finset B :=
  if hx : x∈Λ then Finset.univ.filter (fun a => (⟨x,hx⟩,a)∈H) else Finset.univ

def extend (Λ : Finset X) (v : Slots (B:=B) Λ → ℝ) (x : X) (a : B) : ℝ :=
  if hx : x∈Λ then v (⟨x,hx⟩,a) else 0

omit [Fintype B] in
lemma extend_apply (Λ : Finset X) (v : Slots (B:=B) Λ → ℝ) (x : Λ) (a : B) :
    extend Λ v x a=v (x,a) := by simp [extend]

lemma available_apply (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) (x : Λ) (a : B) :
    a∈available Λ H x ↔ (x,a)∈H := by simp [available]

lemma available_nonempty (Λ : Finset X) [Nonempty B] (H : Set (Slots (B:=B) Λ))
    (x : X) (hx : ¬∃ h : x∈Λ,∀ a : B,(⟨x,h⟩,a)∉H) :
    (available Λ H x).Nonempty := by
  by_cases h : x∈Λ
  · have hx : ∃ a : B,(⟨x,h⟩,a)∈H := by
      by_contra hn
      apply hx
      exact ⟨h,by simpa only [not_exists] using hn⟩
    obtain ⟨a,ha⟩ := hx
    exact ⟨a,by simpa [available,h] using ha⟩
  · simp [available,h]

omit [Fintype B] in
lemma extend_nonneg (Λ : Finset X) (v : Slots (B:=B) Λ → ℝ) (hv : ∀ j,0≤v j) :
    ∀ x a,0≤extend Λ v x a := by
  intro x a
  dsimp [extend]
  split_ifs
  · exact hv _
  · rfl

omit [Fintype B] in
lemma extend_supported (Λ F : Finset X) (v : Slots (B:=B) Λ → ℝ)
    (hv : ∀ j,j.1.val∉F → v j=0) : ∀ x,x∉F → ∀ a,extend Λ v x a=0 := by
  intro x hx a
  dsimp [extend]
  split_ifs
  · exact hv _ hx
  · rfl

abbrev Edges (R : X → X → Prop) (Λ : Finset X) :=
  {e : Slots (B:=B) Λ × Slots (B:=B) Λ // R e.1.1 e.2.1}

lemma frame_eq_pairs (R : X → X → Prop) (Λ : Finset X)
    (H : Set (Slots (B:=B) Λ)) (v : Slots (B:=B) Λ → ℝ) :
    Heisenberg.Flow.frameEnergy R Λ (available Λ H) (extend Λ v) =
    ∑ e : Edges R Λ,if e.val.1∈H ∧ e.val.2∈H then (v e.val.1-v e.val.2)^2 else 0 := by
  unfold Heisenberg.Flow.frameEnergy
  simp_rw [←Finset.sum_coe_sort Λ]
  have he := Finset.sum_subtype
    (Finset.univ.filter (fun e : Slots (B:=B) Λ × Slots (B:=B) Λ => R e.1.1 e.2.1))
    (p:=fun e => R e.1.1 e.2.1) (F:=inferInstance) (by simp)
    (fun e => if e.1∈H ∧ e.2∈H then (v e.1-v e.2)^2 else 0)
  rw [←he]
  simp only [Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hr : R x y
  · simp only [hr,ite_true,available,extend,dite_eq_left x.property,dite_eq_left y.property,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hh : (x,a)∈H
    · simp only [hh,ite_true,true_and]
    · simp [hh]
  · simp [hr]

theorem frame_eq_sweep (R : X → X → Prop) (Λ : Finset X)
    (H : Set (Slots (B:=B) Λ)) (v : EuclideanSpace ℝ (Slots (B:=B) Λ))
    (a b : ℕ → Slots (B:=B) Λ) (n : ℕ)
    (e : Fin n ≃ Edges R Λ)
    (ha : ∀ i : Fin n,a i=(e i).val.1) (hb : ∀ i : Fin n,b i=(e i).val.2) :
    Heisenberg.Flow.frameEnergy R Λ (available Λ H) (extend Λ v.ofLp) =
      Heisenberg.Exposure.quietEnergy H a b n v := by
  rw [frame_eq_pairs]
  rw [←e.sum_comp]
  unfold Heisenberg.Exposure.quietEnergy
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [ha i,hb i]

end

variable {X B : Type*} [Fintype B]
def blocked (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) : Set X :=
  {x | ∃ h : x∈Λ,∀ a : B,(⟨x,h⟩,a)∉H}

omit [Fintype B] in
lemma blocked_finite (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) :
    (blocked Λ H).Finite := Λ.finite_toSet.subset (fun _ h => h.choose)

omit [Fintype B] in
lemma hole_not_blocked (Λ : Finset X) (H : Set (Slots (B:=B) Λ))
    (j : Slots (B:=B) Λ) (hj : j∈H) : j.1.val∉blocked Λ H := by
  rintro ⟨h,hb⟩
  exact hb j.2 hj

lemma available_unblocked (Λ : Finset X) [Nonempty B] (H : Set (Slots (B:=B) Λ))
    (x : X) (hx : x∉blocked Λ H) : (available Λ H x).Nonempty := available_nonempty Λ H x hx
end Heisenberg.SpatialFrame

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.RoutedFlow Heisenberg.SpatialFrame
variable {k : ℕ}

theorem routed_sweep_pair (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (I B : Type*) [Fintype I] [Fintype B] [Nonempty B]
      (Λ F : Finset (ZSite k)) (H : Set (Slots (B:=B) Λ))
      (x : I → ZSite k) (K : Slots (B:=B) Λ → I → ℝ)
      (v : EuclideanSpace ℝ (Slots (B:=B) Λ)) (R : ℕ)
      (a b : ℕ → Slots (B:=B) Λ) (n : ℕ) (e : Fin n ≃ Edges Step Λ),
      (∀ i : Fin n,a i=(e i).val.1) → (∀ i : Fin n,b i=(e i).val.2) →
      F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
      (∀ j,j.1.val∉F → v.ofLp j=0) →
      (∀ j i,0≤K j i) → (∀ i,∑ j,K j i≤1) →
      (∀ z r,0≤r → ((Finset.univ.filter (fun i => dist (x i) z≤r)).card:ℝ) ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ j i,K j i≠0 → j∈H) → (∀ j,0≤v.ofLp j) →
      (∑ i,∑ j,goodMass K x (fun j=>j.1.val) (blocked Λ H) R M i j*v.ofLp j)^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I))*
          Heisenberg.Exposure.quietEnergy H a b n v := by
  obtain ⟨M,C,hC,h⟩ := regular_frame_test hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I B _ _ _ Λ F H x K v R a b n e ha hb hF hframe hvF hK hm hg hKH hv
  have hvext : ∀ z,z∉F → ∀ a∈available Λ H z,extend Λ v.ofLp z a=0 := by
    intro z hz a _
    exact extend_supported Λ F v.ofLp hvF z hz a
  have hs : ∀ j i,K j i≠0 → j.1.val∉blocked Λ H ∧ j.2∈available Λ H j.1 := by
    intro j i hji
    exact ⟨hole_not_blocked Λ H j (hKH j i hji),(available_apply Λ H j.1 j.2).mpr (hKH j i hji)⟩
  have hh := h I (Slots (B:=B) Λ) B K x (fun j=>j.1.val) (blocked Λ H)
    (blocked_finite Λ H) R (available Λ H) (fun j=>j.2) (extend Λ v.ofLp)
    Λ F hvext hF hframe hK hm hg hs (available_unblocked Λ H) (extend_nonneg Λ v.ofLp hv)
  simp only [extend_apply] at hh
  rw [frame_eq_sweep Step Λ H v a b n e ha hb] at hh
  exact hh

end Heisenberg.Flow

end

end OAI
