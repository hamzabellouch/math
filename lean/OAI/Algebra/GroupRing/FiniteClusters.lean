import Mathlib
import OAI.Algebra.GroupRing.ShortClosure

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.FiniteClusters
open scoped Classical BigOperators
variable {V : Type} [Fintype V] (G : SimpleGraph V)
local instance : Fintype G.ConnectedComponent := Fintype.ofFinite _

def block (c : G.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => G.connectedComponentMk v=c)
lemma mem_block {c : G.ConnectedComponent} {v : V} :
    v∈block G c ↔ G.connectedComponentMk v=c := by simp [block]
lemma block_nonempty (c : G.ConnectedComponent) : (block G c).Nonempty := by
  exact ⟨c.out,(mem_block G).mpr c.out_eq⟩
omit [Fintype V] in
lemma same_of_adj {v w : V} (h : G.Adj v w) : G.connectedComponentMk v=G.connectedComponentMk w :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h

omit [Fintype V] in
lemma reachable_closed {B : Finset V}
    (hc : ∀ x∈B,∀ y,G.Adj x y → y∈B) {x y : V}
    (hp : G.Reachable x y) (hx : x∈B) : y∈B := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => exact hx
  | @cons u v w h p ih => exact ih (hc u hx v h)

lemma block_card {K : ℕ}
    (hs : ∀ x : V,∃ B : Finset V,x∈B ∧ B.card≤K ∧ ∀ y∈B,∀ z,G.Adj y z → z∈B)
    (c : G.ConnectedComponent) : (block G c).card≤K := by
  obtain ⟨x,hx⟩ := block_nonempty G c
  obtain ⟨B,hB,hBK,hclosed⟩ := hs x
  apply (Finset.card_le_card (show block G c⊆B from ?_)).trans hBK
  intro y hy
  apply reachable_closed G hclosed _ hB
  apply SimpleGraph.ConnectedComponent.exact
  exact (mem_block G).mp hx |>.trans ((mem_block G).mp hy).symm

lemma sum_blocks {M : Type*} [AddCommMonoid M] (w : V → M) :
    (∑ c : G.ConnectedComponent,∑ v∈block G c,w v)=∑ v,w v := by
  simp only [block,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp

lemma block_sum_le {w : V → ℝ} {b : ℝ} (h : ∀ v,w v≤b) (c : G.ConnectedComponent) :
    (∑ v∈block G c,w v)≤(block G c).card*b := by
  calc
    _ ≤ ∑ _v∈block G c,b := Finset.sum_le_sum fun v _ => h v
    _ = _ := by simp
end TorsionFreeZeroDivisors.FiniteClusters

namespace TorsionFreeZeroDivisors.PairingClusters
open scoped Classical BigOperators
variable {O T : Type} [Fintype O] [Fintype T]
    (f : O → T) (α : O → O) (hα : Function.Involutive α) (keep : T → Prop)
abbrev Vertex := {t // keep t}
def Rel (p q : T) : Prop := ∃ o,f o=p ∧ f (α o)=q
include hα in
omit [Fintype O] [Fintype T] in
lemma rel_symm {p q : T} (h : Rel f α p q) : Rel f α q p := by
  obtain ⟨o,ho,hp⟩ := h
  exact ⟨α o,hp,by simpa only [hα o] using ho⟩
def graph : SimpleGraph (Vertex keep) where
  Adj p q := p≠q ∧ Rel f α p.val q.val
  symm := ⟨by
    intro p q h
    exact ⟨Ne.symm h.1,rel_symm f α hα h.2⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩
local instance : Fintype (graph f α hα keep).ConnectedComponent := Fintype.ofFinite _
abbrev Cluster := (graph f α hα keep).ConnectedComponent

def cluster (t : T) : Option (Cluster f α hα keep) :=
  if h : keep t then some ((graph f α hα keep).connectedComponentMk ⟨t,h⟩) else none
omit [Fintype O] [Fintype T] in
lemma cluster_some {t : T} (h : keep t) :
    cluster f α hα keep t=some ((graph f α hα keep).connectedComponentMk ⟨t,h⟩) := dite_eq_left h
omit [Fintype O] [Fintype T] in
lemma cluster_none {t : T} (h : ¬keep t) : cluster f α hα keep t=none := dite_eq_right h
omit [Fintype O] [Fintype T] in
lemma cluster_exists {t : T} : (∃ c,cluster f α hα keep t=some c) ↔ keep t := by
  by_cases h : keep t
  · simp only [cluster_some f α hα keep h,Option.some.injEq,exists_eq',h]
  · simp only [cluster_none f α hα keep h,reduceCtorEq,exists_false,false_iff]; exact h
omit [Fintype O] [Fintype T] in
lemma cluster_pair {o : O} (h : keep (f o)) (h' : keep (f (α o))) :
    cluster f α hα keep (f o)=cluster f α hα keep (f (α o)) := by
  rw [cluster_some f α hα keep h,cluster_some f α hα keep h']
  apply congrArg some
  by_cases he : (⟨f o,h⟩ : Vertex keep)=⟨f (α o),h'⟩
  · rw [he]
  · apply FiniteClusters.same_of_adj
    exact ⟨he,⟨o,rfl,rfl⟩⟩
omit [Fintype O] [Fintype T] in
lemma same_cluster_partner {o : O} {c : Cluster f α hα keep}
    (hc : cluster f α hα keep (f o)=some c) :
    (cluster f α hα keep (f (α o))=some c ↔ keep (f (α o))) := by
  constructor
  · intro h; exact (cluster_exists f α hα keep).mp ⟨c,h⟩
  · intro h
    rw [←cluster_pair f α hα keep ((cluster_exists f α hα keep).mp ⟨c,hc⟩) h,hc]

def bad (o : O) : Prop := keep (f o) ∧ (α o=o ∨ ¬keep (f (α o)))
def localBad (c : Cluster f α hα keep) (o : O) : Prop :=
  cluster f α hα keep (f o)=some c ∧
    (α o=o ∨ cluster f α hα keep (f (α o))≠some c)
omit [Fintype O] [Fintype T] in
lemma localBad_iff (c : Cluster f α hα keep) (o : O) :
    localBad f α hα keep c o ↔ bad f α keep o ∧ cluster f α hα keep (f o)=some c := by
  constructor
  · rintro ⟨hc,hb⟩
    refine ⟨⟨(cluster_exists f α hα keep).mp ⟨c,hc⟩,?_⟩,hc⟩
    exact hb.imp_right fun hn h => hn ((same_cluster_partner f α hα keep hc).mpr h)
  · rintro ⟨⟨_,hb⟩,hc⟩
    exact ⟨hc,hb.imp_right fun hn h => hn ((same_cluster_partner f α hα keep hc).mp h)⟩

lemma local_bad_sum :
    (∑ c : Cluster f α hα keep,(Finset.univ.filter (localBad f α hα keep c)).card)=
    (Finset.univ.filter (bad f α keep)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [localBad_iff]
  by_cases hb : bad f α keep o
  · obtain ⟨c,hc⟩ := (cluster_exists f α hα keep).mpr hb.1
    simp [hb,hc]
  · simp [hb]

include hα in
omit [Fintype T] in
lemma total_bad_bound : (Finset.univ.filter (bad f α keep)).card≤
    (Finset.univ.filter (fun o => α o=o)).card+
    (Finset.univ.filter (fun o => ¬keep (f o) ∧ α o≠o)).card := by
  let old := Finset.univ.filter (fun o : O => keep (f o) ∧ α o=o)
  let cut := Finset.univ.filter (fun o : O => keep (f o) ∧ α o≠o ∧ ¬keep (f (α o)))
  have cover : Finset.univ.filter (bad f α keep)⊆old∪cut := by
    intro o ho
    have ho := (Finset.mem_filter.mp ho).2
    by_cases he : α o=o
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho.1,he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho.1,he,ho.2.resolve_left he⟩)
  have hold : old.card≤(Finset.univ.filter (fun o => α o=o)).card := by
    apply Finset.card_le_card
    intro o ho
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ho).2.2⟩
  have hcut : cut.card≤(Finset.univ.filter (fun o => ¬keep (f o) ∧ α o≠o)).card := by
    apply Finset.card_le_card_of_injOn (f:=α)
    · intro o ho
      have ho := (Finset.mem_filter.mp ho).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho.2.2,by simpa only [hα o] using Ne.symm ho.2.1⟩
    · exact fun _ _ _ _ h => hα.injective h
  exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hold hcut))

lemma total_local_bad_bound :
    (∑ c : Cluster f α hα keep,(Finset.univ.filter (localBad f α hα keep c)).card)≤
    (Finset.univ.filter (fun o => α o=o)).card+
    (Finset.univ.filter (fun o => ¬keep (f o) ∧ α o≠o)).card := by
  rw [local_bad_sum]
  exact total_bad_bound f α hα keep
end TorsionFreeZeroDivisors.PairingClusters

/-! Arithmetic localization of finite-cluster mass and comparison bounds. -/
namespace TorsionFreeZeroDivisors.PlanarLocalization
open scoped Classical BigOperators

lemma bad_mass {Z : Type} [Fintype Z] (h b : Z → ℝ) (ε : ℝ)
    (hb : ∀ z,0 ≤ b z) :
    ε*(∑ z∈Finset.univ.filter (fun z => ε*h z < b z),h z) ≤ ∑ z,b z := by
  calc
    _ = ∑ z∈Finset.univ.filter (fun z => ε*h z < b z),ε*h z := by rw [Finset.mul_sum]
    _ ≤ ∑ z∈Finset.univ.filter (fun z => ε*h z < b z),b z :=
      Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun z _ _ => hb z)

/-- Three exact exclusions leave a positive amount of source length. -/
theorem exists_good_cluster {Z : Type} [Fintype Z]
    (h b i : Z → ℝ) (H₀ L ε C C₂ : ℝ)
    (hH₀ : 0 < H₀) (hL : 0 < L) (hε : 0 < ε) (hC₂ : 0 < C₂)
    (hh : ∀ z,0 ≤ h z) (hb : ∀ z,0 ≤ b z) (hi : ∀ z,0 ≤ i z)
    (hupper : ∀ z,h z ≤ C*L)
    (hretained : 15/16*H₀ ≤ ∑ z,h z)
    (hunpaired : ∑ z,b z ≤ ε/16*H₀)
    (hcomparisons : ∑ z,i z ≤ C₂/(16*L)*H₀)
    (hshort : ∑ z∈Finset.univ.filter (fun z => h z < L),h z ≤ H₀/2) :
    ∃ z,L ≤ h z ∧ h z ≤ C*L ∧ b z ≤ ε*h z ∧ i z ≤ C₂*h z/L := by
  let badB := Finset.univ.filter (fun z => ε*h z < b z)
  let badI := Finset.univ.filter (fun z => (C₂/L)*h z < i z)
  let short := Finset.univ.filter (fun z => h z < L)
  have hB : ∑ z∈badB,h z ≤ H₀/16 := by
    have ht := (bad_mass h b ε hb).trans hunpaired
    change ε*(∑ z∈badB,h z) ≤ ε/16*H₀ at ht
    nlinarith
  have hI : ∑ z∈badI,h z ≤ H₀/16 := by
    have ht := (bad_mass h i (C₂/L) hi).trans hcomparisons
    change (C₂/L)*(∑ z∈badI,h z) ≤ C₂/(16*L)*H₀ at ht
    have he : C₂/(16*L)*H₀=(C₂/L)*(H₀/16) := by ring
    rw [he] at ht
    have hp := div_pos hC₂ hL
    nlinarith
  by_contra hn
  have hc : ∀ z,z∈badB ∨ z∈badI ∨ z∈short := by
    intro z
    by_cases hB : b z ≤ ε*h z
    · by_cases hI : i z ≤ C₂*h z/L
      · have hs : h z < L := by
          by_contra hl
          exact hn ⟨z,le_of_not_gt hl,hupper z,hB,hI⟩
        exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩))
      · right; left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        simpa only [div_mul_eq_mul_div] using lt_of_not_ge hI
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge hB⟩)
  have hsum : (∑ z,h z) ≤ (∑ z∈badB,h z)+(∑ z∈badI,h z)+(∑ z∈short,h z) := by
    rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib,
      ←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    have hc := hc z
    simp only [badB,badI,short,Finset.mem_filter,Finset.mem_univ,true_and] at hc
    rcases hc with hc|hc|hc
    · simp only [ite_eq_left hc]
      have h1 : 0 ≤ if C₂/L*h z < i z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      have h2 : 0 ≤ if h z < L then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      linarith
    · simp only [ite_eq_left hc]
      have h1 : 0 ≤ if ε*h z < b z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      have h2 : 0 ≤ if h z < L then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      linarith
    · simp only [ite_eq_left hc]
      have h1 : 0 ≤ if ε*h z < b z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      have h2 : 0 ≤ if C₂/L*h z < i z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      linarith
  change (∑ z∈short,h z) ≤ H₀/2 at hshort
  linarith

/-- The discarded short exceptional cluster really costs less than half; the
ordinary girth-length boundary is accounted for separately, not silently lost. -/
lemma exceptional_short_cost (h L H₀ : ℝ) (hlen : h < L) (hordinary : h+L ≤ H₀) :
    h < H₀/2 := by linarith

end TorsionFreeZeroDivisors.PlanarLocalization

namespace TorsionFreeZeroDivisors.ClusterLocalization
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)

abbrev graph := PairingClusters.graph (fun x : Position len => x.1)
  C.pairing.partner C.pairing.involutive keep
abbrev Cluster := (graph C keep).ConnectedComponent
local instance : Fintype (Cluster C keep) := Fintype.ofFinite _
def cluster := PairingClusters.cluster (fun x : Position len => x.1)
  C.pairing.partner C.pairing.involutive keep
abbrev belongs (c : Cluster C keep) (t : T) : Prop := cluster C keep t=some c
abbrev localC (c : Cluster C keep) := RestrictComparisons.comparisons C (belongs C keep c)
def mass (c : Cluster C keep) : ℕ := ∑ t∈Finset.univ.filter (belongs C keep c),len t
def bad (c : Cluster C keep) : ℕ :=
  (Finset.univ.filter (PairingClusters.localBad (fun x : Position len => x.1)
    C.pairing.partner C.pairing.involutive keep c)).card
def comparisons [Fintype E] (c : Cluster C keep) : ℕ :=
  Fintype.card {e // RestrictComparisons.Active C (belongs C keep c) e}
def paths (c : Cluster C keep) : Finset T := Finset.univ.filter (belongs C keep c)

omit [Fintype T] in
lemma cluster_exists {t : T} : (∃ c,belongs C keep c t) ↔ keep t :=
  PairingClusters.cluster_exists _ _ _ _
lemma mass_pos (hlen : ∀ t,0<len t) (c : Cluster C keep) : 0 < mass C keep c := by
  obtain ⟨t,ht⟩ := FiniteClusters.block_nonempty (graph C keep) c
  have ht' : belongs C keep c t.val := by
    change PairingClusters.cluster _ _ _ _ t.val=some c
    rw [PairingClusters.cluster_some _ _ _ _ t.property]
    exact congrArg some ((FiniteClusters.mem_block _).mp ht)
  exact Finset.sum_pos' (fun t _ => Nat.zero_le _) ⟨t.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht'⟩,hlen _⟩

lemma mass_sum : (∑ c,mass C keep c)=∑ t∈Finset.univ.filter keep,len t := by
  simp only [mass,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : keep t
  · obtain ⟨c,hc⟩ := (cluster_exists C keep).mpr ht
    change cluster C keep t=some c at hc
    simp [belongs,hc,ht]
  · have hc : cluster C keep t=none := PairingClusters.cluster_none _ _ _ _ ht
    simp [belongs,hc,ht]

lemma mass_original_loss : (∑ t,len t)≤(∑ c,mass C keep c)+∑ t∈Finset.univ.filter (fun t=>¬keep t),len t := by
  rw [mass_sum]
  exact (le_of_eq (Finset.sum_filter_add_sum_filter_not _ _ _).symm)

lemma bad_sum : (∑ c,bad C keep c)≤
    (Finset.univ.filter (fun x : Position len=>C.pairing.partner x=x)).card+
    (Finset.univ.filter (fun x : Position len=>¬keep x.1 ∧ C.pairing.partner x≠x)).card := by
  convert PairingClusters.total_local_bad_bound (fun x : Position len => x.1) C.pairing.partner C.pairing.involutive keep using 1
  · apply Finset.sum_congr (by ext c; simp)
    intro c _
    unfold bad
    congr 1
  · congr 1 <;> congr 1 <;> ext x <;> simp

lemma comparisons_sum [Fintype E] : (∑ c,comparisons C keep c)≤Fintype.card E := by
  simp only [comparisons,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _e : E,1 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hk : keep (C.source e)
      · obtain ⟨c,hc⟩ := (cluster_exists C keep).mpr hk
        change cluster C keep (C.source e)=some c at hc
        calc
          _ ≤ ∑ d : Cluster C keep, if belongs C keep d (C.source e) then 1 else 0 := by
            apply Finset.sum_le_sum
            intro d _
            by_cases h : belongs C keep d (C.source e)
            · simp only [ite_eq_left h]; split_ifs <;> omega
            · simp only [RestrictComparisons.Active,h,false_and,ite_false,le_refl]
          _ = 1 := by simp [belongs,hc]
      · have hc : cluster C keep (C.source e)=none := PairingClusters.cluster_none _ _ _ _ hk
        simp [RestrictComparisons.Active,belongs,hc]
    _ = _ := by simp

/-- The fixed positions in the literal restricted comparison system are exactly
this cluster's old fixed or lost-partner occurrences. -/
def fixedEquiv (c : Cluster C keep) :
    {x : Position (RestrictComparisons.Length (belongs C keep c) (len:=len)) //
      (localC C keep c).pairing.partner x=x} ≃
    {x : Position len // PairingClusters.localBad (fun x : Position len => x.1)
      C.pairing.partner C.pairing.involutive keep c x} where
  toFun x := ⟨RestrictComparisons.embed _ x.val,x.val.1.property,
    (RestrictComparisons.fixed_iff C _ _).mp x.property⟩
  invFun x := by
    have hx : belongs C keep c x.val.1 ∧
        (C.pairing.partner x.val=x.val ∨ ¬belongs C keep c (C.pairing.partner x.val).1) := x.property
    refine ⟨RestrictComparisons.liftPosition _ x.val hx.1,?_⟩
    apply (RestrictComparisons.fixed_iff C _ _).mpr
    simpa only [RestrictComparisons.embed_local] using hx.2
  left_inv x := by rcases x with ⟨⟨⟨t,ht⟩,q⟩,hx⟩; rfl
  right_inv x := by rcases x with ⟨⟨t,q⟩,hx⟩; rfl
lemma fixed_card (c : Cluster C keep) :
    (Finset.univ.filter (fun x => (localC C keep c).pairing.partner x=x)).card=bad C keep c := by
  simpa only [bad,Fintype.card_subtype] using Fintype.card_congr (fixedEquiv C keep c)

lemma local_mass (c : Cluster C keep) :
    (∑ t : {t // belongs C keep c t},len t.val)=mass C keep c := by
  exact (Finset.sum_subtype (Finset.univ.filter (belongs C keep c)) (by intro t; simp) len).symm

lemma short_member {L : ℕ} (c : Cluster C keep) (hc : mass C keep c<L)
    {t : T} (ht : belongs C keep c t) : len t<L := by
  apply lt_of_le_of_lt _ hc
  exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)

/-- With at most one short exceptional piece there is at most one short cluster.
The estimate counts actual retained path lengths, not abstract cluster masses. -/
lemma short_mass {L : ℕ} (root : Option T)
    (ho : ∀ t,root≠some t → L≤len t) :
    (∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c)≤
      ∑ t∈Finset.univ.filter (fun t=>root=some t),len t := by
  simp only [Finset.sum_filter]
  have expand (c : Cluster C keep) :
      (if mass C keep c<L then mass C keep c else 0)=
      ∑ t,if mass C keep c<L then (if belongs C keep c t then len t else 0) else 0 := by
    by_cases h : mass C keep c<L
    · simp only [ite_eq_left h]
      simp only [mass,Finset.sum_filter]
    · simp only [ite_eq_right h,Finset.sum_const_zero]
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  by_cases hr : root=some t
  · rw [ite_eq_left hr]
    by_cases hk : keep t
    · obtain ⟨c,hc⟩ := (cluster_exists C keep).mpr hk
      change cluster C keep t=some c at hc
      simp only [belongs,hc,Option.some.injEq]
      calc
        _ ≤ ∑ d : Cluster C keep,if c=d then len t else 0 := by
          apply Finset.sum_le_sum
          intro d _
          split_ifs <;> omega
        _ = len t := by simp
    · have hc : cluster C keep t=none := PairingClusters.cluster_none _ _ _ _ hk
      simp [belongs,hc]
  · rw [ite_eq_right hr]
    apply Nat.le_zero.mpr
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : mass C keep c<L
    · have hnt : ¬belongs C keep c t := fun h => (not_lt_of_ge (ho t hr)) (short_member C keep c hc h)
      simp only [ite_eq_left hc,ite_eq_right hnt]
    · simp only [ite_eq_right hc]
end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI
