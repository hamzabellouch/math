import OAI.Combinatorics.Coboundary.Mixing
import OAI.Combinatorics.Coboundary.Averaging

namespace OAI

/-!
Local repairs, fat-ladder inequalities, and uniform raw cosystolic expansion.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def linkRestrict (s : Finset V) (g : Finset V → k) (a : Finset V) : k := g (s ∪ a)
def linkLift (s : Finset V) (b : Finset V → k) (t : Finset V) : k :=
  if s ⊆ t then b (t \ s) else 0

def linkNorm (w : Finset V → ℝ) (s : Finset V) (j : ℕ) (f : Finset V → k) : ℝ :=
  ∑ a ∈ level j, if Disjoint s a then atom (fun a => w (s ∪ a)) f a else 0

omit [Fintype V] in
lemma linkLift_support (s : Finset V) (b : Finset V → k) :
    ∀ t, ¬ s ⊆ t → linkLift s b t = 0 := fun _ ht => ite_eq_right ht

omit [Fintype V] in
lemma delta_linkLift {s t : Finset V} (hst : s ⊆ t) (b : Finset V → k) :
    delta (linkLift s b) t = delta b (t \ s) := by
  unfold delta
  calc
    (∑ v ∈ t, linkLift s b (t.erase v)) = ∑ v ∈ t \ s, linkLift s b (t.erase v) := by
      symm
      apply Finset.sum_subset (Finset.sdiff_subset)
      intro v hvt hvs
      apply linkLift_support
      rw [Finset.subset_erase]
      simp only [hst,true_and]
      simpa [hvt] using hvs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvn := (Finset.mem_sdiff.mp hv).2
      rw [linkLift,ite_eq_left (Finset.subset_erase.mpr ⟨hst,hvn⟩),Finset.erase_sdiff_comm]

omit [Fintype V] in
lemma delta_linkRestrict (s : Finset V) (g : Finset V → k)
    (hg : ∀ t, ¬ s ⊆ t → g t = 0) {a : Finset V} (hdis : Disjoint s a) :
    delta (linkRestrict s g) a = delta g (s ∪ a) := by
  have hsd : (s ∪ a) \ s = a := Finset.union_sdiff_cancel_left hdis
  have hs : s ⊆ s ∪ a := Finset.subset_union_left
  have he : delta g (s ∪ a) = ∑ v ∈ a, g ((s ∪ a).erase v) := by
    unfold delta
    symm
    apply Finset.sum_subset (Finset.subset_union_right)
    intro v hv hva
    apply hg
    rw [Finset.subset_erase]
    simp only [hs,true_and]
    exact not_not.mpr ((Finset.mem_union.mp hv).resolve_right hva)
  rw [he]
  apply Finset.sum_congr rfl
  intro v hv
  have hn : v ∉ s := fun h => Finset.disjoint_left.mp hdis h hv
  change g (s ∪ a.erase v) = g ((s∪a).erase v)
  congr 1
  ext u
  simp only [Finset.mem_union,Finset.mem_erase]
  have hu : u ∈ s → u ≠ v := fun hu he => hn (he ▸ hu)
  tauto

lemma starNorm_linkNorm (w : Finset V → ℝ) (s : Finset V) (r : ℕ)
    (hr : s.card ≤ r) (g : Finset V → k) :
    starNorm w r s g = linkNorm w s (r-s.card) (linkRestrict s g) := by
  unfold starNorm starSum linkNorm
  rw [← Finset.sum_filter,← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => s ∪ a)
  · intro a ha
    obtain ⟨ha,hd⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨mem_level.mpr ?_,Finset.subset_union_left⟩
    rw [Finset.card_union_of_disjoint hd,mem_level.mp ha]
    omega
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have h := congrArg (fun t : Finset V => t \ s) he
    simpa only [Finset.union_sdiff_cancel_left ha',Finset.union_sdiff_cancel_left hb'] using h
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    refine ⟨t \ s,Finset.mem_filter.mpr ⟨mem_level.mpr ?_,(Finset.disjoint_left.mpr (fun v hv hvs => (Finset.mem_sdiff.mp hvs).2 hv))⟩,?_⟩
    · rw [Finset.card_sdiff_of_subset hst,mem_level.mp ht]
    · exact Finset.union_sdiff_of_subset hst
  · intro a ha
    rfl

lemma linkNorm_congr (w : Finset V → ℝ) (s : Finset V) (j : ℕ)
    (f g : Finset V → k) (he : ∀ a, a.card = j → Disjoint s a → f a = g a) :
    linkNorm w s j f = linkNorm w s j g := by
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with h
  · rw [atom,atom,he a (mem_level.mp ha) h]
  · rfl

theorem linkCorrection_of_links {w : Finset V → ℝ} {r : ℕ} {C : ℝ}
    (hlocal : ∀ s : Finset V, s.Nonempty → s.card ≤ r →
      ∀ f : Finset V → k, ∃ b : Finset V → k,
        linkNorm w s (r-s.card) (f+delta b) ≤
          C*linkNorm w s (r-s.card+1) (delta f)) : LinkCorrection w r C := by
  intro s hs hr g hg
  obtain ⟨b,hb⟩ := hlocal s hs hr (linkRestrict s g)
  refine ⟨linkLift s b,linkLift_support s b,?_,?_⟩
  · intro he t ht
    by_cases hst : s ⊆ t
    · have hts : t = s := (Finset.eq_of_subset_of_card_le hst (by rw [mem_level.mp ht,he])).symm
      subst t
      rw [delta_linkLift (Finset.Subset.refl _),Finset.sdiff_self]
      simp [delta]
    · unfold delta
      apply Finset.sum_eq_zero
      intro v hv
      exact linkLift_support s b _ (fun h => hst (h.trans (Finset.erase_subset _ _)))
  · rw [starNorm_linkNorm w s r hr,starNorm_linkNorm w s (r+1) (by omega)]
    have hl : linkNorm w s (r-s.card) (linkRestrict s (g+delta (linkLift s b))) =
        linkNorm w s (r-s.card) (linkRestrict s g+delta b) := by
      apply linkNorm_congr
      intro a ha hd
      change g (s∪a)+delta (linkLift s b) (s∪a) = g (s∪a)+delta b a
      rw [delta_linkLift Finset.subset_union_left,Finset.union_sdiff_cancel_left hd]
    have hd : linkNorm w s (r+1-s.card) (linkRestrict s (delta g)) =
        linkNorm w s (r-s.card+1) (delta (linkRestrict s g)) := by
      have he : r+1-s.card = r-s.card+1 := by omega
      rw [he]
      apply linkNorm_congr
      intro a ha hda
      exact (delta_linkRestrict s g hg hda).symm
    rw [hl,hd]
    exact hb

end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
open Cone Averaging
open scoped Pointwise
variable {V : Type} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

def rawNorm (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (f : Finset V → k) : ℝ :=
  ∑ s ∈ level X r, if f s ≠ 0 then (cofaces X N s:ℝ) else 0

lemma rawNorm_nonneg (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (f : Finset V → k) : 0 ≤ rawNorm X N r f := by
  apply Finset.sum_nonneg
  intro s hs
  split_ifs <;> positivity

lemma rawNorm_weight (X : CoboundaryExpanders.InfiniteChains.Complex V) {N r : ℕ} (hr : r ≤ N) (hP : (level X N).Nonempty)
    (f : Finset V → k) :
    rawNorm X N r f = ((N.choose r:ℝ)*(level X N).card)*supportNorm (weight X N r) f := by
  have hd : (N.choose r:ℝ)*(level X N).card ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Nat.choose_pos hr).ne')
      (by exact_mod_cast (Finset.card_pos.mpr hP).ne')
  unfold rawNorm
  calc
    _ = ∑ s ∈ level X r, ((N.choose r:ℝ)*(level X N).card)*
        (if f s = 0 then 0 else weight X N r s) := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hf : f s = 0
      · simp [hf]
      · simp only [hf,ne_eq,not_false_eq_true,ite_true,ite_false,weight,ite_eq_left hs]
        exact (mul_div_cancel₀ _ hd).symm
    _ = ∑ s, ((N.choose r:ℝ)*(level X N).card)*
        (if f s = 0 then 0 else weight X N r s) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s hs hn
      simp [weight,hn]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem raw_correction {G : Type} [Group G] [Fintype G] [MulAction G V]
    {X : CoboundaryExpanders.InfiniteChains.Complex V} {N n r R : ℕ} (hX : Invariant G X) (hP : Pure X N)
    (hTrans : ∀ a b : X.Face N, ∃ g : G, g • a.val = b.val)
    (H : BoundedCone X n R) (hr : r ≤ n) (hrN : r+1 ≤ N) (f : Finset V → k) :
    ∃ b : Finset V → k,
      rawNorm X N r (f+delta b) ≤ (R:ℝ)*(N.choose r)*rawNorm X N (r+1) (delta f) := by
  obtain ⟨b,hb⟩ := weighted_correction hX hP hTrans H hr hrN f
  refine ⟨b,?_⟩
  rw [rawNorm_weight X (by omega) hP.1,rawNorm_weight X hrN hP.1]
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (N.choose r:ℝ)*(level X N).card by positivity)
  change (N.choose r:ℝ) * (level X N).card * supportNorm (weight X N r)
    (fun s => f s + delta b s) ≤ _
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

lemma linkNorm_cofaces (X : CoboundaryExpanders.InfiniteChains.Complex V) {N : ℕ} {s : Finset V} (hs : s ∈ X.faces)
    (hN : s.card ≤ N) (j : ℕ) (f : Finset V → k) :
    FatLadders.linkNorm (fun t => (cofaces X N t:ℝ)) s j f =
      rawNorm (X.faceLink s hs) (N-s.card) j f := by
  have hl : FatLadders.level (V:=V) j = Finset.univ.filter (fun a : Finset V => a.card = j) := by
    ext a; simp [FatLadders.level]
  unfold FatLadders.linkNorm rawNorm level
  rw [hl]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : a.card = j
  · simp only [hc, and_true,ite_true]
    by_cases hd : Disjoint s a
    · rw [ite_eq_left hd]
      have he := cofaces_link X hs hN hd
      by_cases hf : a ∈ (X.faceLink s hs).faces
      · simp only [ite_eq_left hf,FatLadders.atom]
        rw [←he]
        by_cases hz : f a = 0 <;> simp [hz]
      · have hz := cofaces_zero_of_not_face (X.faceLink s hs) (N-s.card) hf
        simp only [FatLadders.atom]
        rw [←he,hz]
        simp [hf]
    · have hf : a ∉ (X.faceLink s hs).faces := fun h => hd h.1
      simp [hd,hf]
  · simp [hc]

end FiniteWeights
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces

section
open InfiniteChains
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

omit [DecidableEq I] in
lemma IsFace.type_injective {s : Finset (Vertex H)} (hs : IsFace H s) :
    Set.InjOn Sigma.fst (s : Set (Vertex H)) := by
  obtain ⟨g,A,rfl⟩ := hs
  intro x hx y hy hxy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  change i=j at hxy
  subst j
  rfl

def faceStabilizer (s : Finset (Vertex H)) : Subgroup G := MulAction.stabilizer G s

omit [DecidableEq I] in
lemma faceStabilizer_fixes (s : Finset (Vertex H)) (g : faceStabilizer H s) :
    (g.val:G) • s = s := g.property

lemma facesLinkInvariant {s : Finset (Vertex H)} (hs : IsFace H s)
    (g : faceStabilizer H s) {a : Finset (Vertex H)}
    (ha : a ∈ ((complex H).faceLink s hs).faces) :
    g • a ∈ ((complex H).faceLink s hs).faces := by
  change Disjoint s ((g.val:G) • a) ∧ IsFace H (s ∪ (g.val:G) • a)
  have hg := faceStabilizer_fixes H s g
  constructor
  · have hd : Disjoint ((g.val:G) • s) ((g.val:G) • a) := by
      simp only [Finset.smul_finset_def]
      exact (Finset.disjoint_image (f:=fun v : Vertex H => (g.val:G) • v)
        (MulAction.injective (β:=Vertex H) (g.val:G))).mpr ha.1
    simpa only [hg] using hd
  · have hh := ha.2.smul H (g.val:G)
    rw [Finset.smul_finset_union,hg] at hh
    exact hh

lemma facesLinkTransitive [Fintype I] {s : Finset (Vertex H)} (hs : IsFace H s)
    {a b : Finset (Vertex H)} (ha : a ∈ ((complex H).faceLink s hs).faces)
    (hb : b ∈ ((complex H).faceLink s hs).faces)
    (hsc : s.card ≤ Fintype.card I)
    (hac : a.card = Fintype.card I-s.card)
    (hbc : b.card = Fintype.card I-s.card) :
    ∃ g : faceStabilizer H s, g • a = b := by
  have hsa : (s∪a).card = Fintype.card I := by
    rw [Finset.card_union_of_disjoint ha.1,hac,Nat.add_sub_of_le hsc]
  have hsb : (s∪b).card = Fintype.card I := by
    rw [Finset.card_union_of_disjoint hb.1,hbc,Nat.add_sub_of_le hsc]
  obtain ⟨g,hg⟩ := chamber_transitive H ha.2 hb.2 hsa hsb
  have hpoint (v : Vertex H) (hv : v ∈ s) : g • v = v := by
    apply hb.2.type_injective H
    · rw [←hg]
      exact Finset.mem_smul_finset.mpr ⟨v,Finset.mem_union_left a hv,rfl⟩
    · exact Finset.mem_union_left b hv
    · rfl
  have hfix : g • s = s := by
    change s.image (fun v => g • v) = s
    calc
      _ = s.image id := Finset.image_congr hpoint
      _ = s := Finset.image_id
  have hdis : Disjoint s (g • a) := by
    rw [←hfix]
    simp only [Finset.smul_finset_def]
    exact (Finset.disjoint_image (f:=fun v : Vertex H => g • v)
      (MulAction.injective (β:=Vertex H) g)).mpr ha.1
  refine ⟨⟨g,hfix⟩,?_⟩
  change g • a = b
  rw [Finset.smul_finset_union,hfix] at hg
  have he := congrArg (fun t : Finset (Vertex H) => t \ s) hg
  simpa only [Finset.union_sdiff_cancel_left hdis,Finset.union_sdiff_cancel_left hb.1] using he

end

open InfiniteChains FiniteWeights Cone
open scoped Pointwise
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I] (H : I → Subgroup G)
omit [Fintype G] [DecidableEq I] [Fintype I] in
lemma delta_agrees (g : Finset (Vertex H) → k) : Cone.delta g = FatLadders.delta g := by
  funext s
  exact Cone.delta_eq_sum g s

theorem linkCorrection_of_cones {R r : ℕ}
    (hR : ProperLinkCones (complex H) (Fintype.card I) R) (hr : r < Fintype.card I) :
    FatLadders.LinkCorrection (fun t => (cofaces (complex H) (Fintype.card I) t : ℝ)) r
      ((R:ℝ)*2^(Fintype.card I)) := by
  apply FatLadders.linkCorrection_of_links
  intro s hne hsr f
  by_cases hs : s ∈ (complex H).faces
  · let : Fintype (faceStabilizer H s) := Fintype.ofFinite _
    have hsc : s.card ≤ Fintype.card I := by omega
    have hlocal := hR s hne hs (by omega)
    have hp := pure_link (finite_pure H) hs
    have hi : Invariant (faceStabilizer H s) ((complex H).faceLink s hs) :=
      fun g a ha => facesLinkInvariant H hs g ha
    have ht : ∀ a b : ((complex H).faceLink s hs).Face (Fintype.card I-s.card),
        ∃ g : faceStabilizer H s, g • a.val = b.val := by
      intro a b
      exact facesLinkTransitive H hs a.property.1 b.property.1 hsc a.property.2 b.property.2
    obtain ⟨b,hb⟩ := raw_correction hi hp ht hlocal.some
      (show r-s.card ≤ Fintype.card I-s.card-1 by omega)
      (show r-s.card+1 ≤ Fintype.card I-s.card by omega) f
    refine ⟨b,?_⟩
    rw [linkNorm_cofaces (complex H) hs hsc,linkNorm_cofaces (complex H) hs hsc]
    rw [delta_agrees H b,delta_agrees H f] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (rawNorm_nonneg _ _ _ _)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg R)
    have hc := Nat.choose_le_two_pow (Fintype.card I-s.card) (r-s.card)
    have he : 2^(Fintype.card I-s.card) ≤ 2^(Fintype.card I) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    exact_mod_cast hc.trans he
  · have hz (a : Finset (Vertex H)) : cofaces (complex H) (Fintype.card I) (s∪a) = 0 :=
      cofaces_zero_of_not_face _ _ (fun ha => hs ((complex H).downward ha Finset.subset_union_left))
    refine ⟨0,?_⟩
    simp [FatLadders.linkNorm,FatLadders.atom,hz]

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains FiniteWeights TypedCosetFaces

theorem uniform_actual_linkCorrection (n : ℕ) (hn : 1 ≤ n) :
    ∃ Q C : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m →
      letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
      ∀ r : ℕ, r < n+1 →
      FatLadders.LinkCorrection
        (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) t : ℝ)) r C := by
  obtain ⟨Q,R,h⟩ := uniform_actual_proper_link_cones n hn
  refine ⟨Q,R*2^(n+1),?_⟩
  intro p hp hq m hm
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  intro r hr
  have hh := linkCorrection_of_cones (reducedLocalGroup p n hn m)
    (by simpa only [Fintype.card_fin] using h p hp hq m hm)
    (by simpa only [Fintype.card_fin] using hr)
  simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
@[simp] lemma delta_zero : delta (0 : Finset V → k) = 0 := by funext s; simp [delta]
omit [Fintype V] in
@[simp] lemma delta_add (f g : Finset V → k) : delta (f+g) = delta f + delta g := by
  funext s
  simp [delta,Finset.sum_add_distrib]

omit [Fintype V] in
lemma delta_insert (f : Finset V → k) (v : V) (s : Finset V) (hv : v ∉ s) :
    delta f (insert v s) = f s + delta (fun t => f (insert v t)) s := by
  unfold delta
  rw [Finset.sum_insert hv,Finset.erase_insert hv]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.erase_insert_of_ne (by intro e; subst v; exact hv hx)]

omit [Fintype V] in
@[simp] theorem delta_delta (f : Finset V → k) : delta (delta f) = 0 := by
  funext s
  change delta (delta f) s = 0
  induction s using Finset.induction_on generalizing f with
  | empty => simp [delta]
  | @insert v s hv ih =>
      rw [delta_insert _ v s hv]
      have he : delta (fun t => delta f (insert v t)) s =
          delta f s + delta (delta (fun t => f (insert v t))) s := by
        unfold delta
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        exact delta_insert f v (s.erase x) (fun h => hv (Finset.mem_of_mem_erase h))
      rw [he,ih]
      simp [CharTwo.add_self_eq_zero]

omit [Fintype V] in
lemma delta_support {s : Finset V} {f : Finset V → k}
    (hf : ∀ t, ¬s ⊆ t → f t = 0) : ∀ t, ¬s ⊆ t → delta f t = 0 := by
  intro t ht
  apply Finset.sum_eq_zero
  intro x hx
  exact hf _ (fun h => ht (h.trans (Finset.erase_subset _ _)))

omit [DecidableEq V] in
@[simp] lemma norm_zero (w : Finset V → ℝ) (r) : norm w r 0 = 0 := by simp [norm,atom]

omit [DecidableEq V] in
lemma norm_add_le {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r) (f g : Finset V → k) :
    norm w r (f+g) ≤ norm w r f + norm w r g := by
  rw [norm,norm,norm,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun s _ => atom_add_le hw f g s)

def WeightedEq (w : Finset V → ℝ) (r : ℕ) (f g : Finset V → k) : Prop :=
  ∀ s ∈ level r, w s ≠ 0 → f s = g s

omit [DecidableEq V] in
lemma WeightedEq.atom_eq {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) {s} (hs : s ∈ level r) : atom w f s = atom w g s := by
  by_cases hz : w s = 0
  · simp [atom,hz]
  · rw [atom,atom,h s hs hz]

omit [DecidableEq V] in
lemma WeightedEq.norm_eq {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) : norm w r f = norm w r g :=
  Finset.sum_congr rfl (fun _ hs => h.atom_eq hs)

lemma WeightedEq.starNorm_eq {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) (s) : starNorm w r s f = starNorm w r s g := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h.atom_eq ht]

omit [DecidableEq V] in
lemma WeightedEq.add_right {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) (b : Finset V → k) : WeightedEq w r (f+b) (g+b) := by
  intro s hs hw
  simp only [Pi.add_apply,h s hs hw]

lemma WeightedEq.delta_eq {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    {f g : Finset V → k} (h : WeightedEq w r f g) : WeightedEq w (r+1) (delta f) (delta g) := by
  intro s hs hws
  apply Finset.sum_congr rfl
  intro x hx
  have he : s.erase x ∈ level r := by
    apply mem_level.mpr
    rw [Finset.card_erase_of_mem hx,mem_level.mp hs]
    omega
  apply h _ he
  intro hz
  exact hws (hw.weight_eq_zero_of_base (Finset.erase_subset x s) hz)

lemma WeightedEq.nearMinimal {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) {ε : ℝ} (hf : NearMinimal w r ε f) : NearMinimal w r ε g := by
  intro s hs hsr b hb
  have hh := hf s hs hsr b hb
  rwa [h.starNorm_eq s,(h.add_right (delta b)).starNorm_eq s] at hh

lemma fatFamily_top_eq {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    WeightedEq w r f (indicator (fatFamily w N r θ f)) := by
  intro s hs hws
  have hpos := lt_of_le_of_ne (hw s) (Ne.symm hws)
  have hc := mem_level.mp hs
  simp only [indicator,fatFamily,hc,le_refl,true_and,Nat.sub_self,fatAt,hpos,and_true]
  have htwo : ∀ x : k, x = 0 ∨ x = 1 := by decide
  rcases htwo (f s) with hf | hf <;> simp [hf]

theorem small_cochain_expansion {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) (hw0 : w ∅ = 1) {η lam ε C : ℝ}
    (hη : 0 < η) (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hC : 0 < C)
    (hεsmall : ε*(2:ℝ)^r ≤ 1/2)
    (hηsmall : C*(2:ℝ)^(r+1)*((2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*(2*η)) ≤ 1/4)
    (hbudget : ∀ a ≤ r, lam*fatBudget N η a ≤ η)
    (hmix : LocalMixing w N lam) (hcor : LinkCorrection w r C)
    (f : Finset V → k) (hmin : NearMinimal w r ε f)
    (hsmall : norm w r f < 1/fatBudget N η r) :
    (1/4:ℝ)*norm w r f ≤ C*(2:ℝ)^(r+1)*norm w (r+1) (delta f) := by
  let F := fatFamily w N r (fatThreshold N r η) f
  have hEq := fatFamily_top_eq hw.nonneg N r (fatThreshold N r η) f
  have hF : ¬ F ∅ := fat_empty_false hw hN hrN hw0 hη f hsmall
  have hbad : C*(2:ℝ)^(r+1)*norm w (r+1) (indicator (fun T => ¬NoBad F T)) ≤
      (1/4:ℝ)*norm w r (indicator F) := by
    have hd := fat_degeneracy_bound hw hN hrN hη hlam hbudget hmix f (r+1)
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ C*(2:ℝ)^(r+1) by positivity)
    have hh' := mul_le_mul_of_nonneg_right hηsmall (norm_nonneg hw.nonneg r f)
    rw [hEq.norm_eq] at hh'
    exact hh.trans (by simpa only [← mul_assoc,hEq.norm_eq] using hh')
  have hh := small_set_expansion hw.nonneg hF hε hC hεsmall (hEq.nearMinimal hmin) hcor hbad
  rwa [← hEq.norm_eq,← (hEq.delta_eq hw).norm_eq] at hh

end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.LocalRepair

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

structure Size (A : Type*) [AddCommGroup A] where
  val : A → ℝ
  zero : val 0 = 0
  nonneg : ∀ a, 0 ≤ val a
  triangle : ∀ a b, val (a+b) ≤ val a + val b

instance : CoeFun (Size A) (fun _ => A → ℝ) := ⟨Size.val⟩

theorem repair [Fintype A] (na : Size A) (nb : Size B) (δ : A →+ B)
    (P : B → Prop) {C : ℝ} (_ : 0 ≤ C)
    (hstep : ∀ a : A, ¬ P (δ a) → ∃ u : A,
      nb (δ (a+u)) < nb (δ a) ∧
      na u ≤ C * (nb (δ a) - nb (δ (a+u)))) (f : A) :
    ∃ h : A, P (δ (f+h)) ∧ nb (δ (f+h)) ≤ nb (δ f) ∧
      na h ≤ C * (nb (δ f) - nb (δ (f+h))) := by
  classical
  let S : Finset A := Finset.univ.filter (fun h =>
    na h ≤ C * (nb (δ f) - nb (δ (f+h))))
  have hz : (0 : A) ∈ S := by simp [S,na.zero]
  obtain ⟨h,hh,hmin⟩ := S.exists_min_image (fun h => nb (δ (f+h))) ⟨0,hz⟩
  have hbound : na h ≤ C * (nb (δ f) - nb (δ (f+h))) := (Finset.mem_filter.mp hh).2
  refine ⟨h,?_,by simpa only [add_zero] using hmin 0 hz,hbound⟩
  by_contra hp
  obtain ⟨u,hu,hcost⟩ := hstep (f+h) hp
  have hmem : h+u ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    calc
      na (h+u) ≤ na h + na u := na.triangle h u
      _ ≤ C * (nb (δ f) - nb (δ (f+h))) +
          C * (nb (δ (f+h)) - nb (δ ((f+h)+u))) := add_le_add hbound hcost
      _ = C * (nb (δ f) - nb (δ (f+(h+u)))) := by rw [add_assoc]; ring
  have hcontra := hmin (h+u) hmem
  rw [← add_assoc] at hcontra
  exact (not_lt_of_ge hcontra) hu

theorem cosystolic_correction [Fintype A] (na : Size A) (nb : Size B)
    (δ : A →+ B) (P : B → Prop) {C μ : ℝ} (hC : 0 ≤ C) (hμ : 0 < μ)
    (hstep : ∀ a : A, ¬ P (δ a) → ∃ u : A,
      nb (δ (a+u)) < nb (δ a) ∧
      na u ≤ C * (nb (δ a) - nb (δ (a+u))))
    (hsmall : ∀ a : A, P (δ a) → nb (δ a) < μ → δ a = 0)
    (hunit : ∀ a : A, na a ≤ 1)
    (f : A) :
    ∃ h : A, δ (f+h) = 0 ∧ na h ≤ max C (1/μ) * nb (δ f) := by
  by_cases hf : nb (δ f) < μ
  · obtain ⟨h,hp,hdecrease,hbound⟩ := repair na nb δ P hC hstep f
    have hz := hsmall (f+h) hp (hdecrease.trans_lt hf)
    refine ⟨h,hz,?_⟩
    rw [hz,nb.zero,sub_zero] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (nb.nonneg _))
  · refine ⟨-f,by simp,?_⟩
    calc
      na (-f) ≤ 1 := hunit _
      _ ≤ (1/μ) * nb (δ f) := by
        have hh : μ ≤ nb (δ f) := le_of_not_gt hf
        have hd := div_le_div_of_nonneg_right hh hμ.le
        simpa [div_self (ne_of_gt hμ),div_eq_mul_inv,mul_comm] using hd
      _ ≤ max C (1/μ) * nb (δ f) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (nb.nonneg _)

end CoboundaryExpanders.LocalRepair

namespace CoboundaryExpanders.FatLadders

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma support_starNorm {w : Finset V → ℝ} {r : ℕ} {s : Finset V} {f : Finset V → k}
    (hf : ∀ t, ¬s ⊆ t → f t = 0) : starNorm w r s f = norm w r f := by
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : s ⊆ t
  · exact ite_eq_left hs
  · simp [hs,atom,hf t hs]

lemma local_global_difference (w : Finset V → ℝ) (r : ℕ) (s : Finset V)
    (f g : Finset V → k) (hg : ∀ t, ¬s ⊆ t → g t = 0) :
    norm w r f - norm w r (f+g) = starNorm w r s f - starNorm w r s (f+g) := by
  unfold norm starNorm starSum
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : s ⊆ t
  · simp [hs]
  · simp [hs,atom,hg t hs]

theorem nearMinimal_repair_step {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {r : ℕ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hcor : LinkCorrection w (r-1) C) (f : Finset V → k)
    (hmin : ¬NearMinimal w r ε f) :
    ∃ u : Finset V → k, norm w r (f+delta u) < norm w r f ∧
      norm w (r-1) u ≤ (2*C/ε)*(norm w r f-norm w r (f+delta u)) := by
  unfold NearMinimal at hmin
  push Not at hmin
  obtain ⟨s,hs,hsr,b,hb,hdec⟩ := hmin
  obtain ⟨c,hc,htop,hcost⟩ := hcor s hs (by omega) b hb
  let u := b+delta c
  have hdu : delta u = delta b := by simp [u]
  have hu : ∀ t, ¬s ⊆ t → u t = 0 := by
    intro t ht
    simp [u,hb t ht,delta_support hc t ht]
  have hd : ∀ t, ¬s ⊆ t → delta b t = 0 := delta_support hb
  have hdiff := local_global_difference w r s f (delta b) hd
  have hm := starNorm_nonneg hw r s f
  have hm' := starNorm_nonneg hw r s (f+delta b)
  have hpositive : 0 < starNorm w r s f := by nlinarith
  have hstrict : norm w r (f+delta b) < norm w r f := by nlinarith
  have hid : delta b = f+(f+delta b) := by
    funext t
    simp only [Pi.add_apply,← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  have htriangle : starNorm w r s (delta b) ≤
      starNorm w r s f+starNorm w r s (f+delta b) := by
    conv_lhs => rw [hid]
    exact starNorm_add_le hw r s f (f+delta b)
  have hrone : r-1+1 = r := by have := hs.card_pos; omega
  rw [hrone,support_starNorm hu] at hcost
  refine ⟨u,by rwa [hdu],?_⟩
  rw [hdu]
  calc
    norm w (r-1) u ≤ C*starNorm w r s (delta b) := hcost
    _ ≤ C*(starNorm w r s f+starNorm w r s (f+delta b)) :=
      mul_le_mul_of_nonneg_left htriangle hC
    _ ≤ 2*C*starNorm w r s f := by nlinarith
    _ ≤ (2*C/ε)*(norm w r f-norm w r (f+delta b)) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hε).mpr
      have hsmall : ε*starNorm w r s f ≤ norm w r f-norm w r (f+delta b) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2*C by positivity)]

def normSize (w : Finset V → ℝ) (hw : ∀ s, 0 ≤ w s) (r : ℕ) :
    LocalRepair.Size (Finset V → k) where
  val := norm w r
  zero := norm_zero w r
  nonneg := norm_nonneg hw r
  triangle := norm_add_le hw r

def deltaHom : (Finset V → k) →+ (Finset V → k) where
  toFun := delta
  map_zero' := delta_zero
  map_add' := delta_add

theorem repair_coboundary {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {r : ℕ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hcor : LinkCorrection w (r-1) C) (f : Finset V → k) :
    ∃ h : Finset V → k, NearMinimal w r ε (delta (f+h)) ∧
      norm w r (delta (f+h)) ≤ norm w r (delta f) ∧
      norm w (r-1) h ≤ (2*C/ε)*(norm w r (delta f)-norm w r (delta (f+h))) := by
  apply LocalRepair.repair (normSize w hw (r-1)) (normSize w hw r) deltaHom
    (NearMinimal w r ε) (div_nonneg (by positivity) hε.le) _ f
  intro a ha
  obtain ⟨u,hdec,hcost⟩ := nearMinimal_repair_step hw hε hC hcor (delta a) ha
  refine ⟨u,?_,?_⟩
  · change norm w r (delta (a+u)) < norm w r (delta a)
    simpa only [delta_add] using hdec
  · change norm w (r-1) u ≤ (2*C/ε)*(norm w r (delta a)-norm w r (delta (a+u)))
    simpa only [delta_add] using hcost

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma norm_le_choose {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (hw0 : w ∅ = 1) (r : ℕ) (f : Finset V → k) :
    norm w r f ≤ (Nat.choose N r : ℝ) := by
  calc
    norm w r f ≤ ∑ t ∈ level r, w t := Finset.sum_le_sum (fun t _ => atom_le_weight hw.nonneg f t)
    _ = starSum r ∅ w := by simp [starSum]
    _ = _ := by rw [hw.balance ∅ r (by simp)]; simp [hw0]

theorem cosystolic_from_local {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) (hw0 : w ∅ = 1) {η lam ε C : ℝ}
    (hη : 0 < η) (hlam : 0 ≤ lam) (hε : 0 < ε) (hC : 0 < C)
    (hεsmall : ε*(2:ℝ)^r ≤ 1/2)
    (hηsmall : C*(2:ℝ)^(r+1)*((2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*(2*η)) ≤ 1/4)
    (hbudget : ∀ a ≤ r, lam*fatBudget N η a ≤ η)
    (hmix : LocalMixing w N lam) (hcor : LinkCorrection w r C)
    (hcor' : LinkCorrection w (r-1) C) (f : Finset V → k) :
    ∃ h : Finset V → k, norm w r (delta (f+h)) = 0 ∧
      norm w (r-1) h ≤
        (1+2*C/ε+(Nat.choose N (r-1):ℝ)*fatBudget N η r)*norm w r (delta f) := by
  let μ := 1/fatBudget N η r
  have hμ : 0 < μ := one_div_pos.mpr (fatBudget_pos hN hη r)
  have hC0 : 0 ≤ 2*C/ε := div_nonneg (by positivity) hε.le
  have hB0 : 0 ≤ (Nat.choose N (r-1):ℝ)*fatBudget N η r :=
    mul_nonneg (Nat.cast_nonneg _) (fatBudget_pos hN hη r).le
  by_cases hf : norm w r (delta f) < μ
  · obtain ⟨h,hmin,hdecrease,hcost⟩ := repair_coboundary hw.nonneg hε hC.le hcor' f
    have hs := small_cochain_expansion hw hN hrN hw0 hη hlam hε.le hC hεsmall hηsmall
      hbudget hmix hcor (delta (f+h)) hmin (hdecrease.trans_lt hf)
    rw [delta_delta,norm_zero,mul_zero] at hs
    have hz : norm w r (delta (f+h)) = 0 := by
      have hn := norm_nonneg hw.nonneg r (delta (f+h))
      linarith
    refine ⟨h,hz,?_⟩
    rw [hz,sub_zero] at hcost
    apply hcost.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg hw.nonneg r (delta f))
    linarith
  · refine ⟨-f,by simp,?_⟩
    have hbig : μ ≤ norm w r (delta f) := le_of_not_gt hf
    have hbound := mul_le_mul_of_nonneg_left hbig hB0
    have hident : (Nat.choose N (r-1):ℝ)*fatBudget N η r*μ = (Nat.choose N (r-1):ℝ) := by
      dsimp [μ]
      field_simp [ne_of_gt (fatBudget_pos hN hη r)]
    rw [hident] at hbound
    calc
      norm w (r-1) (-f) ≤ (Nat.choose N (r-1):ℝ) := norm_le_choose hw hw0 _ _
      _ ≤ (Nat.choose N (r-1):ℝ)*fatBudget N η r*norm w r (delta f) := hbound
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg hw.nonneg r (delta f))
        linarith

theorem uniform_cosystolic_from_local (N r : ℕ) (hN : 0 < N) (hrN : r ≤ N)
    (C : ℝ) (hC : 0 < C) :
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → w ∅ = 1 →
      LocalMixing w N lam → LinkCorrection w r C → LinkCorrection w (r-1) C →
      ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
  let A : ℝ := C*(2:ℝ)^(r+1)*(2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let η : ℝ := 1/(4*(A+1))
  have hden : 0 < 4*(A+1) := by linarith
  have hη : 0 < η := one_div_pos.mpr hden
  have hηsmall : C*(2:ℝ)^(r+1)*((2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*(2*η)) ≤ 1/4 := by
    have hh : A*η ≤ 1/4 := by
      dsimp [η]
      rw [mul_one_div]
      apply (div_le_iff₀ hden).mpr
      linarith
    convert hh using 1
    dsimp [A]
    ring
  let ε : ℝ := 1/(2*(2:ℝ)^r)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsmall : ε*(2:ℝ)^r ≤ 1/2 := by dsimp [ε]; field_simp; norm_num
  obtain ⟨lam,hlam,hbudget⟩ := exists_mixing_tolerance N r hN hη
  let K : ℝ := 1+2*C/ε+(Nat.choose N (r-1):ℝ)*fatBudget N η r
  have hK : 0 < K := by
    have hb := fatBudget_pos hN hη r
    dsimp [K]
    positivity
  refine ⟨lam,K,hlam,hK,?_⟩
  intro V _ _ w hw hw0 hmix hcor hcor' f
  exact cosystolic_from_local hw hN hrN hw0 hη hlam.le hε hC hεsmall hηsmall hbudget
    hmix hcor hcor' f

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
lemma atom_scale (w : Finset V → ℝ) (a : ℝ) (f : Finset V → k) (s) :
    atom (fun t => a*w t) f s = a*atom w f s := by
  unfold atom
  split_ifs <;> simp
omit [DecidableEq V] in
lemma norm_scale (w : Finset V → ℝ) (a : ℝ) (r) (f : Finset V → k) :
    norm (fun t => a*w t) r f = a*norm w r f := by
  simp only [norm,atom_scale,Finset.mul_sum]
lemma starSum_scale (w : Finset V → ℝ) (a : ℝ) (r s) :
    starSum r s (fun t => a*w t) = a*starSum r s w := by
  simp only [starSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp
lemma starNorm_scale (w : Finset V → ℝ) (a : ℝ) (r s) (f : Finset V → k) :
    starNorm (fun t => a*w t) r s f = a*starNorm w r s f := by
  unfold starNorm starSum
  simp only [atom_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp
lemma collisionMass_scale (w : Finset V → ℝ) (a : ℝ) (F : Finset V → Prop) (s) :
    collisionMass (fun t => a*w t) F s = a*collisionMass w F s := by
  simp only [collisionMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp
lemma Balanced.scale {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {a : ℝ} (ha : 0 ≤ a) : Balanced (fun t => a*w t) N := by
  refine ⟨fun s => mul_nonneg ha (hw.nonneg s),fun s hs => by rw [hw.vanish s hs,mul_zero],?_⟩
  intro s r hr
  rw [starSum_scale,hw.balance s r hr]
  ring
lemma LinkCorrection.scale {w : Finset V → ℝ} {r : ℕ} {C a : ℝ}
    (hc : LinkCorrection w r C) (ha : 0 ≤ a) : LinkCorrection (fun t => a*w t) r C := by
  intro s hs hsr g hg
  obtain ⟨b,hb,he,hbound⟩ := hc s hs hsr g hg
  refine ⟨b,hb,he,?_⟩
  rw [starNorm_scale,starNorm_scale,mul_left_comm C a]
  exact mul_le_mul_of_nonneg_left hbound ha
lemma LinkCorrection.mono {w : Finset V → ℝ} (hw : ∀s,0≤w s)
    {r : ℕ} {C D : ℝ} (hc : LinkCorrection w r C) (hCD : C ≤ D) : LinkCorrection w r D := by
  intro s hs hsr g hg
  obtain ⟨b,hb,he,hbound⟩ := hc s hs hsr g hg
  exact ⟨b,hb,he,hbound.trans (mul_le_mul_of_nonneg_right hCD (starNorm_nonneg hw _ _ _))⟩
lemma LocalMixing.scale {w : Finset V → ℝ} {N : ℕ} {lam a : ℝ}
    (hm : LocalMixing w N lam) (ha : 0 < a) : LocalMixing (fun t => a*w t) N lam := by
  intro F s hs t ht hbound
  rw [starNorm_scale] at hbound
  have hb : starNorm w (s.card+1) s (indicator F) ≤ t*(N-s.card:ℕ)*w s := by
    apply (mul_le_mul_iff_right₀ ha).mp
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound
  have h := mul_le_mul_of_nonneg_left (hm F s hs t ht hb) ha.le
  rw [collisionMass_scale,starNorm_scale]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h
lemma LocalMixing.mono {w : Finset V → ℝ} (hw : ∀s,0≤w s)
    {N : ℕ} {lam mu : ℝ} (hm : LocalMixing w N lam) (hlm : lam ≤ mu) :
    LocalMixing w N mu := by
  intro F s hs t ht hbound
  apply (hm F s hs t ht hbound).trans
  apply mul_le_mul_of_nonneg_right _ (starNorm_nonneg hw _ _ _)
  exact mul_le_mul_of_nonneg_right (add_le_add_right hlm t) (Nat.cast_nonneg N)

end

theorem uniform_all_cosystolic_from_local (N : ℕ) (hN : 0 < N) (C : ℝ) (hC : 0 < C) :
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → w ∅ = 1 →
      LocalMixing w N lam → (∀ r < N, LinkCorrection w r C) →
      ∀ r < N, ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
  have aux : ∀ m ≤ N, ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → w ∅ = 1 →
      LocalMixing w N lam → (∀ r < N, LinkCorrection w r C) →
      ∀ r < m, ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1,1,by norm_num,by norm_num,?_⟩
      intro V _ _ w hw hw0 hm hc r hr
      omega
    | succ m ih =>
      intro hmN
      obtain ⟨l₀,K₀,hl₀,hK₀,h₀⟩ := ih (by omega)
      obtain ⟨l₁,K₁,hl₁,hK₁,h₁⟩ := uniform_cosystolic_from_local N m hN (by omega) C hC
      refine ⟨min l₀ l₁,max K₀ K₁,lt_min hl₀ hl₁,hK₀.trans_le (le_max_left _ _),?_⟩
      intro V _ _ w hw hw0 hm hc r hr f
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · obtain ⟨h,hz,hb⟩ := h₀ V w hw hw0 (hm.mono hw.nonneg (min_le_left _ _)) hc r hr f
        exact ⟨h,hz,hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg hw.nonneg r _))⟩
      · obtain ⟨h,hz,hb⟩ := h₁ V w hw hw0 (hm.mono hw.nonneg (min_le_right _ _))
          (hc r (by omega)) (hc (r-1) (by omega)) f
        exact ⟨h,hz,hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg hw.nonneg r _))⟩
  exact aux N le_rfl

theorem uniform_raw_cosystolic_from_local (N : ℕ) (hN : 0 < N) (C : ℝ) (hC : 0 < C) :
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → 0 < w ∅ →
      LocalMixing w N lam → (∀ r < N, LinkCorrection w r C) →
      ∀ r < N, ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
  obtain ⟨lam,K,hlam,hK,hh⟩ := uniform_all_cosystolic_from_local N hN C hC
  refine ⟨lam,K,hlam,hK,?_⟩
  intro V _ _ w hw hw0 hmix hcor r hr f
  have ha : 0 < (w ∅)⁻¹ := inv_pos.mpr hw0
  have hn : (w ∅)⁻¹*w ∅ = 1 := inv_mul_cancel₀ hw0.ne'
  obtain ⟨h,hz,hb⟩ := hh V (fun s => (w ∅)⁻¹*w s) (hw.scale ha.le) hn
    (hmix.scale ha) (fun r hr => (hcor r hr).scale ha.le) r hr f
  simp only [norm_scale] at hz hb
  refine ⟨h,(mul_eq_zero.mp hz).resolve_left ha.ne',?_⟩
  apply (mul_le_mul_iff_right₀ ha).mp
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hb
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.Construction
open InfiniteChains FiniteWeights TypedCosetFaces

theorem uniform_actual_raw_cosystolic (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m →
      letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
      let w := fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) t : ℝ)
      ∀ r : ℕ, r < n+1 → ∀ f : Finset (Vertex (reducedLocalGroup p n (by omega) m)) → ZMod 2,
        ∃ h, FatLadders.norm w r (FatLadders.delta (f+h)) = 0 ∧
          FatLadders.norm w (r-1) h ≤ K * FatLadders.norm w r (FatLadders.delta f) := by
  obtain ⟨Q₀,C,hC⟩ := uniform_actual_linkCorrection n (by omega)
  have hCp : 0 < (C:ℝ)+1 := by positivity
  obtain ⟨lam,K,hlam,hK,hraw⟩ := FatLadders.uniform_raw_cosystolic_from_local (n+1) (by omega) ((C:ℝ)+1) hCp
  obtain ⟨Q₁,hmix⟩ := uniform_actual_mixing n hn hlam
  refine ⟨max Q₀ Q₁,K,hK,?_⟩
  intro p hp hq m hm
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  dsimp only
  have hP := finite_pure (reducedLocalGroup p n (by omega) m)
  rw [Fintype.card_fin] at hP
  apply hraw _ _ (cofaces_balanced _ (n+1))
  · exact_mod_cast (cofaces_pos_iff hP ∅).mpr (TypedCosetFaces.complex _).empty_mem
  · exact hmix p hp ((le_max_right _ _).trans_lt hq) m hm
  · intro r hr
    exact (hC p hp ((le_max_left _ _).trans_lt hq) m hm r hr).mono
      (fun s => Nat.cast_nonneg _) (by linarith)
end CoboundaryExpanders.Construction

end

end OAI
