import OAI.Combinatorics.ContingencyTables.Transport.PairedComplement

namespace OAI

/-!
# Two-lift transversal variance

The adaptive signed-transport proof from paper 200-02, with its comparison
factor q². The transport weight has addition signatures in complementary
coordinates; the other lift has addition signatures in the original
coordinates. Complement identities, rather than an interchange of those
two signature roles, supply the defect score inequalities.
-/

namespace ContingencyTables.ObservableVariance

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction RecursiveSignedTransport DegreeCompletion PairedComplement

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma choiceVertices_plain_node (gs ps : List (Γ × Γ)) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) (S : Set Γ) (hS : S ∈ choiceVertices ps A) :
    PlainState gs S := by
  have hfresh := hnode.2.1.mono Set.subset_union_left
  have hs := (mem_choiceVertices_iff ps A S hfresh).mp hS
  have hdis : Disjoint B S := choiceVertices_excluded ps A B S hnode.1
    (fun r hr => by
      have h := hnode.2.1.elements_fresh r hr
      exact ⟨fun hx => h.1 (Or.inr hx), fun hx => h.2 (Or.inr hx)⟩) hS
  intro r hr
  by_cases hm : r ∈ ps
  · exact hs.2.2 r hm
  · exact hnode.2.2.2.single ⟨hs.1, hdis⟩ r hr hm

lemma choiceVertices_defect_node (gs ps : List (Γ × Γ)) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) (p r : Γ × Γ)
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r)
    (S : Set Γ) (hS : S ∈ choiceVertices ((ps.erase p).erase r) (insert r.1 (insert r.2 A))) :
    DefectState gs p r S := by
  let qs := (ps.erase p).erase r
  have hperm : ps.Perm (p::r::qs) := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm (A ∪ B)).mp hnode.2.1
  have hq : SlotsFresh qs (insert r.1 (insert r.2 A)) := by
    apply hh.2.2.2.2.2.2.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_union] at hx ⊢
    tauto
  have hs := (mem_choiceVertices_iff qs _ S hq).mp hS
  have hB : Disjoint B S := choiceVertices_excluded qs _ B S
    (by
      apply Set.disjoint_insert_left.mpr
      refine ⟨fun hx => hh.2.2.2.2.1 (Or.inr (Or.inr (Or.inr hx))), ?_⟩
      apply Set.disjoint_insert_left.mpr
      exact ⟨fun hx => hh.2.2.2.2.2.1 (Or.inr (Or.inr (Or.inr hx))), hnode.1⟩)
    (fun t ht => by
      have h := hh.2.2.2.2.2.2.elements_fresh t ht
      exact ⟨fun hx => h.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))),
        fun hx => h.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx)))))⟩) hS
  have hep : PairEmpty p S := by
    have hn (x : Γ) (hxA : x ∉ A) (hxr₁ : x ≠ r.1) (hxr₂ : x ≠ r.2)
        (hxq : x ∉ pairSupport qs) : x ∉ S := by
      intro hx
      have := hs.2.1 hx
      simp only [Set.mem_union, Set.mem_insert_iff] at this
      tauto
    have hr₁ := hh.2.2.2.2.1
    have hr₂ := hh.2.2.2.2.2.1
    have hqd := hh.2.2.2.2.2.2.support_disjoint
    constructor
    · apply hn p.1 (fun h => hh.2.1 (Or.inl h))
      · intro h; exact hr₁ (Or.inl h.symm)
      · intro h; exact hr₂ (Or.inl h.symm)
      · intro h; exact Set.disjoint_left.mp hqd h (Or.inr (Or.inr (Or.inl rfl)))
    · apply hn p.2 (fun h => hh.2.2.1 (Or.inl h))
      · intro h; exact hr₁ (Or.inr (Or.inl h.symm))
      · intro h; exact hr₂ (Or.inr (Or.inl h.symm))
      · intro h; exact Set.disjoint_left.mp hqd h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  refine ⟨hnode.2.2.1 p hp, hnode.2.2.1 r hr, hpr, hep,
    ⟨hs.1 (Or.inl rfl), hs.1 (Or.inr (Or.inl rfl))⟩, ?_⟩
  intro t ht htp htr
  by_cases hm : t ∈ ps
  · exact hs.2.2 t ((List.mem_erase_of_ne htr).mpr ((List.mem_erase_of_ne htp).mpr hm))
  · exact hnode.2.2.2.single ⟨fun x hx => hs.1 (Or.inr (Or.inr hx)), hB⟩ t ht hm

lemma slotTotal_node_agreement (gs ps : List (Γ × Γ)) (f g : Set Γ → ℝ)
    (hagree : ∀ S, PlainState gs S → f S = g S) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) : slotTotal ps f A = slotTotal ps g A := by
  have hfr := hnode.2.1.mono Set.subset_union_left
  rw [slotTotal_eq_choice_sum ps A f hfr, slotTotal_eq_choice_sum ps A g hfr]
  exact Finset.sum_congr rfl (fun S hS => hagree S (choiceVertices_plain_node gs ps A B hnode S hS))

lemma slotDefect_node_comparison (gs ps : List (Γ × Γ)) (f g : Set Γ → ℝ) (q : ℝ)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) (p r : Γ × Γ)
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps f A p r ≤ q*slotDefect ps g A p r := by
  let qs := (ps.erase p).erase r
  have hh := (SlotsFresh.perm (slots_perm_two hp hr hpr) (A ∪ B)).mp hnode.2.1
  have hq : SlotsFresh qs (insert r.1 (insert r.2 A)) := by
    apply hh.2.2.2.2.2.2.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_union] at hx ⊢
    tauto
  unfold slotDefect
  rw [slotTotal_eq_choice_sum qs _ f hq, slotTotal_eq_choice_sum qs _ g hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  exact hcompare S (Or.inr ⟨p, r, choiceVertices_defect_node gs ps A B hnode p r hp hr hpr S hS⟩)

lemma complement_global_pair_bound (ps : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S, 0 < g S) (hsig : HasSlotSignature (complementWeight g))
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps g A p r * slotDefect ps g A r p ≤ (slotTotal ps g A)^2 := by
  have hh := complement_defect_pair ps (complementWeight g) (B.ncard + ps.length)
    (fun S _ => hg Sᶜ) (fun S _ => hsig [] S) A B hAB hps hcover rfl p r hp hr hpr
  have hcc : complementWeight (complementWeight g) = g := by
    funext S
    simp [complementWeight]
  rwa [hcc] at hh

lemma complement_global_triple_bound (ps : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S, 0 < g S) (hsig : HasSlotSignature (complementWeight g))
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (p r t : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps g A p r * slotDefect ps g A r t ≤ slotTotal ps g A * slotDefect ps g A p t := by
  have hh := complement_defect_triple ps (complementWeight g) (B.ncard + ps.length)
    (fun S _ => hg Sᶜ) (fun S _ => hsig [] S) A B hAB hps hcover rfl p r t hp hr ht hpr hrt hpt
  have hcc : complementWeight (complementWeight g) = g := by
    funext S
    simp [complementWeight]
  rwa [hcc] at hh

/-- The sink is proved from the second lift's two- and three-pair inequalities;
its raw signature is in the complementary coordinates. -/
lemma twoLift_scores_sink (gs ps : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S, 0 < g S) (hsig : HasSlotSignature (complementWeight g))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (A B : Set Γ) (hnode : VarianceNode gs ps A B) (hne : ps ≠ []) :
    ∃ p ∈ ps, ∀ r ∈ ps, p ≠ r →
      slotDefect ps g A r p * slotDefect gs g ∅ p r ≤ slotTotal ps g A * slotTotal gs g ∅ := by
  let J := {p : Γ × Γ // p ∈ ps}
  have : Nonempty J := by
    obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil ps hne
    exact ⟨⟨p,hp⟩⟩
  have hne' : ∀ p r : J, p ≠ r → p.val ≠ r.val := fun p r h he => h (Subtype.ext he)
  have hglobal : VarianceNode gs gs ∅ ∅ := ⟨by simp, by simpa using hgs,
    fun _ => id, fun r hr hn => False.elim (hn hr)⟩
  have hpfr := hnode.2.1.mono Set.subset_union_left
  obtain ⟨p,hp⟩ := coefficient_scores_sink
    (fun p r : J => slotDefect ps g A r.val p.val)
    (fun p r : J => slotDefect gs g ∅ r.val p.val)
    (slotTotal ps g A) (slotTotal gs g ∅)
    (slotTotal_pos ps g hg A hpfr) (slotTotal_pos gs g hg ∅ hgs)
    (fun p r h => (slotDefect_pos ps g hg A hpfr r p r.property p.property (hne' r p h.symm)).le)
    (fun p r h => (slotDefect_pos gs g hg ∅ hgs r p (hnode.2.2.1 r r.property)
      (hnode.2.2.1 p p.property) (hne' r p h.symm)).le)
    (fun p r h => complement_global_pair_bound ps g hg hsig A B hnode.1 hnode.2.1
      (PairedComplement.VarianceNode.cover hnode hcover) r p r.property p.property (hne' r p h.symm))
    (fun p r h => complement_global_pair_bound gs g hg hsig ∅ ∅ hglobal.1 hglobal.2.1
      (PairedComplement.VarianceNode.cover hglobal hcover) r p (hnode.2.2.1 r r.property) (hnode.2.2.1 p p.property) (hne' r p h.symm))
    (fun p r t h₁ h₂ h₃ => by
      simpa only [mul_comm] using complement_global_triple_bound ps g hg hsig A B hnode.1 hnode.2.1
        (PairedComplement.VarianceNode.cover hnode hcover) t r p t.property r.property p.property
        (hne' t r h₂.symm) (hne' r p h₁.symm) (hne' t p h₃.symm))
    (fun p r t h₁ h₂ h₃ => by
      simpa only [mul_comm] using complement_global_triple_bound gs g hg hsig ∅ ∅ hglobal.1 hglobal.2.1
        (PairedComplement.VarianceNode.cover hglobal hcover) t r p (hnode.2.2.1 t t.property) (hnode.2.2.1 r r.property)
        (hnode.2.2.1 p p.property) (hne' t r h₂.symm) (hne' r p h₁.symm) (hne' t p h₃.symm))
  refine ⟨p.val,p.property,?_⟩
  intro r hr hpr
  exact hp ⟨r,hr⟩ (fun h => hpr (congrArg Subtype.val h))

/-- One transport split costs at most 1+8s q². -/
theorem transport_node_variance_twoLift (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (q : ℝ)
    (hf : ∀ S, 0 < f S) (hSig : HasSlotSignature f)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hWp : W p = 1) (hWd : W d = 1)
    (hsink : ∀ x ∈ slotPunctures ps,
      slotTotal x.2 f (insert p (insert d A))/W x.1.1 ≤
        4*q^2*(slotTotal ps f (insert p A)+slotTotal ps f (insert d A))) :
    let sp := slotTotal ps f (insert p A)
    let sd := slotTotal ps f (insert d A)
    sp*sd/(sp+sd) *
      (slotTotal ps (fun S => f S*H S) (insert p A)/sp -
        slotTotal ps (fun S => f S*H S) (insert d A)/sd)^2 ≤
      (1+8*(ps.length : ℝ)*q^2)*slotGraphEnergy ps f H A (rootEmbedding p d) W := by
  let sp := slotTotal ps f (insert p A)
  let sd := slotTotal ps f (insert d A)
  have hp : 0 < sp := slotTotal_pos ps f hf _ (hps.mono (by
    intro x hx; rcases hx with rfl | hx
    · exact Or.inr ⟨false,rfl⟩
    · exact Or.inl hx))
  have hd : 0 < sd := slotTotal_pos ps f hf _ (hps.mono (by
    intro x hx; rcases hx with rfl | hx
    · exact Or.inr ⟨true,rfl⟩
    · exact Or.inl hx))
  have hpd' : 0 < sp*sd/(sp+sd) := div_pos (mul_pos hp hd) (add_pos hp hd)
  have hsum := list_sum_map_le_const (slotPunctures ps)
    (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1) (4*q^2*(sp+sd)) hsink
  rw [slotPunctures_length] at hsum
  have hcoef : sp*sd/(sp+sd)*rootCoefficient ps f A p d W ≤ 1+8*(ps.length : ℝ)*q^2 := by
    unfold rootCoefficient
    change sp*sd/(sp+sd)*(1/(sp*W p)+1/(sd*W d)+2/(sp*sd)*_) ≤ _
    rw [hWp,hWd,mul_one,mul_one]
    have heq (s : ℝ) : sp*sd/(sp+sd)*(1/sp+1/sd+2/(sp*sd)*s) = 1+2/(sp+sd)*s := by
      field_simp
      ; ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2/(sp+sd) by positivity)
    have heq' : 2/(sp+sd)*((ps.length : ℝ)*(4*q^2*(sp+sd))) = 8*(ps.length : ℝ)*q^2 := by
      field_simp
      ; ring
    rw [heq'] at hh
    linarith
  have hE : 0 ≤ slotGraphEnergy ps f H A (rootEmbedding p d) W := by
    unfold slotGraphEnergy
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro ST hST
    unfold slotEdgeEnergy
    apply mul_nonneg _ (sq_nonneg _)
    apply le_min
    · exact mul_nonneg (missingMultiplier_nonneg ps _ W (fun i => (hW i).le) _ ) (hf _).le
    · exact mul_nonneg (missingMultiplier_nonneg ps _ W (fun i => (hW i).le) _ ) (hf _).le
  have ht := mul_le_mul_of_nonneg_left
    (transport_graph_bound ps f H A p d W hf hSig hpd hpA hdA hps hW hw) hpd'.le
  dsimp only
  exact ht.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcoef hE)

lemma twoLift_variance_node (gs ps : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : ∀ S, 0 < f S) (hg : ∀ S, 0 < g S)
    (hsigf : HasSlotSignature f) (hsigg : HasSlotSignature (complementWeight g))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S)
    (A B : Set Γ) (hnode : VarianceNode gs ps A B) (hne : ps ≠ []) :
    ∃ p qs, ps.Perm (p::qs) ∧ SlotsFresh (p::qs) A ∧
      VarianceNode gs qs (insert p.1 A) (insert p.2 B) ∧
      VarianceNode gs qs (insert p.2 A) (insert p.1 B) ∧
      slotVariance (p::qs) f H A - slotVariance qs f H (insert p.1 A) -
        slotVariance qs f H (insert p.2 A) ≤
        (1+8*(gs.length : ℝ)*q^2)*restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
  obtain ⟨p,hp,hsink⟩ := twoLift_scores_sink gs ps g hg hsigg hgs hcover A B hnode hne
  let qs := ps.erase p
  have hperm : ps.Perm (p::qs) := List.perm_cons_erase hp
  have hnode' := hnode.perm hperm
  have hfr := hnode'.2.1
  have hfrA : SlotsFresh (p::qs) A := hfr.mono Set.subset_union_left
  have hps : SlotsFresh qs (A ∪ Set.range (rootEmbedding p.1 p.2)) :=
    hfrA.2.2.2.mono (by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · exact Or.inr (Or.inr hx)
      · cases i <;> simp [rootEmbedding])
  let W := pairMultiplier qs (w p)
  have hW : ∀ x, 0 < W x := pairMultiplier_pos qs (w p) (hw p)
  have hws : ∀ r ∈ qs, W r.1 = W r.2 := by
    intro r hr
    dsimp only [W]
    rw [pairMultiplier_on hps _ r hr r.1 (Or.inl rfl), pairMultiplier_on hps _ r hr r.2 (Or.inr rfl)]
  have hWp : W p.1 = 1 := pairMultiplier_fresh hps _ _ (Or.inr ⟨false,rfl⟩)
  have hWd : W p.2 = 1 := pairMultiplier_fresh hps _ _ (Or.inr ⟨true,rfl⟩)
  have hglobal : VarianceNode gs gs ∅ ∅ := ⟨by simp, by simpa using hgs,
    fun _ => id, fun r hr hn => False.elim (hn hr)⟩
  have hz : slotTotal ps g A = slotTotal ps f A := (slotTotal_node_agreement gs ps f g hagree A B hnode).symm
  have hC : slotTotal gs g ∅ = slotTotal gs f ∅ := (slotTotal_node_agreement gs gs f g hagree ∅ ∅ hglobal).symm
  have hsink' : ∀ x ∈ slotPunctures qs,
      slotTotal x.2 f (insert p.1 (insert p.2 A))/W x.1.1 ≤
        4*q^2*(slotTotal qs f (insert p.1 A)+slotTotal qs f (insert p.2 A)) := by
    intro x hx
    have hxq : x.1 ∈ qs := (slotPunctures_perm qs x hx).mem_iff.mpr List.mem_cons_self
    have hxp : p ≠ x.1 := hfr.pair_ne_of_mem hxq
    have hxps : x.1 ∈ ps := hperm.mem_iff.mpr (List.mem_cons_of_mem _ hxq)
    have hpG := hnode.2.2.1 p hp
    have hxG := hnode.2.2.1 x.1 hxps
    have hcpos := slotDefect_pos gs f hf ∅ hgs p x.1 hpG hxG hxp
    have hzpos := slotTotal_pos ps f hf A (hnode.2.1.mono Set.subset_union_left)
    have hs := hsink x.1 hxps hxp
    rw [hz,hC] at hs
    have hm := mul_le_mul
      (slotDefect_node_comparison gs ps f g q hcompare A B hnode x.1 p hxps hp hxp.symm)
      (slotDefect_node_comparison gs gs f g q hcompare ∅ ∅ hglobal p x.1 hpG hxG hxp)
      hcpos.le (mul_nonneg hq (slotDefect_pos ps g hg A (hnode.2.1.mono Set.subset_union_left)
        x.1 p hxps hp hxp.symm).le)
    have hs' : slotDefect ps f A x.1 p * slotDefect gs f ∅ p x.1 ≤
        q^2*(slotTotal ps f A * slotTotal gs f ∅) := by
      calc
        _ ≤ (q*slotDefect ps g A x.1 p)*(q*slotDefect gs g ∅ p x.1) := hm
        _ = q^2*(slotDefect ps g A x.1 p*slotDefect gs g ∅ p x.1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg q)
    rw [slotDefect_perm hperm,slotDefect_puncture qs p A f hfrA x hx] at hs'
    have hg := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hcpos)).mp (hgood p hpG x.1 hxG hxp)
    have hgz := mul_le_mul_of_nonneg_left hg (mul_nonneg (sq_nonneg q) hzpos.le)
    have hbound : slotTotal x.2 f (insert p.1 (insert p.2 A)) ≤
        4*q^2*slotTotal ps f A*w p x.1 := by
      apply (mul_le_mul_iff_of_pos_right hcpos).mp
      nlinarith
    change slotTotal x.2 f (insert p.1 (insert p.2 A))/pairMultiplier qs (w p) x.1.1 ≤ _
    rw [pairMultiplier_on hps _ x.1 hxq x.1.1 (Or.inl rfl)]
    apply (div_le_iff₀ (hw p x.1)).mpr
    rw [slotTotal_perm hperm f,slotTotal_cons p qs f A hfrA.1 hfrA.2.1 hfrA.2.2.1] at hbound
    exact hbound
  have ht := transport_node_variance_twoLift qs f H A p.1 p.2 W q hf hsigf
    hfrA.1 hfrA.2.1 hfrA.2.2.1 hps hW hws hWp hWd hsink'
  have he := variance_energy_identification gs qs A B p w f H hw hf
    hnode'.2.2.1 hnode'.1 hfr hnode'.2.2.2
  have hqle : qs.length ≤ gs.length := by
    have hnodup := (hnode.2.1.nodup).erase p
    exact List.Subperm.length_le (List.subperm_of_subset hnodup (fun r hr => hnode'.2.2.1 r (List.mem_cons_of_mem _ hr)))
  have hqleR : (qs.length : ℝ) ≤ gs.length := by exact_mod_cast hqle
  have hcoef : 1+8*(qs.length:ℝ)*q^2 ≤ 1+8*(gs.length:ℝ)*q^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqleR (sq_nonneg q)]
  have hepos : 0 ≤ restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
    apply restrictedEnergy_nonneg
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
  have hfinal := ht.trans ((mul_le_mul_of_nonneg_left he
    (by positivity : (0:ℝ) ≤ 1+8*(qs.length:ℝ)*q^2)).trans
    (mul_le_mul_of_nonneg_right hcoef hepos))
  refine ⟨p,qs,hperm,hfrA,hnode'.children.1,hnode'.children.2,?_⟩
  rw [slotVariance_split qs f H hf A p hfrA,slotTotal_cons p qs f A hfrA.1 hfrA.2.1 hfrA.2.2.1]
  linarith

/-- Actual adaptive variance bound with the paper's Cp=p(1+8p q²).
No variance, sink, or transport estimate is an input to this theorem. -/
theorem twoLift_transversal_variance (gs : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : ∀ S, 0 < f S) (hg : ∀ S, 0 < g S)
    (hsigf : HasSlotSignature f) (hsigg : HasSlotSignature (complementWeight g))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ)*q^2)*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  apply adaptive_variance_bound f H hf (chainEdges gs) (chainConductance gs w f)
    (fun ST _ => le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
    (1+8*(gs.length:ℝ)*q^2) (by positivity) (VarianceNode gs)
    (fun ps A B hnode hne => twoLift_variance_node gs ps f g H w q hq hf hg hsigf hsigg
      hgs hcover hw hgood hagree hcompare A B hnode hne)
  exact ⟨by simp,by simpa using hgs,fun _ => id,fun r hr hn => False.elim (hn hr)⟩

lemma slotVariance_completeDegree (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) :
    slotVariance ps (completeDegree f k) H A = slotVariance ps f H A := by
  have hs (h : Set Γ → ℝ) : slotTotal ps (fun S => completeDegree f k S * h S) A =
      slotTotal ps (fun S => f S * h S) A := by
    apply coeffDerivs_degree_congr _ _ _ k
    · intro S hS
      simp [completeDegree, hS]
    · simpa only [List.length_map] using hdegree
  unfold slotVariance
  rw [hs, hs, slotTotal_completeDegree ps f k A hdegree]

lemma restrictedEnergy_completeDegree (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (A B : Set Γ) :
    restrictedEnergy (chainEdges gs) (chainConductance gs w (completeDegree f gs.length)) H A B =
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
  unfold restrictedEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro ST hST
  have hh := (Finset.mem_filter.mp hST).2
  have hs := hh.1.ncard hgs hcover
  have ht := hh.2.1.ncard hgs hcover
  simp only [chainConductance, completeDegree, hs, ht, ite_true]

/-- Completion is eliminated from the genuine fixed-degree variance bound.
Only the transport lift's addition signature and the other lift's omission
signature in these encoded coordinates are assumed. -/
theorem validDegree_twoLift_transversal_variance (gs : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : AdditionProperty f gs.length) (hsigg : OmissionProperty g gs.length)
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ)*q^2)*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  let F := completeDegree f gs.length
  let G := complementWeight (completeDegree (complementWeight g) (Fintype.card Γ - gs.length))
  have hk : gs.length ≤ Fintype.card Γ := by
    have hc := slots_ground_card gs hgs hcover
    omega
  have hgc := complement_degreePositive g gs.length hk hg
  have hF : ∀ S, 0 < F S := completeDegree_positive f gs.length hf
  have hG : ∀ S, 0 < G S := fun S => completeDegree_positive _ _ hgc Sᶜ
  have hFsig := completeDegree_hasSlotSignature f gs.length hf hsigf
  have hGsig : HasSlotSignature (complementWeight G) := by
    have heq : complementWeight G = completeDegree (complementWeight g) (Fintype.card Γ - gs.length) := by
      funext S
      simp [G, complementWeight]
    rw [heq]
    exact completeDegree_hasSlotSignature _ _ hgc hsigg
  have hF_eq (S : Set Γ) (hS : S.ncard = gs.length) : F S = f S := by
    simp [F, completeDegree, hS]
  have hG_eq (S : Set Γ) (hS : S.ncard = gs.length) : G S = g S := by
    have hc := S.ncard_add_ncard_compl
    simp only [Nat.card_eq_fintype_card] at hc
    have hSc : Sᶜ.ncard = Fintype.card Γ - gs.length := by omega
    simp [G, complementWeight, completeDegree, hSc]
  have hgood' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs F ∅ / (4*slotDefect gs F ∅ p r) ≤ w p r := by
    intro p hp r hr hpr
    dsimp only [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hgood p hp r hr hpr
  have hagree' : ∀ S, PlainState gs S → F S = G S := by
    intro S hS
    rw [hF_eq S (hS.ncard hgs hcover), hG_eq S (hS.ncard hgs hcover)]
    exact hagree S hS
  have hcompare' : ∀ S, ChainState gs S → F S ≤ q*G S := by
    intro S hS
    rw [hF_eq S (hS.ncard hgs hcover), hG_eq S (hS.ncard hgs hcover)]
    exact hcompare S hS
  have ht := twoLift_transversal_variance gs F G H w q hq hF hG hFsig hGsig
    hgs hcover hw hgood' hagree' hcompare'
  rwa [slotVariance_completeDegree gs f H gs.length ∅ (by simp),
    restrictedEnergy_completeDegree gs f H w hgs hcover ∅ ∅] at ht

end ContingencyTables.ObservableVariance

end OAI
