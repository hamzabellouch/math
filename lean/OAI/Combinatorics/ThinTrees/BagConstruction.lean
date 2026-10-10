import OAI.Combinatorics.ThinTrees.BagBounds

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma dense_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε a b : ℝ} (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U M : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {B : Record n} (hB : B ∈ Z) (hno : B.avoided = none)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a ≤ b)
    (hMn : M.Nonempty) (hMU : M ⊆ U)
    (hinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B)
    (hrange : ∀u ∈ M, a-δ < l1dist (X u) (X B.shell.center) ∧
      l1dist (X u) (X B.shell.center) < b+δ)
    (hcount : 765*δ ≤ (M.card : ℝ)*δ) (hdense : 3*(b-a) ≤ (M.card : ℝ)*δ) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  let Q := M.image (A.input P)
  have hQcard : Q.card = M.card := card_image_of_injective _ (A.input_injective P)
  obtain ⟨u₀,hu₀⟩ := hMn
  have hwidth := Record.interior_width H X (hinter u₀ hu₀)
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := H.dense_operation G X hX A.radius_pos hε hF hZ hB
    (A.input_arrangement (hMU.trans hU) (fun u hu => hvalid u (hU (hMU hu))))
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hAF u (hU (hMU hu)))
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; rfl) hno hwidth ha hb hab
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hrange u hu)
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hinter u hu)
    (by intro D hD E hE hs; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
        simpa [input,Record.excluded] using horder E hE hs)
    (by rwa [hQcard]) (by rwa [hQcard])
  have hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃E ∈ Z, ∃a b,
      D = E.restriction a b ∧ E.shell.inner ≤ a ∧ b ≤ E.shell.outer := by
    intro D hD
    rcases hmeta₀ D hD with hD | hD | ⟨a,b,heq,ha,hb,_⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl hD)
    · exact Or.inr (Or.inr ⟨B,hB,a,b,heq,ha,hb⟩)
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution (by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact Or.inl (hAF u (hU (hMU hu)))) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners (by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact Or.inl rfl) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (M := M) (by
      intro D hD _
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
      exact ⟨u,hu,rfl⟩) hmeta
  have hsep' : A.SameOwnerSeparated P (U\M) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro D hD _ v hv _
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    obtain ⟨hv,hvM⟩ := mem_sdiff.mp hv
    exact A.disjoint (hU hv) (hU (hMU hu)) (fun hh => hvM (hh ▸ hu))
  refine ⟨⟨M,Z',⟨u₀,hu₀⟩,fun u hu => ⟨hMU hu,⟨B,hB,hinter u hu⟩⟩,
    hZ',?_,hevol,howner,hfresh,hsep'⟩⟩
  rwa [hQcard] at hcredit

lemma sparse_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε a b : ℝ} {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U M : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {B : Record n} (hB : B ∈ Z) (hno : B.avoided = none)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hMn : M.Nonempty) (hMU : M ⊆ U)
    (hinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B)
    (hexact : ∀u ∈ U, (A.input P u).InteriorTo (H := H) (X := X) δ Z →
      a-δ < l1dist (X u) (X B.shell.center) →
      l1dist (X u) (X B.shell.center) < b+δ → u ∈ M)
    (hwide : 255*δ ≤ b-a) (hsparse : (M.card : ℝ)*δ ≤ 3*(b-a))
    (hinner : (B.innerRecord A.owner (a+δ) (b-δ)).Valid H G X (q/4))
    (houter : (B.outsideRecord A.owner a b).Valid H G X (q/4)) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  obtain ⟨u₀,hu₀⟩ := hMn
  have hint := hinter u₀ hu₀
  have hov := hvalid u₀ (hU (hMU hu₀))
  have ht := Record.candidate_ancestor H hov.1 (hZ.1 B hB).1
    (fun hs => by simpa [input,Record.excluded] using horder B hB hs) hint.1
  have hstrict : A.owner ⊂ B.owner := Record.strict_owner_of_interior hX
    hov.1 (hZ.1 B hB).1 hov.2.2.1 A.radius_pos.le rfl
    (fun hs => by simpa [input,Record.excluded] using horder B hB hs) (hsep u₀ (hMU hu₀) ⟨B,hB,hint⟩ B hB) hint
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := H.sparse_operation G X hX A.radius_pos
    (fun D hD => ⟨(hF D hD).1,(hF D hD).2.1⟩) hZ hB hno
    (Record.interior_width H X hint) ht ha hb hwide hsparse hinner houter
  let C := B.innerRecord A.owner (a+δ) (b-δ)
  let D := B.outsideRecord A.owner a b
  let Q : Finset (Record n) := {C,D}
  have hmeta : ∀E ∈ Z', E ∈ Z ∨ E ∈ Q ∨ ∃K ∈ Z, ∃c d,
      E = K.restriction c d ∧ K.shell.inner ≤ c ∧ d ≤ K.shell.outer := by
    intro E hE
    rcases hmeta₀ E hE with hE | rfl | rfl | ⟨c,d,heq,hc,hd,_⟩
    · exact Or.inl hE
    · exact Or.inr (Or.inl (mem_insert_self _ _))
    · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton_self _)))
    · exact Or.inr (Or.inr ⟨B,hB,c,d,heq,hc,hd⟩)
  have href := Record.central_radialRefines (hZ.1 B hB).1 hno ht
    (by linarith [A.radius_pos] : B.shell.inner ≤ a+δ)
    (by linarith [A.radius_pos] : b-δ ≤ B.shell.outer) ha hb
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution (by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inr ⟨B,hB,href.1⟩
    · rw [mem_singleton.mp hE]
      exact Or.inr ⟨B,hB,href.2⟩) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners (by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inl rfl
    · rw [mem_singleton.mp hE]
      exact Or.inr ⟨B,hB,rfl⟩) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (P := P) (M := M) (by
      intro E hE hEF
      have hh := (hF E hEF).1
      rcases mem_insert.mp hE with rfl | hE
      · simp [C,Record.innerRecord,RadialShell.hollow] at hh
      · rw [mem_singleton.mp hE] at hh
        simp [D,Record.outsideRecord,RadialShell.hollow] at hh) hmeta
  have hsep' : A.SameOwnerSeparated P (U\M) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro E hE hown u hu hintold
    rcases mem_insert.mp hE with rfl | hE
    · obtain ⟨hu,huM⟩ := mem_sdiff.mp hu
      by_cases hlo : a-δ < l1dist (X u) (X B.shell.center)
      · have hhi : b+δ ≤ l1dist (X u) (X B.shell.center) :=
          le_of_not_gt (fun hh => huM (hexact u hu hintold hlo hh))
        exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith [A.radius_pos])
      · exact RadialShell.ball_disjoint_hollow_upper X _ _ (by
          have := not_lt.mp hlo
          linarith [A.radius_pos])
    · rw [mem_singleton.mp hE] at hown
      exact (hstrict.ne hown.symm).elim
  exact ⟨⟨M,Z',⟨u₀,hu₀⟩,fun u hu => ⟨hMU hu,⟨B,hB,hinter u hu⟩⟩,
    hZ',hcredit,hevol,howner,hfresh,hsep'⟩⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma interior_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : H.LocallyConnectedReal G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    (hhalf : A.centers.card ≤ 2*(U.filter (fun u =>
      (A.input P u).InteriorTo (H := H) (X := X) δ Z)).card) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  by_cases hav : ∃u ∈ U, ∃B ∈ Z, B.avoided.isSome = true ∧
      (A.input P u).Interior H X 256 δ B
  · obtain ⟨u,hu,B,hB,hav,hint⟩ := hav
    exact A.avoiding_move hX hε hU hF hAF hvalid hZ horder hsep hu hB hav hint
  let I := U.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z)
  have hIU : I ⊆ U := by
    intro u hu
    exact (mem_filter.mp hu).1
  have hI : ∀u ∈ I, (A.input P u).InteriorTo (H := H) (X := X) δ Z :=
    fun u hu => (mem_filter.mp hu).2
  obtain ⟨R,hR,hRc,hlarge⟩ := A.large_component hq hconn hη (hIU.trans hU) hhalf
  have hno : ∀u ∈ I, ∀D ∈ Z, (A.input P u).Interior H X 256 δ D → D.avoided = none := by
    intro u hu D hD hint
    cases hh : D.avoided with
    | none => rfl
    | some t => exact (hav ⟨u,hIU hu,D,hD,by simp [hh],hint⟩).elim
  obtain ⟨B,a,b,M,u₁,u₂,hB,hBno,ha,hb,hab,hMn,hMeq,hinter,hdich,
    hu₁,hu₂,hv₁,hv₂,hv₁r,hv₂r,hu₁r,hu₂r⟩ := A.radial_group hX (hIU.trans hU) hZ
      (fun u hu => (hvalid u (hU (hIU hu))).1) horder hI hno hlarge
  have hMI : M ⊆ I := by rw [hMeq]; exact filter_subset _ _
  have hMU : M ⊆ U := hMI.trans hIU
  have hrange : ∀u ∈ M, a-δ < l1dist (X u) (X B.shell.center) ∧
      l1dist (X u) (X B.shell.center) < b+δ := by
    intro u hu
    rw [hMeq] at hu
    exact (mem_filter.mp hu).2
  have hdich' : (768:ℝ) ≤ M.card ∨ 255*δ ≤ b-a := by exact_mod_cast hdich
  by_cases hdense : 3*(b-a) ≤ (M.card : ℝ)*δ
  · have hcount := AssignedSelection.dense_count A.radius_pos.le (by norm_num : (768:ℝ) ≤ 768)
      hdich' hdense
    exact A.dense_move hX hε hU hF hAF hvalid hZ horder hsep hB hBno ha hb hab
      hMn hMU hinter hrange hcount hdense
  · have hsparse : (M.card : ℝ)*δ ≤ 3*(b-a) := (not_le.mp hdense).le
    have hwide := AssignedSelection.sparse_width A.radius_pos.le (by norm_num : (768:ℝ) ≤ 768)
      hdich' hsparse
    obtain ⟨u₀,hu₀⟩ := hMn
    have hint := hinter u₀ hu₀
    have hov := hvalid u₀ (hU (hMU hu₀))
    have ht := Record.candidate_ancestor H hov.1 (hZ.1 B hB).1 (fun hs => by simpa [input,Record.excluded] using horder B hB hs) hint.1
    have hstrict : A.owner ⊂ B.owner := Record.strict_owner_of_interior hX
      hov.1 (hZ.1 B hB).1 hov.2.2.1 A.radius_pos.le rfl
      (fun hs => by simpa [input,Record.excluded] using horder B hB hs) (hsep u₀ (hMU hu₀) ⟨B,hB,hint⟩ B hB) hint
    obtain ⟨e,he⟩ := (A.neighbor_spec (hU (hIU hu₁))).2.2
    obtain ⟨hin,hout⟩ := Record.central_valid H G X (hZ.1 B hB) hBno hq.le hconn ht hstrict
      ha hb A.radius_pos (by linarith [A.radius_pos]) hR hRc
      (A.endpoint u₁ (hU (hIU hu₁))).1 (A.endpoint u₂ (hU (hIU hu₂))).1
      hv₁ hv₂ hu₁r hu₂r hv₁r hv₂r he
    apply A.sparse_move hX hU hF hvalid hZ horder hsep hB hBno ha hb ⟨u₀,hu₀⟩ hMU
      hinter _ hwide hsparse hin hout
    intro u hu hint hlo hhi
    rw [hMeq]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hu,hint⟩,hlo,hhi⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

lemma ownerEvolution_refl (t : Finset (Fin n)) (Z : Finset (Record n)) : OwnerEvolution t Z Z := by
  intro D hD
  exact Or.inr ⟨D,hD,rfl⟩

lemma ownerEvolution_trans {t : Finset (Fin n)} {Z W V : Finset (Record n)}
    (h1 : OwnerEvolution t Z W) (h2 : OwnerEvolution t W V) : OwnerEvolution t Z V := by
  intro D hD
  rcases h2 D hD with hh | ⟨E,hE,hh⟩
  · exact Or.inl hh
  · rcases h1 E hE with he | ⟨B,hB,he⟩
    · exact Or.inl (hh.trans he)
    · exact Or.inr ⟨B,hB,hh.trans he⟩

namespace AssignedBag

lemma interior_loop (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : H.LocallyConnectedReal G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (U : Finset (Fin n)) (hU : U ⊆ A.centers) (Z : Finset (Record n))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z) :
    ∃(V : Finset (Fin n)) (Z' : Finset (Record n)), V ⊆ U ∧
      H.LabeledArrangement G X (q/4) Z' ∧
      2*(V.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')).card <
        A.centers.card ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+
        AssignedAccounting.theta*((U.card : ℝ)-(V.card : ℝ))*δ ≤
          ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      OwnerEvolution A.owner Z Z' ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ U\V, D = A.input P u) ∧
      A.SameOwnerSeparated P V Z' := by
  induction U using Finset.strongInduction generalizing Z with
  | H U ih =>
    by_cases hstop : 2*(U.filter (fun u =>
        (A.input P u).InteriorTo (H := H) (X := X) δ Z)).card < A.centers.card
    · refine ⟨U,Z,Subset.refl _,hZ,hstop,?_,fun _ h => h,ownerEvolution_refl _ _,
        fun _ h _ => Or.inl h,hsep⟩
      simp
    · obtain ⟨W⟩ := A.interior_move hX hq hconn hη hε hU hF hAF hvalid hZ horder hsep
        (not_lt.mp hstop)
      have hMU : W.treated ⊆ U := fun u hu => (W.treated_interior u hu).1
      have hss : U\W.treated ⊂ U := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,?_⟩
        intro hh
        obtain ⟨u,hu⟩ := W.nonempty
        have hm : u ∈ U\W.treated := hh.symm ▸ hMU hu
        exact (mem_sdiff.mp hm).2 hu
      obtain ⟨V,Z',hVU,hZ',hstop',hcredit',hinter',howners',hfresh',hsep'⟩ := ih (U\W.treated) hss
        (sdiff_subset.trans hU) W.next W.valid (ownerEvolution_order horder W.owners) W.separation
      have hcards : ((U\W.treated).card : ℝ)+(W.treated.card : ℝ) = (U.card : ℝ) := by
        exact_mod_cast card_sdiff_add_card_eq_card hMU
      refine ⟨V,Z',hVU.trans sdiff_subset,hZ',hstop',?_,?_,
        ownerEvolution_trans W.owners howners',?_,hsep'⟩
      · calc
          (∑D ∈ Z, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*((U.card : ℝ)-(V.card : ℝ))*δ =
            ((∑D ∈ Z, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*(W.treated.card : ℝ)*δ)+
              AssignedAccounting.theta*(((U\W.treated).card : ℝ)-(V.card : ℝ))*δ := by
                rw [←hcards]
                ring
          _ ≤ (∑D ∈ W.next, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*(((U\W.treated).card : ℝ)-(V.card : ℝ))*δ :=
            add_le_add W.credit (le_refl _)
          _ ≤ _ := hcredit'
      · intro B hB
        exact evolution_interior A.radius_pos.le (fun D hD => (hF D hD).2.1)
          W.evolution (hinter' B hB)
      · intro D hD hDF
        rcases hfresh' D hD hDF with hD | ⟨u,hu,heq⟩
        · rcases W.fresh D hD hDF with hD | ⟨u,hu,heq⟩
          · exact Or.inl hD
          · exact Or.inr ⟨u,mem_sdiff.mpr ⟨hMU hu,
              fun hv => (mem_sdiff.mp (hVU hv)).2 hu⟩,heq⟩
        · exact Or.inr ⟨u,mem_sdiff.mpr ⟨sdiff_subset (mem_sdiff.mp hu).1,
            (mem_sdiff.mp hu).2⟩,heq⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}
namespace Record

def baseToken (r : ℝ) (B : Record n) : ℝ :=
  AssignedAccounting.base B.avoided.isSome B.shell.width r

def shrinkRecord (F : Finset (Record n)) (δ : ℝ) (B : Record n) : Record n :=
  if B ∈ F then B else B.restriction (B.shell.inner+257*δ) (B.shell.outer-257*δ)

def shrinkValue (F : Finset (Record n)) (δ ε : ℝ) (B : Record n) : ℝ :=
  if B ∈ F then AssignedAccounting.fresh δ ε else
    AssignedAccounting.base B.avoided.isSome (B.shell.width-514*δ) ε

lemma fresh_base {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    {B : Record n} (hwidth : B.shell.width = δ) (hno : B.avoided = none) :
    B.baseToken ε = AssignedAccounting.fresh δ ε := by
  simp only [baseToken,hwidth,hno,Option.isSome_none,AssignedAccounting.base,
    Bool.false_eq_true,↓reduceIte,AssignedAccounting.fresh,div_one]
  exact max_eq_left (by linarith)

lemma shrink_refines {δ : ℝ} (hδ : 0 ≤ δ) (F : Finset (Record n)) (B : Record n) :
    (B.shrinkRecord F δ).Refines H X B := by
  by_cases hB : B ∈ F
  · simp only [shrinkRecord,ite_eq_left hB]
    exact ⟨Set.Subset.refl _,Subset.refl _⟩
  · simp only [shrinkRecord,ite_eq_right hB]
    exact B.restriction_refines H X (by linarith) (by linarith)

lemma shrink_valid {δ q : ℝ} (hδ : 0 ≤ δ) {F : Finset (Record n)} {B : Record n}
    (hB : B.Valid H G X q) (hw : 0 < (B.shrinkRecord F δ).shell.width) :
    (B.shrinkRecord F δ).Valid H G X q := by
  by_cases hf : B ∈ F
  · simpa only [shrinkRecord,ite_eq_left hf] using hB
  · simp only [shrinkRecord,ite_eq_right hf] at hw ⊢
    exact Record.restrict_valid H G X hB (by linarith) (by linarith)
      (by simpa only [restriction,RadialShell.hollow,RadialShell.width,sub_pos] using hw)

lemma shrink_base {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (B : Record n) : (B.shrinkRecord F δ).baseToken ε = B.shrinkValue F δ ε := by
  by_cases hf : B ∈ F
  · simp only [shrinkRecord,shrinkValue,ite_eq_left hf]
    exact fresh_base hδ hε (hF B hf).1 (hF B hf).2
  · simp only [shrinkRecord,shrinkValue,ite_eq_right hf,baseToken,restriction,RadialShell.hollow,
      RadialShell.width]
    congr 1
    ring

lemma shrink_cost {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (B : Record n) :
    0 ≤ B.phaseToken F δ ε-B.shrinkValue F δ ε ∧
      B.phaseToken F δ ε-B.shrinkValue F δ ε ≤
        256*(B.baseToken ε-B.phaseToken F δ ε) := by
  by_cases hf : B ∈ F
  · rw [phaseToken,shrinkValue,ite_eq_left hf,ite_eq_left hf,
      fresh_base hδ hscale (hF B hf).1 (hF B hf).2]
    simp
  · simp only [phaseToken,shrinkValue,ite_eq_right hf,baseToken]
    exact AssignedAccounting.shrink_cost _ hδ hε hscale

lemma shrink_discard {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ)
    (B : Record n) (hw : ¬0 < (B.shrinkRecord F δ).shell.width) :
    B.shrinkValue F δ ε = 0 := by
  by_cases hf : B ∈ F
  · rw [shrinkRecord,ite_eq_left hf,hF B hf] at hw
    exact (hw hδ).elim
  · rw [shrinkValue,ite_eq_right hf]
    apply AssignedAccounting.base_discard _ _ hε
    rw [shrinkRecord,ite_eq_right hf] at hw
    dsimp [restriction,RadialShell.hollow,RadialShell.width] at hw ⊢
    linarith [not_lt.mp hw]

lemma border_shrink_compatible {δ : ℝ} (_hδ : 0 ≤ δ) {F : Finset (Record n)}
    (hF : ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint (A.shell.support X) (B.shell.support X))
    {A B : Record n} (hA : A ∈ F) (hne : A ≠ B)
    (hball : A.shell = RadialShell.ball A.shell.center δ)
    (hbor : ¬A.Interior H X 256 δ B) :
    A.Compatible H X (B.shrinkRecord F δ) := by
  by_cases hf : B ∈ F
  · simp only [shrinkRecord,ite_eq_left hf]
    exact Or.inl (hF A hA B hf hne)
  · simp only [shrinkRecord,ite_eq_right hf]
    by_cases hdis : Disjoint (A.conflict H) (B.conflict H)
    · exact Or.inr hdis
    · have hmeet : (A.conflict H ∩ B.conflict H).Nonempty := by
        apply nonempty_iff_ne_empty.mpr
        exact fun hh => hdis (Finset.disjoint_iff_inter_eq_empty.mpr hh)
      left
      rw [hball]
      by_cases hlo : B.shell.inner+256*δ < l1dist (X A.shell.center) (X B.shell.center)
      · have hhi : B.shell.outer-256*δ ≤ l1dist (X A.shell.center) (X B.shell.center) :=
          le_of_not_gt (fun hh => hbor ⟨hmeet,hlo,hh⟩)
        exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith)
      · exact RadialShell.ball_disjoint_hollow_upper X _ _ (by linarith [not_lt.mp hlo])

end Record

def shrinkFamily (F Z : Finset (Record n)) (δ : ℝ) : Finset (Record n) :=
  (Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width)).image (Record.shrinkRecord F δ)

lemma shrinkFamily_valid {q δ : ℝ} (hδ : 0 ≤ δ) {F Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) : H.LabeledArrangement G X q (shrinkFamily F Z δ) := by
  constructor
  · intro D hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    exact Record.shrink_valid hδ (hZ.1 B (mem_filter.mp hB).1) (mem_filter.mp hB).2
  · intro D hD E hE hne hgeo
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hE
    have hh := Record.compatible_refinements H X
      (H.labeled_pair G X hZ (mem_filter.mp hB).1 (mem_filter.mp hC).1
        (fun hh => hne (congrArg (Record.shrinkRecord F δ) hh)))
      (Record.shrink_refines hδ F B) (Record.shrink_refines hδ F C)
    exact hh.resolve_left hgeo

lemma shrinkFamily_sum (hX : ∀v, binary (X v)) {q δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536) {F Z : Finset (Record n)}
    (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (hZ : H.LabeledArrangement G X q Z) :
    ∑D ∈ shrinkFamily F Z δ, D.baseToken ε = ∑B ∈ Z, B.shrinkValue F δ ε := by
  have hinj : ∀B ∈ Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width),
      ∀C ∈ Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width),
      B.shrinkRecord F δ = C.shrinkRecord F δ → B = C := by
    intro B hB C hC heq
    by_contra hh
    have hv := Record.shrink_valid hδ.le (hZ.1 B (mem_filter.mp hB).1) (mem_filter.mp hB).2
    have hc := Record.compatible_refinements H X
      (H.labeled_pair G X hZ (mem_filter.mp hB).1 (mem_filter.mp hC).1 hh)
      (Record.shrink_refines hδ.le F B) (Record.shrink_refines hδ.le F C)
    rw [←heq] at hc
    exact (B.shrinkRecord F δ).compatible_self_iff H X hX hv.1 hv.2.2.1 hc
  rw [shrinkFamily,sum_image hinj,sum_filter]
  apply sum_congr rfl
  intro B hB
  by_cases hw : 0 < (B.shrinkRecord F δ).shell.width
  · rw [ite_eq_left hw,Record.shrink_base hδ.le hscale hF]
  · rw [ite_eq_right hw,Record.shrink_discard hδ hε (fun D hD => (hF D hD).1) B hw]

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
