import OAI.Combinatorics.ThinTrees.BagConstruction

namespace OAI

universe uι uι2

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma border_transition (hX : ∀v, binary (X v)) {q δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    {F Z K : Finset (Record n)}
    (hF : ∀B ∈ F, B.shell.ordinary = true ∧ B.shell.width = δ ∧ B.avoided = none)
    (hFball : ∀B ∈ F, B.shell = RadialShell.ball B.shell.center δ)
    (hFgeo : ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint (A.shell.support X) (B.shell.support X))
    (hFvalid : H.LabeledArrangement G X q F)
    (hZ : H.LabeledArrangement G X q Z) (hKF : K ⊆ F) (hKZ : Disjoint K Z)
    (hbor : ∀A ∈ K, ¬A.InteriorTo (H := H) (X := X) δ Z) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑B ∈ Z, B.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ≤
        ∑B ∈ Z', B.baseToken ε ∧
      (∀D ∈ Z', D ∈ K ∨ ∃B ∈ Z, D.owner = B.owner) := by
  let p := ∑B ∈ Z, B.phaseToken F δ ε
  let q' := ∑B ∈ Z, B.baseToken ε
  have hw : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none :=
    fun B hB => (hF B hB).2
  by_cases hex : AssignedAccounting.theta*(K.card : ℝ)*δ ≤ q'-p
  · exact ⟨Z,hZ,by dsimp [p,q'] at *; linarith,fun D hD => Or.inr ⟨D,hD,rfl⟩⟩
  let W := shrinkFamily F Z δ
  have hW : H.LabeledArrangement G X q W := shrinkFamily_valid hδ.le hZ
  have hK := H.labeled_subset G X hFvalid hKF
  have hKW : ∀A ∈ K, ∀B ∈ W, A.Compatible H X B := by
    intro A hA D hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    have hBZ : B ∈ Z := (mem_filter.mp hB).1
    exact Record.border_shrink_compatible hδ.le hFgeo (hKF hA)
      (fun heq => Finset.disjoint_left.mp hKZ hA (heq.symm ▸ hBZ))
      (hFball A (hKF hA)) (fun hh => hbor A hA ⟨B,hBZ,hh⟩)
  have hdis : Disjoint K W := H.labeled_sets_disjoint G X hX hK hKW
  have hsum : ∑B ∈ W, B.baseToken ε = ∑B ∈ Z, B.shrinkValue F δ ε :=
    shrinkFamily_sum hX hδ hε hscale hw hZ
  have hkSum : ∑B ∈ K, B.baseToken ε = (K.card : ℝ)*AssignedAccounting.fresh δ ε := by
    calc
      ∑B ∈ K, B.baseToken ε = ∑B ∈ K, AssignedAccounting.fresh δ ε :=
        sum_congr rfl (fun B hB => Record.fresh_base hδ.le hscale (hw B (hKF hB)).1 (hw B (hKF hB)).2)
      _ = _ := by simp
  have hcost : p-(∑B ∈ W, B.baseToken ε) ≤ 256*(q'-p) := by
    rw [hsum]
    dsimp [p,q']
    rw [←sum_sub_distrib,←sum_sub_distrib,Finset.mul_sum]
    exact sum_le_sum (fun B hB => (Record.shrink_cost hδ.le hε hscale hw B).2)
  have hdef : p-(∑B ∈ W, B.baseToken ε) ≤ (K.card : ℝ)*δ/2 := by
    have hh := not_le.mp hex
    dsimp [AssignedAccounting.theta] at hh
    linarith
  have hpay := AssignedAccounting.border_payment hδ.le hscale
    (Nat.cast_nonneg K.card : (0:ℝ) ≤ _) hdef
  refine ⟨K∪W,H.labeled_union G X hK hW hKW,?_,?_⟩
  · rw [sum_union hdis,hkSum]
    dsimp [p] at hpay
    linarith
  · intro D hD
    rcases mem_union.mp hD with hD | hD
    · exact Or.inl hD
    · obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
      refine Or.inr ⟨B,(mem_filter.mp hB).1,?_⟩
      dsimp [Record.shrinkRecord]
      split_ifs <;> rfl

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma loop_with_border_debt (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : H.LocallyConnectedReal G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (howner : ∀D ∈ Z, D.owner ≠ A.owner) :
    ∃(Z' K : Finset (Record n)), H.LabeledArrangement G X (q/4) Z' ∧
      K ⊆ A.centers.image (A.input P) ∧ Disjoint K Z' ∧
      (∀B ∈ K, ¬B.InteriorTo (H := H) (X := X) δ Z') ∧
      (∑D ∈ Z, D.phaseToken F δ ε)+
        (AssignedAccounting.theta/2)*(A.centers.card : ℝ)*δ ≤
          (∑D ∈ Z', D.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      OwnerEvolution A.owner Z Z' ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ A.centers, D = A.input P u) := by
  obtain ⟨V,Z',hVA,hZ',hstop,hcredit,hinter,howners,hfresh,_⟩ :=
    A.interior_loop hX hq hconn hη hε hF hAF hvalid A.centers (Subset.refl _) Z hZ horder
      (fun u hu hint B hB hh => (howner B hB hh).elim)
  let I := V.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')
  let B := V.filter (fun u => ¬(A.input P u).InteriorTo (H := H) (X := X) δ Z')
  let K := B.image (A.input P)
  have hKV : ∀D ∈ K, ∃u ∈ V, D = A.input P u ∧
      ¬D.InteriorTo (H := H) (X := X) δ Z' := by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact ⟨u,(mem_filter.mp hu).1,rfl,(mem_filter.mp hu).2⟩
  have hKcard : K.card = B.card := card_image_of_injective _ (A.input_injective P)
  have hcards : (I.card : ℝ)+(K.card : ℝ) = (V.card : ℝ) := by
    rw [hKcard]
    exact_mod_cast card_filter_add_card_filter_not (s := V)
      (p := fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')
  have hI : 2*(I.card : ℝ) < A.centers.card := by exact_mod_cast hstop
  have hcount : (A.centers.card : ℝ)/2 ≤ (A.centers.card : ℝ)-(V.card : ℝ)+(K.card : ℝ) := by
    linarith
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount (by norm_num [AssignedAccounting.theta] :
      (0:ℝ) ≤ AssignedAccounting.theta)) A.radius_pos.le
  refine ⟨Z',K,hZ',?_,?_,fun D hD => (hKV D hD).choose_spec.2.2,?_,hinter,howners,?_⟩
  · intro D hD
    obtain ⟨u,hu,rfl,_⟩ := hKV D hD
    exact mem_image.mpr ⟨u,hVA hu,rfl⟩
  · rw [Finset.disjoint_left]
    intro D hD hDZ
    obtain ⟨u,hu,rfl,_⟩ := hKV D hD
    rcases hfresh _ hDZ (hAF u (hVA hu)) with hh | ⟨v,hv,heq⟩
    · exact howner _ hh rfl
    · have he : u = v := A.input_injective P heq
      exact (mem_sdiff.mp hv).2 (he ▸ hu)
  · dsimp [AssignedAccounting.theta] at hnum hcredit ⊢
    nlinarith
  · intro D hD hDF
    rcases hfresh D hD hDF with hh | ⟨u,hu,heq⟩
    · exact Or.inl hh
    · exact Or.inr ⟨u,(mem_sdiff.mp hu).1,heq⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

lemma phase_loops {ι : Type uι} [DecidableEq ι]
    (A : ι → H.AssignedBag G X δ η) (P : ι → Finset (Finset (Fin n)))
    (hX : ∀v, binary (X v)) {q ε : ℝ} (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536)
    {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (J : Finset ι) (hAi : Set.InjOn (fun i => (A i).owner) J)
    (hAF : ∀i ∈ J, ∀u ∈ (A i).centers, (A i).input (P i) u ∈ F)
    (hvalid : ∀i ∈ J, ∀u ∈ (A i).centers, ((A i).input (P i) u).Valid H G X (q/4))
    (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀i ∈ J, ∀D ∈ Z, D.owner ⊂ (A i).owner → D.owner ∈ P i)
    (howner : ∀i ∈ J, ∀D ∈ Z, D.owner ≠ (A i).owner) :
    ∃(Z' K : Finset (Record n)), H.LabeledArrangement G X (q/4) Z' ∧ K ⊆ F ∧
      (∀D ∈ K, ∃i ∈ J, D.owner = (A i).owner) ∧ Disjoint K Z' ∧
      (∀B ∈ K, ¬B.InteriorTo (H := H) (X := X) δ Z') ∧
      (∑D ∈ Z, D.phaseToken F δ ε)+
        (AssignedAccounting.theta/2)*(∑i ∈ J, ((A i).centers.card : ℝ))*δ ≤
          (∑D ∈ Z', D.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      (∀D ∈ Z', (∃i ∈ J, D.owner = (A i).owner) ∨ ∃B ∈ Z, D.owner = B.owner) ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃i ∈ J, ∃u ∈ (A i).centers, D = (A i).input (P i) u) := by
  induction J using Finset.strongInduction generalizing Z with
  | H J ih =>
    by_cases hn : J.Nonempty
    · obtain ⟨j,hj,hmax⟩ := J.exists_max_image (fun i => (A i).owner.card) hn
      obtain ⟨Z₁,K₁,hZ₁,hKA,hKZ₁,hbor₁,hcredit₁,hint₁,hown₁,hfresh₁⟩ :=
        (A j).loop_with_border_debt hX hq hconn hη hε hF (hAF j hj) (hvalid j hj)
          hZ (horder j hj) (howner j hj)
      have hKi : ∀D ∈ K₁, ∃u ∈ (A j).centers, D = (A j).input (P j) u := by
        intro D hD
        obtain ⟨u,hu,heq⟩ := mem_image.mp (hKA hD)
        exact ⟨u,hu,heq.symm⟩
      have hKown : ∀D ∈ K₁, D.owner = (A j).owner := by
        intro D hD
        obtain ⟨u,hu,rfl⟩ := hKi D hD
        rfl
      have hKAf : K₁ ⊆ F := by
        intro D hD
        obtain ⟨u,hu,rfl⟩ := hKi D hD
        exact hAF j hj u hu
      have hInj : Set.InjOn (fun i => (A i).owner) (J.erase j) := hAi.mono (erase_subset _ _)
      have horder₁ : ∀i ∈ J.erase j, ∀D ∈ Z₁, D.owner ⊂ (A i).owner → D.owner ∈ P i := by
        intro i hi D hD hs
        rcases hown₁ D hD with hh | ⟨B,hB,hh⟩
        · rw [hh] at hs
          have hcard := card_lt_card hs
          have hmax := hmax i (mem_of_mem_erase hi)
          omega
        · rw [hh] at hs ⊢
          exact horder i (mem_of_mem_erase hi) B hB hs
      have howner₁ : ∀i ∈ J.erase j, ∀D ∈ Z₁, D.owner ≠ (A i).owner := by
        intro i hi D hD heq
        rcases hown₁ D hD with hh | ⟨B,hB,hh⟩
        · exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (heq.symm.trans hh))
        · exact howner i (mem_of_mem_erase hi) B hB (hh.symm.trans heq)
      obtain ⟨Z₂,K₂,hZ₂,hKF₂,hKown₂,hKZ₂,hbor₂,hcredit₂,hint₂,hown₂,hfresh₂⟩ :=
        ih (J.erase j) (erase_ssubset hj) hInj
          (fun i hi => hAF i (mem_of_mem_erase hi))
          (fun i hi => hvalid i (mem_of_mem_erase hi)) Z₁ hZ₁ horder₁ howner₁
      have hdis : Disjoint K₁ K₂ := by
        rw [Finset.disjoint_left]
        intro D hD hD₂
        obtain ⟨i,hi,heq⟩ := hKown₂ D hD₂
        exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (heq.symm.trans (hKown D hD)))
      have hKZ : Disjoint K₁ Z₂ := by
        rw [Finset.disjoint_left]
        intro D hD hDZ
        rcases hfresh₂ D hDZ (hKAf hD) with hD₁ | ⟨i,hi,u,hu,heq⟩
        · exact Finset.disjoint_left.mp hKZ₁ hD hD₁
        · have hoi : D.owner = (A i).owner := congrArg Record.owner heq
          exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (hoi.symm.trans (hKown D hD)))
      refine ⟨Z₂,K₁∪K₂,hZ₂,union_subset hKAf hKF₂,?_,disjoint_union_left.mpr ⟨hKZ,hKZ₂⟩,
        ?_,?_,fun B hh => hint₁ B (hint₂ B hh),?_,?_⟩
      · intro D hD
        rcases mem_union.mp hD with hD | hD
        · exact ⟨j,hj,hKown D hD⟩
        · obtain ⟨i,hi,hh⟩ := hKown₂ D hD
          exact ⟨i,mem_of_mem_erase hi,hh⟩
      · intro D hD hint
        rcases mem_union.mp hD with hD | hD
        · exact hbor₁ D hD (hint₂ D hint)
        · exact hbor₂ D hD hint
      · have hsum := sum_erase_add J (fun i => ((A i).centers.card : ℝ)) hj
        have hcard : ((K₁∪K₂).card : ℝ) = (K₁.card : ℝ)+(K₂.card : ℝ) := by
          exact_mod_cast card_union_of_disjoint hdis
        rw [hcard,←hsum]
        dsimp [AssignedAccounting.theta] at hcredit₁ hcredit₂ ⊢
        nlinarith
      · intro D hD
        rcases hown₂ D hD with ⟨i,hi,hh⟩ | ⟨B,hB,hh⟩
        · exact Or.inl ⟨i,mem_of_mem_erase hi,hh⟩
        · rcases hown₁ B hB with heq | ⟨C,hC,heq⟩
          · exact Or.inl ⟨j,hj,hh.trans heq⟩
          · exact Or.inr ⟨C,hC,hh.trans heq⟩
      · intro D hD hDF
        rcases hfresh₂ D hD hDF with hD | ⟨i,hi,u,hu,heq⟩
        · rcases hfresh₁ D hD hDF with hD | ⟨u,hu,heq⟩
          · exact Or.inl hD
          · exact Or.inr ⟨j,hj,u,hu,heq⟩
        · exact Or.inr ⟨i,mem_of_mem_erase hi,u,hu,heq⟩
    · have he : J = ∅ := not_nonempty_iff_eq_empty.mp hn
      subst J
      refine ⟨Z,∅,hZ,empty_subset _,?_,disjoint_empty_left _,?_,?_,fun _ hh => hh,?_,?_⟩
      · simp
      · simp
      · simp
      · intro D hD
        exact Or.inr ⟨D,hD,rfl⟩
      · intro D hD _
        exact Or.inl hD

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

lemma assigned_phase {ι : Type uι2} [DecidableEq ι]
    (A : ι → H.AssignedBag G X δ η) (P : ι → Finset (Finset (Fin n)))
    (hX : ∀v, binary (X v)) {q ε : ℝ} (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    (J : Finset ι) (hAi : Set.InjOn (fun i => (A i).owner) J)
    (hvalid : ∀i ∈ J, ∀u ∈ (A i).centers, ((A i).input (P i) u).Valid H G X (q/4))
    (hgeo : ∀i ∈ J, ∀u ∈ (A i).centers, ∀j ∈ J, ∀v ∈ (A j).centers,
      ((A i).input (P i) u) ≠ ((A j).input (P j) v) →
      Disjoint ((RadialShell.ball u δ).support X) ((RadialShell.ball v δ).support X))
    (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀i ∈ J, ∀D ∈ Z, D.owner ⊂ (A i).owner → D.owner ∈ P i)
    (howner : ∀i ∈ J, ∀D ∈ Z, D.owner ≠ (A i).owner) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X (q/4) Z' ∧
      (∑D ∈ Z, D.baseToken δ)+(AssignedAccounting.theta/2)*
        (∑i ∈ J, ((A i).centers.card : ℝ))*δ ≤ ∑D ∈ Z', D.baseToken ε ∧
      (∀D ∈ Z', (∃i ∈ J, D.owner = (A i).owner) ∨ ∃B ∈ Z, D.owner = B.owner) := by
  let F := J.biUnion (fun i => ((A i).centers.image ((A i).input (P i))))
  have hFmem : ∀D : Record n, D ∈ F ↔ ∃i ∈ J, ∃u ∈ (A i).centers, D = (A i).input (P i) u := by
    intro D
    simp only [F,mem_biUnion,mem_image]
    constructor
    · rintro ⟨i,hi,u,hu,heq⟩
      exact ⟨i,hi,u,hu,heq.symm⟩
    · rintro ⟨i,hi,u,hu,heq⟩
      exact ⟨i,hi,u,hu,heq.symm⟩
  have hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none := by
    intro D hD
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
    simp [AssignedBag.input,RadialShell.ball,RadialShell.width]
  have hFball : ∀B ∈ F, B.shell = RadialShell.ball B.shell.center δ := by
    intro D hD
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
    rfl
  have hFg : ∀B ∈ F, ∀D ∈ F, B ≠ D → Disjoint (B.shell.support X) (D.shell.support X) := by
    intro B hB D hD hne
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem B).mp hB
    obtain ⟨j,hj,v,hv,rfl⟩ := (hFmem D).mp hD
    exact hgeo i hi u hu j hj v hv hne
  have hFv : H.LabeledArrangement G X (q/4) F := by
    refine ⟨?_,?_⟩
    · intro D hD
      obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
      exact hvalid i hi u hu
    · intro B hB D hD hne hh
      exact (hh (hFg B hB D hD hne)).elim
  have hAF : ∀i ∈ J, ∀u ∈ (A i).centers, (A i).input (P i) u ∈ F :=
    fun i hi u hu => (hFmem _).mpr ⟨i,hi,u,hu,rfl⟩
  obtain ⟨Z₁,K,hZ₁,hKF,hKo,hKZ,hbor,hcredit,hint,hown,hfresh⟩ :=
    phase_loops A P hX hq hconn hη hscale hF J hAi hAF hvalid Z hZ horder howner
  obtain ⟨Z₂,hZ₂,hcredit₂,hown₂⟩ :=
    border_transition hX hδ hε hscale hF hFball hFg hFv hZ₁ hKF hKZ hbor
  have hsum : ∑D ∈ Z, D.phaseToken F δ ε = ∑D ∈ Z, D.baseToken δ := by
    apply sum_congr rfl
    intro D hD
    have hn : D ∉ F := by
      intro hf
      obtain ⟨i,hi,u,hu,heq⟩ := (hFmem D).mp hf
      exact howner i hi D hD (congrArg Record.owner heq)
    simp only [Record.phaseToken,ite_eq_right hn,Record.baseToken]
  refine ⟨Z₂,hZ₂,?_,?_⟩
  · rw [hsum] at hcredit
    linarith
  · intro D hD
    rcases hown₂ D hD with hDK | ⟨B,hB,heq⟩
    · exact Or.inl (hKo D hDK)
    · rcases hown B hB with ⟨i,hi,hoi⟩ | ⟨C,hC,hoi⟩
      · exact Or.inl ⟨i,hi,heq.trans hoi⟩
      · exact Or.inr ⟨C,hC,heq.trans hoi⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
