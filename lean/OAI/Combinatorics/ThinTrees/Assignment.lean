import OAI.Combinatorics.ThinTrees.Selection

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma compatible_ne (hX : ∀v, binary (X v)) {B D : Record n}
    (hB : B.Shape H) (hval : B.shell.Valid X) (hBD : B.Compatible H X D) : B ≠ D := by
  rintro rfl
  exact B.compatible_self_iff H X hX hB hval hBD

def phaseToken (F : Finset (Record n)) (δ ε : ℝ) (B : Record n) : ℝ :=
  if B ∈ F then AssignedAccounting.fresh δ ε else
    AssignedAccounting.base B.avoided.isSome B.shell.width δ

lemma restriction_not_fresh {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b : ℝ) :
    B.restriction a b ∉ F := by
  intro hh
  have hh' := hF _ hh
  simp [restriction,RadialShell.hollow] at hh'

lemma restriction_token {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b δ ε : ℝ) :
    phaseToken F δ ε (B.restriction a b) =
      AssignedAccounting.base B.avoided.isSome (b-a) δ := by
  rw [phaseToken,ite_eq_right (restriction_not_fresh hF B a b)]
  rfl

lemma interior_width {δ : ℝ} {A B : Record n} (hh : A.Interior H X 256 δ B) :
    512*δ < B.shell.width := by
  dsimp [RadialShell.width]
  linarith [hh.2.1,hh.2.2]

lemma interior_ball_subset {δ : ℝ} {A B : Record n} (hδ : 0 ≤ δ)
    (hA : A.shell = RadialShell.ball A.shell.center δ)
    (hh : A.Interior H X 256 δ B) : A.shell.support X ⊆ B.shell.support X := by
  rw [hA]
  apply RadialShell.ball_subset_of_radial_margin
  · linarith [hh.2.1]
  · linarith [hh.2.2]

end Record

lemma labeled_singleton {q : ℝ} {B : Record n} (hB : B.Valid H G X q) :
    H.LabeledArrangement G X q {B} := by
  constructor
  · intro A hA
    simpa only [mem_singleton.mp hA] using hB
  · intro A hA D hD hne
    exact (hne ((mem_singleton.mp hA).trans (mem_singleton.mp hD).symm)).elim

lemma labeled_insert {q : ℝ} {Z : Finset (Record n)} {B : Record n}
    (hZ : H.LabeledArrangement G X q Z) (hB : B.Valid H G X q)
    (hcompat : ∀D ∈ Z, B.Compatible H X D) :
    H.LabeledArrangement G X q (insert B Z) := by
  rw [← singleton_union]
  apply H.labeled_union G X (H.labeled_singleton G X hB) hZ
  intro A hA D hD
  simpa only [mem_singleton.mp hA] using hcompat D hD

lemma avoiding_operation (hX : ∀v, binary (X v))
    {q δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ/1536)
    {F Z : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.avoided = none)
    (hZ : H.LabeledArrangement G X q Z) {A B : Record n}
    (hA : A.Valid H G X q) (hAF : A ∈ F)
    (hAball : A.shell = RadialShell.ball A.shell.center δ)
    (hB : B ∈ Z) (havoid : B.avoided.isSome = true)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ A.excluded)
    (hinter : A.Interior H X 256 δ B) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D = A ∨ ∃a b, D = B.restriction a b ∧
        B.shell.inner ≤ a ∧ b ≤ B.shell.outer ∧ a < b := by
  let r := l1dist (X A.shell.center) (X B.shell.center)
  let B₁ := B.restriction B.shell.inner (r-δ)
  let B₂ := B.restriction (r+δ) B.shell.outer
  have hbvalid := hZ.1 B hB
  have h1a : B.shell.inner < r-δ := by dsimp [r]; linarith [hinter.2.1]
  have h1b : r-δ ≤ B.shell.outer := by dsimp [r]; linarith [hinter.2.2]
  have h2a : B.shell.inner ≤ r+δ := by dsimp [r]; linarith [hinter.2.1]
  have h2b : r+δ < B.shell.outer := by dsimp [r]; linarith [hinter.2.2]
  have hB₁ : B₁.Valid H G X q := Record.restrict_valid H G X hbvalid (le_refl _) h1b h1a
  have hB₂ : B₂.Valid H G X q := Record.restrict_valid H G X hbvalid h2a (le_refl _) h2b
  have h12 : B₁.Compatible H X B₂ := Or.inl
    (RadialShell.concentric_disjoint X B.shell.center (by linarith : r-δ ≤ r+δ))
  have hA1 : A.Compatible H X B₁ := by
    left
    change Disjoint (A.shell.support X) ((RadialShell.hollow B.shell.center B.shell.inner (r-δ)).support X)
    rw [hAball]
    exact RadialShell.ball_disjoint_hollow_lower X _ _ (by dsimp [r]; linarith)
  have hA2 : A.Compatible H X B₂ := by
    left
    change Disjoint (A.shell.support X) ((RadialShell.hollow B.shell.center (r+δ) B.shell.outer).support X)
    rw [hAball]
    exact RadialShell.ball_disjoint_hollow_upper X _ _ (le_refl _)
  let W : Finset (Record n) := {A,B₁,B₂}
  have hW : H.LabeledArrangement G X q W := by
    apply H.labeled_insert G X
    · apply H.labeled_insert G X (H.labeled_singleton G X hB₂) hB₁
      intro D hD
      simpa only [mem_singleton.mp hD] using h12
    · exact hA
    · intro D hD
      rcases mem_insert.mp hD with rfl | hD
      · exact hA1
      · simpa only [mem_singleton.mp hD] using hA2
  have hancestor : A.owner ∈ B.conflict H :=
    Record.candidate_ancestor H hA.1 hbvalid.1 (horder B hB) hinter.1
  have hcompat : ∀D ∈ Z.erase B, ∀C ∈ W, D.Compatible H X C := by
    intro D hD C hC
    obtain ⟨hDB,hDZ⟩ := mem_erase.mp hD
    have hBC : B.Compatible H X D := H.labeled_pair G X hZ hB hDZ hDB.symm
    apply Record.compatible_symm H X
    rcases mem_insert.mp hC with rfl | hC
    · exact Record.insert_compatible H G X hZ hA.1 hB hDZ hDB.symm hancestor horder
        (Record.interior_ball_subset H X hδ.le hAball hinter)
    rcases mem_insert.mp hC with rfl | hC
    · exact Record.compatible_heredity H X hBC
        (B.restriction_refines H X (le_refl _) h1b).1 (Subset.refl _)
    · have heq := mem_singleton.mp hC
      subst C
      exact Record.compatible_heredity H X hBC
        (B.restriction_refines H X h2a (le_refl _)).1 (Subset.refl _)
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2] at havoid
    simp at havoid
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*δ ≤
      ∑D ∈ W, Record.phaseToken F δ ε D := by
    have hne12 := Record.compatible_ne H X hX hB₁.1 hB₁.2.2.1 h12
    have hneA1 := Record.compatible_ne H X hX hA.1 hA.2.2.1 hA1
    have hneA2 := Record.compatible_ne H X hX hA.1 hA.2.2.1 hA2
    have hAnot : A ∉ ({B₁,B₂} : Finset (Record n)) := by simp [hneA1,hneA2]
    have h1not : B₁ ∉ ({B₂} : Finset (Record n)) := by simpa using hne12
    dsimp [W]
    rw [sum_insert hAnot,sum_insert h1not,sum_singleton]
    rw [Record.phaseToken,ite_eq_right hBF,havoid]
    rw [show Record.phaseToken F δ ε A = AssignedAccounting.fresh δ ε by simp [Record.phaseToken,hAF]]
    rw [Record.restriction_token (fun D hD => (hF D hD).1) B,
      Record.restriction_token (fun D hD => (hF D hD).1) B,havoid]
    have hh := AssignedAccounting.avoiding_carve hδ.le hε
      (Record.interior_width H X hinter).le
      (show (r-δ-B.shell.inner)+(B.shell.outer-(r+δ))=B.shell.width-2*δ by
        dsimp [RadialShell.width]; ring)
    linarith
  refine ⟨Z.erase B∪W,H.labeled_replace G X hZ hW B hcompat,
    H.replacement_credit G X hX hZ hB hcompat _ hcredit,?_⟩
  intro D hD
  rcases mem_union.mp hD with hD | hD
  · exact Or.inl (mem_of_mem_erase hD)
  right
  rcases mem_insert.mp hD with rfl | hD
  · exact Or.inl rfl
  right
  rcases mem_insert.mp hD with rfl | hD
  · exact ⟨B.shell.inner,r-δ,rfl,le_refl _,h1b,h1a⟩
  · have heq := mem_singleton.mp hD
    exact ⟨r+δ,B.shell.outer,heq,h2a,le_refl _,h2b⟩

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def restrictionSet (B : Record n) (a b : ℝ) : Finset (Record n) :=
  if a < b then {B.restriction a b} else ∅

lemma mem_restrictionSet {B D : Record n} {a b : ℝ} :
    D ∈ B.restrictionSet a b ↔ a < b ∧ D = B.restriction a b := by
  by_cases hh : a < b <;> simp [restrictionSet,hh]

lemma restrictionSet_valid {q a b : ℝ} {B : Record n} (hB : B.Valid H G X q)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    H.LabeledArrangement G X q (B.restrictionSet a b) := by
  by_cases hab : a < b
  · rw [restrictionSet,ite_eq_left hab]
    exact H.labeled_singleton G X (restrict_valid H G X hB ha hb hab)
  · rw [restrictionSet,ite_eq_right hab]
    exact H.labeled_empty G X q

lemma restrictionSet_refines {B D : Record n} {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hD : D ∈ B.restrictionSet a b) : D.Refines H X B := by
  obtain ⟨hab,rfl⟩ := mem_restrictionSet.mp hD
  exact B.restriction_refines H X ha hb

lemma restrictionSet_token {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b : ℝ)
    {δ ε : ℝ} (hδ : 0 ≤ δ) :
    (∑D ∈ B.restrictionSet a b, phaseToken F δ ε D) =
      AssignedAccounting.base B.avoided.isSome (b-a) δ := by
  by_cases hab : a < b
  · rw [restrictionSet,ite_eq_left hab,sum_singleton,restriction_token hF]
  · rw [restrictionSet,ite_eq_right hab,sum_empty,AssignedAccounting.base_discard _ (by linarith) hδ]

lemma restrictions_compatible (B : Record n) {a b c d : ℝ} (hbc : b ≤ c)
    {D E : Record n} (hD : D ∈ B.restrictionSet a b) (hE : E ∈ B.restrictionSet c d) :
    D.Compatible H X E := by
  obtain ⟨_,rfl⟩ := mem_restrictionSet.mp hD
  obtain ⟨_,rfl⟩ := mem_restrictionSet.mp hE
  exact Or.inl (RadialShell.concentric_disjoint X B.shell.center hbc)

end Record

lemma dense_operation (hX : ∀v, binary (X v))
    {q δ ε a b : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ/1536)
    {F Z M : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hZ : H.LabeledArrangement G X q Z) {B : Record n} (hB : B ∈ Z)
    (hMZ : H.LabeledArrangement G X q M) (hMF : M ⊆ F)
    (hMball : ∀A ∈ M, A.shell = RadialShell.ball A.shell.center δ)
    (hno : B.avoided = none) (hwidth : 512*δ < B.shell.width)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a ≤ b)
    (hrange : ∀A ∈ M, a-δ < l1dist (X A.shell.center) (X B.shell.center) ∧
      l1dist (X A.shell.center) (X B.shell.center) < b+δ)
    (hinter : ∀A ∈ M, A.Interior H X 256 δ B)
    (horder : ∀A ∈ M, ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ A.excluded)
    (hcount : 765*δ ≤ (M.card : ℝ)*δ) (hdense : 3*(b-a) ≤ (M.card : ℝ)*δ) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*(M.card : ℝ)*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D ∈ M ∨ ∃c d, D = B.restriction c d ∧
        B.shell.inner ≤ c ∧ d ≤ B.shell.outer ∧ c < d := by
  let W₁ := B.restrictionSet B.shell.inner (a-2*δ)
  let W₂ := B.restrictionSet (b+2*δ) B.shell.outer
  let W := W₁∪W₂∪M
  have hbvalid := hZ.1 B hB
  have h1b : a-2*δ ≤ B.shell.outer := by linarith
  have h2a : B.shell.inner ≤ b+2*δ := by linarith
  have hW₁ : H.LabeledArrangement G X q W₁ :=
    B.restrictionSet_valid H G X hbvalid (le_refl _) h1b
  have hW₂ : H.LabeledArrangement G X q W₂ :=
    B.restrictionSet_valid H G X hbvalid h2a (le_refl _)
  have h12 : ∀D ∈ W₁, ∀E ∈ W₂, D.Compatible H X E := by
    intro D hD E hE
    exact B.restrictions_compatible H X (by linarith : a-2*δ ≤ b+2*δ) hD hE
  have hWM : ∀D ∈ W₁∪W₂, ∀A ∈ M, D.Compatible H X A := by
    intro D hD A hAM
    apply Record.compatible_symm H X
    left
    rw [hMball A hAM]
    rcases mem_union.mp hD with hD | hD
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hD
      exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith [(hrange A hAM).1])
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hD
      exact RadialShell.ball_disjoint_hollow_upper X _ _ (by linarith [(hrange A hAM).2])
  have hW12 := H.labeled_union G X hW₁ hW₂ h12
  have hW : H.LabeledArrangement G X q W := H.labeled_union G X hW12 hMZ hWM
  have hcompat : ∀D ∈ Z.erase B, ∀C ∈ W, D.Compatible H X C := by
    intro D hD C hC
    obtain ⟨hDB,hDZ⟩ := mem_erase.mp hD
    have hBD := H.labeled_pair G X hZ hB hDZ hDB.symm
    apply Record.compatible_symm H X
    rcases mem_union.mp hC with hC | hC
    · rcases mem_union.mp hC with hC | hC
      · have hh := B.restrictionSet_refines H X (le_refl _) h1b hC
        exact Record.compatible_heredity H X hBD hh.1 hh.2
      · have hh := B.restrictionSet_refines H X h2a (le_refl _) hC
        exact Record.compatible_heredity H X hBD hh.1 hh.2
    · have hancestor := Record.candidate_ancestor H (hMZ.1 C hC).1 hbvalid.1
        (horder C hC B hB) (hinter C hC).1
      exact Record.insert_compatible H G X hZ (hMZ.1 C hC).1 hB hDZ hDB.symm hancestor
        (horder C hC) (Record.interior_ball_subset H X hδ.le (hMball C hC) (hinter C hC))
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2.1] at hwidth
    linarith
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*(M.card : ℝ)*δ ≤
      ∑D ∈ W, Record.phaseToken F δ ε D := by
    have hd12 := H.labeled_sets_disjoint G X hX hW₁ h12
    have hdM := H.labeled_sets_disjoint G X hX hW12 hWM
    dsimp only [W]
    rw [sum_union hdM,sum_union hd12,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le]
    have hsumM : (∑D ∈ M, Record.phaseToken F δ ε D) =
        (M.card : ℝ)*AssignedAccounting.fresh δ ε := by
      calc
        _ = ∑D ∈ M, AssignedAccounting.fresh δ ε := sum_congr rfl (fun D hD => by
          simp only [Record.phaseToken,ite_eq_left (hMF hD)])
        _ = _ := by simp
    rw [hsumM,Record.phaseToken,ite_eq_right hBF,hno,Option.isSome_none]
    exact AssignedAccounting.dense_carve hδ.le hε (Nat.cast_nonneg _) hwidth.le
      (by dsimp [RadialShell.width]; ring) hdense hcount
  refine ⟨Z.erase B∪W,H.labeled_replace G X hZ hW B hcompat,
    H.replacement_credit G X hX hZ hB hcompat _ hcredit,?_⟩
  intro D hD
  rcases mem_union.mp hD with hD | hD
  · exact Or.inl (mem_of_mem_erase hD)
  right
  rcases mem_union.mp hD with hD | hD
  · right
    rcases mem_union.mp hD with hD | hD
    · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hD
      exact ⟨B.shell.inner,a-2*δ,heq,le_refl _,h1b,hpos⟩
    · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hD
      exact ⟨b+2*δ,B.shell.outer,heq,h2a,le_refl _,hpos⟩
  · exact Or.inl hD

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma central_refines {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) {a b c d : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hc : B.shell.inner ≤ c) (hd : d ≤ B.shell.outer) :
    (B.innerRecord t a b).Refines H X B ∧ (B.outsideRecord t c d).Refines H X B := by
  obtain ⟨h1,h2⟩ := central_conflict H hshape hno ht a b c d
  exact ⟨⟨RadialShell.restriction_subset X B.shell ha hb,h1 ▸ filter_subset _ _⟩,
    ⟨RadialShell.restriction_subset X B.shell hc hd,h2 ▸ filter_subset _ _⟩⟩

lemma hollow_token {F : Finset (Record n)} (hF : ∀D ∈ F, D.shell.ordinary = true)
    {B : Record n} (hB : B.shell.ordinary = false) (δ ε : ℝ) :
    phaseToken F δ ε B = AssignedAccounting.base B.avoided.isSome B.shell.width δ := by
  rw [phaseToken,ite_eq_right]
  intro hh
  have := hF B hh
  simp [hB] at this

end Record

lemma sparse_operation (hX : ∀v, binary (X v))
    {q δ ε a b M : ℝ} (hδ : 0 < δ)
    {F Z : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.shell.width = δ)
    (hZ : H.LabeledArrangement G X q Z) {B : Record n} (hB : B ∈ Z)
    (hno : B.avoided = none) (hwidth : 512*δ < B.shell.width)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hwide : 255*δ ≤ b-a) (hsparse : M*δ ≤ 3*(b-a))
    (hinner : (B.innerRecord t (a+δ) (b-δ)).Valid H G X q)
    (houter : (B.outsideRecord t a b).Valid H G X q) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*M*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D = B.innerRecord t (a+δ) (b-δ) ∨
        D = B.outsideRecord t a b ∨ ∃c d, D = B.restriction c d ∧
          B.shell.inner ≤ c ∧ d ≤ B.shell.outer ∧ c < d := by
  let C := B.innerRecord t (a+δ) (b-δ)
  let D := B.outsideRecord t a b
  let W₁ := B.restrictionSet B.shell.inner a
  let W₂ := B.restrictionSet b B.shell.outer
  let W₀ := W₁∪W₂
  let W₃ := insert C W₀
  let W := insert D W₃
  have hab : a ≤ b := by linarith
  have hv := hZ.1 B hB
  have hW₁ : H.LabeledArrangement G X q W₁ :=
    Record.restrictionSet_valid H G X hv (le_refl _) (hab.trans hb)
  have hW₂ : H.LabeledArrangement G X q W₂ :=
    Record.restrictionSet_valid H G X hv (ha.trans hab) (le_refl _)
  have h12 : ∀E ∈ W₁, ∀J ∈ W₂, E.Compatible H X J := by
    intro E hE J hJ
    exact Record.restrictions_compatible H X B hab hE hJ
  have hW₀ : H.LabeledArrangement G X q W₀ := H.labeled_union G X hW₁ hW₂ h12
  have hC0 : ∀E ∈ W₀, C.Compatible H X E := by
    intro E hE
    rcases mem_union.mp hE with hE | hE
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl ((RadialShell.concentric_disjoint X B.shell.center (by linarith : a ≤ a+δ)).symm)
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl (RadialShell.concentric_disjoint X B.shell.center (by linarith : b-δ ≤ b))
  have hW₃ : H.LabeledArrangement G X q W₃ := H.labeled_insert G X hW₀ hinner hC0
  have hD3 : ∀E ∈ W₃, D.Compatible H X E := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inr (Record.central_domain_disjoint H hv.1 hno ht (a+δ) (b-δ) a b).symm
    rcases mem_union.mp hE with hE | hE
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl ((RadialShell.concentric_disjoint X B.shell.center (le_refl a)).symm)
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl (RadialShell.concentric_disjoint X B.shell.center (le_refl b))
  have hW : H.LabeledArrangement G X q W := H.labeled_insert G X hW₃ houter hD3
  have hCD := Record.central_refines H X hv.1 hno ht
    (show B.shell.inner ≤ a+δ by linarith) (show b-δ ≤ B.shell.outer by linarith) ha hb
  have hWB : ∀E ∈ W, E.Refines H X B := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact hCD.2
    rcases mem_insert.mp hE with rfl | hE
    · exact hCD.1
    rcases mem_union.mp hE with hE | hE
    · exact Record.restrictionSet_refines H X (le_refl _) (hab.trans hb) hE
    · exact Record.restrictionSet_refines H X (ha.trans hab) (le_refl _) hE
  have hcompat : ∀J ∈ Z.erase B, ∀E ∈ W, J.Compatible H X E := by
    intro J hJ E hE
    obtain ⟨hne,hJ⟩ := mem_erase.mp hJ
    exact Record.compatible_symm H X (Record.compatible_heredity H X
      (H.labeled_pair G X hZ hB hJ hne.symm) (hWB E hE).1 (hWB E hE).2)
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2] at hwidth
    linarith
  have hDC : D ∉ W₃ := by
    intro hh
    exact Record.compatible_self_iff H X D hX houter.1 houter.2.2.1 (hD3 D hh)
  have hCW : C ∉ W₀ := by
    intro hh
    exact Record.compatible_self_iff H X C hX hinner.1 hinner.2.2.1 (hC0 C hh)
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*M*δ ≤
      ∑E ∈ W, Record.phaseToken F δ ε E := by
    have hdis := H.labeled_sets_disjoint G X hX hW₁ h12
    change _ ≤ ∑E ∈ insert D W₃, _
    rw [sum_insert hDC]
    change _ ≤ _+(∑E ∈ insert C W₀, _)
    rw [sum_insert hCW]
    change _ ≤ _+(_+(∑E ∈ W₁∪W₂, _))
    rw [sum_union hdis,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.hollow_token (fun D hD => (hF D hD).1) (show D.shell.ordinary = false from rfl),
      Record.hollow_token (fun D hD => (hF D hD).1) (show C.shell.ordinary = false from rfl),
      Record.phaseToken,ite_eq_right hBF]
    simp only [D,C,Record.innerRecord,Record.outsideRecord,RadialShell.hollow,
      hno,Option.isSome_none,Option.isSome_some,RadialShell.width]
    have hh := AssignedAccounting.sparse_carve hδ.le hwidth.le
      (R₁ := a-B.shell.inner) (R₂ := B.shell.outer-b) (L := b-a)
      (by dsimp [RadialShell.width]; ring) hwide hsparse
    rw [show b-δ-(a+δ) = b-a-2*δ by ring]
    dsimp only [RadialShell.width] at hh
    linarith
  refine ⟨Z.erase B∪W,H.labeled_replace G X hZ hW B hcompat,
    H.replacement_credit G X hX hZ hB hcompat _ hcredit,?_⟩
  intro E hE
  rcases mem_union.mp hE with hE | hE
  · exact Or.inl (mem_of_mem_erase hE)
  right
  rcases mem_insert.mp hE with heq | hE
  · exact Or.inr (Or.inl heq)
  rcases mem_insert.mp hE with heq | hE
  · exact Or.inl heq
  right; right
  rcases mem_union.mp hE with hE | hE
  · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hE
    exact ⟨B.shell.inner,a,heq,le_refl _,hab.trans hb,hpos⟩
  · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hE
    exact ⟨b,B.shell.outer,heq,ha.trans hab,le_refl _,hpos⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
