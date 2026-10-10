import OAI.Probability.DilutedSpin.MarkerHistoryTransport

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance markerJointHistoryDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
noncomputable local instance markerJointHistoryDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] {n : ℕ}

def markerEmbedding {D : Type} (a : D) : Option C → D ⊕ C :=
  Option.elim' (Sum.inl a) Sum.inr

omit [Fintype C] in
lemma markerEmbedding_injective {D : Type} (a : D) : Function.Injective (markerEmbedding (C := C) a) := by
  intro x y h
  cases x <;> cases y <;> simp_all [markerEmbedding]

/-- Exact enlargement of the signed marker history by all the protected old
paths. The matrix constraints force the added tree to separate before the
old tree branches; no old-position branch is silently retained or discarded. -/
theorem marker_history_augment
    (S T Q : PrescribedTree n) (a : S.Leaf) (q : Option C → T.Leaf)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y : Option C,
      splitDepth T (q x) (q y)=
        splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a)<splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (cs : List C) (hcs : cs.Nodup)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    weightedMatrixHistory Q (Sum.elim qold qfresh)
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z *
        (F (fun d => R.pathAt (pos (Sum.inl d)) z) *
          A (fun c => R.pathAt (pos (markerEmbedding a c)) z))))
      m (cs.map Sum.inr) S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (fun _ => 1) := by
  let e := markerEmbedding (C := C) a
  let P : Finset (S.Leaf ⊕ C) := Finset.univ.image Sum.inl
  let V := fun (R : PrescribedTree n) (pos : Option C → R.Leaf) (g : Sample Ω R → ℝ) =>
    if ∀ x y, splitDepth R (pos x) (pos y)=splitDepth T (q x) (q y)
    then (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)) else 0
  have hdis : ∀ c ∈ cs.map Sum.inr, c ∉ P := by
    intro c hc hp
    rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
    simp [P] at hp
  have hsplit : ∀ x ∈ P, ∀ y ∈ P,
      splitDepth S (Sum.elim id (fun _ : C => a) x) (Sum.elim id (fun _ : C => a) y)=
        splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y) := by
    rintro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨d,hd,rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
    exact hold d b
  rw [weightedMatrixHistory_drop_available T q _ m none _ (hcs.map (Option.some_injective C))
    (by simp) S (Finset.univ.erase a) id (fun _ => a) (by
      intro c hc d hd
      rcases List.mem_map.mp hc with ⟨c,hc,rfl⟩
      have hs := hsep c d
      simp only [id_eq,hold,hmarker,Option.elim']
      rw [splitDepth_symm Q (qold d) (qold a)]
      exact (ne_of_lt hs).symm) _]
  change labeledHistory m V (cs.map some) S ∅ id (fun _ => a) _ = _
  have hre := labeledHistory_reindex m e (markerEmbedding_injective a) V (cs.map some)
    S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (fun z => F (fun d => S.pathAt d z))
  have hmap : (cs.map some).map e=cs.map Sum.inr := by simp [List.map_map,e,markerEmbedding,Function.comp_def]
  have hpos : Sum.elim id (fun _ : C => a) ∘ e = fun _ => a := by
    funext c; cases c <;> rfl
  rw [hmap,hpos] at hre
  rw [← hre]
  let G := fun x : (S.Leaf ⊕ C → FinitePath Ω n) => F (fun d => x (Sum.inl d))
  have hpull := labeledHistory_protected_function m (fun R pos g => V R (pos ∘ e) g)
    P G (by
      intro x y h
      apply congrArg F
      funext d
      exact h (Sum.inl d) (by simp [P])) (cs.map Sum.inr) hdis
    S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (fun _ => 1)
  simp only [one_mul,G,Sum.elim_inl,id_eq] at hpull
  rw [← hpull]
  unfold weightedMatrixHistory
  apply labeledHistory_congr_protected_split m _ _ P
    (fun x y => splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y)) _
    (cs.map Sum.inr) hdis S ∅ id _ hsplit
  intro R pos hR g
  have hr : ∀ d b, splitDepth R (pos (Sum.inl d)) (pos (Sum.inl b))=
      splitDepth Q (qold d) (qold b) := fun d b => hR _ (by simp [P]) _ (by simp [P])
  have hm := marker_matrix_iff R Q (fun d => pos (Sum.inl d)) (fun c => pos (Sum.inr c)) a qold qfresh hr hsep
  have hopt : pos ∘ e = Option.elim' (pos (Sum.inl a)) (fun c => pos (Sum.inr c)) := by
    funext c; cases c <;> rfl
  have hsum : Sum.elim (fun d => pos (Sum.inl d)) (fun c => pos (Sum.inr c)) = pos := by
    funext c; cases c <;> rfl
  have htest : (∀ x y, splitDepth R ((pos ∘ e) x) ((pos ∘ e) y)=splitDepth T (q x) (q y)) ↔
      (∀ x y, splitDepth R (pos x) (pos y)=splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y)) := by
    simpa only [hmarker,hopt,hsum] using hm
  dsimp only [V]
  simp only [htest]
  split_ifs
  · apply FiniteLaw.expect_congr
    intro z
    simp only [Function.comp_def,e,mul_assoc]
  · rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
