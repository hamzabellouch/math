import OAI.Probability.DilutedSpin.MarkerJointHistory

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance markerNormalizationPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] {n : ℕ}

omit [Fintype C] in
lemma all_old_history_cover (S : PrescribedTree n) (a : S.Leaf) :
    HistoryCover S (∅ : Finset S.Leaf) id
      (Finset.univ.image (Sum.inl : S.Leaf → S.Leaf ⊕ C)) (Sum.elim id (fun _ => a)) := by
  classical
  refine ⟨⟨Function.injective_id, ?_, by simp⟩, ?_⟩
  · intro x hx y hy h
    rcases Finset.mem_image.mp hx with ⟨d,hd,rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
    exact congrArg Sum.inl h
  · intro b
    exact Or.inr ⟨Sum.inl b, by simp, rfl⟩

lemma marker_history_joint_ratio (S T Q : PrescribedTree n) (a : S.Leaf)
    (q : Option C → T.Leaf) (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a)<splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    (partialKappa Q m (Finset.univ.image (Sum.elim qold qfresh)) /
      partialKappa Q m ((Finset.univ.image Sum.inl).image (Sum.elim qold qfresh))) *
      (Q.sampleLaw K).expect (fun z => F (fun d => Q.pathAt (qold d) z) *
        A (fun c => Q.pathAt (Option.elim' (qold a) qfresh c) z)) := by
  classical
  have hmem (c : C) : c ∈ cs := by
    have : c ∈ cs.toFinset := by rw [hfull]; simp
    simpa using this
  rw [marker_history_augment S T Q a q qold qfresh hold hmarker hsep K m cs hcs F A]
  have h := weightedMatrixHistory_protected_one Q (Sum.elim qold qfresh) hqQ K m hm hp hend
    (cs.map Sum.inr) (hcs.map Sum.inr_injective) (Finset.univ.image Sum.inl)
    (by exact ⟨Sum.inl a, by simp⟩) (by
      intro c hc
      rcases List.mem_map.mp hc with ⟨c,hc,rfl⟩
      simp) (by
      ext x
      cases x with
      | inl d => simp
      | inr c => simp [hmem])
    S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (all_old_history_cover S a)
    (by
      rintro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨d,hd,rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
      exact hold d b)
    (fun x => F (fun d => x (Sum.inl d))*A (x ∘ markerEmbedding a))
  convert h using 1
  · rfl
  · congr 2
    funext z
    congr 1
    apply congrArg A
    funext c
    cases c <;> rfl

/-- The exact marker history coefficient is the anchor-alone kappa; this
proof obtains the equality by normalization of the *same* histories, without
an independent combinatorial simplification of kappa. -/
theorem marker_history_joint (S T Q : PrescribedTree n) (a : S.Leaf)
    (q : Option C → T.Leaf) (hq : Function.Bijective q)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a)<splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    partialKappa T m (Finset.univ.image q) *
      (Q.sampleLaw K).expect (fun z => F (fun d => Q.pathAt (qold d) z) *
        A (fun c => Q.pathAt (Option.elim' (qold a) qfresh c) z)) := by
  classical
  have hmem (c : C) : c ∈ cs := by
    have : c ∈ cs.toFinset := by rw [hfull]; simp
    simpa using this
  have hn := weightedMatrixHistory_one T q hq K m hm hp hend none
    (cs.map some) (hcs.map (Option.some_injective C)) (by simp)
    (by ext x; cases x <;> simp [hmem]) S a (fun _ => 1)
  have hr := marker_history_joint_ratio S T Q a q qold qfresh hqQ hold hmarker hsep
    K m hm hp hend cs hcs hfull (fun _ => 1) (fun _ => 1)
  simp only [FiniteLaw.expect_const,mul_one] at hn hr
  rw [marker_history_joint_ratio S T Q a q qold qfresh hqQ hold hmarker hsep
    K m hm hp hend cs hcs hfull F A, ← hr, hn]

end DilutedSpinGlass.PrescribedTree

end

end OAI
