import OAI.Analysis.KadisonKastler.PointedFiniteBlock
import OAI.Analysis.KadisonKastler.PointedWordMoments
import OAI.Analysis.KadisonKastler.MatrixProductStateSwap

namespace OAI

/-! # Product moments for disjoint finite matrix blocks -/

namespace KadisonKastler

noncomputable section

variable {I : Type*}

def matrixSiteBlockWord : (l : List I) →
    MatrixSiteBlockIndex l → MatrixSiteBlockIndex l → MatrixSiteWord I
  | [], _, _ => []
  | i :: l, r, c => (i, r.1, c.1) :: matrixSiteBlockWord l r.2 c.2

theorem matrixSiteBlockWord_indices (l : List I) (r c : MatrixSiteBlockIndex l) :
    MatrixSiteWord.indices (matrixSiteBlockWord l r c) = l := by
  induction l with
  | nil => rfl
  | cons i l ih => exact congrArg (List.cons i) (ih r.2 c.2)

theorem matrixSiteBlockWord_weight (ν : I → ℝ) (l : List I)
    (r c : MatrixSiteBlockIndex l) :
    MatrixSiteWord.weight ν (matrixSiteBlockWord l r c) = matrixSiteBlockWeight ν l r c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change _ * MatrixSiteWord.weight ν (matrixSiteBlockWord l r.2 c.2) = _
    rw [ih]
    rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω ν)

private theorem wordWeight_append (w v : MatrixSiteWord I) :
    MatrixSiteWord.weight ν (w ++ v) =
      MatrixSiteWord.weight ν w * MatrixSiteWord.weight ν v := by
  simp only [MatrixSiteWord.weight, List.map_append, List.prod_append]

theorem blockWord_eval (l : List I) (r c : MatrixSiteBlockIndex l) :
    MatrixSiteWord.eval S.site (matrixSiteBlockWord l r c) = S.blockEntry l r c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (S.site i).entry r.1 c.1 *
      MatrixSiteWord.eval S.site (matrixSiteBlockWord l r.2 c.2) =
      (S.site i).entry r.1 c.1 * S.blockEntry l r.2 c.2
    exact congrArg ((S.site i).entry r.1 c.1 * ·) (ih r.2 c.2)

theorem disjoint_blockEntry_moment {l k : List I} (hl : l.Nodup) (hk : k.Nodup)
    (hd : List.Disjoint l k) (r c : MatrixSiteBlockIndex l) (a b : MatrixSiteBlockIndex k) :
    productVectorState Ω (S.blockEntry l r c * S.blockEntry k a b) =
      matrixSiteBlockWeight ν l r c * matrixSiteBlockWeight ν k a b := by
  have hnodup : (MatrixSiteWord.indices
      (matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b)).Nodup := by
    simp only [MatrixSiteWord.indices, List.map_append]
    change (MatrixSiteWord.indices (matrixSiteBlockWord l r c) ++
      MatrixSiteWord.indices (matrixSiteBlockWord k a b)).Nodup
    rw [matrixSiteBlockWord_indices, matrixSiteBlockWord_indices]
    exact List.nodup_append'.mpr ⟨hl, hk, hd⟩
  have hm := S.word_moment_of_nodup
    (matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) hnodup
  change productVectorState Ω (MatrixSiteWord.eval S.site
    (matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b)) = _ at hm
  rw [MatrixSiteWord.eval_append, S.blockWord_eval, S.blockWord_eval] at hm
  rw [wordWeight_append, matrixSiteBlockWord_weight, matrixSiteBlockWord_weight] at hm
  exact hm

theorem disjoint_block_algebra_independent {l k : List I} (hl : l.Nodup) (hk : k.Nodup)
    (hd : List.Disjoint l k) (r c : MatrixSiteBlockIndex l)
    (b : (S.finiteBlock k hk).algebra) :
    productVectorState Ω (S.blockEntry l r c * b.val) =
      productVectorState Ω (S.blockEntry l r c) * productVectorState Ω b.val := by
  obtain ⟨a, ha⟩ := ((S.finiteBlock k hk).mem_algebra b.val).mp b.property
  let φ := productVectorLinear Ω
  have he (i j : MatrixSiteBlockIndex k) :
      φ (S.blockEntry l r c * S.blockEntry k i j) =
        φ (S.blockEntry l r c) * φ (S.blockEntry k i j) := by
    change productVectorState Ω (S.blockEntry l r c * S.blockEntry k i j) =
      productVectorState Ω (S.blockEntry l r c) * productVectorState Ω (S.blockEntry k i j)
    rw [S.disjoint_blockEntry_moment hl hk hd]
    exact congrArg₂ (· * ·) (S.blockEntry_moment l hl r c).symm
      (S.blockEntry_moment k hk i j).symm
  change φ (S.blockEntry l r c * b.val) = φ (S.blockEntry l r c) * φ b.val
  rw [← ha]
  change φ (S.blockEntry l r c *
    ∑ i, ∑ j, a i j • S.blockEntry k i j) =
    φ (S.blockEntry l r c) * φ (∑ i, ∑ j, a i j • S.blockEntry k i j)
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, he, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem disjoint_three_blockEntry_moment {l k m : List I}
    (hl : l.Nodup) (hk : k.Nodup) (hm : m.Nodup)
    (hlk : List.Disjoint l k) (hlm : List.Disjoint l m) (hkm : List.Disjoint k m)
    (r c : MatrixSiteBlockIndex l) (a b : MatrixSiteBlockIndex k)
    (d e : MatrixSiteBlockIndex m) :
    productVectorState Ω ((S.blockEntry l r c * S.blockEntry k a b) *
      S.blockEntry m d e) = matrixSiteBlockWeight ν l r c *
        matrixSiteBlockWeight ν k a b * matrixSiteBlockWeight ν m d e := by
  have hdisj : List.Disjoint (l ++ k) m := by
    apply List.disjoint_left.mpr
    intro i hi him
    rcases List.mem_append.mp hi with hi | hi
    · exact List.disjoint_left.mp hlm hi him
    · exact List.disjoint_left.mp hkm hi him
  have hnodup : (MatrixSiteWord.indices
      ((matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) ++
        matrixSiteBlockWord m d e)).Nodup := by
    simp only [MatrixSiteWord.indices, List.map_append]
    change ((MatrixSiteWord.indices (matrixSiteBlockWord l r c) ++
      MatrixSiteWord.indices (matrixSiteBlockWord k a b)) ++
      MatrixSiteWord.indices (matrixSiteBlockWord m d e)).Nodup
    rw [matrixSiteBlockWord_indices, matrixSiteBlockWord_indices, matrixSiteBlockWord_indices]
    exact (hl.append hk hlk).append hm hdisj
  have h := S.word_moment_of_nodup
    ((matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) ++
      matrixSiteBlockWord m d e) hnodup
  change productVectorState Ω (MatrixSiteWord.eval S.site
    ((matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) ++
      matrixSiteBlockWord m d e)) = _ at h
  rw [MatrixSiteWord.eval_append, MatrixSiteWord.eval_append,
    S.blockWord_eval, S.blockWord_eval, S.blockWord_eval] at h
  rw [wordWeight_append, wordWeight_append, matrixSiteBlockWord_weight,
    matrixSiteBlockWord_weight, matrixSiteBlockWord_weight] at h
  exact h

end PointedMatrixSites

end

end KadisonKastler

end OAI
