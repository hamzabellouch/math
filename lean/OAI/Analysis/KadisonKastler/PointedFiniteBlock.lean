import OAI.Analysis.KadisonKastler.PointedWordReduction
import OAI.Analysis.FactorGeneration.MatrixRefinement

namespace OAI

/-! # Full matrix blocks on finitely many product sites

The index type records one binary matrix index at each site. Distinct
sites commute, so their ordered products form a full matrix system.
This is the finite algebraic construction needed for the product stages.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {I : Type*}

abbrev MatrixSiteBlockIndex : List I → Type
  | [] => Unit
  | _ :: l => Fin 2 × MatrixSiteBlockIndex l

instance matrixSiteBlockIndexFintype : (l : List I) → Fintype (MatrixSiteBlockIndex l)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: l => by
    letI := matrixSiteBlockIndexFintype l
    exact inferInstanceAs (Fintype (Fin 2 × MatrixSiteBlockIndex l))

instance matrixSiteBlockIndexDecidableEq : (l : List I) →
    DecidableEq (MatrixSiteBlockIndex l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | _ :: l => by
    letI := matrixSiteBlockIndexDecidableEq l
    exact inferInstanceAs (DecidableEq (Fin 2 × MatrixSiteBlockIndex l))

def matrixSiteBlockZero : (l : List I) → MatrixSiteBlockIndex l
  | [] => ()
  | _ :: l => (0, matrixSiteBlockZero l)

instance (l : List I) : Nonempty (MatrixSiteBlockIndex l) := ⟨matrixSiteBlockZero l⟩

def matrixSiteBlockMapEquiv {J : Type*} (f : I → J) :
    (l : List I) → MatrixSiteBlockIndex l ≃ MatrixSiteBlockIndex (l.map f)
  | [] => Equiv.refl _
  | _ :: l => (Equiv.refl (Fin 2)).prodCongr (matrixSiteBlockMapEquiv f l)

def matrixSiteBlockIndexOfFunction : (l : List I) → (I → Fin 2) → MatrixSiteBlockIndex l
  | [], _ => ()
  | i :: l, f => (f i, matrixSiteBlockIndexOfFunction l f)

theorem matrixSiteBlockIndexOfFunction_congr (l : List I) {f g : I → Fin 2}
    (h : ∀ i ∈ l, f i = g i) :
    matrixSiteBlockIndexOfFunction l f = matrixSiteBlockIndexOfFunction l g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    exact Prod.ext (h i (by simp)) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem matrixSiteBlockIndexOfFunction_surjective (l : List I) (hl : l.Nodup) :
    Function.Surjective (matrixSiteBlockIndexOfFunction l) := by
  classical
  induction l with
  | nil => intro r; cases r; exact ⟨fun _ => 0, rfl⟩
  | cons i l ih =>
    intro r
    obtain ⟨f, hf⟩ := ih (List.nodup_cons.mp hl).2 r.2
    refine ⟨Function.update f i r.1, Prod.ext ?_ ?_⟩
    · change Function.update f i r.1 i = r.1
      exact Function.update_self _ _ _
    apply Eq.trans (matrixSiteBlockIndexOfFunction_congr l ?_) hf
    intro j hj
    exact Function.update_of_ne (fun h : j = i => (List.nodup_cons.mp hl).1 (h ▸ hj)) _ _

def matrixSiteBlockWeight (ν : I → ℝ) :
    (l : List I) → MatrixSiteBlockIndex l → MatrixSiteBlockIndex l → ℂ
  | [], _, _ => 1
  | i :: l, r, c =>
    (if r.1 = c.1 then (twoSiteWeight (ν i) r.1 : ℂ) else 0) *
      matrixSiteBlockWeight ν l r.2 c.2

theorem matrixSiteBlockWeight_ofFunction (ν : I → ℝ) (l : List I) (r c : I → Fin 2) :
    matrixSiteBlockWeight ν l (matrixSiteBlockIndexOfFunction l r)
      (matrixSiteBlockIndexOfFunction l c) =
      (l.map fun i => if r i = c i then (twoSiteWeight (ν i) (r i) : ℂ) else 0).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [matrixSiteBlockWeight, matrixSiteBlockIndexOfFunction,
      List.map_cons, List.prod_cons, ih]
    rfl

theorem matrixSiteBlockWeight_map {J : Type*} (ν : I → ℝ) (η : J → ℝ) (f : I → J)
    (hf : ∀ i, η (f i) = ν i) (l : List I) (r c : MatrixSiteBlockIndex l) :
    matrixSiteBlockWeight η (l.map f) (matrixSiteBlockMapEquiv f l r)
      (matrixSiteBlockMapEquiv f l c) = matrixSiteBlockWeight ν l r c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (if r.1 = c.1 then (twoSiteWeight (η (f i)) r.1 : ℂ) else 0) * _ = _
    change (if r.1 = c.1 then (twoSiteWeight (η (f i)) r.1 : ℂ) else 0) *
      matrixSiteBlockWeight η (l.map f) (matrixSiteBlockMapEquiv f l r.2)
        (matrixSiteBlockMapEquiv f l c.2) = _
    rw [hf i, ih]
    rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω ν)

def blockEntry : (l : List I) → MatrixSiteBlockIndex l → MatrixSiteBlockIndex l →
    (H →L[ℂ] H)
  | [], _, _ => 1
  | i :: l, r, c => (S.site i).entry r.1 c.1 * blockEntry l r.2 c.2

theorem blockEntry_ofFunction (l : List I) (r c : I → Fin 2) :
    S.blockEntry l (matrixSiteBlockIndexOfFunction l r)
      (matrixSiteBlockIndexOfFunction l c) =
      (l.map fun i => (S.site i).entry (r i) (c i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [blockEntry, matrixSiteBlockIndexOfFunction,
      List.map_cons, List.prod_cons, ih]

theorem blockEntry_moment (l : List I) (hl : l.Nodup) (r c : MatrixSiteBlockIndex l) :
    inner ℂ Ω (S.blockEntry l r c Ω) = matrixSiteBlockWeight ν l r c := by
  obtain ⟨r, rfl⟩ := matrixSiteBlockIndexOfFunction_surjective l hl r
  obtain ⟨c, rfl⟩ := matrixSiteBlockIndexOfFunction_surjective l hl c
  rw [S.blockEntry_ofFunction, matrixSiteBlockWeight_ofFunction]
  exact S.moments l hl r c

theorem site_commutes_blockEntry (i : I) (a b : Fin 2) (l : List I)
    (hi : i ∉ l) (r c : MatrixSiteBlockIndex l) :
    Commute ((S.site i).entry a b) (S.blockEntry l r c) := by
  induction l with
  | nil => exact Commute.one_right _
  | cons j l ih =>
    exact (S.commuting i j (fun h => hi (by simp [h])) a b r.1 c.1).mul_right
      (ih (fun h => hi (List.mem_cons_of_mem _ h)) r.2 c.2)

theorem blockEntry_star (l : List I) (hl : l.Nodup)
    (r c : MatrixSiteBlockIndex l) : star (S.blockEntry l r c) = S.blockEntry l c r := by
  induction l with
  | nil => simp [blockEntry]
  | cons i l ih =>
    rw [blockEntry, star_mul, ih (List.nodup_cons.mp hl).2, (S.site i).star_entry]
    exact (S.site_commutes_blockEntry i c.1 r.1 l
      (List.nodup_cons.mp hl).1 c.2 r.2).eq.symm

theorem blockEntry_mul (l : List I) (hl : l.Nodup)
    (r c a b : MatrixSiteBlockIndex l) :
    S.blockEntry l r c * S.blockEntry l a b =
      if c = a then S.blockEntry l r b else 0 := by
  induction l with
  | nil => simp [blockEntry, MatrixSiteBlockIndex]
  | cons i l ih =>
    rw [blockEntry, blockEntry,
      (S.site_commutes_blockEntry i a.1 b.1 l
        (List.nodup_cons.mp hl).1 r.2 c.2).symm.mul_mul_mul_comm]
    rw [(S.site i).mul_entry, ih (List.nodup_cons.mp hl).2]
    by_cases h₁ : c.1 = a.1 <;> by_cases h₂ : c.2 = a.2 <;>
      simp [h₁, h₂, Prod.ext_iff, blockEntry]

theorem blockEntry_total (l : List I) :
    ∑ r, S.blockEntry l r r = 1 := by
  induction l with
  | nil => simp [blockEntry, MatrixSiteBlockIndex]
  | cons i l ih =>
    change (∑ r : Fin 2 × MatrixSiteBlockIndex l,
      (S.site i).entry r.1 r.1 * S.blockEntry l r.2 r.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ih, mul_one, (S.site i).total]

def finiteBlock (l : List I) (hl : l.Nodup) :
    MatrixUnitSystem (MatrixSiteBlockIndex l) (H →L[ℂ] H) where
  entry := S.blockEntry l
  star_entry := S.blockEntry_star l hl
  mul_entry := S.blockEntry_mul l hl
  total := S.blockEntry_total l

theorem finiteBlock_cons (i : I) (l : List I) (hl : (i :: l).Nodup) :
    S.finiteBlock (i :: l) hl =
      (S.site i).product (S.finiteBlock l (List.nodup_cons.mp hl).2)
        (S.site_commutes_blockEntry i · · l (List.nodup_cons.mp hl).1) := by
  rfl

theorem finiteBlock_le (l : List I) (hl : l.Nodup) :
    (S.finiteBlock l hl).algebra ≤ M.toStarSubalgebra := by
  apply ((S.finiteBlock l hl).algebra_le_iff _).mpr
  intro r c
  change S.blockEntry l r c ∈ M
  induction l with
  | nil => exact M.one_mem
  | cons i l ih =>
    apply M.mul_mem
    · have he := subset_generatedVonNeumannAlgebra _
        ((le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem r.1 c.1))
      exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H =>
        (S.site i).entry r.1 c.1 ∈ N) S.generates) he
    · exact ih (List.nodup_cons.mp hl).2 r.2 c.2

theorem finiteBlock_le_of_sites_le (l : List I) (hl : l.Nodup)
    (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (hT : ∀ i ∈ l, (S.site i).algebra ≤ T) : (S.finiteBlock l hl).algebra ≤ T := by
  apply ((S.finiteBlock l hl).algebra_le_iff _).mpr
  intro r c
  change S.blockEntry l r c ∈ T
  induction l with
  | nil => exact T.one_mem
  | cons i l ih =>
    exact T.mul_mem (hT i (by simp) ((S.site i).entry_mem _ _))
      (ih (List.nodup_cons.mp hl).2 (fun j hj => hT j (List.mem_cons_of_mem _ hj)) r.2 c.2)

theorem site_le_finiteBlock (l : List I) (hl : l.Nodup) (i : I) (hi : i ∈ l) :
    (S.site i).algebra ≤ (S.finiteBlock l hl).algebra := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    let E := S.finiteBlock (j :: l) hl
    have htail : (S.finiteBlock l (List.nodup_cons.mp hl).2).algebra ≤ E.algebra := by
      apply ((S.finiteBlock l (List.nodup_cons.mp hl).2).algebra_le_iff _).mpr
      intro a b
      have he : (S.finiteBlock l (List.nodup_cons.mp hl).2).entry a b =
          ∑ r : Fin 2, E.entry (r, a) (r, b) := by
        change S.blockEntry l a b = ∑ r : Fin 2,
          (S.site j).entry r r * S.blockEntry l a b
        rw [← Finset.sum_mul, (S.site j).total, one_mul]
      rw [he]
      exact E.algebra.sum_mem fun r _ => E.entry_mem _ _
    rcases List.mem_cons.mp hi with hij | hi
    · subst i
      apply ((S.site j).algebra_le_iff _).mpr
      intro a b
      have he : (S.site j).entry a b =
          ∑ r : MatrixSiteBlockIndex l, E.entry (a, r) (b, r) := by
        change (S.site j).entry a b = ∑ r : MatrixSiteBlockIndex l,
          (S.site j).entry a b * S.blockEntry l r r
        rw [← Finset.mul_sum, S.blockEntry_total, mul_one]
      rw [he]
      exact E.algebra.sum_mem fun r _ => E.entry_mem _ _
    · exact (ih (List.nodup_cons.mp hl).2 hi).trans htail

theorem finiteBlock_mono {l k : List I} (hl : l.Nodup) (hk : k.Nodup)
    (h : ∀ i ∈ l, i ∈ k) :
    (S.finiteBlock l hl).algebra ≤ (S.finiteBlock k hk).algebra :=
  S.finiteBlock_le_of_sites_le l hl _ (fun i hi => S.site_le_finiteBlock k hk i (h i hi))

theorem finiteBlock_commuting {l k : List I} (h : List.Disjoint l k)
    (r c : MatrixSiteBlockIndex l) (a b : MatrixSiteBlockIndex k) :
    Commute (S.blockEntry l r c) (S.blockEntry k a b) := by
  induction l with
  | nil => exact Commute.one_left _
  | cons i l ih =>
    apply Commute.mul_left
    · exact S.site_commutes_blockEntry i r.1 c.1 k
        (fun hi => (List.disjoint_left.mp h) (by simp) hi) a b
    · exact ih (List.disjoint_left.mpr (fun j hj hk =>
        (List.disjoint_left.mp h) (List.mem_cons_of_mem _ hj) hk)) r.2 c.2

end PointedMatrixSites

end

end KadisonKastler

end OAI
