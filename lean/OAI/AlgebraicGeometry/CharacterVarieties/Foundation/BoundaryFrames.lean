import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.SplitFlags

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Change of bases on the named graded fibers. -/
def GradeDiagonal (a : α → ℕ) (M : Matrix α α R) : Prop :=
  ∀ i j, a i≠a j → M i j=0

lemma conjugate_flag_entries (a : α → ℕ) (w : MatrixIso R α α)
    (hw : GradeDiagonal a w.val) (hi : GradeDiagonal a w.inv)
    (M : Matrix α α R) (hM : ∀ i j,a j≤a i → M i j=(1 : Matrix α α R) i j) :
    ∀ i j,a j≤a i → (w.inv*M*w.val) i j=(1 : Matrix α α R) i j := by
  intro i j hij
  have hh : (w.inv*M*w.val) i j=(w.inv*(1 : Matrix α α R)*w.val) i j := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : a k=a j
    · rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hil : a i=a l
      · rw [hM l k (by omega)]
      · rw [hi i l hil]
        simp
    · rw [hw k j hkj]
      simp
  rw [hh,Matrix.mul_one,w.inv_val]

/-- Common block changes on the source and common ambient changes on the TARGET preserve both flags
and their specified grade maps. -/
lemma sameFramedFlag_bases (a : α → ℕ) (x y : MatrixIso R α β)
    (w : MatrixIso R α α) (z : MatrixIso R β β)
    (hw : GradeDiagonal a w.val) (hi : GradeDiagonal a w.inv)
    (h : SameFramedFlag a x.linearEquiv y.linearEquiv) :
    SameFramedFlag a ((w.trans x).trans z).linearEquiv
      ((w.trans y).trans z).linearEquiv := by
  rw [sameFramedFlag_iff] at h ⊢
  have hh := conjugate_flag_entries a w hw hi (y.inv*x.val) h
  intro i j hij
  convert hh i j hij using 1
  simp only [trans]
  apply congrArg (fun M : Matrix α α R => M i j)
  calc
    (w.inv*y.inv*z.inv)*(z.val*(x.val*w.val)) =
        w.inv*y.inv*(z.inv*z.val)*(x.val*w.val) := by simp only [Matrix.mul_assoc]
    _ = w.inv*(y.inv*x.val)*w.val := by rw [z.inv_val]; simp [Matrix.mul_assoc]

lemma block_GradeDiagonal {ι : Type*} [Fintype ι] {d : ι → Type*}
    [∀ i,Fintype (d i)] (a : ι → ℕ) (w : ∀ i,MatrixIso R (d i) (d i)) :
    GradeDiagonal (fun x : (i : ι) × d i => a x.1) (block w).val ∧
    GradeDiagonal (fun x : (i : ι) × d i => a x.1) (block w).inv := by
  constructor <;> rintro ⟨i,x⟩ ⟨j,y⟩ h
  · apply Matrix.blockDiagonal'_apply_ne
    exact fun hij => h (congrArg a hij)
  · apply Matrix.blockDiagonal'_apply_ne
    exact fun hij => h (congrArg a hij)

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[simp] theorem trans_symm_self (x : MatrixIso R α β) : x.trans x.symm=refl := by
  apply ext <;> simp only [trans,symm,refl,x.inv_val]
@[simp] theorem symm_trans_self (x : MatrixIso R α β) : x.symm.trans x=refl := by
  apply ext <;> simp only [trans,symm,refl,x.val_inv]
@[simp] theorem refl_trans (x : MatrixIso R α β) : (refl (R:=R)).trans x=x := by
  apply ext <;> simp only [trans,refl,Matrix.mul_one,Matrix.one_mul]
@[simp] theorem trans_refl (x : MatrixIso R α β) : x.trans refl=x := by
  apply ext <;> simp only [trans,refl,Matrix.mul_one,Matrix.one_mul]
@[simp] theorem reindex_symm_eq {α' β' : Type*} [Fintype α'] [Fintype β']
    (x : MatrixIso R α β) (a : α' ≃ α) (b : β' ≃ β) :
    (x.reindex a b).symm=x.symm.reindex b a := rfl

@[simp] theorem sum_trans {α' β' γ' : Type*} [Fintype α'] [Fintype β'] [Fintype γ']
    (x : MatrixIso R α β) (y : MatrixIso R β γ)
    (x' : MatrixIso R α' β') (y' : MatrixIso R β' γ') :
    (x.sum x').trans (y.sum y')=(x.trans y).sum (x'.trans y') := by
  apply ext <;> simp [trans,sum,Matrix.fromBlocks_multiply]

@[simp] theorem sum_symm {α' β' : Type*} [Fintype α'] [Fintype β']
    (x : MatrixIso R α β) (x' : MatrixIso R α' β') :
    (x.sum x').symm=x.symm.sum x'.symm := rfl

@[simp] theorem congr_gauge (e : α ≃ β) (w : MatrixIso R α α) :
    (congr (R:=R) e).trans (w.reindex e.symm e.symm)=w.trans (congr e) := by
  have he : ∀ (b : β) (a : α), b=e a ↔ a=e.symm b := by
    intro b a
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  apply ext <;> ext i j <;>
    simp only [trans,congr,reindex,refl,Matrix.mul_apply,Matrix.submatrix_apply,
      Equiv.coe_refl,Matrix.one_apply,ite_mul,mul_ite,
      one_mul,mul_one,zero_mul,mul_zero]
  all_goals
    simp only [id_eq,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · simp [he]
  · simp_rw [eq_comm,he]
    simp


end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[simp] theorem reindex_reindex_eq (x : MatrixIso R α β)
    (e : γ ≃ α) (f : δ ≃ β) {ε ζ : Type*} [Fintype ε] [Fintype ζ]
    (g : ε ≃ γ) (h : ζ ≃ δ) :
    (x.reindex e f).reindex g h=x.reindex (g.trans e) (h.trans f) := rfl

lemma bases_reindex (x : MatrixIso R α β) (C : MatrixIso R α α)
    (P : MatrixIso R β β) (e : γ ≃ α) (f : δ ≃ β) :
    ((C.symm.trans x).trans P).reindex e f=
      ((C.reindex e e).symm.trans (x.reindex e f)).trans (P.reindex f f) := by
  rw [reindex_trans _ P e f f,reindex_trans _ x e e f]
  rfl

omit [Fintype α] [Fintype γ] in
lemma GradeDiagonal_reindex (a : α → ℕ) (M : Matrix α α R)
    (h : GradeDiagonal a M) (e : γ ≃ α) :
    GradeDiagonal (a ∘ e) (M.submatrix e e) := by
  intro i j hij
  exact h (e i) (e j) hij

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {m : ℕ} {t : Passage m} (d : LocalRanks (.passage m t))
local instance : Fintype ((Kind.passage m t).table.Child false) := fintypeChild (.passage m t) false
local instance : Fintype (d.Columns false) := d.fintypeColumns false
local instance : Fintype (d.Columns true) := d.fintypeColumns true

/-- Rebase every named fiber continued through a passage, with the exact permutation and rank
equalities of the original vertex. -/
def changePassageBases (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (C : MatrixIso R (d.Columns false) (d.Columns false))
    (P : MatrixIso R (d.Parent false) (d.Parent false)) :
    ∀ p, MatrixIso R (d.Columns p) (d.Parent p)
  | false => (C.symm.trans (f false)).trans P
  | true => ((C.reindex d.passageColumns.symm d.passageColumns.symm).symm.trans
      (f true)).trans (P.reindex d.passageParent.symm d.passageParent.symm)

lemma changePassageBases_holds
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (C : MatrixIso R (d.Columns false) (d.Columns false))
    (P : MatrixIso R (d.Parent false) (d.Parent false))
    (hC : MatrixIso.GradeDiagonal (fun j => passageGrade t j.1) C.val)
    (hI : MatrixIso.GradeDiagonal (fun j => passageGrade t j.1) C.inv)
    (h : (d.passageComparison f).Holds) :
    (d.passageComparison (d.changePassageBases f C P)).Holds := by
  change SameFramedFlag _ _ _
  dsimp only [passageComparison,changePassageBases]
  rw [MatrixIso.bases_reindex]
  simp only [MatrixIso.reindex_reindex_eq,Equiv.self_trans_symm,
    MatrixIso.reindex_refl_eq]
  exact MatrixIso.sameFramedFlag_bases _ _ _ C.symm P hI hC h


lemma changePassageBlockBases_holds
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (w : ∀ j, MatrixIso R (d.Child false j) (d.Child false j))
    (P : MatrixIso R (d.Parent false) (d.Parent false))
    (h : (d.passageComparison f).Holds) :
    (d.passageComparison (d.changePassageBases f (MatrixIso.block w) P)).Holds := by
  have hw := MatrixIso.block_GradeDiagonal (passageGrade t) w
  exact d.changePassageBases_holds f (MatrixIso.block w) P hw.1 hw.2 h

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {A A' B W C C' : Type*}
  [Fintype A] [Fintype A'] [Fintype B] [Fintype W] [Fintype C] [Fintype C']

lemma congr_pull (e : A' ≃ A) (w : MatrixIso R A A) :
    (w.reindex e e).trans (congr e)=(congr e).trans w := by
  have h := congr_gauge e (w.reindex e e)
  simpa only [reindex_reindex_eq,Equiv.symm_trans_self,reindex_refl_eq] using h.symm

lemma congr_bases_cancel (e : A' ≃ A) (w : MatrixIso R A A) :
    ((w.reindex e e).symm.trans (congr e)).trans w=congr e := by
  rw [reindex_symm_eq,congr_pull,trans_assoc,symm_trans_self,trans_refl]

/-- Every untouched prefix/suffix strand cancels its two common basis changes; only the prescribed
branch frame remains. -/
lemma split_refinement_natural (e : A' ≃ A) (f : C' ≃ C)
    (v : MatrixIso R B W) (GA : MatrixIso R A A) (GB : MatrixIso R B B)
    (GW : MatrixIso R W W) (GC : MatrixIso R C C) :
    (congr e).sum (((GB.symm.trans v).trans GW).sum (congr f))=
      (((GA.reindex e e).sum (GB.sum (GC.reindex f f))).symm.trans
        ((congr e).sum (v.sum (congr f)))).trans (GA.sum (GW.sum GC)) := by
  rw [sum_symm,sum_symm,sum_trans,sum_trans,sum_trans,sum_trans]
  rw [congr_bases_cancel,congr_bases_cancel]

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {a b c : ℕ} (d : LocalRanks (.splitting a b c false))
local instance : Fintype (d.Columns .before) := d.fintypeColumns .before
local instance : Fintype (d.Columns .after) := d.fintypeColumns .after
local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch

/-- Coherent changes in the six fiber types of a split, transported through the exact named corner
equalities rather than through rank alone. -/
def splitBeforeBasis (GA : MatrixIso R (d.SplitA false) (d.SplitA false))
    (GW : MatrixIso R d.SplitW d.SplitW)
    (GC : MatrixIso R (d.SplitC false) (d.SplitC false)) :=
  (GA.sum (GW.sum GC)).reindex d.splitBefore d.splitBefore

def splitAfterBasis (GA : MatrixIso R (d.SplitA false) (d.SplitA false))
    (GB : MatrixIso R d.SplitB d.SplitB)
    (GC : MatrixIso R (d.SplitC false) (d.SplitC false)) :=
  ((GA.reindex d.splitPrefix d.splitPrefix).sum
    (GB.sum (GC.reindex d.splitSuffix d.splitSuffix))).reindex d.splitAfter d.splitAfter

def splitBranchBasis (GB : MatrixIso R d.SplitB d.SplitB) :=
  GB.reindex d.splitBranchChildren.symm d.splitBranchChildren.symm

def splitMiddleBasis (GW : MatrixIso R d.SplitW d.SplitW) :=
  GW.reindex d.splitBranchParent.symm d.splitBranchParent.symm

lemma splitRefinement_bases
    (v : MatrixIso R (d.Columns .branch) (d.Parent .branch))
    (GA : MatrixIso R (d.SplitA false) (d.SplitA false))
    (GB : MatrixIso R d.SplitB d.SplitB) (GW : MatrixIso R d.SplitW d.SplitW)
    (GC : MatrixIso R (d.SplitC false) (d.SplitC false)) :
    d.splitRefinement (((d.splitBranchBasis GB).symm.trans v).trans (d.splitMiddleBasis GW))=
      (((d.splitAfterBasis GA GB GC).symm.trans (d.splitRefinement v)).trans
        (d.splitBeforeBasis GA GW GC)) := by
  dsimp only [splitRefinement,splitAfterBasis,splitBeforeBasis,
    splitBranchBasis,splitMiddleBasis]
  rw [MatrixIso.bases_reindex]
  simp only [MatrixIso.reindex_reindex_eq,Equiv.self_trans_symm,
    MatrixIso.reindex_refl_eq]
  rw [MatrixIso.reindex_symm_eq]
  rw [← MatrixIso.reindex_trans _ _ d.splitAfter d.splitAfter d.splitBefore]
  rw [← MatrixIso.reindex_trans _ _ d.splitAfter d.splitBefore d.splitBefore]
  congr 1
  exact MatrixIso.split_refinement_natural _ _ _ GA GB GW GC


def changeSplitBases (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (GA : MatrixIso R (d.SplitA false) (d.SplitA false))
    (GB : MatrixIso R d.SplitB d.SplitB) (GW : MatrixIso R d.SplitW d.SplitW)
    (GC : MatrixIso R (d.SplitC false) (d.SplitC false))
    (P : MatrixIso R (d.Parent .before) (d.Parent .before)) :
    ∀ p, MatrixIso R (d.Columns p) (d.Parent p)
  | .before => ((d.splitBeforeBasis GA GW GC).symm.trans (f .before)).trans P
  | .after => ((d.splitAfterBasis GA GB GC).symm.trans (f .after)).trans
      (P.reindex d.splitParent d.splitParent)
  | .branch => ((d.splitBranchBasis GB).symm.trans (f .branch)).trans
      (d.splitMiddleBasis GW)

lemma changeSplitBases_holds
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (GA : MatrixIso R (d.SplitA false) (d.SplitA false))
    (GB : MatrixIso R d.SplitB d.SplitB) (GW : MatrixIso R d.SplitW d.SplitW)
    (GC : MatrixIso R (d.SplitC false) (d.SplitC false))
    (P : MatrixIso R (d.Parent .before) (d.Parent .before))
    (hC : MatrixIso.GradeDiagonal
      (fun j => ((Kind.splitting a b c false).childEnumeration .after j.1).val)
      (d.splitAfterBasis GA GB GC).val)
    (hI : MatrixIso.GradeDiagonal
      (fun j => ((Kind.splitting a b c false).childEnumeration .after j.1).val)
      (d.splitAfterBasis GA GB GC).inv)
    (h : (d.splitComparison f).Holds) :
    (d.splitComparison (d.changeSplitBases f GA GB GW GC P)).Holds := by
  let CA := d.splitAfterBasis GA GB GC
  let CB := d.splitBeforeBasis GA GW GC
  have hr : (d.splitComparison (d.changeSplitBases f GA GB GW GC P)).right=
      ((CA.symm.trans (d.splitComparison f).right).trans
        (P.reindex d.splitParent d.splitParent)) := by
    change ((d.splitRefinement
      (((d.splitBranchBasis GB).symm.trans (f .branch)).trans (d.splitMiddleBasis GW))).trans
        ((CB.symm.trans (f .before)).trans P)).reindex (Equiv.refl _) d.splitParent=_
    rw [d.splitRefinement_bases _ GA GB GW GC]
    change (((CA.symm.trans (d.splitRefinement (f .branch))).trans CB).trans
      ((CB.symm.trans (f .before)).trans P)).reindex (Equiv.refl _) d.splitParent=_
    have hc : ((CA.symm.trans (d.splitRefinement (f .branch))).trans CB).trans
        ((CB.symm.trans (f .before)).trans P)=
        (CA.symm.trans ((d.splitRefinement (f .branch)).trans (f .before))).trans P := by
      simp only [MatrixIso.trans_assoc,← MatrixIso.trans_assoc CB CB.symm,
        MatrixIso.trans_symm_self,MatrixIso.refl_trans]
    rw [hc,MatrixIso.reindex_trans _ P (Equiv.refl _) d.splitParent d.splitParent,
      MatrixIso.reindex_trans _ _ (Equiv.refl _) (Equiv.refl _) d.splitParent,
      MatrixIso.reindex_refl_eq]
    rfl
  change SameFramedFlag _ _ _
  rw [hr]
  exact MatrixIso.sameFramedFlag_bases _ _ _ CA.symm
    (P.reindex d.splitParent d.splitParent) hI hC h

lemma splitAfterBasis_blocks_diagonal
    (wA : ∀ i, MatrixIso R (Fin (d.prefixRank false i)) (Fin (d.prefixRank false i)))
    (wB : ∀ i : Fin b, MatrixIso R (Fin (d.rank .after (some (.inr (.inl i)))))
      (Fin (d.rank .after (some (.inr (.inl i))))))
    (wC : ∀ i, MatrixIso R (Fin (d.suffixRank false i)) (Fin (d.suffixRank false i))) :
    MatrixIso.GradeDiagonal
      (fun j => ((Kind.splitting a b c false).childEnumeration .after j.1).val)
      (d.splitAfterBasis (MatrixIso.block wA) (MatrixIso.block wB) (MatrixIso.block wC)).val ∧
    MatrixIso.GradeDiagonal
      (fun j => ((Kind.splitting a b c false).childEnumeration .after j.1).val)
      (d.splitAfterBasis (MatrixIso.block wA) (MatrixIso.block wB) (MatrixIso.block wC)).inv := by
  constructor <;> rintro ⟨i,x⟩ ⟨j,y⟩ hij
  all_goals
    rcases i with i|i|i <;> rcases j with j|j|j <;>
      simp only [splitAfterBasis,MatrixIso.reindex,MatrixIso.sum,splitAfter,
        splitPrefix,splitSuffix,Matrix.submatrix_apply,Equiv.coe_fn_mk,Equiv.sigmaCongrRight_apply,
        Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,MatrixIso.block]
  all_goals
    have h : i≠j := by
      intro h
      subst j
      exact hij rfl
    simp [Matrix.blockDiagonal',h]

lemma changeSplitBlockBases_holds
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (wA : ∀ i, MatrixIso R (Fin (d.prefixRank false i)) (Fin (d.prefixRank false i)))
    (wB : ∀ i : Fin b, MatrixIso R (Fin (d.rank .after (some (.inr (.inl i)))))
      (Fin (d.rank .after (some (.inr (.inl i))))))
    (GW : MatrixIso R d.SplitW d.SplitW)
    (wC : ∀ i, MatrixIso R (Fin (d.suffixRank false i)) (Fin (d.suffixRank false i)))
    (P : MatrixIso R (d.Parent .before) (d.Parent .before))
    (h : (d.splitComparison f).Holds) :
    (d.splitComparison (d.changeSplitBases f (MatrixIso.block wA) (MatrixIso.block wB)
      GW (MatrixIso.block wC) P)).Holds := by
  have hw := d.splitAfterBasis_blocks_diagonal wA wB wC
  exact d.changeSplitBases_holds f _ _ _ _ P hw.1 hw.2 h

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

/- Necessary word identities for the lower-facet band attachments for the band reduction. -/

end

end OAI
