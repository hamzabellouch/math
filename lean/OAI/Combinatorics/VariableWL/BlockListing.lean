import OAI.Combinatorics.VariableWL.BlockCatalog

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.BlockCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
 theorem literal_true_bit (v : Env n) : (literal [true] : Expr n).bit v=true := rfl
structure Listing (n : ℕ) where
  rows : Expr n
  internal : Expr n
  reals : Expr n
  comparisons : Expr n
  validReal : Expr (n+1)
  validComparison : Expr (n+1)
  source : Expr (n+1)
  target : Expr (n+1)
  domain : Expr (n+3)
  map : Expr (n+3)
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  rows := D.rows.number v
  internal := D.internal.number v
  reals := D.reals.number v
  comparisons := D.comparisons.number v
  validReal i := D.validReal.bit (cons (List.replicate i true) v)
  validComparison i := D.validComparison.bit (cons (List.replicate i true) v)
  source i := D.source.number (cons (List.replicate i true) v)
  target i := D.target.number (cons (List.replicate i true) v)
  domain i j a := D.domain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  map i j a := D.map.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
def up : Listing (n+1) where
  rows := D.rows.up
  internal := D.internal.up
  reals := D.reals.up
  comparisons := D.comparisons.up
  validReal := underOne D.validReal
  validComparison := underOne D.validComparison
  source := underOne D.source
  target := underOne D.target
  domain := underThree D.domain
  map := underThree D.map
theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  unfold eval up
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j a; exact underThree_bit ..
  · funext i j a; exact underThree_number ..

def vertices : Expr n := add D.reals (mul D.comparisons D.internal)
def links : Expr n := mul D.comparisons (add D.internal (numeral 1))
def horizontals : Expr n := mul (mul D.rows D.vertices) (numeral 4)
def squares : Expr n := mul (mul D.rows D.links) (numeral 4)
def verticals : Expr n := mul (mul D.rows D.links) (numeral 2)
def blocks : Expr n := add D.horizontals D.squares
def reads : Expr n := add D.horizontals D.verticals
def validVertex (I : Expr n) : Expr n := choose (lt I D.reals) (applyNat D.validReal I) (applyNat D.validComparison (div (sub I D.reals) D.internal))
def validLink (I : Expr n) : Expr n := applyNat D.validComparison (div I (add D.internal (numeral 1)))
def validH (I : Expr n) : Expr n := D.validVertex (mod (div I (numeral 4)) D.vertices)
def validS (I : Expr n) : Expr n := D.validLink (mod (div I (numeral 4)) D.links)
def validV (I : Expr n) : Expr n := D.validLink (mod (div I (numeral 2)) D.links)
def rawValid (I : Expr n) : Expr n := choose (lt I D.horizontals) (D.validH I) (D.validS (sub I D.horizontals))
def readValid (I : Expr n) : Expr n := choose (lt I D.horizontals) (D.validH I) (D.validV (sub I D.horizontals))
def hrow (I : Expr n) : Expr n := div (div I (numeral 4)) D.vertices
def htype (I : Expr n) : Expr n := mod (div I (numeral 4)) D.vertices
def srow (I : Expr n) : Expr n := div (div I (numeral 4)) D.links
def slink (I : Expr n) : Expr n := mod (div I (numeral 4)) D.links
def first (I : Expr n) : Expr n := div (mod I (numeral 4)) (numeral 2)
def last (I : Expr n) : Expr n := mod I (numeral 2)
def next (I : Expr n) : Expr n := mod (add I (numeral 1)) D.rows
def labels (T I A : Expr n) : Expr n := choose (lt T D.reals) (literal [true]) (applyNat₃ D.domain (div (sub T D.reals) D.internal) I A)
def horizontalValid (I : Expr n) : Expr n := conj (D.labels (D.htype I) (D.hrow I) (first I)) (D.labels (D.htype I) (D.next (D.hrow I)) (last I))
def squareValid (I : Expr n) : Expr n := conj (applyNat₃ D.domain (div (D.slink I) (add D.internal (numeral 1))) (D.srow I) (first I))
  (applyNat₃ D.domain (div (D.slink I) (add D.internal (numeral 1))) (D.next (D.srow I)) (last I))
def validBlock (I : Expr n) : Expr n := conj (D.rawValid I) (choose (lt I D.horizontals) (D.horizontalValid I) (D.squareValid (sub I D.horizontals)))
def left (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) (numeral 0)) (applyNat D.source (div L (add D.internal (numeral 1))))
  (add (add D.reals (mul (div L (add D.internal (numeral 1))) D.internal)) (sub (mod L (add D.internal (numeral 1))) (numeral 1)))
def right (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal) (applyNat D.target (div L (add D.internal (numeral 1))))
  (add (add D.reals (mul (div L (add D.internal (numeral 1))) D.internal)) (mod L (add D.internal (numeral 1))))
def output (L I A : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal)
  (applyNat₃ D.map (div L (add D.internal (numeral 1))) I A) A
def horizontalCode (I T A B : Expr n) : Expr n := add (add (mul (add (mul I D.vertices) T) (numeral 4)) (mul A (numeral 2))) B
def verticalCode (I L A : Expr n) : Expr n := add (add D.horizontals (mul (add (mul I D.links) L) (numeral 2))) A
def squareLeft (S : Expr n) : Expr n := D.horizontalCode (D.srow S) (D.left (D.slink S)) (first S) (last S)
def squareRight (S : Expr n) : Expr n := D.horizontalCode (D.srow S) (D.right (D.slink S))
  (D.output (D.slink S) (D.srow S) (first S)) (D.output (D.slink S) (D.next (D.srow S)) (last S))
def squareBottom (S : Expr n) : Expr n := D.verticalCode (D.srow S) (D.slink S) (first S)
def squareTop (S : Expr n) : Expr n := D.verticalCode (D.next (D.srow S)) (D.slink S) (last S)
def has (B A : Expr n) : Expr n := choose (lt B D.horizontals) (eq A B)
  (disj (eq A (D.squareLeft (sub B D.horizontals)))
    (disj (eq A (D.squareRight (sub B D.horizontals)))
      (disj (eq A (D.squareBottom (sub B D.horizontals))) (eq A (D.squareTop (sub B D.horizontals))))))

theorem vertices_number (v : Env n) : (D.vertices ).number v=(D.eval v).vertices  := by
  simp only [vertices,add_number,mul_number,Data.vertices,eval]

theorem links_number (v : Env n) : (D.links ).number v=(D.eval v).links  := by
  simp only [links,add_number,mul_number,numeral_number,Data.links,eval]

theorem horizontals_number (v : Env n) : (D.horizontals ).number v=(D.eval v).horizontals  := by
  simp only [horizontals,mul_number,numeral_number,vertices_number,Data.horizontals,eval]

theorem squares_number (v : Env n) : (D.squares ).number v=(D.eval v).squares  := by
  simp only [squares,mul_number,numeral_number,links_number,Data.squares,eval]

theorem verticals_number (v : Env n) : (D.verticals ).number v=(D.eval v).verticals  := by
  simp only [verticals,mul_number,numeral_number,links_number,Data.verticals,eval]

theorem blocks_number (v : Env n) : (D.blocks ).number v=(D.eval v).blocks  := by
  simp only [blocks,add_number,horizontals_number,squares_number,Data.blocks,eval]

theorem reads_number (v : Env n) : (D.reads ).number v=(D.eval v).reads  := by
  simp only [reads,add_number,horizontals_number,verticals_number,Data.reads,eval]

theorem validVertex_bit (I : Expr n) (v : Env n) : (D.validVertex I).bit v=(D.eval v).validVertex (I.number v) := by
  simp only [validVertex,div_number,sub_number,choose_bit,lt_bit,applyNat_bit,decide_eq_true_eq,Data.validVertex,eval]
  rfl

theorem validLink_bit (I : Expr n) (v : Env n) : (D.validLink I).bit v=(D.eval v).validLink (I.number v) := by
  simp only [validLink,add_number,div_number,numeral_number,applyNat_bit,Data.validLink,eval]

theorem validH_bit (I : Expr n) (v : Env n) : (D.validH I).bit v=(D.eval v).validH (I.number v) := by
  simp only [validH,div_number,mod_number,numeral_number,vertices_number,validVertex_bit,Data.validH,eval]

theorem validS_bit (I : Expr n) (v : Env n) : (D.validS I).bit v=(D.eval v).validS (I.number v) := by
  simp only [validS,div_number,mod_number,numeral_number,links_number,validLink_bit,Data.validS,eval]

theorem validV_bit (I : Expr n) (v : Env n) : (D.validV I).bit v=(D.eval v).validV (I.number v) := by
  simp only [validV,div_number,mod_number,numeral_number,links_number,validLink_bit,Data.validV,eval]

theorem rawValid_bit (I : Expr n) (v : Env n) : (D.rawValid I).bit v=(D.eval v).rawValid (I.number v) := by
  simp only [rawValid,sub_number,choose_bit,lt_bit,decide_eq_true_eq,horizontals_number,validH_bit,validS_bit,Data.rawValid,eval]
  rfl

theorem readValid_bit (I : Expr n) (v : Env n) : (D.readValid I).bit v=(D.eval v).readValid (I.number v) := by
  simp only [readValid,sub_number,choose_bit,lt_bit,decide_eq_true_eq,horizontals_number,validH_bit,validV_bit,Data.readValid,eval]
  rfl

theorem hrow_number (I : Expr n) (v : Env n) : (D.hrow I).number v=(D.eval v).hrow (I.number v) := by
  simp only [hrow,div_number,numeral_number,vertices_number,Data.hrow,eval]

theorem htype_number (I : Expr n) (v : Env n) : (D.htype I).number v=(D.eval v).htype (I.number v) := by
  simp only [htype,div_number,mod_number,numeral_number,vertices_number,Data.htype,eval]

theorem srow_number (I : Expr n) (v : Env n) : (D.srow I).number v=(D.eval v).srow (I.number v) := by
  simp only [srow,div_number,numeral_number,links_number,Data.srow,eval]

theorem slink_number (I : Expr n) (v : Env n) : (D.slink I).number v=(D.eval v).slink (I.number v) := by
  simp only [slink,div_number,mod_number,numeral_number,links_number,Data.slink,eval]

theorem first_number (I : Expr n) (v : Env n) : (first I).number v=Data.first (I.number v) := by
  simp only [first,div_number,mod_number,numeral_number,Data.first]

theorem last_number (I : Expr n) (v : Env n) : (last I).number v=Data.last (I.number v) := by
  simp only [last,mod_number,numeral_number,Data.last]

theorem next_number (I : Expr n) (v : Env n) : (D.next I).number v=(D.eval v).next (I.number v) := by
  simp only [next,add_number,mod_number,numeral_number,Data.next,eval]

theorem labels_bit (T I A : Expr n) (v : Env n) : (D.labels T I A).bit v=(D.eval v).labels (T.number v) (I.number v) (A.number v) := by
  simp only [labels,choose_bit,lt_bit,literal_true_bit,applyNat₃_bit,div_number,sub_number,decide_eq_true_eq,Data.labels,eval]
  rfl

theorem horizontalValid_bit (I : Expr n) (v : Env n) : (D.horizontalValid I).bit v=(D.eval v).horizontalValid (I.number v) := by
  simp only [horizontalValid,conj_bit,labels_bit,htype_number,hrow_number,first_number,last_number,next_number,Data.horizontalValid]

theorem squareValid_bit (I : Expr n) (v : Env n) : (D.squareValid I).bit v=(D.eval v).squareValid (I.number v) := by
  simp only [squareValid,add_number,div_number,numeral_number,conj_bit,applyNat₃_bit,srow_number,slink_number,first_number,last_number,next_number,Data.squareValid,eval]

theorem validBlock_bit (I : Expr n) (v : Env n) : (D.validBlock I).bit v=(D.eval v).validBlock (I.number v) := by
  simp only [validBlock,conj_bit,rawValid_bit,choose_bit,lt_bit,horizontals_number,decide_eq_true_eq,sub_number,horizontalValid_bit,squareValid_bit,Data.validBlock]

theorem left_number (L : Expr n) (v : Env n) : (D.left L).number v=(D.eval v).left (L.number v) := by
  simp only [left,add_number,mul_number,div_number,mod_number,sub_number,numeral_number,NumericProgram.choose_number,eq_bit,applyNat_number,decide_eq_true_eq,Data.left,eval]
  rfl

theorem right_number (L : Expr n) (v : Env n) : (D.right L).number v=(D.eval v).right (L.number v) := by
  simp only [right,add_number,mul_number,div_number,mod_number,numeral_number,NumericProgram.choose_number,eq_bit,applyNat_number,decide_eq_true_eq,Data.right,eval]
  rfl

theorem output_number (L I A : Expr n) (v : Env n) : (D.output L I A).number v=(D.eval v).output (L.number v) (I.number v) (A.number v) := by
  simp only [output,add_number,div_number,mod_number,numeral_number,NumericProgram.choose_number,eq_bit,applyNat₃_number,decide_eq_true_eq,Data.output,eval]
  rfl

theorem horizontalCode_number (I T A B : Expr n) (v : Env n) : (D.horizontalCode I T A B).number v=(D.eval v).horizontalCode (I.number v) (T.number v) (A.number v) (B.number v) := by
  simp only [horizontalCode,add_number,mul_number,numeral_number,vertices_number,Data.horizontalCode,eval]

theorem verticalCode_number (I L A : Expr n) (v : Env n) : (D.verticalCode I L A).number v=(D.eval v).verticalCode (I.number v) (L.number v) (A.number v) := by
  simp only [verticalCode,add_number,mul_number,numeral_number,links_number,horizontals_number,Data.verticalCode,eval]

theorem squareLeft_number (S : Expr n) (v : Env n) : (D.squareLeft S).number v=(D.eval v).squareLeft (S.number v) := by
  simp only [squareLeft,srow_number,slink_number,first_number,last_number,left_number,horizontalCode_number,Data.squareLeft,eval]

theorem squareRight_number (S : Expr n) (v : Env n) : (D.squareRight S).number v=(D.eval v).squareRight (S.number v) := by
  simp only [squareRight,srow_number,slink_number,first_number,last_number,next_number,right_number,output_number,horizontalCode_number,Data.squareRight,eval]

theorem squareBottom_number (S : Expr n) (v : Env n) : (D.squareBottom S).number v=(D.eval v).squareBottom (S.number v) := by
  simp only [squareBottom,srow_number,slink_number,first_number,verticalCode_number,Data.squareBottom,eval]

theorem squareTop_number (S : Expr n) (v : Env n) : (D.squareTop S).number v=(D.eval v).squareTop (S.number v) := by
  simp only [squareTop,srow_number,slink_number,last_number,next_number,verticalCode_number,Data.squareTop,eval]

theorem has_bit (B A : Expr n) (v : Env n) : (D.has B A).bit v=(D.eval v).has (B.number v) (A.number v) := by
  simp only [has,sub_number,choose_bit,disj_bit,eq_bit,lt_bit,decide_eq_true_eq,horizontals_number,squareLeft_number,squareRight_number,squareBottom_number,squareTop_number,Data.has]
  split_ifs <;> apply Bool.eq_iff_iff.mpr <;> simp only [Bool.or_eq_true,decide_eq_true_eq]

end Listing
end VariableWL.BlockCatalog.Program

namespace VariableWL.AffineAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable

abbrev SquareCoordinate (d e : ℕ) := (Fin d ⊕ Fin e) ⊕ Bool

def squareCoordinate (d e : ℕ) : SquareVal d e ≃+ (SquareCoordinate d e → Bit) where
  toFun z := Sum.elim (Sum.elim z.1.1 z.1.2) (fun t=>if t then z.2.2 else z.2.1)
  invFun f := ((fun i=>f (.inl (.inl i)),fun i=>f (.inl (.inr i))),(f (.inr false),f (.inr true)))
  left_inv z := by cases z; rfl
  right_inv f := by
    funext i
    rcases i with (i|i)|t
    · rfl
    · rfl
    · cases t <;> rfl
  map_add' z w := by
    funext i
    rcases i with (i|i)|t
    · rfl
    · rfl
    · cases t <;> rfl

noncomputable def horizontalEncode (d : ℕ) : Vec d ≃+ Vec (Fintype.card (Fin d)) where
  toFun z := z ∘ (Fintype.equivFin (Fin d)).symm
  invFun f := f ∘ Fintype.equivFin (Fin d)
  left_inv z := by funext i; simp only [Function.comp_apply,Equiv.symm_apply_apply]
  right_inv f := by funext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
  map_add' _ _ := rfl

noncomputable def squareEncode (d e : ℕ) : SquareVal d e ≃+ Vec (Fintype.card (SquareCoordinate d e)) where
  toFun z := squareCoordinate d e z ∘ (Fintype.equivFin (SquareCoordinate d e)).symm
  invFun f := (squareCoordinate d e).symm (f ∘ Fintype.equivFin (SquareCoordinate d e))
  left_inv z := by
    simp only [Function.comp_def,Equiv.symm_apply_apply]
    exact (squareCoordinate d e).symm_apply_apply z
  right_inv f := by funext i; simp
  map_add' z w := by funext i; exact congrFun ((squareCoordinate d e).map_add z w) _

 theorem horizontal_count_le (d : Fin 3) : Fintype.card (Fin d.val)≤6 := by simp only [Fintype.card_fin]; omega
 theorem square_count_le (d e : Fin 3) : Fintype.card (SquareCoordinate d.val e.val)≤6 := by
  simp only [SquareCoordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool]
  omega

noncomputable instance linearFintype (d : ℕ) : Fintype (Vec d →ₗ[Bit] Bit) :=
  Fintype.ofInjective (fun L : Vec d →ₗ[Bit] Bit => (L : Vec d → Bit)) DFunLike.coe_injective

abbrev Form := Σd : Fin 3, Vec d.val →ₗ[Bit] Bit
noncomputable instance formFintype : Fintype Form := Fintype.ofFinite _
noncomputable def formNumber : Form ≃ Fin (Fintype.card Form) := Fintype.equivFin _
noncomputable def formCount : ℕ := Fintype.card Form
noncomputable def encodeForm {d : ℕ} (hd : d≤2) (L : Vec d →ₗ[Bit] Bit) : ℕ :=
  (formNumber ⟨⟨d,by omega⟩,L⟩).val
 theorem encodeForm_lt {d : ℕ} (hd : d≤2) (L : Vec d →ₗ[Bit] Bit) : encodeForm hd L<formCount :=
  (formNumber ⟨⟨d,by omega⟩,L⟩).isLt

noncomputable def horizontalLegal (d i : ℕ) : Bool :=
  decide (∃ hd : d≤2,∃z : Vec d,PrefixAlphabet.encode (by simp only [Fintype.card_fin]; omega)
    (horizontalEncode d z)=i)
noncomputable def squareLegal (l r c i : ℕ) : Bool :=
  if hl : l<formCount then if hr : r<formCount then
    let L:=formNumber.symm ⟨l,hl⟩
    let R:=formNumber.symm ⟨r,hr⟩
    decide (∃z : SquareVal L.1.val R.1.val,boundary L.2 R.2 z=(c : Bit) ∧
      PrefixAlphabet.encode (square_count_le L.1 R.1) (squareEncode L.1.val R.1.val z)=i)
  else false else false
 theorem horizontalLegal_eq {d : ℕ} (hd : d≤2) (i : ℕ) :
    horizontalLegal d i=true ↔ ∃z : Vec d,PrefixAlphabet.encode (by simp only [Fintype.card_fin]; omega)
      (horizontalEncode d z)=i := by
  simp only [horizontalLegal,decide_eq_true_eq]
  exact ⟨fun ⟨_,z,hz⟩=>⟨z,hz⟩,fun ⟨z,hz⟩=>⟨hd,z,hz⟩⟩
 theorem encodeForm_heq {d e : ℕ} (hd : d≤2) (he : e≤2)
    (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (h : d=e) (hLR : HEq L R) : encodeForm hd L=encodeForm he R := by
  subst e
  cases hLR
  rfl
 theorem decodeForm {d : ℕ} (hd : d≤2) (L : Vec d →ₗ[Bit] Bit) :
    formNumber.symm ⟨encodeForm hd L,encodeForm_lt hd L⟩=⟨⟨d,by omega⟩,L⟩ := by
  apply formNumber.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rfl
 theorem squareLegal_eq {d e : ℕ} (hd : d≤2) (he : e≤2) (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c : Bit) (i : ℕ) : squareLegal (encodeForm hd L) (encodeForm he R) c.val i=true ↔
    ∃z : SquareVal d e,boundary L R z=c ∧
      PrefixAlphabet.encode (square_count_le ⟨d,by omega⟩ ⟨e,by omega⟩) (squareEncode d e z)=i := by
  rw [squareLegal,dite_eq_left (encodeForm_lt hd L),dite_eq_left (encodeForm_lt he R)]
  dsimp only
  simp only [ZMod.natCast_zmod_val,decide_eq_true_eq]
  let F (X Y : Form) : Prop := ∃z : SquareVal X.1.val Y.1.val,boundary X.2 Y.2 z=c ∧
    PrefixAlphabet.encode (square_count_le X.1 Y.1) (squareEncode X.1.val Y.1.val z)=i
  exact Iff.of_eq (congrArg₂ F (decodeForm hd L) (decodeForm he R))

end VariableWL.AffineAlphabet

namespace VariableWL.BlockCoordinates
open Blocks Subdivision VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)
 theorem horizontal_encode_eq (h : Horizontal r n P E) :
    encode J (.inl h)=AffineAlphabet.horizontalEncode (dimension J h.type) := rfl
 theorem square_encode_eq (s : Square r n E) : encode J (.inr s)=
    AffineAlphabet.squareEncode (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) := rfl
end VariableWL.BlockCoordinates

namespace VariableWL.AffineAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable

 theorem embedding_le {m d : ℕ} (e : Fin m ↪ Fin d) : m≤d := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
noncomputable def extend {m d : ℕ} (e : Fin m ↪ Fin d) : Equiv.Perm (Fin d) :=
  (Equiv.Perm.exists_extending_pair
    (fun i : Fin m=>(⟨i.val,lt_of_lt_of_le i.isLt (embedding_le e)⟩ : Fin d)) e
    (fun a b h=>Fin.ext (show a.val=b.val from congrArg (fun x : Fin d=>x.val) h)) e.injective).choose
noncomputable def horizontalEmbedding (d : ℕ) : Fin d ↪ Fin (Fintype.card (Fin d)) :=
  (Function.Embedding.refl (Fin d)).trans (Fintype.equivFin (Fin d)).toEmbedding
noncomputable def leftEmbedding (d e : ℕ) : Fin d ↪ Fin (Fintype.card (SquareCoordinate d e)) :=
  (⟨fun i=>Sum.inl (Sum.inl i),fun _ _ h=>Sum.inl.inj (Sum.inl.inj h)⟩ : Fin d ↪ SquareCoordinate d e).trans
    (Fintype.equivFin (SquareCoordinate d e)).toEmbedding
noncomputable def rightEmbedding (d e : ℕ) : Fin e ↪ Fin (Fintype.card (SquareCoordinate d e)) :=
  (⟨fun i=>Sum.inl (Sum.inr i),fun _ _ h=>Sum.inr.inj (Sum.inl.inj h)⟩ : Fin e ↪ SquareCoordinate d e).trans
    (Fintype.equivFin (SquareCoordinate d e)).toEmbedding
noncomputable def scalarEmbedding (d e : ℕ) (a : Bool) : Fin 1 ↪ Fin (Fintype.card (SquareCoordinate d e)) :=
  (⟨fun _=>Sum.inr a,fun _ _ _=>Subsingleton.elim _ _⟩ : Fin 1 ↪ SquareCoordinate d e).trans
    (Fintype.equivFin (SquareCoordinate d e)).toEmbedding
noncomputable def horizontalOrder (d : ℕ) : ℕ := if hd : d≤2 then
  PrefixAlphabet.encodeOrder (horizontal_count_le ⟨d,by omega⟩) (extend (horizontalEmbedding d)) else 0
noncomputable def squareOrder (d e a : ℕ) : ℕ := if hd : d≤2 then if he : e≤2 then
  PrefixAlphabet.encodeOrder (square_count_le ⟨d,by omega⟩ ⟨e,by omega⟩)
    (if a=0 then extend (leftEmbedding d e) else if a=1 then extend (rightEmbedding d e) else
      extend (scalarEmbedding d e (decide (a≠2)))) else 0 else 0
noncomputable def zeroOrder (d : ℕ) : ℕ := if hd : d≤6 then PrefixAlphabet.encodeOrder hd (Equiv.refl _) else 0
end VariableWL.AffineAlphabet

namespace VariableWL.BlockCoordinates
open Blocks Subdivision VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E) (hr : 2≤r) (hn : 0<n)
 theorem coordinate_lift_unique {b : RawBlock r n P E} {a : Readout r n P E}
    (ha : HasReadout J b a) (e : Fin (readoutDimension J a) ↪ Coordinate J b)
    (he : ∀z i,coordinateEquiv J b z (e i)=readoutEquiv J a (readout J z ha) i) :
    (coordinate_lift J hr hn ha).choose=e := by
  ext i
  have hh : ∀f : Coordinate J b → Bit,f ((coordinate_lift J hr hn ha).choose i)=f (e i) := by
    intro f
    obtain ⟨z,rfl⟩ := (coordinateEquiv J b).surjective f
    exact ((coordinate_lift J hr hn ha).choose_spec z i).trans (he z i).symm
  by_contra hne
  have h := hh (fun j=>if j=e i then 1 else 0)
  simp only [ite_eq_right hne] at h
  exact zero_ne_one h

 theorem order_eq_extend {b : RawBlock r n P E} {a : Readout r n P E} (ha : HasReadout J b a) :
    (exists_readout_order J hr hn ha).choose=AffineAlphabet.extend (readoutEmbedding J hr hn ha) := rfl

 theorem embedding_horizontal (h : Horizontal r n P E) :
    readoutEmbedding J hr hn (b := .inl h) (a := .inl h) rfl=
      AffineAlphabet.horizontalEmbedding (dimension J h.type) := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inl h) (a := .inl h) rfl (Function.Embedding.refl _) (by
    intro z i
    rw [readout_eq J hr hn (b := .inl h) (z := z) (a := .inl h) rfl ⟨rfl,HEq.rfl⟩]
    rfl)
  rw [he]
  rfl

 theorem embedding_left (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inl (squareLeft J s)) (Or.inl rfl)=
      AffineAlphabet.leftEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inl (squareLeft J s)) (Or.inl rfl)
    ⟨fun i=>.inl (.inl i),fun _ _ h=>Sum.inl.inj (Sum.inl.inj h)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inl (squareLeft J s)) (Or.inl rfl) (Or.inl ⟨rfl,HEq.rfl⟩)]
      rfl)
  rw [he]
  rfl

 theorem embedding_right (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl))=
      AffineAlphabet.rightEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl))
    ⟨fun i=>.inl (.inr i),fun _ _ h=>Sum.inr.inj (Sum.inl.inj h)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))]
      rfl)
  rw [he]
  rfl

 theorem embedding_bottom (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))=
      AffineAlphabet.scalarEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) false := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))
    ⟨fun _=>.inr false,fun i j _=>Fin.ext (by have hi := i.isLt; have hj := j.isLt; change i.val<1 at hi; change j.val<1 at hj; omega)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))]
      rfl)
  rw [he]
  rfl

 theorem embedding_top (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))=
      AffineAlphabet.scalarEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) true := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))
    ⟨fun _=>.inr true,fun i j _=>Fin.ext (by have hi := i.isLt; have hj := j.isLt; change i.val<1 at hi; change j.val<1 at hj; omega)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))]
      rfl)
  rw [he]
  rfl
end VariableWL.BlockCoordinates

end OAI
