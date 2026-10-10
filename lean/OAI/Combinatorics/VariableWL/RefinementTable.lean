import OAI.Combinatorics.VariableWL.Encoding

namespace OAI

namespace VariableWL.MachineReduction
open MachineOneHead
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)

noncomputable def schemaConstant : ℕ :=
  16*(Fintype.card (Letter M)+(Fintype.card (Letter M))^3+1)

theorem input_le_bits (w : Word) : (input M w).length ≤ bits M c d w := by
  have h := inputExponent_ge_length c d w.length
  have hh := input_length M w
  unfold bits addressBits simulationExponent
  omega

theorem kind_card (a : ℕ) : Fintype.card (Circuit.ProductCellular.Kind a) ≤ 3*(a+1)^2 := by
  simp only [Circuit.ProductCellular.Kind,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_option,Fintype.card_bool]
  nlinarith

theorem triple_card (L : Type) [Fintype L] : Fintype.card (Circuit.Cellular.Triple L)=(Fintype.card L)^3 := by
  simp only [Circuit.Cellular.Triple,Fintype.card_prod]
  ring

theorem edge_card (w : Word) : Fintype.card (Circuit.ProductCellular.Edge (Letter M) (bits M c d w)) ≤
    3*(Fintype.card (Letter M))^3*(bits M c d w+1)^2 := by
  change Fintype.card (Circuit.Cellular.Triple (Letter M) × Circuit.ProductCellular.Kind (bits M c d w)) ≤ _
  rw [Fintype.card_prod,triple_card]
  have h := Nat.mul_le_mul_left ((Fintype.card (Letter M))^3) (kind_card (bits M c d w))
  convert h using 1; ring

theorem real_card (w : Word) : Fintype.card (Real M c d w) ≤
    schemaConstant M*(bits M c d w+1)^2 := by
  let q := Fintype.card (Letter M)
  let U := (bits M c d w+1)^2
  have hu : 1 ≤ U := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have he := edge_card M c d w
  have hq : q ≤ q*U := Nat.le_mul_of_pos_right _ hu
  have hq3 : q^3 ≤ q^3*U := Nat.le_mul_of_pos_right _ hu
  change Fintype.card ((Letter M ⊕ (Circuit.Cellular.Triple (Letter M) × Bool)) ⊕
    (Circuit.ProductCellular.Edge (Letter M) (bits M c d w) ⊕ Unit)) ≤ _
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_sum,
    Fintype.card_prod (α := Circuit.Cellular.Triple (Letter M)) (β := Bool),
    triple_card,Fintype.card_bool,Fintype.card_unit]
  change q+q^3*2+(Fintype.card (Circuit.ProductCellular.Edge (Letter M) (bits M c d w))+1) ≤
    16*(q+q^3+1)*U
  change Fintype.card (Circuit.ProductCellular.Edge (Letter M) (bits M c d w)) ≤ 3*q^3*U at he
  calc
    _ ≤ q*U+(q^3*U)*2+(3*q^3*U+U) := by omega
    _ ≤ 16*(q+q^3+1)*U := by nlinarith [Nat.zero_le (q*U),Nat.zero_le (q^3*U)]

theorem comparison_card (w : Word) : Fintype.card (Comparison M c d w) ≤
    schemaConstant M*(bits M c d w+1)^2 := by
  let : Fintype {h : Fin (bits M c d w) // (circuit M c d w).threshold h=false} := Fintype.ofFinite _
  let : Fintype {f : Letter M // f ∈ (circuit M c d w).accepting} := Fintype.ofFinite _
  let q := Fintype.card (Letter M)
  let U := (bits M c d w+1)^2
  have hu : 1 ≤ U := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have ht : bits M c d w+1 ≤ U := by dsimp [U]; nlinarith
  have hi := (input_le_bits M c d w).trans (Nat.le_succ _)
  have hq : q ≤ q*U := Nat.le_mul_of_pos_right _ hu
  have he := edge_card M c d w
  have hf : Fintype.card {h : Fin (bits M c d w) // (circuit M c d w).threshold h=false} ≤ bits M c d w := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)
  have ha : Fintype.card {f : Letter M // f ∈ (circuit M c d w).accepting} ≤ q := Fintype.card_subtype_le _
  change Fintype.card ((Circuit.ProductCellular.Edge (Letter M) (bits M c d w) ⊕
    (Circuit.ProductCellular.Edge (Letter M) (bits M c d w) ⊕
      Circuit.ProductCellular.Edge (Letter M) (bits M c d w))) ⊕
    ((Fin (input M w).length ⊕ Option {h : Fin (bits M c d w) // (circuit M c d w).threshold h=false}) ⊕
      {f : Letter M // f ∈ (circuit M c d w).accepting})) ≤ _
  simp only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin]
  change _ ≤ 16*(q+q^3+1)*U
  change Fintype.card (Circuit.ProductCellular.Edge (Letter M) (bits M c d w)) ≤ 3*q^3*U at he
  calc
    _ ≤ 3*(3*q^3*U)+2*U+q*U := by omega
    _ ≤ 16*(q+q^3+1)*U := by nlinarith [Nat.zero_le (q*U),Nat.zero_le (q^3*U)]

theorem bits_le_dimension (w : Word) : bits M c d w ≤ dimension M c d w := by unfold dimension; omega

theorem schemas_in_dimension (w : Word) :
    Fintype.card (Real M c d w) ≤ schemaConstant M*(dimension M c d w+1)^2 ∧
    Fintype.card (Comparison M c d w) ≤ schemaConstant M*(dimension M c d w+1)^2 := by
  have h := Nat.mul_le_mul_left (schemaConstant M) (Nat.pow_le_pow_left
    (Nat.add_le_add_right (bits_le_dimension M c d w) 1) 2)
  exact ⟨(real_card M c d w).trans h,(comparison_card M c d w).trans h⟩

theorem blocks_card (w : Word) :
    Fintype.card (Blocks.Block (n := internal M c d w) (imageInstance M c d w)) ≤
      40*schemaConstant M*(dimension M c d w+1)^4 := by
  have h := RealizationSize.block_card (n := internal M c d w) (imageInstance M c d w)
  obtain ⟨hp,he⟩ := schemas_in_dimension M c d w
  have hs := Nat.add_le_add hp (Nat.mul_le_mul_right (2*internal M c d w+1) he)
  refine h.trans ((Nat.mul_le_mul_left (4*dimension M c d w) hs).trans ?_)
  unfold internal
  have hm : 4*dimension M c d w*(1+(2*(4*(dimension M c d w+1))+1)) ≤
      40*(dimension M c d w+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_right (schemaConstant M*(dimension M c d w+1)^2) hm
  nlinarith only [hh]

end VariableWL.MachineReduction

namespace VariableWL.RefinementTable
attribute [local instance] Classical.propDecidable

def sameCounts {α : Type} (eq : α → α → Bool) (xs ys : List α) : Bool :=
  (xs++ys).all fun a => decide ((xs.filter (eq a)).length=(ys.filter (eq a)).length)

theorem sameCounts_iff {α β : Type} [DecidableEq β] (f : α → β)
    (eq : α → α → Bool) (heq : ∀ a b, eq a b=true ↔ f a=f b) (xs ys : List α) :
    sameCounts eq xs ys=true ↔ (xs.map f : Multiset β)=(ys.map f : Multiset β) := by
  have hcount (a) (zs : List α) : (zs.filter (eq a)).length=(zs.map f).count (f a) := by
    induction zs with
    | nil => rfl
    | cons b zs ih =>
      by_cases h : f a=f b
      · have he : eq a b=true := (heq a b).mpr h
        simp [he,h,ih]
      · have he : eq a b=false := Bool.eq_false_iff.mpr (fun hb => h ((heq a b).mp hb))
        simp [he,Ne.symm h,ih]
  simp only [sameCounts,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro b
    by_cases hb : b ∈ xs.map f ∨ b ∈ ys.map f
    · rcases hb with hb|hb
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        simpa only [Multiset.coe_count,← hcount] using h a (List.mem_append_left ys ha)
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        simpa only [Multiset.coe_count,← hcount] using h a (List.mem_append_right xs ha)
    · have hx : b ∉ xs.map f := fun hx => hb (.inl hx)
      have hy : b ∉ ys.map f := fun hy => hb (.inr hy)
      simp only [Multiset.coe_count,List.count_eq_zero.mpr hx,List.count_eq_zero.mpr hy]
  · intro h a _
    rw [hcount,hcount]
    simpa only [Multiset.coe_count] using congrArg (Multiset.count (f a)) h

variable (G H : Graph) (k : ℕ)
abbrev Entry := TaggedTuple G H k
abbrev Vector := Fin k → Entry G H k

def neighbors : Entry G H k → List (Vector G H k)
  | .inl v => List.ofFn fun z : Fin G.order => fun i => Sum.inl (Function.update v i z)
  | .inr v => List.ofFn fun z : Fin H.order => fun i => Sum.inr (Function.update v i z)

def vectorEqual (R : Entry G H k → Entry G H k → Bool) (x y : Vector G H k) : Bool :=
  (List.finRange k).all fun i => R (x i) (y i)

def update (R : Entry G H k → Entry G H k → Bool) (x y : Entry G H k) : Bool :=
  R x y && sameCounts (vectorEqual G H k R) (neighbors G H k x) (neighbors G H k y)

 theorem vectorEqual_iff (R : Entry G H k → Entry G H k → Bool) (s : ℕ)
    (hr : ∀ a b, R a b=true ↔ tagColor G H k s a=tagColor G H k s b)
    (x y : Vector G H k) : vectorEqual G H k R x y=true ↔
      (fun i => tagColor G H k s (x i))=(fun i => tagColor G H k s (y i)) := by
  simp only [vectorEqual,List.all_eq_true,List.mem_finRange,forall_const,hr,funext_iff]

 theorem neighbors_color (x : Entry G H k) (s : ℕ) :
    ((neighbors G H k x).map (fun a i => tagColor G H k s (a i)) : Multiset (Fin k → Color k s)) =
      (tagColor G H k (s+1) x).2 := by
  classical
  cases x with
  | inl v =>
    rw [neighbors,List.map_ofFn]
    change (List.ofFn (fun z : Fin G.order => fun i => color G k s (Function.update v i z)) : Multiset (Fin k → Color k s)) = Finset.univ.val.map (fun z : Fin G.order => fun i => color G k s (Function.update v i z))
    exact (Fin.univ_val_map _).symm
  | inr v =>
    rw [neighbors,List.map_ofFn]
    change (List.ofFn (fun z : Fin H.order => fun i => color H k s (Function.update v i z)) : Multiset (Fin k → Color k s)) = Finset.univ.val.map (fun z : Fin H.order => fun i => color H k s (Function.update v i z))
    exact (Fin.univ_val_map _).symm

 theorem update_correct (R : Entry G H k → Entry G H k → Bool) (s : ℕ)
    (hr : ∀ a b, R a b=true ↔ tagColor G H k s a=tagColor G H k s b)
    (x y : Entry G H k) : update G H k R x y=true ↔
      tagColor G H k (s+1) x=tagColor G H k (s+1) y := by
  classical
  rw [update,Bool.and_eq_true,hr,sameCounts_iff (fun a i => tagColor G H k s (a i)) _
    (vectorEqual_iff G H k R s hr),neighbors_color,neighbors_color]
  have hx : (tagColor G H k (s+1) x).1=tagColor G H k s x := by cases x <;> rfl
  have hy : (tagColor G H k (s+1) y).1=tagColor G H k s y := by cases y <;> rfl
  rw [← hx,← hy]
  exact Prod.ext_iff.symm

noncomputable def initial (x y : Entry G H k) : Bool :=
  decide (tagColor G H k 0 x=tagColor G H k 0 y)

noncomputable def table : ℕ → Entry G H k → Entry G H k → Bool
  | 0 => initial G H k
  | s+1 => update G H k (table s)

 theorem table_correct (s : ℕ) (x y : Entry G H k) : table G H k s x y=true ↔
    tagColor G H k s x=tagColor G H k s y := by
  induction s generalizing x y with
  | zero => simp [table,initial]
  | succ s ih => exact update_correct G H k (table G H k s) s (fun a b => ih a b) x y

noncomputable def histogramEqual (R : Entry G H k → Entry G H k → Bool) : Bool :=
  sameCounts R ((Finset.univ : Finset (Tuple G k)).toList.map Sum.inl)
    ((Finset.univ : Finset (Tuple H k)).toList.map Sum.inr)

 theorem histogramEqual_correct (R : Entry G H k → Entry G H k → Bool) (s : ℕ)
    (hr : ∀ a b, R a b=true ↔ tagColor G H k s a=tagColor G H k s b) :
    histogramEqual G H k R=true ↔ histogram G k s=histogram H k s := by
  classical
  rw [histogramEqual,sameCounts_iff (tagColor G H k s) R hr]
  simp only [List.map_map,Function.comp_def,tagColor,Sum.elim_inl,Sum.elim_inr,
    ← Multiset.map_coe,Finset.coe_toList,histogram]

noncomputable def accepts : Bool := histogramEqual G H k (table G H k ((G.order^k+H.order^k)^2))

 theorem accepts_correct : accepts G H k=true ↔ Equivalent G H k := by
  rw [accepts,histogramEqual_correct _ _ _ _ _ (table_correct G H k _),equivalent_iff_bounded_round]

end VariableWL.RefinementTable

namespace VariableWL.RealizationSize
open VariableWL.Affine Blocks Subdivision
variable {r n : ℕ} {P E : Type} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (marked : Fin r)

 theorem general_order_polynomial (ε : Bit) :
    (General.finiteGraph (n := n) J marked ε).order ≤
      4224*(Fintype.card (Block (n := n) J)+1)^3 := by
  apply (general_order J marked ε).trans
  generalize Fintype.card (Block (n := n) J)=B
  nlinarith [Nat.zero_le (B^3),Nat.zero_le (B^2)]

 theorem subcubic_order_polynomial (hr : 2≤r) (hn : 0<n) (ε : Bit) :
    (Subcubic.finiteGraph J hr hn marked ε).order ≤
      330369*(Fintype.card (Block (n := n) J)+1)^4 := by
  apply (subcubic_order J hr hn marked ε).trans
  generalize Fintype.card (Block (n := n) J)=B
  have h1 : B*(1+512*(4*B+1)) ≤ 2561*(B+1)^2 := by nlinarith
  have h2 : B*(1+8*(4*B+1))+2 ≤ 43*(B+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_right 3 h1) h2
  have he : 2561*(B+1)^2*3*(43*(B+1)^2)=330369*(B+1)^4 := by ring
  rw [he] at hh
  exact hh

end VariableWL.RealizationSize

namespace VariableWL.MachineReduction
open MachineOneHead
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)

 theorem blocks_succ_bound (w : Word) :
    Fintype.card (Blocks.Block (n := internal M c d w) (imageInstance M c d w))+1 ≤
      (40*schemaConstant M+1)*(dimension M c d w+1)^4 := by
  have h := blocks_card M c d w
  have hp : 1 ≤ (dimension M c d w+1)^4 := Nat.succ_le_of_lt (pow_pos (by omega) _)
  nlinarith

 theorem general_order_dimension (w : Word) (ε : Affine.Bit) :
    (generalGraph M c d w ε).order ≤
      (4224*(40*schemaConstant M+1)^3)*(dimension M c d w+1)^12 := by
  have h := RealizationSize.general_order_polynomial (n := internal M c d w)
    (imageInstance M c d w) (marked M c d w) ε
  have hh := Nat.mul_le_mul_left 4224 (Nat.pow_le_pow_left (blocks_succ_bound M c d w) 3)
  exact h.trans (hh.trans_eq (by ring))

 theorem subcubic_order_dimension (w : Word) (ε : Affine.Bit) :
    (subcubicGraph M c d w ε).order ≤
      (330369*(40*schemaConstant M+1)^4)*(dimension M c d w+1)^16 := by
  have h := RealizationSize.subcubic_order_polynomial (n := internal M c d w)
    (imageInstance M c d w) (marked M c d w)
    (by have := dimension_large M c d w; omega) (internal_pos M c d w) ε
  have hh := Nat.mul_le_mul_left 330369 (Nat.pow_le_pow_left (blocks_succ_bound M c d w) 4)
  exact h.trans (hh.trans_eq (by ring))

noncomputable def dimensionConstant : ℕ := 2*(quadraticConstant M+2*c+7)+1

 theorem dimension_succ_polynomial (w : Word) :
    dimension M c d w+1 ≤ dimensionConstant M c*(w.length+1)^(d+1) := by
  have h := dimension_polynomial M c d w
  have hp : 1 ≤ (w.length+1)^(d+1) := Nat.succ_le_of_lt (pow_pos (by omega) _)
  unfold dimensionConstant
  nlinarith

 theorem general_order_input (w : Word) (ε : Affine.Bit) :
    (generalGraph M c d w ε).order ≤
      (4224*(40*schemaConstant M+1)^3*(dimensionConstant M c)^12)*(w.length+1)^((d+1)*12) := by
  have h := Nat.mul_le_mul_left (4224*(40*schemaConstant M+1)^3)
    (Nat.pow_le_pow_left (dimension_succ_polynomial M c d w) 12)
  refine (general_order_dimension M c d w ε).trans (h.trans_eq ?_)
  rw [mul_pow,← pow_mul]
  ring

 theorem subcubic_order_input (w : Word) (ε : Affine.Bit) :
    (subcubicGraph M c d w ε).order ≤
      (330369*(40*schemaConstant M+1)^4*(dimensionConstant M c)^16)*(w.length+1)^((d+1)*16) := by
  have h := Nat.mul_le_mul_left (330369*(40*schemaConstant M+1)^4)
    (Nat.pow_le_pow_left (dimension_succ_polynomial M c d w) 16)
  refine (subcubic_order_dimension M c d w ε).trans (h.trans_eq ?_)
  rw [mul_pow,← pow_mul]
  ring

noncomputable def generalWord (w : Word) : Word :=
  pairCode (generalGraph M c d w 0) (generalGraph M c d w 1) (dimension M c d w)
noncomputable def subcubicWord (w : Word) : Word :=
  pairCode (subcubicGraph M c d w 0) (subcubicGraph M c d w 1) (dimension M c d w)

 theorem generalWord_correct (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) : generalWord M c d w ∈ WL ↔ b=true := by
  rw [generalWord,Encoding.pair_mem_WL,general_correct M c d w b h]
  have hk := dimension_large M c d w
  simp only [show 2≤dimension M c d w by omega,true_and]

 theorem subcubicWord_correct (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) : subcubicWord M c d w ∈ SubWL ↔ b=true := by
  rw [subcubicWord,Encoding.pair_mem_SubWL,subcubic_correct M c d w b h]
  obtain ⟨hp,he,hc,hc',hs,hs'⟩ := subcubic_promise M c d w
  have hk := dimension_large M c d w
  constructor
  · intro h'; exact h'.2.2.2.2.2.2.2
  · intro hb; exact ⟨by omega,hp,he,hc,hc',hs,hs',hb⟩

end VariableWL.MachineReduction

end OAI
