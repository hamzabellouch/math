import OAI.Combinatorics.VariableWL.MachineSimulation

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.MachineOneHead
variable (M : Machine)

noncomputable def linearConstant : ℕ := 2*MultiStack.operationsBound M+5
noncomputable def quadraticConstant : ℕ :=
  linearConstant M * (1+MultiStack.operationsBound M *
    (2*(1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)+2)) * instructionsBound M

theorem stackTime_le (m T : ℕ) : stackTime M m T ≤ linearConstant M*(m+T+1) := by
  unfold stackTime linearConstant
  have hC := Nat.zero_le (MultiStack.operationsBound M)
  nlinarith

theorem time_le (m T : ℕ) : time M m T ≤ quadraticConstant M*(m+T+1)^2 := by
  let X := m+T+1
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hm : m ≤ X := by dsimp [X]; omega
  have hc : MultiStack.operationsBound M ≤ MultiStack.operationsBound M*X := Nat.le_mul_of_pos_right _ hx
  have hsum : m+stackTime M m T*MultiStack.operationsBound M+MultiStack.operationsBound M ≤
      (1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)*X := by
    have hs := Nat.mul_le_mul_right (MultiStack.operationsBound M) (stackTime_le M m T)
    dsimp only [X] at hx hm hc ⊢
    nlinarith
  have hfactor : 1+MultiStack.operationsBound M*(2*(m+stackTime M m T*MultiStack.operationsBound M+
      MultiStack.operationsBound M)+2) ≤
      (1+MultiStack.operationsBound M*(2*(1+linearConstant M*MultiStack.operationsBound M+
      MultiStack.operationsBound M)+2))*X := by
    have hh : 2*(m+stackTime M m T*MultiStack.operationsBound M+MultiStack.operationsBound M)+2 ≤
        (2*(1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)+2)*X := by
      nlinarith
    have := Nat.mul_le_mul_left (MultiStack.operationsBound M) hh
    nlinarith
  unfold time quadraticConstant
  calc
    _ ≤ (linearConstant M*X)*((1+MultiStack.operationsBound M*
      (2*(1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)+2))*X)*instructionsBound M :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (stackTime_le M m T) hfactor)
    _ = _ := by dsimp [X]; ring

def inputExponent (c d m : ℕ) : ℕ := (c+1)*(m+1)^(d+1)
noncomputable def simulationExponent (c d m : ℕ) : ℕ :=
  quadraticConstant M+3+2*inputExponent c d m
noncomputable def addressBits (c d m : ℕ) : ℕ := simulationExponent M c d m+2

theorem inputExponent_ge_time (c d m : ℕ) : c*(m+1)^d ≤ inputExponent c d m := by
  unfold inputExponent
  rw [pow_succ,← Nat.mul_assoc]
  exact (Nat.mul_le_mul_right _ (Nat.le_succ c)).trans
    (Nat.le_mul_of_pos_right _ (by omega))

theorem inputExponent_ge_length (c d m : ℕ) : m+1 ≤ inputExponent c d m := by
  unfold inputExponent
  rw [pow_succ]
  have hp : 1 ≤ (c+1)*(m+1)^d := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos (by omega) _))
  simpa only [Nat.mul_assoc,one_mul] using Nat.mul_le_mul_right (m+1) hp

theorem exponential_input_bound (c d m : ℕ) :
    m+2^(c*(m+1)^d)+1 ≤ 2^(inputExponent c d m+1) := by
  have ht : 2^(c*(m+1)^d) ≤ 2^inputExponent c d m :=
    Nat.pow_le_pow_right (by omega) (inputExponent_ge_time c d m)
  have hm : m+1 ≤ 2^inputExponent c d m :=
    (inputExponent_ge_length c d m).trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  rw [pow_succ]
  omega

theorem simulation_bound (c d m : ℕ) :
    time M m (2^(c*(m+1)^d)) ≤ 2^simulationExponent M c d m := by
  have h := time_le M m (2^(c*(m+1)^d))
  have hp := Nat.pow_le_pow_left (exponential_input_bound c d m) 2
  have hc : quadraticConstant M ≤ 2^(quadraticConstant M+1) :=
    (Nat.le_succ _).trans (Nat.le_of_lt Nat.lt_two_pow_self)
  refine h.trans ((Nat.mul_le_mul hc hp).trans_eq ?_)
  rw [← pow_mul,← pow_add]
  congr 1
  unfold simulationExponent
  omega

theorem input_fits_budget (c d m : ℕ) : m+1 ≤ 2^simulationExponent M c d m := by
  have h : inputExponent c d m ≤ simulationExponent M c d m := by
    unfold simulationExponent; omega
  exact (inputExponent_ge_length c d m).trans ((Nat.le_of_lt Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by omega) h))

theorem ring_budget (c d m : ℕ) :
    2*(2^simulationExponent M c d m) < 2^addressBits M c d m := by
  unfold addressBits
  rw [pow_add]
  have h := Nat.two_pow_pos (simulationExponent M c d m)
  norm_num
  omega

theorem addressBits_ge_four (c d m : ℕ) : 4 ≤ addressBits M c d m := by
  unfold addressBits simulationExponent
  omega

theorem addressBits_polynomial (c d m : ℕ) :
    addressBits M c d m ≤ (quadraticConstant M+2*c+7)*(m+1)^(d+1) := by
  unfold addressBits simulationExponent inputExponent
  have h : 1 ≤ (m+1)^(d+1) := one_le_pow₀ (by omega)
  nlinarith

end VariableWL.MachineOneHead

namespace VariableWL.MachineReduction
open MachineOneHead
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)

abbrev Letter := OneHead.Cell (Control M) (Alphabet M)
noncomputable instance letterFintype : Fintype (Letter M) := inferInstance
noncomputable def bits (w : Word) : ℕ := addressBits M c d w.length
noncomputable def dimension (w : Word) : ℕ := bits M c d w+bits M c d w
noncomputable def internal (w : Word) : ℕ := 4*(dimension M c d w+1)

theorem fits (w : Word) : (input M w).length < 2^bits M c d w := by
  have hi := (input_length M w).trans (input_fits_budget M c d w.length)
  have hr := ring_budget M c d w.length
  change (input M w).length < 2^addressBits M c d w.length
  omega

noncomputable def circuit (w : Word) : Circuit.ProductCellular.Data (Letter M)
    (bits M c d w) (input M w).length :=
  OneHead.product (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j]) (fits M c d w)

abbrev Real (w : Word) := Circuit.Description.Real
  (S := Letter M) (A := Circuit.Cellular.Triple (Letter M) × Bool)
  (E := Circuit.ProductCellular.Edge (Letter M) (bits M c d w))
abbrev Comparison (w : Word) := Circuit.Description.Comparison
  (E := Circuit.ProductCellular.Edge (Letter M) (bits M c d w))
  (R := (circuit M c d w).Request)

noncomputable def imageInstance (w : Word) : ProductImages.Instance (dimension M c d w)
    (Real M c d w) (Comparison M c d w) := (circuit M c d w).description.consistency

noncomputable instance realFintype (w : Word) : Fintype (Real M c d w) := inferInstance
noncomputable instance comparisonFintype (w : Word) : Fintype (Comparison M c d w) := by
  classical
  letI : Fintype (Circuit.ProductCellular.Edge (Letter M) (bits M c d w)) := inferInstance
  letI : Fintype {h : Fin (bits M c d w) // (circuit M c d w).threshold h=false} := Fintype.ofFinite _
  letI : Fintype {f : Letter M // f ∈ (circuit M c d w).accepting} := Fintype.ofFinite _
  unfold Comparison Circuit.Description.Comparison Circuit.ProductCellular.Data.Request
  infer_instance
instance realNonempty (w : Word) : Nonempty (Real M c d w) := ⟨.inr (.inr ())⟩

theorem dimension_large (w : Word) : 8 ≤ dimension M c d w := by
  have h := addressBits_ge_four M c d w.length
  unfold dimension bits
  omega

theorem internal_pos (w : Word) : 0 < internal M c d w := by unfold internal; omega

theorem enough_links (w : Word) : dimension M c d w+1 < internal M c d w+1 := by
  unfold internal
  omega

noncomputable def marked (w : Word) : Fin (dimension M c d w) := ⟨0,by have := dimension_large M c d w; omega⟩

noncomputable def generalGraph (w : Word) (ε : Affine.Bit) : Graph :=
  General.finiteGraph (imageInstance M c d w) (marked M c d w) (n := internal M c d w) ε

noncomputable def subcubicGraph (w : Word) (ε : Affine.Bit) : Graph :=
  Subcubic.finiteGraph (imageInstance M c d w) (by have := dimension_large M c d w; omega)
    (internal_pos M c d w) (marked M c d w) ε

theorem consistent_iff_output (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) :
    (imageInstance M c d w).Consistent ↔ b=true := by
  obtain ⟨t,ht,halt,accept⟩ := outputs_oneHead M w b _ h
  have he := OneHead.product_consistent_iff (oneHead M) default
    (fun j : Fin (input M w).length => (input M w)[j]) (fits M c d w) (input_pos M w)
    (2^simulationExponent M c d w.length) t (ring_budget M c d w.length)
    ((input_length M w).trans (input_fits_budget M c d w.length))
    (ht.trans (simulation_bound M c d w.length)) halt
  change (imageInstance M c d w).Consistent ↔ _ at he
  rw [he,accept]
  cases b <;> decide

 theorem general_correct (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) :
    Equivalent (generalGraph M c d w 0) (generalGraph M c d w 1) (dimension M c d w) ↔ b=true := by
  rw [generalGraph,generalGraph,General.equivalent_iff_consistent _ _
    (by have := dimension_large M c d w; omega) (internal_pos M c d w) (enough_links M c d w)]
  exact consistent_iff_output M c d w b h

 theorem subcubic_correct (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) :
    Equivalent (subcubicGraph M c d w 0) (subcubicGraph M c d w 1) (dimension M c d w) ↔ b=true := by
  rw [subcubicGraph,subcubicGraph,Subcubic.equivalent_iff_consistent _ _ _ _
    (by have := dimension_large M c d w; omega) (enough_links M c d w)]
  exact consistent_iff_output M c d w b h

 theorem subcubic_promise (w : Word) :
    0 < (subcubicGraph M c d w 0).order ∧
    (subcubicGraph M c d w 0).order=(subcubicGraph M c d w 1).order ∧
    (subcubicGraph M c d w 0).graph.Connected ∧ (subcubicGraph M c d w 1).graph.Connected ∧
    Subcubic (subcubicGraph M c d w 0) ∧ Subcubic (subcubicGraph M c d w 1) :=
  Subcubic.promise (imageInstance M c d w) _ _ _

 theorem general_promise (w : Word) :
    0 < (generalGraph M c d w 0).order ∧
    (generalGraph M c d w 0).order=(generalGraph M c d w 1).order :=
  ⟨General.positive_order _ _ _,General.equal_orders _ _⟩

 theorem dimension_polynomial (w : Word) :
    dimension M c d w ≤ (2*(quadraticConstant M+2*c+7))*(w.length+1)^(d+1) := by
  have h := addressBits_polynomial M c d w.length
  unfold dimension bits
  nlinarith

end VariableWL.MachineReduction

namespace VariableWL.RealizationSize
open VariableWL.Affine Blocks Subdivision
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E)

omit [Fintype P] [Fintype E] in
theorem dimension_le_two (t : Subdivision.Vertex P E n) : Blocks.dimension J t ≤ 2 := by
  cases t with
  | inl p => rcases J.dimension_one_or_two p with h|h <;> simp [Blocks.dimension,h]
  | inr q => simp [Blocks.dimension]

theorem horizontal_card : Fintype.card (Horizontal r n P E) ≤
    4*r*(Fintype.card P+Fintype.card E*n) := by
  have h := Fintype.card_le_of_injective (fun h : Horizontal r n P E => (h.row,h.type,h.first,h.last))
    (by
      rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ he
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl⟩
      rfl)
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_sum,Fintype.card_bool,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem square_card : Fintype.card (Square r n E) ≤ 4*r*(Fintype.card E*(n+1)) := by
  have h := Fintype.card_le_of_injective (fun h : Square r n E => (h.row,h.link,h.first,h.last))
    (by
      rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ he
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl⟩
      rfl)
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem block_card : Fintype.card (Block (n := n) J) ≤
    4*r*(Fintype.card P+Fintype.card E*(2*n+1)) := by
  have h : Fintype.card (Block (n := n) J) ≤ Fintype.card (RawBlock r n P E) := Fintype.card_subtype_le _
  have hh := horizontal_card (r := r) (n := n) (P := P) (E := E)
  have hs := square_card (r := r) (n := n) (E := E)
  rw [Fintype.card_sum] at h
  nlinarith

omit [Fintype P] [Fintype E] in
theorem coordinate_card (b : RawBlock r n P E) : Fintype.card (BlockCoordinates.Coordinate J b) ≤ 6 := by
  cases b with
  | inl h =>
    have hd : Blocks.dimension J h.type ≤ 6 := (dimension_le_two J h.type).trans (by omega)
    simpa [BlockCoordinates.Coordinate] using hd
  | inr s =>
    have hl := dimension_le_two J (left J.source s.link)
    have hr := dimension_le_two J (right J.target s.link)
    simpa only [BlockCoordinates.Coordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool] using
      (show Blocks.dimension J (left J.source s.link)+Blocks.dimension J (right J.target s.link)+2 ≤ 6 by omega)

omit [Fintype P] [Fintype E] in
theorem rawValue_card (b : RawBlock r n P E) : Fintype.card (RawValue J b) ≤ 64 := by
  rw [Fintype.card_congr (BlockCoordinates.coordinateEquiv J b).toEquiv]
  simpa only [Fintype.card_fun,ZMod.card,show (2:ℕ)^6=64 by decide] using
    (Nat.pow_le_pow_right (by omega : 0<2) (coordinate_card J b))

omit [Fintype P] [Fintype E] in
theorem valuation_card (marked : Fin r) (ε : Bit) (b : Block (n := n) J) :
    Fintype.card (Valuation J marked ε b) ≤ 64 :=
  (Fintype.card_subtype_le _).trans (rawValue_card J b.val)

theorem general_base_card (marked : Fin r) (ε : Bit) :
    Fintype.card (General.Base (n := n) J marked ε) ≤ 64*Fintype.card (Block (n := n) J) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ b : Block (n := n) J, 64 := Finset.sum_le_sum (fun b _ => valuation_card J marked ε b)
    _ = _ := by simp [Nat.mul_comm]

theorem general_leaves (marked : Fin r) (b : Block (n := n) J) :
    General.leafCount J marked b ≤ Fintype.card (Block (n := n) J)*
      (64*Fintype.card (Block (n := n) J)+1) := by
  unfold General.leafCount
  exact Nat.mul_le_mul (Nat.succ_le_of_lt (Fintype.equivFin _ b).isLt)
    (Nat.add_le_add_right (general_base_card J marked 0) _)

theorem general_order (marked : Fin r) (ε : Bit) :
    (General.finiteGraph J marked (n := n) ε).order ≤
      64*Fintype.card (Block (n := n) J)*(1+Fintype.card (Block (n := n) J)*
        (64*Fintype.card (Block (n := n) J)+1)) := by
  change Fintype.card (General.Vertex J marked (General.leafCount J marked) ε) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ b : Block (n := n) J, 64*(1+Fintype.card (Block (n := n) J)*
        (64*Fintype.card (Block (n := n) J)+1)) := by
      apply Finset.sum_le_sum
      intro b _
      change Fintype.card (Valuation J marked ε b × Option (Fin (General.leafCount J marked b))) ≤ _
      rw [Fintype.card_prod,Fintype.card_option,Fintype.card_fin]
      exact Nat.mul_le_mul (valuation_card J marked ε b)
        (by have := general_leaves J marked b; omega)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]; ring

end VariableWL.RealizationSize

namespace VariableWL.RealizationSize
open VariableWL.Affine Blocks Subdivision BlockCoordinates PrefixParts
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E)

noncomputable def readoutSet : RawBlock r n P E → Finset (Readout r n P E)
  | .inl h => {.inl h}
  | .inr s => {.inl (squareLeft J s),.inl (squareRight J s),.inr (squareBottom s),.inr (squareTop s)}

theorem readout_card (b : RawBlock r n P E) :
    Fintype.card {a : Readout r n P E // HasReadout J b a} ≤ 4 := by
  have hc : Fintype.card {a : Readout r n P E // HasReadout J b a}=(readoutSet J b).card :=
    Fintype.card_of_subtype _ (by intro a; cases b <;> simp [readoutSet,HasReadout])
  rw [hc]
  cases b with
  | inl h => simp [readoutSet]
  | inr s =>
    unfold readoutSet
    calc
      _ ≤ 1+(1+(1+1)) := by
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
            ((Finset.card_insert_le _ _).trans (by simp)) _)) _)
      _ = _ := by decide

theorem proper_card (b : Block (n := n) J) :
    Fintype.card (Proper J b) ≤ 4*Fintype.card (Block (n := n) J) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ c : {c : Block (n := n) J // c≠b}, 4 := by
      apply Finset.sum_le_sum
      intro c _
      exact (Fintype.card_le_of_injective
        (fun a : {a : Readout r n P E // HasReadout J b.val a ∧ HasReadout J c.val.val a} =>
          (⟨a.val,a.property.1⟩ : {a : Readout r n P E // HasReadout J b.val a}))
        (by intro a a' h; apply Subtype.ext; exact congrArg (fun x : {a : Readout r n P E // HasReadout J b.val a} => x.val) h)).trans (readout_card J b.val)
    _ = 4*Fintype.card {c : Block (n := n) J // c≠b} := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (Fintype.card_subtype_le _)

theorem data_dimension (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J) :
    (data J hr hn marked b).dimension ≤ 6 := coordinate_card J b.val

theorem data_channels (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J) :
    (data J hr hn marked b).channels ≤ 4*Fintype.card (Block (n := n) J)+1 :=
  Nat.add_le_add_right (proper_card J b) _

end VariableWL.RealizationSize

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable (D : Data) (hD : D.dimension ≤ 6)
include hD

theorem valuation_card_bound (ε : Bit) : Fintype.card (D.Valuation ε) ≤ 64 := by
  have hc : Fintype.card (D.Valuation ε) ≤ Fintype.card (Vec D.dimension) := Fintype.card_subtype_le _
  have hp : (2:ℕ)^D.dimension ≤ 2^6 := Nat.pow_le_pow_right (by omega) hD
  simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card] at hc
  exact hc.trans hp

theorem tree_card_bound (ε : Bit) : Fintype.card (D.Tree ε) ≤ 448*D.channels := by
  have hc : Fintype.card (D.Tree ε) ≤ Fintype.card D.RawTree := Fintype.card_subtype_le _
  change Fintype.card (D.Tree ε) ≤ Fintype.card (Fin D.channels × Fin (D.dimension+1) × Vec D.dimension) at hc
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card] at hc
  have hp : (2:ℕ)^D.dimension ≤ 64 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hD
  have hm := Nat.mul_le_mul_left D.channels (Nat.mul_le_mul (by omega : D.dimension+1 ≤ 7) hp)
  exact hc.trans (by nlinarith)

theorem vertex_card_bound (ε : Bit) : Fintype.card (D.Vertex ε) ≤ 1+512*D.channels := by
  change Fintype.card (Unit ⊕ ((Fin D.channels × D.Valuation ε) ⊕ D.Tree ε)) ≤ _
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,Fintype.card_fin]
  have hv := Nat.mul_le_mul_left D.channels (valuation_card_bound D hD ε)
  have ht := tree_card_bound D hD ε
  nlinarith

theorem sort_card_bound : Fintype.card D.SortTag ≤ 1+8*D.channels := by
  change Fintype.card (Unit ⊕ (Fin D.channels ⊕ (Σ c : Fin D.channels,
    {h : Fin (D.dimension+1) // D.root c ≤ h.val}))) ≤ _
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,Fintype.card_sigma]
  have h : (∑ c : Fin D.channels, Fintype.card {h : Fin (D.dimension+1) // D.root c ≤ h.val}) ≤
      ∑ _c : Fin D.channels, 7 := by
    apply Finset.sum_le_sum
    intro c _
    exact (Fintype.card_subtype_le _).trans (by simpa using (show D.dimension+1 ≤ 7 by omega))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  omega

end VariableWL.PrefixParts.Data

namespace VariableWL.RealizationSize
open VariableWL.Affine Blocks Subdivision BlockCoordinates PrefixParts
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)

theorem owner_card (ε : Bit) : Fintype.card (Wiring.Vertex (data J hr hn marked) ε) ≤
    Fintype.card (Block (n := n) J)*(1+512*(4*Fintype.card (Block (n := n) J)+1)) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _b : Block (n := n) J, (1+512*(4*Fintype.card (Block (n := n) J)+1)) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Data.vertex_card_bound _ (data_dimension J hr hn marked b) ε).trans
        (by have := data_channels J hr hn marked b; omega)
    _ = _ := by simp

theorem sort_card : Fintype.card (Wiring.SortTag (data J hr hn marked)) ≤
    Fintype.card (Block (n := n) J)*(1+8*(4*Fintype.card (Block (n := n) J)+1)) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _b : Block (n := n) J, (1+8*(4*Fintype.card (Block (n := n) J)+1)) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Data.sort_card_bound _ (data_dimension J hr hn marked b)).trans
        (by have := data_channels J hr hn marked b; omega)
    _ = _ := by simp

theorem subcubic_order (ε : Bit) :
    (Subcubic.finiteGraph J hr hn marked ε).order ≤
      (Fintype.card (Block (n := n) J)*(1+512*(4*Fintype.card (Block (n := n) J)+1)))*3*
        (Fintype.card (Block (n := n) J)*(1+8*(4*Fintype.card (Block (n := n) J)+1))+2) := by
  change Fintype.card (Wiring.UncoloredVertex (data J hr hn marked) ε) ≤ _
  rw [Fintype.card_congr (SubcubicRealization.Vertex.equivSigma (color := Wiring.color (data J hr hn marked)))]
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _v : Wiring.Vertex (data J hr hn marked) ε, 3*
        (Fintype.card (Block (n := n) J)*(1+8*(4*Fintype.card (Block (n := n) J)+1))+2) := by
      apply Finset.sum_le_sum
      intro v _
      rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
      apply Nat.mul_le_mul_left
      have hc : Wiring.color (data J hr hn marked) v ≤ Fintype.card (Wiring.SortTag (data J hr hn marked)) :=
        Nat.succ_le_of_lt (Fintype.equivFin _ (Wiring.sort (data J hr hn marked) v)).isLt
      have hs := sort_card J hr hn marked
      omega
    _ ≤ _ := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
      exact (Nat.mul_le_mul_right _ (owner_card J hr hn marked ε)).trans_eq (by ring)

end VariableWL.RealizationSize

end OAI
