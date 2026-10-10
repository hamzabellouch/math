import OAI.Computability.MeanPayoff.RecursiveExecution

namespace OAI

namespace MeanPayoff.Label
 theorem exponent_arithmetic (n W L : ℕ) (hn : n≤L)
    (hw : W≤(n+1)*2^L) : Nat.clog 2 (64*(n+1)*(W+1))≤3*L+9 := by
  have hl : L+1≤2^(L+1) := Nat.lt_two_pow_self.le
  have hn' : n+1≤2^(L+1) := (by omega : n+1≤L+1).trans hl
  have hp : 1≤(n+1)*2^L := by simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1≤n+1 by omega) (Nat.one_le_pow L 2 (by decide))
  have hw' : W+1≤2^((L+1)+L+1) := by
    have hm := Nat.mul_le_mul_right (2^L) hn'
    rw [←Nat.pow_add] at hm
    rw [Nat.pow_succ]
    omega
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
  calc
    _≤64*2^(L+1)*2^((L+1)+L+1) := Nat.mul_le_mul (Nat.mul_le_mul_left 64 hn') hw'
    _=2^(6+(L+1)+((L+1)+L+1)) := by
      rw [Nat.pow_add 2 (6+(L+1)),Nat.pow_add 2 6]
    _=2^(3*L+9) := by congr 1; omega
 theorem initialExponent_linear (G : Game) : initialExponent G≤3*(input G).length+9 := by
  apply exponent_arithmetic G.n (sourceWeight G) (input G).length (input_n_le G)
  have h := input_weightBound_le G
  rw [weightBound_eq_source] at h
  exact_mod_cast h
 theorem root_steps_bound (G : Game) :
    2*Label.callBound (TreeDevice.Certified.DetDriver.branchFactor G.n)
      (initialExponent G+budget (uniformMass G) (uniformMass G) (uniformMass_pos G) (uniformMass_pos G))
      (budget (uniformMass G) (uniformMass G) (uniformMass_pos G) (uniformMass_pos G))
      ≤2^(25000*(Nat.clog 2 ((input G).length+2))^2) := by
  let L := (input G).length
  let h := Nat.clog 2 (L+2)
  let B := budget (uniformMass G) (uniformMass G) (uniformMass_pos G) (uniformMass_pos G)
  let H := initialExponent G+B
  let s := TreeDevice.Certified.DetDriver.branchFactor G.n
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hL : L+2≤2^h := Nat.le_pow_clog (by decide) _
  have hhL : h≤L+2 := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr Nat.lt_two_pow_self.le
  have hn : G.n≤L := input_n_le G
  have hB : B≤6*h := (initial_budget_le G).trans (Nat.mul_le_mul_left 6 (Nat.clog_mono_right 2 (by omega)))
  have hd := initialExponent_linear G
  have hH : H+1≤22*(L+2) := by dsimp [H]; change initialExponent G≤3*L+9 at hd; omega
  have hHp : H+1≤2^(6*h) := by
    calc
      _≤32*2^h := (hH.trans (Nat.mul_le_mul_left 22 hL)).trans (by omega)
      _=2^(5+h) := by rw [pow_add]; rfl
      _≤2^(6*h) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsp : s≤2^(13*h) := by
    have hs : s≤4096*(L+2) := by dsimp [s,TreeDevice.Certified.DetDriver.branchFactor]; omega
    calc
      _≤4096*2^h := hs.trans (Nat.mul_le_mul_left 4096 hL)
      _=2^(12+h) := by rw [pow_add]; rfl
      _≤2^(13*h) := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : 1+H*s≤2^(20*h) := by
    have hm := Nat.mul_le_mul (show H≤2^(6*h) by omega) hsp
    rw [←pow_add] at hm
    have hp : 1≤2^(6*h+13*h) := Nat.one_le_pow _ 2 (by decide)
    calc
      _≤2^(6*h+13*h+1) := by rw [pow_succ]; omega
      _≤2^(20*h) := Nat.pow_le_pow_right (by decide) (by omega)
  change 2*((H+1)*(1+H*s)^B)≤2^(25000*h^2)
  calc
    _≤2*(2^(6*h)*(2^(20*h))^(6*h)) := Nat.mul_le_mul_left 2
      (Nat.mul_le_mul hHp ((Nat.pow_le_pow_left ht B).trans
        (Nat.pow_le_pow_right (by positivity) hB)))
    _=2^(1+(6*h+(20*h)*(6*h))) := by
      rw [Nat.pow_add 2 1,Nat.pow_add 2 (6*h),Nat.pow_mul 2 (20*h) (6*h)]
    _=2^(1+6*h+(20*h)*(6*h)) := by rw [Nat.add_assoc]
    _≤2^(25000*h^2) := Nat.pow_le_pow_right (by decide) (by nlinarith only [hh])
end MeanPayoff.Label

namespace MeanPayoff.TreeDevice.Certified
open Label
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Counter
@[simp] theorem inc_length (cs : Count) : (inc cs).length=cs.length+1 := rfl
end Counter
namespace DetRoot
noncomputable def nWord : Code Parsed W := InputCode.n ≫ₚ Counter.word
noncomputable def nPlus : Code Parsed W := (nWord ⋏ₚ Word.constant 1) ≫ₚ Word.add
noncomputable def wPlus : Code Parsed W := (InputCode.bound ⋏ₚ Word.constant 1) ≫ₚ Word.add
noncomputable def threshold : Code Parsed W := ((nPlus ⋏ₚ wPlus) ≫ₚ Word.mul) ≫ₚ RawBudget.times 64
noncomputable def exponent : Code Parsed Count := threshold ≫ₚ NaturalLog.ceil
noncomputable def width : Code Parsed W := exponent ≫ₚ Word.power
noncomputable def lower : Code Parsed (List W) := (Word.constant 0 ⋏ₚ InputCode.n) ≫ₚ Array.replicate
noncomputable def mass : Code Parsed DetMass.Data := nWord ⋏ₚ ((Word.constant 1 ⋏ₚ InputCode.n) ≫ₚ Array.replicate)
noncomputable def input : Code Parsed DetRaw.Input := (width ⋏ₚ lower) ⋏ₚ mass ⋏ₚ mass
noncomputable def root : Code Digits DetDriver.Env := InputCode.parse ≫ₚ (InputCode.rows ⋏ₚ DetDriver.callCode input (const []))
 theorem threshold_val (G : Game) : (threshold (InputCode.game G)).val=64*(G.n+1)*(Label.sourceWeight G+1) := by
  simp only [threshold,comp_eval,pair_eval,RawBudget.times_val,Word.mul_val,nPlus,wPlus,
    Word.add_val,Word.constant_val,nWord,Counter.word_val,InputCode.n_game,List.length_replicate,
    InputCode.bound_val,Label.weightBound_eq_source]
  ring
 theorem exponent_length (G : Game) : (exponent (InputCode.game G)).length=Label.initialExponent G := by
  change (NaturalLog.ceil (threshold (InputCode.game G))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [threshold_val]; positivity),threshold_val]
  norm_cast
 theorem input_rep (G : Game) : DetRaw.Rep (fun _ => 0) (Label.initialExponent G)
    (uniformMass G) (uniformMass G) (input (InputCode.game G)) := by
  have hm : DetMass.Rep (uniformMass G) (mass (InputCode.game G)) := by
    refine ⟨?_,fun _ => EdgeRead.encodedWord 1,?_,?_,?_⟩
    · change 0<(Counter.word (InputCode.n (InputCode.game G))).val
      simp only [Counter.word_val,InputCode.n_game,List.length_replicate]
      exact_mod_cast G.positive
    · change (InputCode.n (InputCode.game G)).map (fun _ => EdgeRead.encodedWord 1)=List.ofFn _
      simp only [InputCode.n_game,List.map_replicate,List.ofFn_const]
    · intro i
      change 0<(Word.constant 1 ()).val
      rw [Word.constant_val]
      norm_num
    · intro i
      change 1/(G.n:ℚ)=((Word.constant 1 ()).val:ℚ)/((Counter.word (InputCode.n (InputCode.game G))).val:ℚ)
      simp only [Word.constant_val,Counter.word_val,InputCode.n_game,List.length_replicate,Int.cast_one,Int.cast_natCast]
  refine ⟨?_,?_,hm,hm⟩
  · change (Word.power (exponent (InputCode.game G))).val=_
    rw [Word.power_val,exponent_length]
  · have h := Array.repeat_rep (n:=G.n) (Word.constant 0 (InputCode.game G)) (InputCode.n (InputCode.game G))
        (by rw [InputCode.n_game,List.length_replicate])
    change VectorRep (fun _ : Fin G.n => (0 : ℤ))
      (Array.replicate (Word.constant 0 (InputCode.game G),InputCode.n (InputCode.game G)))
    simpa only [Word.constant_val] using h
 theorem root_game (G : Game) : root ⟨MeanPayoff.input G⟩=
    (Graph.codeVertices G (Normalize.word G),DetDriver.call (input (InputCode.game G)) []) := by
  simp only [root,comp_eval,pair_eval,InputCode.parse_game,InputCode.rows_game,DetDriver.callCode_eval,const_eval]
end DetRoot

namespace DetPreparation
noncomputable def inputLength : Code Digits Count := by
  let F := Map.device (TreeDevice.constant boolData Median.unitData ())
  refine ⟨fun d => d.bits.map (fun _ => ()),F.recode encode encode Digits.bits
    (fun d => d.bits.map (fun _ => ())) (fun _ => rfl) (fun _ => rfl),?_⟩
  obtain ⟨K,d,h⟩ := PolynomialCost.map (LinearCost.constant boolData Median.unitData ()).polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def logarithm : Code Digits Count :=
  inputLength ≫ₚ Counter.inc ≫ₚ Counter.inc ≫ₚ Counter.word ≫ₚ NaturalLog.ceil
noncomputable def exponent : Code Digits Count :=
  (const (List.replicate 25000 ()) ⋏ₚ ((logarithm ⋏ₚ logarithm) ≫ₚ Counter.mul)) ≫ₚ Counter.mul
 theorem logarithm_length (d : Digits) : (logarithm d).length=Nat.clog 2 (d.bits.length+2) := by
  change (NaturalLog.ceil (Counter.word (Counter.inc (Counter.inc (inputLength d))))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [Counter.word_val]; simp only [Counter.inc_length]; positivity),Counter.word_val,Int.toNat_natCast]
  change Nat.clog 2 ((d.bits.map (fun _ => ())).length+1+1)=_
  simp only [List.length_map,Nat.add_assoc]
 theorem exponent_length (d : Digits) : (exponent d).length=25000*(Nat.clog 2 (d.bits.length+2))^2 := by
  simp only [exponent,comp_eval,pair_eval,Counter.mul_length,const_eval,List.length_replicate,logarithm_length,pow_two]
noncomputable def seed : Code Digits (Count×DetDriver.Env) := exponent ⋏ₚ DetRoot.root
noncomputable def inflate : Device encode encode
    (fun z : Count×DetDriver.Env => (Fold.fold Allocation.double.eval [()] z.1,z.2)) :=
  pairMap Allocation.device (TreeDevice.identity encode)
noncomputable def assemble : Code (Count×DetDriver.Env) (List Bool) :=
  swap ≫ₚ DetDriver.run ≫ₚ snd ≫ₚ fst ≫ₚ snd ≫ₚ snd
noncomputable def value (d : Digits) : List Bool :=
  assemble (Fold.fold Allocation.double.eval [()] (exponent d),DetRoot.root d)
noncomputable def device : Device encode encode value :=
  @compose Digits (Count×DetDriver.Env) (List Bool) encode encode encode seed.eval
    (fun z => assemble (Fold.fold Allocation.double.eval [()] z.1,z.2)) seed.device
    (@compose (Count×DetDriver.Env) (Count×DetDriver.Env) (List Bool) encode encode encode
      (fun z => (Fold.fold Allocation.double.eval [()] z.1,z.2)) assemble.eval inflate assemble.device)
 theorem value_game (G : Game) : value ⟨MeanPayoff.input G⟩=List.ofFn (Label.mainLabels G) := by
  obtain ⟨k,hk,he⟩ := DetDriver.call_exec G (fun _ => 0) (Label.initialExponent G)
    (uniformMass G) (uniformMass G) (uniformMass_pos G) (uniformMass_pos G)
    (Normalize.word G) (Normalize.word_val G) _ (DetRoot.input_rep G) []
  have hb := Label.root_steps_bound G
  let N := 2^(exponent ⟨MeanPayoff.input G⟩).length
  have hkN : k≤N := by dsimp [N]; rw [exponent_length]; change k≤2^(25000*(Nat.clog 2 ((MeanPayoff.input G).length+2))^2); omega
  have hr : ∀ j, (DetDriver.advance (Graph.codeVertices G (Normalize.word G)))^[j]
      (DetDriver.ret (List.ofFn (Label.mainLabels G)) [])=DetDriver.ret (List.ofFn (Label.mainLabels G)) [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply',ih]; rfl
  have heN : (DetDriver.advance (Graph.codeVertices G (Normalize.word G)))^[N]
      (DetDriver.call (DetRoot.input (InputCode.game G)) [])=DetDriver.ret (List.ofFn (Label.mainLabels G)) [] := by
    rw [show N=(N-k)+k by omega,Function.iterate_add_apply,he]
    exact hr _
  change (DetDriver.run (DetRoot.root ⟨MeanPayoff.input G⟩,Fold.fold Allocation.double.eval [()] (exponent ⟨MeanPayoff.input G⟩))).2.1.2.2=_
  rw [DetDriver.run_eval,DetRoot.root_game,Allocation.exact,List.length_replicate]
  change ((DetDriver.advance (Graph.codeVertices G (Normalize.word G)))^[N]
    (DetDriver.call (DetRoot.input (InputCode.game G)) [])).1.2.2=_
  rw [heN]
  rfl
end DetPreparation
end MeanPayoff.TreeDevice.Certified

namespace MeanPayoff.TreeDevice.Certified.DetPreparation
open BinaryData
 theorem seed_eval (d : Digits) : seed d=(exponent d,DetRoot.root d) := rfl
 theorem inflate_limit (z : Count×DetDriver.Env) : inflate.limit z=Allocation.device.limit z.1+1+
    24*treeSize (encode (Fold.fold Allocation.double.eval [()] z.1))+24*treeSize (encode z.2)+50 := by
  rcases z with ⟨c,s⟩
  rw [inflate,pairMap_limit]
  change _+1+24*_+12*_+12*_+50=_
  simp only [id_eq]
  omega
 theorem device_limit (d : Digits) : device.limit d=
    seed.device.limit d+inflate.limit (seed d)+
      assemble.device.limit (Fold.fold Allocation.double.eval [()] (exponent d),DetRoot.root d)+4 := by
  simp only [device, compose_limit]
  simp only [seed_eval]
  omega

 theorem exponent_poly : PolynomialCost exponent.device := exponent.polynomial
 theorem root_poly : PolynomialCost DetRoot.root.device := DetRoot.root.polynomial
 theorem seed_poly : PolynomialCost seed.device := PolynomialCost.fanout exponent_poly root_poly
 theorem assemble_poly : PolynomialCost assemble.device := assemble.polynomial
end MeanPayoff.TreeDevice.Certified.DetPreparation

namespace MeanPayoff.TreeDevice.Certified.DetPreparation
open BinaryData
noncomputable def resource (d : Digits) : ℕ := treeSize (encode d)+2^(exponent d).length
 theorem input_bound : PolyBound resource (fun d => treeSize (encode d)) :=
  (PolyBound.base resource).mono (fun _ => Nat.le_add_right _ _)
 theorem seed_cost : PolyBound resource seed.device.limit := by
  obtain ⟨K,e,h⟩ := seed_poly
  refine ⟨K,e,fun d => (h d).trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.le_add_right _ _) 1
 theorem seed_size_le (d : Digits) : treeSize (encode (seed d)) ≤ treeSize (encode d)+seed.device.limit d :=
  output_size seed.device d
 theorem seed_size : PolyBound resource (fun d => treeSize (encode (seed d))) :=
  (input_bound.add seed_cost).mono seed_size_le
 theorem exponent_size : PolyBound resource (fun d => treeSize (encode (exponent d))) := by
  apply seed_size.mono
  intro d
  have h := Size.fst (seed d)
  rw [seed_eval] at h
  exact h
 theorem exponent_size_length : PolyBound resource (fun d => (exponent d).length) :=
  exponent_size.mono (fun _ => Size.length _)
 theorem power_bound : PolyBound resource (fun d => 2^(exponent d).length) :=
  (PolyBound.base resource).mono (fun _ => Nat.le_add_left _ _)
 theorem allocation_init_cost : PolyBound resource (fun d => Allocation.init.device.limit (exponent d)) :=
  polynomial_limit Allocation.init.polynomial resource exponent exponent_size
 theorem allocation_fold_cost : PolyBound resource
    (fun d => (Fold.device Allocation.double.device).limit ([()],exponent d)) := by
  obtain ⟨K,e,hK⟩ := Allocation.fold_bound
  apply ((PolyBound.const resource K).mul
    (((power_bound.add exponent_size_length).add (PolyBound.const resource 1)).pow e)).mono
  intro d
  simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul,Nat.add_comm] using hK [()] (exponent d)
 theorem allocation_cost : PolyBound resource (fun d => Allocation.device.limit (exponent d)) := by
  apply ((allocation_init_cost.add allocation_fold_cost).add (PolyBound.const resource 2)).mono
  intro d
  rfl
 theorem allocation_size : PolyBound resource
    (fun d => treeSize (encode (Fold.fold Allocation.double.eval [()] (exponent d)))) :=
  polynomial_output Allocation.device resource exponent exponent_size allocation_cost
 theorem root_size : PolyBound resource (fun d => treeSize (encode (DetRoot.root d))) := by
  apply seed_size.mono
  intro d
  have h := Size.snd (seed d)
  rw [seed_eval] at h
  exact h
 theorem inflate_cost : PolyBound resource (fun d => inflate.limit (seed d)) := by
  apply ((((allocation_cost.add (PolyBound.const resource 1)).add
    ((PolyBound.const resource 24).mul allocation_size)).add
    ((PolyBound.const resource 24).mul root_size)).add (PolyBound.const resource 50)).mono
  intro d
  rw [inflate_limit,seed_eval]
 theorem inflate_size : PolyBound resource
    (fun d => treeSize (encode (Fold.fold Allocation.double.eval [()] (exponent d),DetRoot.root d))) := by
  have h := polynomial_output inflate resource (fun d => seed d) seed_size inflate_cost
  simpa only [seed_eval] using h
 theorem assemble_cost : PolyBound resource
    (fun d => assemble.device.limit (Fold.fold Allocation.double.eval [()] (exponent d),DetRoot.root d)) :=
  @polynomial_limit Digits (Count×DetDriver.Env) (List Bool) encode encode assemble.eval assemble.device
    assemble_poly resource (fun d => (Fold.fold Allocation.double.eval [()] (exponent d),DetRoot.root d)) inflate_size
 theorem cost_bound : PolyBound resource device.limit := by
  apply (((seed_cost.add inflate_cost).add assemble_cost).add (PolyBound.const resource 4)).mono
  intro d
  rw [device_limit]
 theorem output_size_le (d : Digits) : treeSize (encode (value d)) ≤ treeSize (encode d)+device.limit d :=
  output_size device d
 theorem output_bound : PolyBound resource (fun d => treeSize (encode (value d))) :=
  (input_bound.add cost_bound).mono output_size_le
end MeanPayoff.TreeDevice.Certified.DetPreparation

end OAI
