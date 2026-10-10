import OAI.Computability.MeanPayoff.RawMass

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
@[simp] theorem any_ofFn {α : Type} [Encoding α] {n : ℕ} (f : Code α Bool) (xs : Fin n → α) :
    any f (List.ofFn xs) = decide (∃ i, f (xs i)=true) := by
  simp only [any,comp_eval,filter_eval,empty_eval,not_eval]
  apply Bool.eq_iff_iff.mpr
  simp [List.filter_eq_nil_iff]
end Code

namespace DetRaw
abbrev Input := (W × List W) × DetMass.Pair
noncomputable def width : Code Input W := fst ≫ₚ fst
noncomputable def lower : Code Input (List W) := fst ≫ₚ snd
noncomputable def masses : Code Input DetMass.Pair := snd
noncomputable def a : Code Input DetMass.Data := masses ≫ₚ fst
noncomputable def b : Code Input DetMass.Data := masses ≫ₚ snd
noncomputable def box : Code Input RawBox.Data :=
  width ⋏ₚ lower ⋏ₚ ((width ⋏ₚ lower) ≫ₚ Array.translate)
noncomputable def small : Code Input Bool := (width ⋏ₚ Word.constant 4096) ≫ₚ Word.lt
noncomputable def base : Code Input Bool := masses ≫ₚ DetMass.base
noncomputable def baseLabels : Code Input (List Bool) := b ≫ₚ DetMass.labels
noncomputable def piece (k : ℕ) : Code Input W :=
  (width ⋏ₚ const (List.replicate k ())) ≫ₚ Word.shiftRight
noncomputable def amount (r : ℤ) : Code Input W := piece 12 ≫ₚ RawBudget.times r
noncomputable def center : Code Input (List W) := ((piece 1) ⋏ₚ lower) ≫ₚ Array.translate

noncomputable def child (up : Bool) : Code (Input × List W) Input :=
  ((fst ≫ₚ piece 7) ⋏ₚ (((fst ≫ₚ piece 8 ≫ₚ Word.neg) ⋏ₚ snd) ≫ₚ Array.translate)) ⋏ₚ
    (if up then ((fst ≫ₚ a ≫ₚ DetMass.scale 4 3) ⋏ₚ (fst ≫ₚ b))
     else ((fst ≫ₚ a) ⋏ₚ (fst ≫ₚ b ≫ₚ DetMass.scale 4 3)))
noncomputable def provisional : Code (Input × List W) Input :=
  ((fst ≫ₚ piece 1) ⋏ₚ (((fst ≫ₚ piece 2 ≫ₚ Word.neg) ⋏ₚ snd) ≫ₚ Array.translate)) ⋏ₚ
    (fst ≫ₚ masses)
noncomputable def continuation : Code (Input × List Bool) Input :=
  (fst ≫ₚ fst) ⋏ₚ
    ((((fst ≫ₚ a) ⋏ₚ snd) ≫ₚ DetMass.reweight) ⋏ₚ
      (((fst ≫ₚ b) ⋏ₚ (snd ≫ₚ Array.complement)) ≫ₚ DetMass.reweight))

noncomputable def lowerCap : Code Input (List W) := (amount 1536 ⋏ₚ lower) ≫ₚ Array.translate
noncomputable def upperCap : Code Input (List W) := (amount 2560 ⋏ₚ lower) ≫ₚ Array.translate
noncomputable def minus : Code (Input × List W) (List W) :=
  ((((fst ≫ₚ piece 12 ≫ₚ Word.neg) ⋏ₚ snd) ≫ₚ Array.translate) ⋏ₚ (fst ≫ₚ lowerCap)) ≫ₚ Array.max
noncomputable def plus : Code (Input × List W) (List W) :=
  ((((fst ≫ₚ piece 12) ⋏ₚ snd) ≫ₚ Array.translate) ⋏ₚ (fst ≫ₚ upperCap)) ≫ₚ Array.min
abbrev Update := Input × List W × List Bool
noncomputable def down : Code Update (List W) :=
  ((snd ≫ₚ snd) ⋏ₚ (snd ≫ₚ fst) ⋏ₚ ((fst ⋏ₚ (snd ≫ₚ fst)) ≫ₚ minus)) ≫ₚ Array.choose
noncomputable def up : Code Update (List W) :=
  ((snd ≫ₚ snd) ⋏ₚ ((fst ⋏ₚ (snd ≫ₚ fst)) ≫ₚ plus) ⋏ₚ (snd ≫ₚ fst)) ≫ₚ Array.choose
noncomputable def equalWord : Code (W × W) Bool := (Word.le ⋏ₚ (swap ≫ₚ Word.le)) ≫ₚ Code.and
noncomputable def different : Code (List W × List W) Bool :=
  zip Array.zero Array.zero (equalWord ≫ₚ Code.not) ≫ₚ any Code.id
noncomputable def changed (u : Bool) : Code Update Bool :=
  ((if u then up else down) ⋏ₚ (snd ≫ₚ fst)) ≫ₚ different
noncomputable def lowMark : Code (Input × List W) (List Bool) :=
  (snd ⋏ₚ (((fst ≫ₚ amount 1920) ⋏ₚ (fst ≫ₚ lower)) ≫ₚ Array.translate)) ≫ₚ Array.lt
noncomputable def highMark : Code (Input × List W) (List Bool) :=
  ((((fst ≫ₚ amount 2176) ⋏ₚ (fst ≫ₚ lower)) ≫ₚ Array.translate) ⋏ₚ snd) ≫ₚ Array.lt
noncomputable def selectBool : Code (Bool × Bool × Bool) Bool := Code.branch fst (snd ≫ₚ fst) (snd ≫ₚ snd)
noncomputable def chooseBool : Code (List Bool × List Bool × List Bool) (List Bool) :=
  (fst ⋏ₚ (snd ≫ₚ zip false false (fst ⋏ₚ snd))) ≫ₚ zip false (false,false) selectBool
abbrev Finish := Input × List W × List W × List Bool
noncomputable def highFinish : Code Finish (List Bool) :=
  (((fst ⋏ₚ (snd ≫ₚ snd ≫ₚ fst)) ≫ₚ highMark) ⋏ₚ
    ((snd ≫ₚ snd ≫ₚ snd) ≫ₚ map (const true)) ⋏ₚ (snd ≫ₚ snd ≫ₚ snd)) ≫ₚ chooseBool
noncomputable def finish : Code Finish (List Bool) :=
  (((fst ⋏ₚ (snd ≫ₚ fst)) ≫ₚ lowMark) ⋏ₚ
    ((snd ≫ₚ snd ≫ₚ snd) ≫ₚ map (const false)) ⋏ₚ highFinish) ≫ₚ chooseBool

noncomputable def widthLabels : Code (Input × List W) (List Bool) :=
  ((((fst ≫ₚ width) ⋏ₚ (fst ≫ₚ lower ≫ₚ map Word.double)) ≫ₚ Array.translate) ⋏ₚ
    (snd ≫ₚ map Word.double)) ≫ₚ Array.lt
noncomputable def basicCount : Code Input Count :=
  (const (List.replicate 4096 ()) ⋏ₚ (lower ≫ₚ count)) ≫ₚ Counter.mul
noncomputable def basic : Code (RawBasic.Arena × Input) (List Bool) :=
  (snd ⋏ₚ (((fst ⋏ₚ (snd ≫ₚ box)) ⋏ₚ (snd ≫ₚ basicCount)) ≫ₚ RawBasic.solve)) ≫ₚ widthLabels

structure Rep {n : ℕ} (A : Fin n → ℤ) (d : ℕ) (a b : Fin n → ℚ) (x : Input) : Prop where
  width : x.1.1.val=(2:ℤ)^d
  lower : VectorRep A x.1.2
  a : DetMass.Rep a x.2.1
  b : DetMass.Rep b x.2.2

variable {n : ℕ} {A : Fin n → ℤ} {d : ℕ} {a b : Fin n → ℚ} {x : Input}

@[simp] theorem equalWord_eq (p : W × W) : equalWord p=decide (p.1.val=p.2.val) := by
  change (if Word.le p then Word.le (p.2,p.1) else false) = _
  rw [Word.le_eval,Word.le_eval]
  by_cases h : p.1.val ≤ p.2.val
  · by_cases h' : p.2.val ≤ p.1.val
    · simp [le_antisymm h h']
    · have hn : p.1.val ≠ p.2.val := fun he => h' (by rw [he])
      simp [h,h',hn]
  · have hn : p.1.val ≠ p.2.val := fun he => h (by rw [he])
    simp [h,hn]

theorem different_eq {v w : Fin n → ℤ} {vs ws : List W}
    (hv : VectorRep v vs) (hw : VectorRep w ws) :
    different (vs,ws)=decide (v≠w) := by
  obtain ⟨as,rfl,ha⟩ := hv
  obtain ⟨bs,rfl,hb⟩ := hw
  simp only [different,Code.comp_eval,Code.zip_eval,Array.zip_ofFn,Code.any_ofFn,Code.id_eval,
    equalWord_eq,Code.not_eval,←decide_not,ha,hb,decide_eq_true_eq]
  exact decide_eq_decide.mpr Function.ne_iff.symm

theorem base_eq (h : Rep A d a b x) : base x=decide (∀ i, 1<a i*b i) :=
  DetMass.base_eq h.a h.b

theorem baseLabels_eq (h : Rep A d a b x) : baseLabels x=List.ofFn (Label.massLabels b) :=
  DetMass.labels_eq h.b

theorem small_eq (h : Rep A d a b x) : small x=decide (d<12) := by
  change Word.lt (x.1.1,_) = _
  rw [Word.lt_eval]
  have hc : (Word.constant 4096 x).val = (4096:ℤ) := Word.constant_val 4096 x
  rw [hc,h.width]
  apply decide_eq_decide.mpr
  have he : (4096:ℤ)=(2:ℤ)^12 := by norm_num
  rw [he]
  exact pow_lt_pow_iff_right₀ (by norm_num)

theorem piece_val (h : Rep A d a b x) (k : ℕ) (hk : k≤d) :
    (piece k x).val=(2:ℤ)^(d-k) := by
  change (Word.shiftRight (x.1.1,List.replicate k ())).val=_
  rw [Word.shiftRight_val,List.length_replicate,h.width]
  rw [show d=(d-k)+k by omega,pow_add,Int.mul_ediv_cancel _ (by positivity : (2:ℤ)^k≠0)]
  congr 1
  omega

theorem amount_val (h : Rep A d a b x) (hd : 12≤d) (c : ℤ) :
    (amount c x).val=c*(2:ℤ)^(d-12) := by
  simp only [amount,Code.comp_eval,RawBudget.times,Code.pair_eval,Code.id_eval,Word.mul_val,Word.constant_val]
  rw [piece_val h 12 hd,mul_comm]

theorem box_rep (h : Rep A d a b x) :
    RawBox.Rep (show SolveBox n (2^d) from
      { a:=A, b:=shift A ((2:ℤ)^d), width:=2^d,
        ordered:=fun i => le_add_of_nonneg_right (by positivity),
        positive:=by positivity, bounded:=le_rfl,
        width_bound:=fun i => by simp [shift] }) (box x) := by
  refine ⟨?_,h.lower,?_⟩
  · exact_mod_cast h.width
  · convert Array.translate_rep h.lower x.1.1 using 1 <;> try rfl
    funext i
    simp only [shift,h.width,add_comm]

theorem center_rep (h : Rep A d a b x) (hd : 12≤d) :
    VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) Label.gridCenter) (center x) := by
  rw [Label.gridPivot_center]
  convert Array.translate_rep h.lower (piece 1 x) using 1 <;> try rfl
  funext i
  rw [piece_val h 1 (by omega),(Label.dyadic_splits hd).2.2]
  ring

theorem child_rep (h : Rep A d a b x) (hd : 12≤d) (u : Bool)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    Rep (fun i => v i-16*(2:ℤ)^(d-12)) (d-7)
      (if u then fun i => 4/3*a i else a) (if u then b else fun i => 4/3*b i)
      (child u (x,vs)) := by
  have hlow : VectorRep (fun i => v i-16*(2:ℤ)^(d-12))
      (Array.translate (Word.neg (piece 8 x),vs)) := by
    convert Array.translate_rep hv (Word.neg (piece 8 x)) using 1
    funext i
    rw [Word.neg_val,piece_val h 8 (by omega)]
    have he : (2:ℤ)^(d-8)=16*(2:ℤ)^(d-12) := by
      rw [show d-8=(d-12)+4 by omega,pow_add]
      norm_num
      ring
    rw [he]
    ring
  cases u
  · exact ⟨piece_val h 7 (by omega),hlow,h.a,DetMass.scale_rep h.b (by norm_num) (by norm_num)⟩
  · exact ⟨piece_val h 7 (by omega),hlow,DetMass.scale_rep h.a (by norm_num) (by norm_num),h.b⟩

theorem provisional_rep (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    Rep (fun i => v i-1024*(2:ℤ)^(d-12)) (d-1) a b (provisional (x,vs)) := by
  refine ⟨piece_val h 1 (by omega),?_,h.a,h.b⟩
  convert Array.translate_rep hv (Word.neg (piece 2 x)) using 1 <;> try rfl
  funext i
  rw [Word.neg_val,piece_val h 2 (by omega)]
  have he : (2:ℤ)^(d-2)=1024*(2:ℤ)^(d-12) := by
    rw [show d-2=(d-12)+10 by omega,pow_add]
    norm_num
    ring
  rw [he]
  ring

theorem continuation_rep (h : Rep A d a b x) (ls : Fin n → Bool) :
    Rep A d (Label.reweight a ls) (Label.reweight b (fun i => !(ls i)))
      (continuation (x,List.ofFn ls)) := by
  refine ⟨h.width,h.lower,DetMass.reweight_rep h.a ls,?_⟩
  have hc : Array.complement (List.ofFn ls)=List.ofFn (fun i => !(ls i)) := by
    simp [Array.complement,Code.not,List.map_ofFn,Function.comp_def]
  change DetMass.Rep _ (DetMass.reweight (x.2.2,Array.complement (List.ofFn ls)))
  rw [hc]
  exact DetMass.reweight_rep h.b _

theorem minus_rep (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    VectorRep (fun i => max (v i-(2:ℤ)^(d-12)) (A i+1536*(2:ℤ)^(d-12))) (minus (x,vs)) := by
  convert Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _)
    (Array.translate_rep hv (Word.neg (piece 12 x)))
    (Array.translate_rep h.lower (amount 1536 x)) using 1 <;> try rfl
  funext i
  rw [Word.neg_val,piece_val h 12 hd,amount_val h hd]
  congr 1 <;> ring

theorem plus_rep (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    VectorRep (fun i => min (v i+(2:ℤ)^(d-12)) (A i+2560*(2:ℤ)^(d-12))) (plus (x,vs)) := by
  convert Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _)
    (Array.translate_rep hv (piece 12 x))
    (Array.translate_rep h.lower (amount 2560 x)) using 1 <;> try rfl
  funext i
  rw [piece_val h 12 hd,amount_val h hd]
  congr 1 <;> ring

theorem choose_rep_bool {v w : Fin n → ℤ} {vs ws : List W}
    (hv : VectorRep v vs) (hw : VectorRep w ws) (ls : Fin n → Bool) :
    VectorRep (fun i => if ls i then v i else w i) (Array.choose (List.ofFn ls,vs,ws)) := by
  have hm : MaskRep (Finset.univ.filter (fun i => ls i=true)) (List.ofFn ls) := by
    simp [MaskRep]
  simpa using Array.choose_rep hm hv hw

theorem down_rep (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) (ls : Fin n → Bool) :
    VectorRep (Label.downStep A ((2:ℤ)^(d-12)) v ls) (down (x,vs,List.ofFn ls)) := by
  convert choose_rep_bool hv (minus_rep h hd hv) ls using 1 <;> try rfl
  funext i
  simp only [Label.downStep,max_comm]

theorem up_rep (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) (ls : Fin n → Bool) :
    VectorRep (Label.upStep A ((2:ℤ)^(d-12)) v ls) (up (x,vs,List.ofFn ls)) := by
  convert choose_rep_bool (plus_rep h hd hv) hv ls using 1 <;> try rfl
  funext i
  simp only [Label.upStep,min_comm]

theorem lt_eq {v w : Fin n → ℤ} {vs ws : List W}
    (hv : VectorRep v vs) (hw : VectorRep w ws) :
    Array.lt (vs,ws)=List.ofFn (fun i => decide (v i<w i)) := by
  simpa [MaskRep] using Array.lt_rep hv hw

theorem lowMark_eq (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    lowMark (x,vs)=List.ofFn (fun i => decide (v i<A i+1920*(2:ℤ)^(d-12))) := by
  convert lt_eq hv (Array.translate_rep h.lower (amount 1920 x)) using 1 <;> try rfl
  congr 1
  funext i
  rw [amount_val h hd,add_comm]

theorem highMark_eq (h : Rep A d a b x) (hd : 12≤d)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    highMark (x,vs)=List.ofFn (fun i => decide (A i+2176*(2:ℤ)^(d-12)<v i)) := by
  convert lt_eq (Array.translate_rep h.lower (amount 2176 x)) hv using 1 <;> try rfl
  congr 1
  funext i
  rw [amount_val h hd,add_comm]

@[simp] theorem chooseBool_eq (m p q : Fin n → Bool) :
    chooseBool (List.ofFn m,List.ofFn p,List.ofFn q)=
      List.ofFn (fun i => if m i then p i else q i) := by
  change Zip.zip _ _ (List.ofFn _) (Zip.zip _ _ (List.ofFn _) (List.ofFn _)) = _
  rw [Array.zip_ofFn,Array.zip_ofFn]
  rfl

theorem finish_eq (h : Rep A d a b x) (hd : 12≤d)
    {vd vu : Fin n → ℤ} {ds us : List W} (hdv : VectorRep vd ds) (huv : VectorRep vu us)
    (ls : Fin n → Bool) : finish (x,ds,us,List.ofFn ls)=
      List.ofFn (Label.override A vd vu ((2:ℤ)^(d-12)) ls) := by
  change chooseBool (lowMark (x,ds),List.map (fun _ => false) (List.ofFn ls),
    chooseBool (highMark (x,us),List.map (fun _ => true) (List.ofFn ls),List.ofFn ls)) = _
  rw [lowMark_eq h hd hdv,highMark_eq h hd huv,List.map_ofFn,List.map_ofFn,chooseBool_eq,chooseBool_eq]
  congr 1
  funext i
  simp only [decide_eq_true_eq,Function.comp_apply,Label.override]

theorem widthLabels_eq (h : Rep A d a b x)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    widthLabels (x,vs)=List.ofFn (Label.widthLabels A v ((2:ℤ)^d)) := by
  convert lt_eq (Array.translate_rep (Array.map_rep Word.double (2*·) Word.double_val h.lower) x.1.1)
    (Array.map_rep Word.double (2*·) Word.double_val hv) using 1 <;> try rfl
  congr 1
  funext i
  simp only [Label.widthLabels,h.width,add_comm]

theorem basic_eq (G : Game) {A : Fin G.n → ℤ} {d : ℕ} {a b : Fin G.n → ℚ} {x : Input}
    (h : Rep A d a b x) (hd : d<12) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val=transformed G e) :
    basic (Graph.codeVertices G w,x)=List.ofFn (Label.widthLabels A
      (MeanPayoff.basic G A (shift A ((2:ℤ)^d)) (fun i => by
        dsimp [shift]; exact le_add_of_nonneg_right (by positivity))).1 ((2:ℤ)^d)) := by
  apply widthLabels_eq h
  apply RawBasic.solve_rep G (box_rep h) w hw
  have hn : x.1.2.length=G.n := by obtain ⟨ws,he,_⟩ := h.lower; simp [he]
  change G.n*2^d ≤ (Counter.mul (List.replicate 4096 (), Code.count x.1.2)).length
  rw [Counter.mul_length]
  simp only [List.length_replicate,Code.count,Code.map_eval,List.length_map,hn]
  have hd' : 2^d ≤ 4096 := by
    have hh := Nat.pow_le_pow_right (by omega : 1≤2) (show d≤12 by omega)
    norm_num at hh ⊢
    exact hh
  nlinarith

end DetRaw
end MeanPayoff.TreeDevice.Certified

end OAI
