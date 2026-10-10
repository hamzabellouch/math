import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.TimedExecution
import OAI.GroupTheory.PeriodicGroups.Rules.DataWords

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Rigid

omit [NeZero q] in
lemma adjacent_blocks {n : ℕ} (i j : Fin (n*width q)) (hij : i.val+1=j.val) :
    if position (coord i)=.stop then (block i).val+1=(block j).val
    else (block i).val=(block j).val := by
  have hdiv := Nat.div_add_mod i.val (width q)
  rw [Nat.mul_comm] at hdiv
  have hm := Nat.mod_lt i.val (width_pos (q:=q))
  split_ifs with hi
  · have hr := (position_stop_iff (coord i)).mp hi
    have hj : j.val=((block i).val+1)*width q := by
      dsimp [coord] at hr
      dsimp [block]
      rw [Nat.add_mul,Nat.one_mul]
      have hrw : i.val%width q+1=width q := by change i.val%width q+1=2*q+1;omega
      omega
    simp [block,hj,ne_of_gt width_pos]
  · have hr : i.val%width q≠2*q := by
      simpa only [position_stop_iff,coord] using hi
    have hb : i.val%width q+1<width q := by
      change i.val%width q+1<2*q+1
      change i.val%width q<2*q+1 at hm
      omega
    have hj : j.val=(block i).val*width q+(i.val%width q+1) := by
      dsimp [block]
      omega
    rw [show (block j).val=j.val/width q from rfl,hj,Nat.add_comm,
      Nat.add_mul_div_right _ _ width_pos,Nat.div_eq_of_lt hb]
    simp

namespace Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

def cell (i : Fin ((task.arity.val+1)*width q)) : Cell q :=
  { skeleton := ⟨position (coord i),.idle,⟨task.arity,task.zeroTask,block i⟩⟩
    checker := .idle
    data := fun s => match position (coord i) with
      | .core p => if hp : p.val<d then u s (block i) ⟨p.val,hp⟩ else 0
      | _ => 0
    certificate := match position (coord i) with
      | .core p => if (block i).val=0 then cert p else 0
      | _ => 0
    head := defaultHead }

@[simp] lemma pos (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).pos=position (coord i) := rfl
@[simp] lemma metadata (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).metadata=⟨task.arity,task.zeroTask,block i⟩ := rfl

lemma first_iff (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).skeleton.first ↔ i.val=0 := by
  change ((block i).val=0 ∧ ∃p,position (coord i)=.core p ∧ p.val=0) ↔ _
  simp only [position_core_iff]
  constructor
  · rintro ⟨hb,p,hp,hp0⟩
    have he := Nat.div_add_mod i.val (width q)
    change i.val/width q=0 at hb
    change i.val%width q=p.val at hp
    rw [hb,hp,hp0] at he
    simpa using he.symm
  · intro hi
    refine ⟨?_,0,?_,rfl⟩ <;> simp [block,coord,hi]

lemma last_iff (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).skeleton.last ↔ i.val+1=(task.arity.val+1)*width q := by
  change ((block i).val=task.arity.val ∧ position (coord i)=.stop) ↔ _
  simp only [position_stop_iff]
  have he := Nat.div_add_mod i.val (width q)
  have hm := (coord i).isLt
  change i.val%width q<2*q+1 at hm
  constructor
  · rintro ⟨hb,hp⟩
    change i.val/width q=task.arity.val at hb
    change i.val%width q=2*q at hp
    rw [hb,hp] at he
    dsimp [width] at he ⊢
    nlinarith
  · intro hi
    have hic : i.val=task.arity.val*width q+2*q := by
      dsimp [width] at hi ⊢
      nlinarith
    constructor
    · change i.val/width q=task.arity.val
      rw [hic,Nat.add_comm,Nat.add_mul_div_right _ _ width_pos,
        Nat.div_eq_of_lt (by dsimp [width];omega)]
      simp
    · change i.val%width q=2*q
      simp only [hic,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by dsimp [width];omega)

lemma adjacent (i j : Fin ((task.arity.val+1)*width q)) (hij : i.val+1=j.val) :
    Structural (cell task u cert i).skeleton (cell task u cert j).skeleton ∧
    Internal (cell task u cert i).skeleton (cell task u cert j).skeleton := by
  constructor
  · have hs : (List.ofFn (encoded (q:=q) (u false))).IsChain Pair := by
      rw [encoded_ofFn]
      exact encodeWord_pair_chain _
    have hh := List.isChain_ofFn.mp hs i.val (by rw [hij];exact j.isLt)
    have hh' : Pair (encoded (u false) i) (encoded (u false) j) := by
      convert hh using 1
      congr 1
      exact Fin.ext hij.symm
    exact hh'.1.1
  · refine ⟨rfl,rfl,?_,?_,?_⟩
    · exact adjacent_blocks i j hij
    · rw [first_iff]
      omega
    · rw [last_iff]
      have := j.isLt
      omega

lemma payload_format (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).PayloadFormat d := by
  unfold Cell.PayloadFormat Cell.isPalette Cell.isCore
  rw [pos]
  constructor
  · intro; rfl
  constructor
  · intro p hp hd
    funext s
    simp [cell,hp,Nat.not_lt_of_ge hd]
  · intro hi
    cases hp : position (coord i) with
    | core p => exact (hi ⟨p,hp⟩).elim
    | palette c => simp [cell,hp]; rfl
    | stop => simp [cell,hp]; rfl

def region : Region q d where
  size := (task.arity.val+1)*width q
  positive := Nat.mul_pos (by omega) width_pos
  task := task
  cell := cell task u cert
  task_eq := fun _ => rfl
  first_iff := first_iff task u cert
  last_iff := last_iff task u cert
  adjacent := adjacent task u cert
  payload_format := payload_format task u cert

end Template
end Rigid
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Region
variable (R : Region q d) (S : Schedule q)
lemma acquire (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Reach S d (R.idleWord s)
      (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,s⟩)) :=
  reach_symm ((Relation.ReflTransGen.single (R.unfinish S s hs)).trans
    (R.release S R.last s hs))

theorem literal_change (s : Bool) (hz : R.task.zeroTask=false)
    (hc : ∀j,(R.plan S).Holds j) : Reach S d (R.idleWord s) (R.idleWord (!s)) := by
  have hs : R.task.zeroTask=true → s=false := by simp [hz]
  have ht : R.task.zeroTask=true → (!s)=false := by simp [hz]
  exact (R.acquire S s hs).trans ((R.literal_success S s hs hc).trans
    ((Relation.ReflTransGen.single (R.edge_realize_step S (.flip s hz) hs)).trans
      ((reach_symm (R.literal_success S (!s) ht hc)).trans (reach_symm (R.acquire S (!s) ht)))))

theorem literal_zero (hz : R.task.zeroTask=true) (hc : ∀j,(R.plan S).Holds j) :
    ∃ p a t, Reach S d (R.idleWord false) (p++[a]++t) ∧ Zero S d [a] := by
  have hs : R.SideOK S ⟨.success,0,false⟩ := by intro; rfl
  let state : HeadTour.FullState (S.count R.task).val R.size := ⟨.success,0,false⟩
  have hv : Reach S d (R.idleWord false) (R.realize S state) :=
    (R.acquire S false (by intro;rfl)).trans (R.literal_success S false (by intro;rfl) hc)
  refine ⟨(R.realize S state).take (R.position S state).val,
    R.realizeCell S state (R.position S state),
    (R.realize S state).drop ((R.position S state).val+1),?_,?_⟩
  · convert hv using 1
    exact (ofFn_split_one (R.realizeCell S state) (R.position S state)).symm
  · exact Or.inl ⟨_,rfl,Or.inr (Or.inl (R.realize_semanticZero S state (Or.inr ⟨rfl,hz⟩)))⟩
end Region

namespace Rigid.Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

lemma idle_cell (s : Bool) (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).idle s=encoded (u s) i := by
  unfold encoded
  cases hp : position (coord i) <;>
    simp [Cell.idle,cell,canonicalCell,Cell.pos,hp]

lemma idle_word (s : Bool) :
    (region task u cert).idleWord s=encodeWord (List.ofFn (u s)) := by
  rw [←encoded_ofFn]
  apply congrArg List.ofFn
  funext i
  exact idle_cell task u cert s i

lemma locate (b : Fin (task.arity.val+1)) (p : Fin q) :
    (region task u cert).locate b p=core b p := by
  symm
  apply (region task u cert).locate_unique b p (core b p)
  · change (block (core b p)).val=b.val
    rw [core,block_cell]
  · change position (coord (core b p))=.core p
    rw [core,coord_cell,position_core_iff]

lemma slot (s : Bool) (b : Fin (task.arity.val+1)) (p : Fin q) :
    (region task u cert).slot s b p = if hp : p.val<d then u s b ⟨p.val,hp⟩ else 0 := by
  unfold Region.slot
  rw [locate]
  change (cell task u cert (core b p)).data s = _
  have hp : position (coord (core b p))=.core p := by rw [core,coord_cell,position_core_iff]
  simp only [cell,hp]
  rw [core,block_cell]

lemma certificate (p : Fin q) : (region task u cert).certificate p=cert p := by
  change ((region task u cert).cell ((region task u cert).locate (0 : Fin (task.arity.val+1)) p)).certificate=cert p
  rw [locate task u cert (0 : Fin (task.arity.val+1)) p]
  change (cell task u cert (core 0 p)).certificate = _
  have hp : position (coord (core (n:=task.arity.val+1) 0 p))=.core p := by
    rw [core,coord_cell,position_core_iff]
  simp only [cell,hp]
  rw [core,block_cell]
  simp

theorem replacement (S : Schedule q) (s : Bool) (hz : task.zeroTask=false)
    (hc : ∀j,((region task u cert).plan S).Holds j) :
    Reach S d (encodeWord (List.ofFn (u s))) (encodeWord (List.ofFn (u (!s)))) := by
  simpa only [idle_word] using (region task u cert).literal_change S s hz hc

theorem zero (S : Schedule q) (hz : task.zeroTask=true)
    (hc : ∀j,((region task u cert).plan S).Holds j) :
    ∃ p a t, Reach S d (encodeWord (List.ofFn (u false))) (p++[a]++t) ∧ Zero S d [a] := by
  simpa only [idle_word] using (region task u cert).literal_zero S hz hc

end Rigid.Template
end SourceBurnside.FiniteTable

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable FiniteTable.Codec
variable {q d h D : ℕ} [NeZero q]
def regionData (R : Region q d) : DataAddress q → Bool :=
  fun a => physicalBits R (.data a.1 a.2.1 a.2.2)
def regionCert (R : Region q d) : Fin q → Bool :=
  fun p => physicalBits R (.certificate p)
lemma physical_assemble (R : Region q d) :
    physicalBits R=Layout.assemble (regionData R) (regionCert R) := by
  funext a
  cases a <;> rfl
lemma candidate_region (R : Region q (10000*h)) (hdq : 10000*h≤q)
    (hl10 : R.task.arity.val+1≤10) (s : Bool) :
    List.ofFn (candidateWord (l:=R.task.arity.val+1) (regionData R) hdq hl10 s)=
      (R.dataWord hdq s).map (fun w j => Addressable.unbit (w j)) := by
  rw [Region.dataWord,List.map_ofFn]
  congr 1
  funext b p
  simp only [candidateWord,regionData,physicalBits,Region.read]
  simp only [show b.val<R.task.arity.val+1 from b.isLt,dite_eq_left]
  rfl

theorem fixed_region_entry (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 4≤h0), ∀(h : ℕ) (hh : h0≤h),
      let a := WrappedInput.specialize t t
      ∃(fit : RawFit.Fits β g D h a.length) (fitnext : RawFit.Fits β g D (D*h) a.length),
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
      let hdnext : 0<10000*(D*(D*h)) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      ∀ R : Region (2^h) (10000*(D*h)),
      (∀j,(R.plan (sourceSchedule a fit hd)).Holds j) →
      entry (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) R.task.zeroTask
        ((R.dataWord fit.2.2.2.1 false).map (fun w j => Addressable.unbit (w j)))
        (if R.task.zeroTask then [] else
          (R.dataWord fit.2.2.2.1 true).map (fun w j => Addressable.unbit (w j)))=true := by
  obtain ⟨t,h0,h0pos,H⟩ := fixed_table_certificate D hD
  refine ⟨t,h0,h0pos,?_⟩
  intro h hh
  obtain ⟨fit,fitnext,hcert⟩ := H h hh
  refine ⟨fit,fitnext,?_⟩
  dsimp only
  intro R hc
  have hc' := (physical_clauses_iff _ _ _ _ _ _ R).mp hc
  rw [physical_assemble R] at hc'
  have he := (hcert R.task (regionData R)).mp ⟨regionCert R,hc'⟩
  rw [candidate_region R fit.2.2.2.1 _ false,
    candidate_region R fit.2.2.2.1 _ true] at he
  exact he
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ}
def Step (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v w : List (Raw h)) : Prop :=
  ∃ p s a b, v=p++a++s ∧ w=p++b++s ∧ replacement hh S d a b
abbrev Reach (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) := Relation.ReflTransGen (Step hh S d)
def Survives (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (w : List (Raw h)) : Prop :=
  ∀p z s, Reach hh S d w (p++z++s) → ¬zero hh S d z
lemma replacement_symm (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (a b : List (Raw h)) :
    replacement hh S d a b ↔ replacement hh S d b a := by
  unfold replacement
  cases ha : decodeWord hh a <;> cases hb : decodeWord hh b <;>
    simp only [FiniteTable.replacement_symm]
lemma step_symm {hh : 0<h} {S : Schedule (2^h)} {v w : List (Raw h)}
    (he : Step hh S d v w) : Step hh S d w v := by
  obtain ⟨p,s,a,b,rfl,rfl,he⟩ := he
  exact ⟨p,s,b,a,rfl,rfl,(replacement_symm hh S d a b).mp he⟩
lemma step_encode (hh : 4≤h) {S : Schedule (2^h)} {v w : List (Cell (2^h))}
    (he : FiniteTable.Step S d v w) : Step (by omega) S d (v.map encode) (w.map encode) := by
  obtain ⟨p,s,a,b,rfl,rfl,he⟩ := he
  exact ⟨p.map encode,s.map encode,a.map encode,b.map encode,by simp,by simp,
    (replacement_encode hh S d a b).mpr he⟩
lemma reach_encode (hh : 4≤h) {S : Schedule (2^h)} {v w : List (Cell (2^h))}
    (he : FiniteTable.Reach S d v w) : Reach (by omega) S d (v.map encode) (w.map encode) := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (step_encode hh e)
lemma split_encoding {α γ : Type*} {f : α→γ} {v : List α} {p a s : List γ}
    (hv : v.map f=p++a++s) : ∃p' a' s', v=p'++a'++s' ∧ p'.map f=p ∧ a'.map f=a ∧ s'.map f=s := by
  obtain ⟨u,s',rfl,hu,hs⟩ := List.map_eq_append_iff.mp hv
  obtain ⟨p',a',rfl,hp,ha⟩ := List.map_eq_append_iff.mp hu
  exact ⟨p',a',s',rfl,hp,ha,hs⟩
lemma step_from_encoding (hh : 4≤h) {S : Schedule (2^h)} {v : List (Cell (2^h))}
    {w : List (Raw h)} (he : Step (by omega) S d (v.map encode) w) :
    ∃ w', w=w'.map encode ∧ FiniteTable.Step S d v w' := by
  obtain ⟨p,s,a,b,hv,rfl,he⟩ := he
  obtain ⟨p',a',s',rfl,hp,ha,hs⟩ := split_encoding hv
  obtain ⟨_,b',_,hb,_⟩ := replacement_has_encodings hh S d a b he
  refine ⟨p'++b'++s',by simp [hp,hb,hs],p',s',a',b',rfl,rfl,?_⟩
  apply (replacement_encode hh S d a' b').mp
  simpa only [ha,←hb] using he
lemma reach_from_encoding (hh : 4≤h) {S : Schedule (2^h)} {v : List (Cell (2^h))}
    {w : List (Raw h)} (he : Reach (by omega) S d (v.map encode) w) :
    ∃ w', w=w'.map encode ∧ FiniteTable.Reach S d v w' := by
  induction he with
  | refl => exact ⟨v,rfl,.refl⟩
  | tail h e ih =>
    obtain ⟨u,rfl,hu⟩ := ih
    obtain ⟨w',rfl,he⟩ := step_from_encoding hh e
    exact ⟨w',rfl,hu.tail he⟩
lemma survives_encode_iff (hh : 4≤h) {S : Schedule (2^h)} (w : List (Cell (2^h))) :
    Survives (by omega) S d (w.map encode) ↔ FiniteTable.Survives S d w := by
  constructor
  · intro hw p z s hr hz
    exact hw (p.map encode) (z.map encode) (s.map encode)
      (by simpa using reach_encode hh hr) ((zero_encode hh S d z).mpr hz)
  · intro hw p z s hr hz
    obtain ⟨v,hv,hr⟩ := reach_from_encoding hh hr
    obtain ⟨p',z',s',rfl,hp,hz',hs⟩ := split_encoding hv.symm
    apply hw p' z' s' hr
    apply (zero_encode hh S d z').mp
    simpa only [hz'] using hz
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q H h D : ℕ} [NeZero q]
def bits {n : ℕ} (w : Fin n→ZMod 2) : Fin n→Bool := fun j => Addressable.unbit (w j)
def scalars {n : ℕ} (w : Fin n→Bool) : Fin n→ZMod 2 := fun j => Addressable.bit (w j)
@[simp] lemma bits_scalars {n : ℕ} (w : Fin n→Bool) : bits (scalars w)=w := by
  funext j
  exact Addressable.unbit_bit _
@[simp] lemma scalars_bits {n : ℕ} (w : Fin n→ZMod 2) : scalars (bits w)=w := by
  funext j
  exact Addressable.bit_unbit _
lemma checkedSwap_raw {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    {v w : List (Fin (10000*H)→ZMod 2)} (he : CheckedSwap S hd v w) :
    Codec.Step hh T d' (v.map bits) (w.map bits) := by
  cases he with
  | mk R s hz hc p t =>
    have he := law R hc
    simp only [hz,Bool.false_eq_true,ite_false] at he
    have he := (Codec.entry_replacement hh T d' _ _).mp he
    cases s
    · exact ⟨p.map bits,t.map bits,(R.dataWord hd false).map bits,
        (R.dataWord hd true).map bits,by simp,by simp,he⟩
    · exact ⟨p.map bits,t.map bits,(R.dataWord hd true).map bits,
        (R.dataWord hd false).map bits,by simp,by simp,(Codec.replacement_symm hh T d' _ _).mp he⟩
lemma checkedReach_raw {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    {v w : List (Fin (10000*H)→ZMod 2)} (he : CheckedReach S hd v w) :
    Codec.Reach hh T d' (v.map bits) (w.map bits) := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (checkedSwap_raw hh hd d' law e)
lemma checkedZero_raw {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    {w : List (Fin (10000*H)→ZMod 2)} (he : CheckedZero S hd w) :
    ∃p z t, w.map bits=p++z++t ∧ Codec.zero hh T d' z := by
  obtain ⟨R,p,t,hz,hc,rfl⟩ := he
  have he := law R hc
  simp only [hz,ite_true] at he
  exact ⟨p.map bits,(R.dataWord hd false).map bits,t.map bits,by simp,
    ((Codec.entry_zero hh T d' _ _).mp he).2⟩
lemma clean_nonzero {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    (w : List (Codec.Raw H)) (hw : Codec.Survives hh T d' w) :
    FiniteTable.Survives S (10000*H) (encodeWord (w.map scalars)) := by
  apply Rigid.clean_survives hd
  intro v hv hz
  have hr := checkedReach_raw hh hd d' law hv
  have hh' : (w.map scalars).map bits=w := by simp [List.map_map,Function.comp_def]
  rw [hh'] at hr
  obtain ⟨p,z,t,hv,hz⟩ := checkedZero_raw hh hd d' law hz
  exact hw p z t (by rwa [hv] at hr) hz

def embedding (h D : ℕ) (w : List (Codec.Raw (D*h))) : List (Codec.Raw h) :=
  (encodeWord (q:=2^h) (w.map scalars)).map Codec.encode

theorem fixed_clean_nonzero (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 4≤h0), ∀(h : ℕ) (hh : h0≤h),
      let a := WrappedInput.specialize t t
      ∃(fit : RawFit.Fits β g D h a.length) (fitnext : RawFit.Fits β g D (D*h) a.length),
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
      let hdnext : 0<10000*(D*(D*h)) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      ∀w : List (Codec.Raw (D*h)),
      Codec.Survives (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) w →
      Codec.Survives (by omega : 0<h) (sourceSchedule a fit hd) (10000*(D*h)) (embedding h D w) := by
  obtain ⟨t,h0,h0pos,H⟩ := fixed_region_entry D hD
  refine ⟨t,h0,h0pos,?_⟩
  intro h hh
  obtain ⟨fit,fitnext,hlaw⟩ := H h hh
  refine ⟨fit,fitnext,?_⟩
  dsimp only
  intro w hw
  apply (Codec.survives_encode_iff (by omega) _).mpr
  apply clean_nonzero (by nlinarith) fit.2.2.2.1 (10000*(D*(D*h))) _ w hw
  exact hlaw
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q d h D : ℕ} [NeZero q]
def templateData (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → Bool) : DataAddress q → Bool :=
  fun a => if hb : a.2.1.val<task.arity.val+1 then
    if hp : a.2.2.val<d then u a.1 ⟨a.2.1.val,hb⟩ ⟨a.2.2.val,hp⟩ else false
    else false
omit [NeZero q] in
lemma candidate_template (task : Task) (u : Bool → Fin (task.arity.val+1) → Codec.Raw h)
    (hd : 10000*h≤q) (hl : task.arity.val+1≤10) (s : Bool) :
    List.ofFn (candidateWord (l:=task.arity.val+1) (templateData (q:=q) task u) hd hl s)=List.ofFn (u s) := by
  congr 1
  funext b p
  simp [candidateWord,templateData,b.isLt,p.isLt]
lemma physical_template (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → Bool) (cert : Fin q → Bool) :
    physicalBits (Rigid.Template.region task (fun s b => scalars (u s b)) (fun p => Addressable.bit (cert p)))=
      Layout.assemble (templateData task u) cert := by
  funext a
  cases a with
  | certificate p =>
    simp only [physicalBits,Region.read,Rigid.Template.certificate,Layout.assemble]
    exact Addressable.unbit_bit _
  | data s b p =>
    simp only [physicalBits,Region.read,Rigid.Template.region]
    change Addressable.unbit (if hb : b.val<task.arity.val+1 then
      (Rigid.Template.region task (fun s b => scalars (u s b)) (fun p => Addressable.bit (cert p))).slot s ⟨b.val,hb⟩ p else 0)=_
    by_cases hb : b.val<task.arity.val+1
    · erw [dite_eq_left hb,Rigid.Template.slot]
      by_cases hp : p.val<d
      · simp [hp,Layout.assemble,templateData,hb,scalars]
        rfl
      · simp [hp,Layout.assemble,templateData,hb,Addressable.unbit]
    · simp [hb,Layout.assemble,templateData,Addressable.unbit]
lemma template_certificate (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (task : Task)
    (u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h)) (cert : Fin (2^h) → Bool)
    (hc : ∀i, ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
      (sourceInitial a fit hd task) blankBits acceptBits i).Holds (Layout.assemble (templateData task u) cert)) :
    ∀i, ((Rigid.Template.region task (fun s b => scalars (u s b)) (fun p => Addressable.bit (cert p))).plan
      (sourceSchedule a fit hd)).Holds i := by
  apply (physical_clauses_iff _ _ _ _ _ _ _).mpr
  rw [physical_template]
  exact hc

theorem fixed_forward (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 4≤h0), ∀(h : ℕ) (hh : h0≤h),
      let a := WrappedInput.specialize t t
      ∃(fit : RawFit.Fits β g D h a.length) (fitnext : RawFit.Fits β g D (D*h) a.length),
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
      let hdnext : 0<10000*(D*(D*h)) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      ∀(task : Task) (u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h)),
      Codec.entry (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) task.zeroTask
        (List.ofFn (u false)) (if task.zeroTask then [] else List.ofFn (u true))=true  →
      (task.zeroTask=false  →  Codec.Reach (by omega : 0<h) (sourceSchedule a fit hd) (10000*(D*h))
        (embedding h D (List.ofFn (u false))) (embedding h D (List.ofFn (u true)))) ∧
      (task.zeroTask=true  →  ∃p z r, Codec.Reach (by omega : 0<h) (sourceSchedule a fit hd) (10000*(D*h))
        (embedding h D (List.ofFn (u false))) (p++z++r) ∧
        Codec.zero (by omega : 0<h) (sourceSchedule a fit hd) (10000*(D*h)) z) := by
  obtain ⟨t,h0,h0pos,H⟩ := fixed_table_certificate D hD
  refine ⟨t,h0,h0pos,?_⟩
  intro h hh
  obtain ⟨fit,fitnext,hcert⟩ := H h hh
  refine ⟨fit,fitnext,?_⟩
  dsimp only
  intro task u he
  have heq := hcert task (templateData (q:=2^h) task u)
  rw [candidate_template task u fit.2.2.2.1 _ false,
    candidate_template task u fit.2.2.2.1 _ true] at heq
  obtain ⟨cert,hc⟩ := heq.mpr he
  have hr := template_certificate _ fit (by nlinarith) task u cert hc
  constructor
  · intro hz
    have hs := Rigid.Template.replacement task (fun s b => scalars (u s b))
      (fun p => Addressable.bit (cert p)) _ false hz hr
    have he := Codec.reach_encode (by omega : 4≤h) hs
    simpa only [embedding,List.map_ofFn,Function.comp_def,Bool.not_false] using he
  · intro hz
    obtain ⟨p,a,r,hs,hz⟩ := Rigid.Template.zero task (fun s b => scalars (u s b))
      (fun p => Addressable.bit (cert p)) _ hz hr
    refine ⟨p.map Codec.encode,[Codec.encode a],r.map Codec.encode,?_,?_⟩
    · simpa only [embedding,List.map_ofFn,Function.comp_def,List.map_append,List.map_cons,List.map_nil] using
        Codec.reach_encode (by omega : 4≤h) hs
    · exact (Codec.zero_encode (by omega : 4≤h) _ _ [a]).mpr hz
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable

structure MachineHierarchy (D : ℕ) (hD : 2≤D) where
  program : List Bool
  threshold : ℕ
  threshold_four : 4≤threshold
  fits : ∀ h, threshold≤h → RawFit.Fits β g D h (WrappedInput.specialize program program).length
  certifies : ∀ (h : ℕ) (hh : threshold≤h) (task : Task) (data : DataAddress (2^h) → Bool),
    let a := WrappedInput.specialize program program
    let fit := fits h hh
    let fitnext := fits (D*h) (by nlinarith)
    let hd : 0<10000*(D*h) := by nlinarith
    let hdnext : 0<10000*(D*(D*h)) := by nlinarith
    (∃cert : Fin (2^h) → Bool, ∀i,
      ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
        (sourceInitial a fit hd task) blankBits acceptBits i).Holds (Layout.assemble data cert)) ↔
    Codec.entry (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) task.zeroTask
      (List.ofFn (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) false))
      (if task.zeroTask then [] else List.ofFn
        (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) true))=true

def hierarchy (D : ℕ) (hD : 2≤D) : MachineHierarchy D hD := Classical.choice (by
  obtain ⟨t,h0,h0pos,H⟩ := fixed_table_certificate D hD
  refine ⟨{ program := t
            threshold := h0
            threshold_four := h0pos
            fits := fun h hh => Classical.choose (H h hh)
            certifies := ?_ }⟩
  intro h hh task data
  obtain ⟨fit,fitnext,hcert⟩ := H h hh
  exact hcert task data)
namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
def code := WrappedInput.specialize A.program A.program
lemma next_large {h : ℕ} (hh : A.threshold≤h) : A.threshold≤D*h := by nlinarith [A.threshold_four]
lemma data_pos {h : ℕ} (hh : A.threshold≤h) : 0<10000*(D*h) := by nlinarith [A.threshold_four]
lemma height_pos {h : ℕ} (hh : A.threshold≤h) : 0<h := by have := A.threshold_four;omega
def schedule (h : ℕ) (hh : A.threshold≤h) : Schedule (2^h) :=
  sourceSchedule A.code (A.fits h hh) (A.data_pos hh)
lemma region_entry {h : ℕ} (hh : A.threshold≤h) (R : Region (2^h) (10000*(D*h)))
    (hc : ∀j,(R.plan (A.schedule h hh)).Holds j) :
    Codec.entry (A.height_pos (A.next_large hh)) (A.schedule (D*h) (A.next_large hh)) (10000*(D*(D*h)))
      R.task.zeroTask ((R.dataWord (A.fits h hh).2.2.2.1 false).map bits)
      (if R.task.zeroTask then [] else (R.dataWord (A.fits h hh).2.2.2.1 true).map bits)=true := by
  have hc' := (physical_clauses_iff _ _ _ _ _ _ R).mp hc
  rw [physical_assemble R] at hc'
  have he := (A.certifies h hh R.task (regionData R)).mp ⟨regionCert R,hc'⟩
  rw [candidate_region R (A.fits h hh).2.2.2.1 _ false,
    candidate_region R (A.fits h hh).2.2.2.1 _ true] at he
  exact he

theorem faithful {h : ℕ} (hh : A.threshold≤h) (w : List (Codec.Raw (D*h)))
    (hw : Codec.Survives (A.height_pos (A.next_large hh)) (A.schedule (D*h) (A.next_large hh))
      (10000*(D*(D*h))) w) :
    Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) (embedding h D w) := by
  apply (Codec.survives_encode_iff (by have := A.threshold_four;omega) _).mpr
  exact clean_nonzero (A.height_pos (A.next_large hh)) (A.fits h hh).2.2.2.1 _
    (A.region_entry hh) w hw

theorem simulate {h : ℕ} (hh : A.threshold≤h) (task : Task)
    (u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h))
    (he : Codec.entry (A.height_pos (A.next_large hh)) (A.schedule (D*h) (A.next_large hh))
      (10000*(D*(D*h))) task.zeroTask (List.ofFn (u false))
      (if task.zeroTask then [] else List.ofFn (u true))=true) :
    (task.zeroTask=false → Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h))
      (embedding h D (List.ofFn (u false))) (embedding h D (List.ofFn (u true)))) ∧
    (task.zeroTask=true → ∃p z r, Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h))
      (embedding h D (List.ofFn (u false))) (p++z++r) ∧
      Codec.zero (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) z) := by
  have heq := A.certifies h hh task (templateData (q:=2^h) task u)
  dsimp only at heq
  rw [candidate_template task u (A.fits h hh).2.2.2.1 _ false,
    candidate_template task u (A.fits h hh).2.2.2.1 _ true] at heq
  obtain ⟨cert,hc⟩ := heq.mpr he
  have hr := template_certificate A.code (A.fits h hh) (A.data_pos hh) task u cert hc
  have h4 : 4≤h := A.threshold_four.trans hh
  constructor
  · intro hz
    have hs := Rigid.Template.replacement task (fun s b => scalars (u s b))
      (fun p => Addressable.bit (cert p)) _ false hz hr
    simpa only [embedding,schedule,List.map_ofFn,Function.comp_def,Bool.not_false] using Codec.reach_encode h4 hs
  · intro hz
    obtain ⟨p,a,r,hs,hz⟩ := Rigid.Template.zero task (fun s b => scalars (u s b))
      (fun p => Addressable.bit (cert p)) _ hz hr
    refine ⟨p.map Codec.encode,[Codec.encode a],r.map Codec.encode,?_,?_⟩
    · simpa only [embedding,schedule,List.map_ofFn,Function.comp_def,List.map_append,List.map_cons,List.map_nil] using
        Codec.reach_encode h4 hs
    · exact (Codec.zero_encode h4 _ _ [a]).mpr hz
end MachineHierarchy
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
@[simp] lemma embedding_length (h D : ℕ) (w : List (Codec.Raw (D*h))) :
    (embedding h D w).length=(2*2^h+1)*w.length := by
  simp [embedding]
lemma idleCore_survives {q : ℕ} [NeZero q] (S : Schedule q) (d : ℕ) (p : Fin q) (hp : p.val≠0) :
    FiniteTable.Survives S d [idleCore p] := by
  intro l z r hr hz
  have he := (reach_interior_idle_iff (by rfl : (idleCore p).marker=.idle)
    ⟨p,rfl,hp⟩ _).mp hr
  exact idleCore_not_contextual_zero S d p l z r hz he.symm
namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
theorem nonzero_letter {h : ℕ} (hh : A.threshold≤h) :
    ∃c : Codec.Raw h, Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) [c] := by
  have h4 : 4≤h := A.threshold_four.trans hh
  have hq : 1<2^h := Nat.one_lt_two_pow_iff.mpr (by omega)
  let p : Fin (2^h) := ⟨1,hq⟩
  refine ⟨Codec.encode (idleCore p),?_⟩
  exact (Codec.survives_encode_iff h4 [idleCore p]).mpr (idleCore_survives _ _ p (by change (1:ℕ)≠0;omega))

theorem unbounded_survivors (n : ℕ) : ∀(h : ℕ) (hh : A.threshold≤h),
    ∃w : List (Codec.Raw h), n<w.length ∧
      Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) w := by
  induction n with
  | zero =>
    intro h hh
    obtain ⟨c,hc⟩ := A.nonzero_letter hh
    exact ⟨[c],by simp,hc⟩
  | succ n ih =>
    intro h hh
    obtain ⟨w,hw,hs⟩ := ih (D*h) (A.next_large hh)
    refine ⟨embedding h D w,?_,A.faithful hh w hs⟩
    rw [embedding_length]
    have hq : 0<2^h := by positivity
    nlinarith
end MachineHierarchy
end
end SourceBurnside.SourceMachine

end

end OAI
