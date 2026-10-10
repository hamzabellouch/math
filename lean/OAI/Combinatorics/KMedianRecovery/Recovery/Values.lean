import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Basic

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
open WordOperations BinaryArithmetic WordList BinaryOpeningActivity
lemma distanceWord_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (f : Fin m) :
    distanceWord (pairBits (context distance v z j,f.val.bits))=BinaryRational.encode (distance f j) := by
  unfold distanceWord
  simp only [table,client,context,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [MetricTable.get_pack]
noncomputable def values : List Bool → List Bool := mapWith distanceWord
noncomputable def values_computes : PolyComputes values := mapWith_computes distanceWord_computes
lemma values_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (fs : List (Fin m)) :
    values (pairBits (context distance v z j,indices fs))=RationalArray.encode (fs.map (fun f=>distance f j)) := by
  simp only [values,indices,mapWith_encode,List.map_map,Function.comp_def,distanceWord_context,RationalArray.encode]
noncomputable def run : List Bool → List Bool := RationalMin.run ∘ values
noncomputable def run_computes : PolyComputes run := values_computes.comp RationalMin.run_computes
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (fs : List (Fin m)) :
    run (pairBits (context distance v z j,indices fs))=
      BinaryRational.encode (RationalMin.minimum (fs.map (fun f=>distance f j))) := by
  rw [run,Function.comp_apply,values_pack,RationalMin.run_encode]

lemma minimum_nearest {m d : ℕ} (distance : Fin m → Fin d → ℚ) (W : Finset (Fin m))
    (j : Fin d) (fs : List (Fin m)) (hfs : ∀ f,f∈fs ↔ f∈W) :
    RationalMin.minimum (fs.map (fun f=>distance f j))=RationalOpenability.nearest distance W j := by
  unfold RationalOpenability.nearest
  split_ifs with hW
  · obtain ⟨f,hf,he⟩ := Finset.exists_mem_eq_inf' hW (fun f=>distance f j)
    have hm : distance f j∈fs.map (fun f=>distance f j) := List.mem_map.mpr ⟨f,(hfs f).mpr hf,rfl⟩
    apply le_antisymm
    · rw [he]
      exact RationalMin.minimum_le_mem _ _ hm
    · apply RationalMin.minimum_lower
      · intro hn; simp only [hn,List.not_mem_nil] at hm
      · intro q hq
        obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hq
        exact Finset.inf'_le _ ((hfs g).mp hg)
  · have hw : W=∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have hf : fs=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro f hf
      have hh := (hfs f).mp hf
      simp [hw] at hh
    rw [hf,List.map_nil]
    rfl

lemma run_source {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (W : Finset (Fin m)) :
    run (pairBits (context distance v z j,
      indices ((EffectiveOpenability.subtypeList W).map Subtype.val)))=
      BinaryRational.encode (RationalOpenability.nearest distance W j) := by
  rw [run_pack]
  congr 1
  apply minimum_nearest
  intro f
  constructor
  · intro hf
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hf
    exact g.property
  · intro hf
    exact List.mem_map.mpr ⟨⟨f,hf⟩,EffectiveOpenability.mem_subtypeList W ⟨f,hf⟩,rfl⟩
end MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
noncomputable def max {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (max (f x) (g x))) := by
  have hh := (le hf hg).cond hg hf
  simpa only [decide_eq_true_eq,max_def,apply_ite] using hh
end RatOps
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : List Bool :=
  WordList.encode [Rectangular.encode distance,
    BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList W).map Subtype.val),
    BinaryRational.encode v,BinaryRational.encode z,BinaryRational.encode lam,
    BinaryRational.encode eta,i.val.bits,List.replicate d true,
    BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList F).map Subtype.val)]
def field (k : ℕ) (x : List Bool) : List Bool := Lookup.run (pairBits (k.bits,x))
noncomputable def field_computes (k : ℕ) : PolyComputes (field k) :=
  ((const_computes k.bits).pair id_computes).comp Lookup.run_computes
lemma field_encode (k : ℕ) (ws : List (List Bool)) : field k (encode ws)=ws[k]?.getD [] :=
  Lookup.run_encode k ws

def itemField (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
noncomputable def itemField_computes (k : ℕ) : PolyComputes (itemField k) :=
  extractPrefix_computes.comp (field_computes k)
def paramV (x : List Bool) : ℚ := BinaryRational.decode (itemField 2 x)
def paramZ (x : List Bool) : ℚ := BinaryRational.decode (itemField 3 x)
noncomputable def paramV_computes : PolyComputes (fun x=>BinaryRational.encode (paramV x)) :=
  RatOps.ofWords (itemField_computes 2)
noncomputable def paramZ_computes : PolyComputes (fun x=>BinaryRational.encode (paramZ x)) :=
  RatOps.ofWords (itemField_computes 3)
def scale (x : List Bool) : ℚ := 1-3*paramV x
noncomputable def scale_computes : PolyComputes (fun x=>BinaryRational.encode (scale x)) :=
  RatOps.sub (RatOps.const 1) (RatOps.mul (RatOps.const 3) paramV_computes)
noncomputable def activityInput (x : List Bool) : List Bool :=
  pairBits (pairBits (pairBits (itemField 0 x,discardPrefix x),
    pairBits (itemField 2 x,itemField 3 x)),itemField 1 x)
noncomputable def activityInput_computes : PolyComputes activityInput :=
  (((itemField_computes 0).pair discardPrefix_computes).pair
    ((itemField_computes 2).pair (itemField_computes 3))).pair (itemField_computes 1)
lemma activityInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    activityInput (pairBits (pack distance F W v z lam eta i,j.val.bits))=
      pairBits (BinaryOpeningActivity.context distance v z j,
        BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList W).map Subtype.val)) := by
  simp only [activityInput,itemField,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryOpeningActivity.context]
noncomputable def active (x : List Bool) : Bool :=
  (BinaryOpeningActivity.run (activityInput x)).head?.getD false
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  (activityInput_computes.comp BinaryOpeningActivity.run_computes).comp
    MetricKMedianRecovery.BitMachine.head_computes
lemma active_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    active (pairBits (pack distance F W v z lam eta i,j.val.bits))=
      decide (EffectiveOpenability.active distance v z W j) := by
  rw [active,activityInput_pack,BinaryOpeningActivity.run_source]
  rfl
noncomputable def nearest (x : List Bool) : ℚ :=
  BinaryRational.decode (BinaryOpeningNearest.run (activityInput x))
noncomputable def nearest_computes : PolyComputes (fun x=>BinaryRational.encode (nearest x)) := by
  unfold nearest
  simpa only [Function.comp_def] using
    (RatOps.ofWords (f:=BinaryOpeningNearest.run ∘ activityInput)
      (PolyComputes.comp (f:=activityInput) (g:=BinaryOpeningNearest.run)
        activityInput_computes BinaryOpeningNearest.run_computes))
lemma nearest_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    nearest (pairBits (pack distance F W v z lam eta i,j.val.bits))=
      RationalOpenability.nearest distance W j := by
  rw [nearest,activityInput_pack,BinaryOpeningNearest.run_source,BinaryRational.decode_encode]
noncomputable def distanceWords (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (itemField 0 x,itemField 6 x),discardPrefix x))
noncomputable def distanceWords_computes : PolyComputes distanceWords := by
  unfold distanceWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (pairBits (itemField 0 input,itemField 6 input),discardPrefix input))
      (g:=MetricTable.get)
      (((itemField_computes 0).pair (itemField_computes 6)).pair discardPrefix_computes)
      MetricTable.get_computes)
noncomputable def distance (x : List Bool) : ℚ := BinaryRational.decode (distanceWords x)
noncomputable def distance_computes : PolyComputes (fun x=>BinaryRational.encode (distance x)) :=
  RatOps.ofWords distanceWords_computes
lemma distance_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    distance (pairBits (pack distances F W v z lam eta i,j.val.bits))=distances i j := by
  unfold distance distanceWords
  simp only [itemField,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [MetricTable.get_pack,BinaryRational.decode_encode]

noncomputable def summand (x : List Bool) : ℚ :=
  if active x then
    if distance x≤paramV x*paramZ x then -(scale x*distance x)
    else max (paramZ x-scale x*distance x) 0
  else max (scale x*nearest x-scale x*distance x) 0
noncomputable def summand_computes : PolyComputes (fun x=>BinaryRational.encode (summand x)) := by
  have hsd := RatOps.mul scale_computes distance_computes
  have ha := (RatOps.le distance_computes (RatOps.mul paramV_computes paramZ_computes)).cond
    (RatOps.neg hsd) (RatOps.max (RatOps.sub paramZ_computes hsd) (RatOps.const 0))
  have hi := RatOps.max (RatOps.sub (RatOps.mul scale_computes nearest_computes) hsd) (RatOps.const 0)
  have hh := active_computes.cond ha hi
  unfold summand
  simpa only [decide_eq_true_eq,apply_ite] using hh

def sourceSummand {m d : ℕ} (distance : Fin m → Fin d → ℚ) (W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (j : Fin d) : ℚ :=
  if EffectiveOpenability.active distance v z W j then
    if distance i j≤v*z then -((1-3*v)*distance i j)
    else max (z-(1-3*v)*distance i j) 0
  else max ((1-3*v)*RationalOpenability.nearest distance W j-(1-3*v)*distance i j) 0
lemma summand_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    summand (pairBits (pack distances F W v z lam eta i,j.val.bits))=
      sourceSummand distances W v z i j := by
  rw [summand,active_pack,distance_pack,nearest_pack]
  simp only [sourceSummand,decide_eq_true_eq,scale,paramV,paramZ,itemField,
    Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode]

noncomputable def input (x : List Bool) : List Bool :=
  pairBits (x,BinaryEllipsoidInitial.indices (field 7 x))
noncomputable def input_computes : PolyComputes input :=
  id_computes.pair ((field_computes 7).comp BinaryEllipsoidInitial.indices_computes)
noncomputable def values : List Bool → List Bool := mapWith (fun x=>BinaryRational.encode (summand x)) ∘ input
noncomputable def values_computes : PolyComputes values := input_computes.comp (mapWith_computes summand_computes)
lemma values_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) :
    values (pack distances F W v z lam eta i)=
      RationalArray.encode (List.ofFn (sourceSummand distances W v z i)) := by
  unfold values input
  rw [Function.comp_apply]
  have hh : field 7 (pack distances F W v z lam eta i)=List.replicate d true := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hh,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn]
  simp only [summand_pack,RationalArray.encode,List.map_ofFn,Function.comp_def]
noncomputable def sumWords : List Bool → List Bool := RationalArray.sumWords ∘ values
noncomputable def sumWords_computes : PolyComputes sumWords := values_computes.comp RationalArray.sumWords_computes
lemma sumWords_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) :
    sumWords (pack distances F W v z lam eta i)=
      BinaryRational.encode (∑ j,sourceSummand distances W v z i j) := by
  rw [sumWords,Function.comp_apply,values_pack,RationalArray.sumWords_encode,List.sum_ofFn]

lemma source_constant {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) :
    (EffectiveOpenability.payment distances F W v z i).constant=
      ∑ j,sourceSummand distances W v z i j := by
  simp only [EffectiveOpenability.payment,Form.sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold sourceSummand
  split_ifs <;> simp only [EffectiveOpenability.bid,Form.coord,Form.sub,Form.const,zero_sub]

noncomputable def run (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (field 4 x) -
    (BinaryArithmetic.value (UnaryResources.lengthBits (field 7 x)):ℚ)*BinaryRational.decode (field 5 x) -
    BinaryRational.decode (sumWords x))
noncomputable def run_computes : PolyComputes run :=
  RatOps.sub
    (RatOps.sub (RatOps.ofWords (field_computes 4))
      (RatOps.mul (RatOps.nat ((field_computes 7).comp UnaryResources.lengthBits_computes))
        (RatOps.ofWords (field_computes 5))))
    (RatOps.ofWords sumWords_computes)

lemma run_source {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) :
    run (pack distances F W v z lam eta i)=BinaryRational.encode
      ((EffectiveOpenability.forms distances F W v z lam eta i RationalOpenability.Kind.payment).constant) := by
  unfold run
  rw [sumWords_pack,BinaryRational.decode_encode]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate,value_bits,BinaryRational.decode_encode,
    EffectiveOpenability.forms,Form.sub,Form.const,Fintype.card_fin]
  rw [source_constant]
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
