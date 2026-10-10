import OAI.Analysis.FreeGroupFactor.Generation

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace RankTwo

section
open Monoid.CoprodI

abbrev SyllableGroups (_ : Bool) := Multiplicative ℤ
abbrev SyllableGroup := Monoid.CoprodI SyllableGroups
abbrev NW (i j : Bool) := Monoid.CoprodI.NeWord SyllableGroups i j

def syllable (i : Bool) (z : ℤ) : SyllableGroup :=
  Monoid.CoprodI.of (i := i) (Multiplicative.ofAdd z)

def singleWord (i : Bool) (z : ℤ) (hz : z ≠ 0) : NW i i :=
  NeWord.singleton (Multiplicative.ofAdd z) hz

@[simp] theorem singleWord_prod (i : Bool) (z : ℤ) (hz : z ≠ 0) :
    (singleWord i z hz).prod = syllable i z := by
  exact NeWord.prod_singleton _ _

@[simp] theorem syllable_add (i : Bool) (z w : ℤ) :
    syllable i (z+w) = syllable i z * syllable i w := by
  exact map_mul (Monoid.CoprodI.of (i := i)) (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)

@[simp] theorem syllable_neg (i : Bool) (z : ℤ) :
    syllable i (-z) = (syllable i z)⁻¹ := by
  exact map_inv _ _

@[simp] theorem syllable_zero (i : Bool) : syllable i 0 = 1 := map_one _

theorem neWord_prod_ne_one {i j : Bool} (w : NW i j) : w.prod ≠ 1 := by
  classical
  intro h
  have hinj : Function.Injective (Word.prod : Word SyllableGroups → SyllableGroup) :=
    (Word.equiv (M := SyllableGroups)).symm.injective
  have heq : w.toWord = Word.empty := hinj (by simpa [NeWord.prod] using h)
  exact w.toList_ne_nil (congrArg Word.toList heq)

variable {ι : Type uι}

def longBlock (start finish : ι → ℤ) (core : ι → NW true true) (i : ι) : SyllableGroup :=
  syllable true 1 * syllable false (start i) * (core i).prod * syllable false (finish i)

def PositiveHead (start : ι → ℤ) (i : ι) (g : SyllableGroup) : Prop :=
  ∃ j, ∃ W : NW false j, W.head = Multiplicative.ofAdd (start i) ∧
    g = syllable true 1 * W.prod

def NegativeHead (finish : ι → ℤ) (i : ι) (g : SyllableGroup) : Prop :=
  ∃ j, ∃ W : NW true j, g = syllable false (-(finish i)) * W.prod

theorem positiveHead_ne_one {start : ι → ℤ} {i : ι} {g : SyllableGroup}
    (h : PositiveHead start i g) : g ≠ 1 := by
  obtain ⟨j,W,_hW,rfl⟩ := h
  exact neWord_prod_ne_one ((singleWord true 1 (by norm_num)).append (by decide) W)

theorem negativeHead_ne_one {finish : ι → ℤ} {i : ι} (hi : finish i ≠ 0)
    {g : SyllableGroup} (h : NegativeHead finish i g) : g ≠ 1 := by
  obtain ⟨j,W,rfl⟩ := h
  exact neWord_prod_ne_one ((singleWord false (-finish i) (neg_ne_zero.mpr hi)).append (by decide) W)

variable (start finish : ι → ℤ) (core : ι → NW true true)
variable (hs : ∀ i, start i ≠ 0) (ht : ∀ i, finish i ≠ 0)
include hs ht

theorem longBlock_positive (i : ι) :
    PositiveHead start i (longBlock start finish core i) := by
  let W := ((singleWord false (start i) (hs i)).append (by decide) (core i)).append
    (by decide) (singleWord false (finish i) (ht i))
  refine ⟨false,W,?_,?_⟩
  · rfl
  · simp [W,longBlock,mul_assoc]

omit ht in
theorem longBlock_negative (i : ι) :
    NegativeHead finish i (longBlock start finish core i)⁻¹ := by
  let W := ((core i).inv.append (by decide) (singleWord false (-start i) (neg_ne_zero.mpr (hs i)))).append
    (by decide) (singleWord true (-1) (by norm_num))
  refine ⟨true,W,?_⟩
  simp [W,longBlock,mul_inv_rev,mul_assoc]

theorem positive_mul_positive (i j : ι) {g : SyllableGroup}
    (h : PositiveHead start j g) :
    PositiveHead start i (longBlock start finish core i * g) := by
  obtain ⟨k,V,_hV,rfl⟩ := h
  let W := ((((singleWord false (start i) (hs i)).append (by decide) (core i)).append
    (by decide) (singleWord false (finish i) (ht i))).append (by decide)
    (singleWord true 1 (by norm_num))).append (by decide) V
  refine ⟨k,W,rfl,?_⟩
  simp [W,longBlock,mul_assoc]

theorem negative_mul_negative (i j : ι) {g : SyllableGroup}
    (h : NegativeHead finish j g) :
    NegativeHead finish i ((longBlock start finish core i)⁻¹ * g) := by
  obtain ⟨k,V,rfl⟩ := h
  let W := ((((core i).inv.append (by decide) (singleWord false (-start i) (neg_ne_zero.mpr (hs i)))).append
    (by decide) (singleWord true (-1) (by norm_num))).append (by decide)
    (singleWord false (-finish j) (neg_ne_zero.mpr (ht j)))).append (by decide) V
  refine ⟨k,W,?_⟩
  simp [W,longBlock,mul_inv_rev,mul_assoc]

omit ht in
theorem positive_mul_negative (i j : ι) (hij : finish i ≠ finish j) {g : SyllableGroup}
    (h : NegativeHead finish j g) :
    PositiveHead start i (longBlock start finish core i * g) := by
  obtain ⟨k,V,rfl⟩ := h
  let W := (((singleWord false (start i) (hs i)).append (by decide) (core i)).append
    (by decide) (singleWord false (finish i-finish j) (sub_ne_zero.mpr hij))).append (by decide) V
  refine ⟨k,W,rfl,?_⟩
  simp [W,longBlock,sub_eq_add_neg,mul_assoc]

omit hs ht in
theorem negative_mul_positive (i j : ι) (hij : start i ≠ start j) {g : SyllableGroup}
    (h : PositiveHead start j g) :
    NegativeHead finish i ((longBlock start finish core i)⁻¹ * g) := by
  obtain ⟨k,V,hV,rfl⟩ := h
  have hno : (Multiplicative.ofAdd (-(start i))) * V.head ≠ 1 := by
    rw [hV]
    change -(start i) + start j ≠ 0
    omega
  let W := (core i).inv.append (by decide) (V.mulHead (Multiplicative.ofAdd (-(start i))) hno)
  refine ⟨k,W,?_⟩
  simp [W,longBlock,mul_inv_rev,syllable,mul_assoc]

variable (hinjs : Function.Injective start) (hinjt : Function.Injective finish)
include hinjs hinjt

def evalLetters (f : ι → SyllableGroup) (L : List (ι × Bool)) : SyllableGroup :=
  (L.map (fun x => cond x.2 (f x.1) (f x.1)⁻¹)).prod

omit hs ht hinjs hinjt in
@[simp] theorem evalLetters_nil (f : ι → SyllableGroup) : evalLetters f [] = 1 := rfl

omit hs ht hinjs hinjt in
@[simp] theorem evalLetters_cons (f : ι → SyllableGroup) (i : ι) (b : Bool) (L : List (ι × Bool)) :
    evalLetters f ((i,b)::L) = (cond b (f i) (f i)⁻¹) * evalLetters f L := rfl

theorem longBlock_head (L : List (ι × Bool)) (i : ι) (b : Bool)
    (hL : FreeGroup.IsReduced ((i,b)::L)) :
    if b then PositiveHead start i (evalLetters (longBlock start finish core) ((i,b)::L))
    else NegativeHead finish i (evalLetters (longBlock start finish core) ((i,b)::L)) := by
  induction L generalizing i b with
  | nil =>
    cases b
    · simpa using longBlock_negative start finish core hs i
    · simpa using longBlock_positive start finish core hs ht i
  | cons a L ih =>
    obtain ⟨j,c⟩ := a
    obtain ⟨hij,hred⟩ := FreeGroup.isReduced_cons_cons.mp hL
    have hrec := ih j c hred
    cases b <;> cases c
    · simpa using negative_mul_negative start finish core hs ht i j hrec
    · have hne : start i ≠ start j := fun h => by simpa using hij (hinjs h)
      simpa using negative_mul_positive start finish core i j hne hrec
    · have hne : finish i ≠ finish j := fun h => by simpa using hij (hinjt h)
      simpa using positive_mul_negative start finish core hs i j hne hrec
    · simpa using positive_mul_positive start finish core hs ht i j hrec

theorem longBlock_injective :
    Function.Injective (FreeGroup.lift (longBlock start finish core)) := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hred := FreeGroup.isReduced_toWord (x := g)
  have he : evalLetters (longBlock start finish core) g.toWord = 1 := by
    unfold evalLetters
    rw [← FreeGroup.lift_mk,FreeGroup.mk_toWord]
    exact hg
  cases hw : g.toWord with
  | nil => exact FreeGroup.toWord_eq_nil_iff.mp hw
  | cons a L =>
    obtain ⟨i,b⟩ := a
    rw [hw] at hred he
    have hh := longBlock_head start finish core hs ht hinjs hinjt L i b hred
    cases b
    · exact False.elim (negativeHead_ne_one (ht i) hh he)
    · exact False.elim (positiveHead_ne_one hh he)

end
open Monoid.CoprodI

def piece (E : ℕ → ℤ) (j : ℕ) : SyllableGroup := syllable true 1 * syllable false (E j)

def segment (E : ℕ → ℤ) (s : ℕ) : ℕ → SyllableGroup
  | 0 => 1
  | k+1 => segment E s k * piece E (s+k)

@[simp] theorem segment_zero (E : ℕ → ℤ) (s : ℕ) : segment E s 0 = 1 := rfl
@[simp] theorem segment_succ (E : ℕ → ℤ) (s k : ℕ) :
    segment E s (k+1) = segment E s k * piece E (s+k) := rfl

@[simp] theorem segment_one (E : ℕ → ℤ) (s : ℕ) : segment E s 1 = piece E s := by simp

theorem segment_append (E : ℕ → ℤ) (s j k : ℕ) :
    segment E s (j+k) = segment E s j * segment E (s+j) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Nat.add_succ,segment_succ,ih,Nat.add_assoc,mul_assoc]

theorem segment_cons (E : ℕ → ℤ) (s k : ℕ) :
    segment E s (k+1) = piece E s * segment E (s+1) k := by
  simpa [Nat.add_comm] using segment_append E s 1 k

def coreWord (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0) (s : ℕ) : ℕ → NW true true
  | 0 => singleWord true 1 (by norm_num)
  | k+1 => ((coreWord E hE s k).append (by decide)
      (singleWord false (E (s+k)) (hE (s+k)))).append (by decide)
      (singleWord true 1 (by norm_num))

theorem segment_core (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0) (s k : ℕ) :
    segment E s (k+1) = (coreWord E hE s k).prod * syllable false (E (s+k)) := by
  induction k with
  | zero => simp [coreWord,piece]
  | succ k ih =>
    rw [segment_succ,ih]
    simp only [coreWord,NeWord.append_prod,singleWord_prod,piece,mul_assoc]

theorem segment_longBlock (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0) (s k : ℕ) :
    segment E s (k+2) = syllable true 1 * syllable false (E s) *
      (coreWord E hE (s+1) k).prod * syllable false (E (s+k+1)) := by
  rw [show k+2 = (k+1)+1 by omega,segment_cons,segment_core E hE]
  have he : s+1+k = s+k+1 := by omega
  simp only [piece,mul_assoc,he]

def cumulative {G : Type uG} [Group G] (f : ℕ → G) : ℕ → G
  | 0 => 1
  | k+1 => cumulative f k * f k

@[simp] theorem cumulative_zero {G : Type uG} [Group G] (f : ℕ → G) : cumulative f 0 = 1 := rfl
@[simp] theorem cumulative_succ {G : Type uG} [Group G] (f : ℕ → G) (k : ℕ) :
    cumulative f (k+1) = cumulative f k * f k := rfl

theorem map_cumulative {G : Type uG} {H : Type uH} [Group G] [Group H] (φ : G →* H) (f : ℕ → G) (k : ℕ) :
    φ (cumulative f k) = cumulative (φ ∘ f) k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]

def finGenerator (m j : ℕ) : FreeGroup (Fin m) :=
  if h : j < m then FreeGroup.of ⟨j,h⟩ else 1

def prefixGenerator (m j : ℕ) : FreeGroup (Fin m) :=
  if j = 0 then 1 else finGenerator m (j-1)

@[simp] theorem prefixGenerator_zero (m : ℕ) : prefixGenerator m 0 = 1 := by simp [prefixGenerator]
@[simp] theorem prefixGenerator_succ (m j : ℕ) : prefixGenerator m (j+1) = finGenerator m j := by
  simp [prefixGenerator]

@[simp] theorem finGenerator_fin {m : ℕ} (i : Fin m) : finGenerator m i.val = FreeGroup.of i := by
  simp [finGenerator,i.is_lt]

def triangularHom (m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun i => cumulative (finGenerator m) (i.val+1))

def differenceHom (m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun i => (prefixGenerator m i.val)⁻¹ * prefixGenerator m (i.val+1))

theorem difference_cumulative (m k : ℕ) (hk : k ≤ m) :
    differenceHom m (cumulative (finGenerator m) k) = prefixGenerator m k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m := by omega
    rw [cumulative_succ,map_mul,ih (by omega)]
    simp only [finGenerator,dite_eq_left hkm,differenceHom,FreeGroup.lift_apply_of]
    simp

theorem triangularHom_injective (m : ℕ) : Function.Injective (triangularHom m) := by
  have hcomp : (differenceHom m).comp (triangularHom m) = MonoidHom.id _ := by
    ext i
    simp only [MonoidHom.comp_apply,triangularHom,FreeGroup.lift_apply_of,MonoidHom.id_apply]
    rw [difference_cumulative m (i.val+1) (by omega)]
    simp
  intro x y hxy
  have := congrArg (differenceHom m) hxy
  change ((differenceHom m).comp (triangularHom m)) x =
    ((differenceHom m).comp (triangularHom m)) y at this
  simpa only [hcomp,MonoidHom.id_apply] using this

theorem cumulative_injective {G : Type uG} [Group G] (m : ℕ) (f : ℕ → G)
    (hf : Function.Injective (FreeGroup.lift (fun i : Fin m => f i.val))) :
    Function.Injective (FreeGroup.lift (fun i : Fin m => cumulative f (i.val+1))) := by
  have hc (k : ℕ) (hk : k ≤ m) :
      FreeGroup.lift (fun i : Fin m => f i.val) (cumulative (finGenerator m) k) = cumulative f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkm : k < m := by omega
      rw [cumulative_succ,map_mul,ih (by omega),cumulative_succ]
      simp only [finGenerator,dite_eq_left hkm,FreeGroup.lift_apply_of]
  have he : FreeGroup.lift (fun i : Fin m => cumulative f (i.val+1)) =
      (FreeGroup.lift (fun i : Fin m => f i.val)).comp (triangularHom m) := by
    ext i
    simp only [MonoidHom.comp_apply,triangularHom,FreeGroup.lift_apply_of]
    exact (hc (i.val+1) (by omega)).symm
  rw [he]
  exact hf.comp (triangularHom_injective m)

theorem intervalBlocks_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (k : ℕ) (b : Fin (k+1) → ℕ)
    (hb : ∀ i : Fin k, b i.castSucc + 2 ≤ b i.succ) :
    Function.Injective (FreeGroup.lift (fun i : Fin k =>
      segment E (b i.castSucc) (b i.succ - b i.castSucc))) := by
  have hbm : StrictMono b := Fin.strictMono_iff_lt_succ.mpr (fun i => by have := hb i; omega)
  let start (i : Fin k) : ℤ := E (b i.castSucc)
  let finish (i : Fin k) : ℤ := E (b i.succ-1)
  let core (i : Fin k) : NW true true :=
    coreWord E hE (b i.castSucc+1) (b i.succ-b i.castSucc-2)
  have hstart : Function.Injective start := by
    intro i j hij
    have he := congrArg Fin.val (hbm.injective (hiE hij))
    exact Fin.ext he
  have hfinish : Function.Injective finish := by
    intro i j hij
    have he := hiE hij
    have hi := hb i
    have hj := hb j
    have he' : b i.succ = b j.succ := by omega
    have hev := congrArg Fin.val (hbm.injective he')
    apply Fin.ext
    exact Nat.add_right_cancel hev
  have hh := longBlock_injective start finish core (fun i => hE _) (fun i => hE _) hstart hfinish
  have he (i : Fin k) : segment E (b i.castSucc) (b i.succ-b i.castSucc) =
      longBlock start finish core i := by
    have hbi := hb i
    have hn : b i.succ-b i.castSucc = (b i.succ-b i.castSucc-2)+2 := by omega
    rw [hn,segment_longBlock E hE]
    dsimp only [longBlock,start,finish,core]
    have he' : b i.castSucc+(b i.succ-b i.castSucc-2)+1 = b i.succ-1 := by omega
    rw [he']
  simpa only [he] using hh

theorem boundaryPrefixes_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (k : ℕ) (b : Fin (k+1) → ℕ)
    (hb0 : b 0 = 0) (hb : ∀ i : Fin k, b i.castSucc + 2 ≤ b i.succ) :
    Function.Injective (FreeGroup.lift (fun i : Fin k => segment E 0 (b i.succ))) := by
  let f (j : ℕ) : SyllableGroup := if h : j < k then
      segment E (b (⟨j,h⟩ : Fin k).castSucc) (b (⟨j,h⟩ : Fin k).succ-b (⟨j,h⟩ : Fin k).castSucc)
    else 1
  have hf : Function.Injective (FreeGroup.lift (fun i : Fin k => f i.val)) := by
    simpa only [f,dite_eq_left (Fin.is_lt _)] using intervalBlocks_injective E hE hiE k b hb
  have hc (j : ℕ) (hj : j ≤ k) : cumulative f j = segment E 0 (b ⟨j,by omega⟩) := by
    induction j with
    | zero => simp [hb0]
    | succ j ih =>
      have hjk : j < k := by omega
      have hbj := hb ⟨j,hjk⟩
      change b (⟨j,by omega⟩ : Fin (k+1))+2 ≤ b (⟨j+1,by omega⟩ : Fin (k+1)) at hbj
      rw [cumulative_succ,ih (by omega)]
      simp only [f,dite_eq_left hjk]
      have happ := segment_append E 0 (b (⟨j,by omega⟩ : Fin (k+1)))
        (b (⟨j+1,by omega⟩ : Fin (k+1))-b (⟨j,by omega⟩ : Fin (k+1)))
      simp only [zero_add] at happ
      change segment E 0 (b (⟨j,by omega⟩ : Fin (k+1))) *
        segment E (b (⟨j,by omega⟩ : Fin (k+1)))
          (b (⟨j+1,by omega⟩ : Fin (k+1))-b (⟨j,by omega⟩ : Fin (k+1))) = _
      rw [← happ]
      congr 1
      change b (⟨j,by omega⟩ : Fin (k+1)) +
        (b (⟨j+1,by omega⟩ : Fin (k+1))-b (⟨j,by omega⟩ : Fin (k+1))) = _
      omega
  have he (i : Fin k) : cumulative f (i.val+1) = segment E 0 (b i.succ) := hc _ (by omega)
  simpa only [he] using cumulative_injective k f hf

theorem separatedPrefixes_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (k : ℕ) (r : Fin k → ℕ)
    (hr : ∀ i j : Fin k, i < j → r i + 2 ≤ r j) :
    Function.Injective (FreeGroup.lift (fun i : Fin k => segment E 0 (r i+2))) := by
  let b : Fin (k+1) → ℕ := Fin.cases 0 (fun i => r i+2)
  have hb0 : b 0 = 0 := rfl
  have hb (i : Fin k) : b i.castSucc+2 ≤ b i.succ := by
    change b i.castSucc+2 ≤ r i+2
    by_cases hi : i.val = 0
    · have he : i.castSucc = 0 := Fin.ext hi
      rw [he,hb0]
      omega
    · let j : Fin k := ⟨i.val-1,by have := i.is_lt; omega⟩
      have hji : j < i := by change i.val-1 < i.val; omega
      have he : i.castSucc = j.succ := Fin.ext (by dsimp [j]; omega)
      rw [he]
      have hg := hr j i hji
      change (r j+2)+2 ≤ r i+2
      omega
  simpa only [b,Fin.cases_succ] using boundaryPrefixes_injective E hE hiE k b hb0 hb

def runExponent (B j : ℕ) : ℤ := ((B : ℤ)-1)*(B : ℤ)^j

theorem runExponent_pos {B : ℕ} (hB : 2 ≤ B) (j : ℕ) : 0 < runExponent B j := by
  have hb : (1 : ℤ) < B := by exact_mod_cast hB
  unfold runExponent
  positivity

theorem runExponent_strictMono {B : ℕ} (hB : 2 ≤ B) : StrictMono (runExponent B) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hp := runExponent_pos hB j
  have hb : (1 : ℤ) < B := by exact_mod_cast hB
  have he : runExponent B (j+1) = runExponent B j * B := by simp [runExponent,pow_succ,mul_assoc]
  rw [he]
  nlinarith

theorem separatedSetPrefixes_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) {m : ℕ} (s : Finset (Fin m))
    (hs : ∀ i ∈ s, ∀ j ∈ s, i.val+1 ≠ j.val) :
    Function.Injective (FreeGroup.lift (fun i : s => segment E 0 (i.val.val+2))) := by
  classical
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  have hr (i j : Fin s.card) (hij : i < j) : (e i).val.val+2 ≤ (e j).val.val := by
    have hlt : (e i).val < (e j).val := e.strictMono hij
    have hne := hs (e i).val (e i).property (e j).val (e j).property
    change (e i).val.val < (e j).val.val at hlt
    omega
  have hf := separatedPrefixes_injective E hE hiE s.card (fun i => (e i).val.val) hr
  have he : (FreeGroup.lift (fun i : Fin s.card => segment E 0 ((e i).val.val+2))).comp
      (FreeGroup.map e.symm) = FreeGroup.lift (fun i : s => segment E 0 (i.val.val+2)) := by
    ext i
    simp
  rw [← he]
  exact hf.comp (FreeGroup.map_injective e.symm.injective)

theorem mk_eq_one_of_restricted_lift {ι : Type uι} {G : Type uG} [Group G]
    (f : ι → G) (s : Finset ι)
    (hf : Function.Injective (FreeGroup.lift (fun i : s => f i.val)))
    (L : List (ι × Bool)) (hL : ∀ p ∈ L, p.1 ∈ s)
    (he : FreeGroup.lift f (FreeGroup.mk L) = 1) : FreeGroup.mk L = 1 := by
  classical
  by_cases hs : s.Nonempty
  · let z : s := ⟨hs.choose,hs.choose_spec⟩
    let r (i : ι) : s := if h : i ∈ s then ⟨i,h⟩ else z
    have hr (i : ι) (hi : i ∈ s) : (r i).val = i := by simp [r,hi]
    let R := (FreeGroup.map r) (FreeGroup.mk L)
    have hR : FreeGroup.map (fun i : s => i.val) R = FreeGroup.mk L := by
      simp only [R,FreeGroup.map.mk,List.map_map]
      congr 1
      have hmap : L.map ((fun x : s × Bool => (x.1.val,x.2)) ∘
          (fun x : ι × Bool => (r x.1,x.2))) = L.map id := by
        apply List.map_congr_left
        intro p hp
        exact Prod.ext (hr p.1 (hL p hp)) rfl
      exact hmap.trans (List.map_id L)
    have hh : (FreeGroup.lift f).comp (FreeGroup.map (fun i : s => i.val)) =
        FreeGroup.lift (fun i : s => f i.val) := by ext i; simp
    have heR : FreeGroup.lift (fun i : s => f i.val) R = 1 := by
      rw [← hh, MonoidHom.comp_apply,hR,he]
    have hR1 : R = 1 := hf (heR.trans (map_one _).symm)
    rw [← hR,hR1,map_one]
  · have hnil : L = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      exact hs ⟨p.1,hL p hp⟩
    subst L
    rfl

theorem prefixRelation_of_separated {m : ℕ} (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (L : List (Fin m × Bool))
    (hsep : ∀ p ∈ L, ∀ q ∈ L, p.1.val+1 ≠ q.1.val)
    (he : FreeGroup.lift (fun i : Fin m => segment E 0 (i.val+2)) (FreeGroup.mk L) = 1) :
    FreeGroup.mk L = 1 := by
  classical
  let s := (L.map Prod.fst).toFinset
  have hs : ∀ i ∈ s, ∀ j ∈ s, i.val+1 ≠ j.val := by
    intro i hi j hj
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact hsep p hp q hq
  apply mk_eq_one_of_restricted_lift _ s (separatedSetPrefixes_injective E hE hiE s hs) L _ he
  intro p hp
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)

end RankTwo

end

end FreeGroupFactorMain

end OAI
