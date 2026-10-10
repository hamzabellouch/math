import OAI.Computability.Superstring.RequestAttachment

namespace OAI

namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode
variable {α ι κ : Type} [Inhabited α] [DecidableEq α] {V : Set (List α)}

theorem filter_sum_reserve (I : List κ) (P : κ → Bool) (weight : κ → ℕ) (i : κ)
    (hi : i ∈ I) (hp : P i = false) :
    weight i + ((I.filter P).map weight).sum ≤ (I.map weight).sum := by
  have hb (L : List κ) : ((L.filter P).map weight).sum ≤ (L.map weight).sum := by
    induction L with
    | nil => simp
    | cons j L ih =>
      cases h : P j <;> simp only [List.filter_cons,h,Bool.false_eq_true,↓reduceIte,
        List.map_cons,List.sum_cons] <;> omega
  induction I with
  | nil => simp at hi
  | cons j I ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp only [List.filter_cons,hp,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons]
      exact Nat.add_le_add_left (hb I) _
    · have hh := ih hi
      cases h : P j <;> simp only [List.filter_cons,h,Bool.false_eq_true,↓reduceIte,
        List.map_cons,List.sum_cons] <;> omega

omit [DecidableEq α] in
def entryOf {A : ℤ → α} {q : ℕ} {D : Layer V A q} (H : ι → HostedGroup D)
    (g : κ → ι) (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ) (i : κ) : Entry α :=
  (tag (g i),W (g i),(H (g i)).start,(H (g i)).stop,(R i).stop)

theorem normalized_spec {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (hU : U.length = q) (hUt : PeriodWord.text U = A)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (I : List κ) (i₀ : κ) (hi₀ : i₀ ∈ I)
    (hmin : ∀ i ∈ I, (H (g i₀)).period ≤ (H (g i)).period)
    (hreq : ∀ i ∈ I, g i = g i₀ → (R i₀).stop ≤ (R i).stop)
    (horder : ∀ i ∈ I,
      (H (g i₀)).start ≤ (H (g i)).start ∧ (H (g i)).start ≤ (H (g i₀)).start+q ∧
      (H (g i₀)).stop ≤ (H (g i)).stop ∧ (H (g i)).stop ≤ (H (g i₀)).stop+q) :
    let E := entryOf H g R W tag
    Runs V [] [] (normalized U (E i₀) (I.map E)) ∧
      cost (normalized U (E i₀) (I.map E)) ≤ q+(I.map (fun i => (H (g i)).period)).sum ∧
      textWord A (H (g i₀)).start (H (g i₀)).stop ∈ normalized U (E i₀) (I.map E) ∧
      ∀ i ∈ I, textWord (H (g i)).text (H (g i)).start (R i).stop ∈ normalized U (E i₀) (I.map E) := by
  classical
  let E := entryOf H g R W tag
  let J := I.filter (fun i => decide (g i ≠ g i₀))
  have hJ (i : κ) : i ∈ J ↔ i ∈ I ∧ g i ≠ g i₀ := by simp [J]
  let s := fun i => min ((H (g i)).start+(H (g i)).period) ((H (g i₀)).start+q)
  let h := fun i => max (R i).stop (H (g i₀)).stop
  let F := fun i => (W (g i),((H (g i)).start,(R i).stop),(s i,h i))
  have hmap : (later (E i₀) (I.map E)).map (Entry.target U.length (E i₀)) = J.map F := by
    have hl : later (E i₀) (I.map E) = J.map E := by
      unfold later J
      rw [List.filter_map]
      congr 1
      apply congrArg (fun f => I.filter f)
      funext i
      simp [E,entryOf,Entry.tag,equal,htag.eq_iff]
    rw [hl,List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply,E,entryOf,Entry.target,Entry.word,Entry.start,Entry.req,Entry.stop,hU,hW,F,s,h]
  have hb (i : κ) (hi : i ∈ J) :
      (H (g i)).start ≤ s i ∧ s i ≤ (H (g i)).start+(H (g i)).period ∧
      s i ≤ h i ∧ h i ≤ (H (g i)).stop ∧ (R i).stop ≤ h i ∧
      h i ≤ (R i).stop+(H (g i)).period ∧ (H (g i₀)).start ≤ s i ∧
      s i ≤ (H (g i₀)).start+q ∧ (H (g i₀)).stop ≤ h i ∧ h i < (H (g i₀)).start+q+(H (g i₀)).period := by
    obtain ⟨hiI,hne⟩ := (hJ i).mp hi
    exact hosted_target_bounds D hq per _ _ (R i) (hmin i hiI) (horder i hiI)
      (by simpa only [add_zero] using different (g i₀) (g i) (Ne.symm hne) 0)
      (by simpa only [← sub_eq_add_neg] using different (g i) (g i₀) hne (-(q:ℤ)))
  have hv (i : κ) (hi : i ∈ J) : textWord A (s i) (h i) ∈ V :=
    closed (H (g i)).host_mem (textWord_infix A (hb i hi).1 (hb i hi).2.2.1 (hb i hi).2.2.2.1)
  have heq (i : κ) (hi : i ∈ J) : textWord (H (g i)).text (s i) (h i) = textWord A (s i) (h i) :=
    textWord_eq_of_agree (fun x hx hy => (H (g i)).agree x ((hb i hi).1.trans hx) (hy.trans_le (hb i hi).2.2.2.1))
  have hen : (H (g i₀)).start+(H (g i₀)).period < (R i₀).stop := (R i₀).long
  have heb : (R i₀).stop ≤ (H (g i₀)).stop := by have := (R i₀).margin; omega
  have hshort : (H (g i₀)).stop < (H (g i₀)).start+q+(H (g i₀)).period := by
    have hh := (H (g i₀)).length_lt hq per; omega
  obtain ⟨hQ,hQc,hQr,hQv,hQatt⟩ := raw_spec closed U (by simpa only [hUt] using letters)
    (H (g i₀)).period (H (g i₀)).positive (H (g i₀)).start (H (g i₀)).stop (R i₀).stop
    hen heb (by simpa only [PeriodWord.window_eq,hUt] using (H (g i₀)).host_mem)
    (by simpa only [hU] using hshort) (J.map F)
    (by intro r hr t ht; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
        exact hosted_targets_chain D H g R different _ _ i j)
    (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        dsimp only [F]; rw [hU]
        exact ⟨(hb i hi).2.2.2.2.2.2.1,(hb i hi).2.2.2.2.2.2.2.1,
          (hb i hi).2.2.1,(hb i hi).2.2.2.2.2.2.2.2.1,(hb i hi).2.2.2.2.2.2.2.2.2⟩)
    (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        simpa only [F,PeriodWord.window_eq,hUt] using hv i hi)
    (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        dsimp only [F]
        simp only [hW,PeriodWord.window_eq,hWt,hUt]
        refine ⟨child_letters _,?_,(hb i hi).1,(hb i hi).2.1,(hb i hi).2.2.2.2.1,
          (hb i hi).2.2.2.2.2.1,(R i).word_mem,heq i hi⟩
        have := (R i).long; omega)
  have hpath : normalized U (E i₀) (I.map E) =
      raw U (H (g i₀)).period (H (g i₀)).start (H (g i₀)).stop (R i₀).stop (J.map F) := by
    rw [normalized,hmap]
    simp only [E,entryOf,Entry.word,Entry.start,Entry.stop,Entry.req,hW]
  change Runs V [] [] (normalized U (E i₀) (I.map E)) ∧ _
  rw [hpath]
  refine ⟨hQ,?_,?_,?_⟩
  · simp only [hU,List.map_map,Function.comp_def,F,hW] at hQc
    have hh := filter_sum_reserve I (fun i => decide (g i ≠ g i₀))
      (fun i => (H (g i)).period) i₀ hi₀ (by simp)
    dsimp only [J,F] at hQc ⊢
    omega
  · simpa only [PeriodWord.window_eq,hUt] using hQr
  · intro i hi
    by_cases hg : g i = g i₀
    · have heq' : textWord (H (g i)).text (H (g i)).start (R i).stop =
          textWord A (H (g i₀)).start (R i).stop := by
        rw [← hg]
        apply textWord_eq_of_agree
        intro x hx hy
        apply (H (g i)).agree x hx
        have := (R i).margin
        omega
      rw [heq']
      have hb' : (R i).stop ≤ (H (g i₀)).stop := by
        have := (R i).margin
        have hs := congrArg (fun j => (H j).stop) hg
        omega
      simpa only [PeriodWord.window_eq,hUt] using hQv _ (hreq i hi hg) hb'
    · have hh := hQatt _ (List.mem_map.mpr ⟨i,(hJ i).mpr ⟨hi,hg⟩,rfl⟩)
      simpa only [F,PeriodWord.window_eq,hWt] using hh
end Superstring.HostCode


namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode

def normalDelta (q : ℕ) (a b a₀ b₀ : ℤ) : ℤ :=
  let d := a₀+((a-a₀) % (q:ℤ)).toNat-a
  if decide (b₀ ≤ b+d) then d else d+q

@[simp] theorem normalDelta_self (q : ℕ) (a b : ℤ) : normalDelta q a b a b = 0 := by
  simp [normalDelta]

theorem normalDelta_spec {α : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}
    (D : Layer V A q) (hq : 0 < q) {a b a₀ b₀ : ℤ}
    (hf : D.first a ≤ b) (hl : b ≤ D.last a)
    (hf₀ : D.first a₀ ≤ b₀) (hl₀ : b₀ ≤ D.last a₀) :
    ∃ m : ℤ, normalDelta q a b a₀ b₀ = m*q ∧
      a₀ ≤ a+m*q ∧ a+m*q ≤ a₀+q ∧ b₀ ≤ b+m*q ∧ b+m*q ≤ b₀+q := by
  let m : ℤ := -((a-a₀)/q)
  let r : ℤ := a+m*q
  let e : ℤ := b+m*q
  have hr : r = a₀+(a-a₀)%q := by
    have hh := Int.emod_add_ediv_mul (a-a₀) (q:ℤ)
    dsimp only [r,m]
    simp only [neg_mul]
    omega
  have hrlo : a₀ ≤ r := by have := Int.emod_nonneg (a-a₀) (show (q:ℤ) ≠ 0 by omega); omega
  have hrhi : r < a₀+q := by have := Int.emod_lt_of_pos (a-a₀) (show (0:ℤ) < q by omega); omega
  have hfe : D.first r ≤ e := by dsimp only [r,e]; rw [D.first_shift_int]; omega
  have hle : e ≤ D.last r := by
    dsimp only [r,e,Layer.last]
    rw [D.shift_int]
    change b ≤ D.z a at hl
    omega
  have hfnext : D.first (a₀+q) ≤ b₀+q := by rw [D.first_shift]; omega
  have hehi : e ≤ b₀+q := D.window_order hle hfnext hrhi
  have hd : a₀+(((a-a₀)%(q:ℤ)).toNat:ℤ)-a = m*q := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    dsimp only [r] at hr
    omega
  by_cases hb : b₀ ≤ e
  · refine ⟨m,?_,hrlo,hrhi.le,hb,hehi⟩
    simp only [normalDelta,hd,show b₀ ≤ b+m*q from hb,decide_true,↓reduceIte]
  · have hre : r = a₀ := by
      by_contra hn
      have hh := D.window_order hl₀ hfe (by omega : a₀ < r)
      omega
    have hfn : D.first (r+q) ≤ e+q := by rw [D.first_shift]; omega
    have helon : b₀ ≤ e+q := D.window_order hl₀ hfn (by omega)
    refine ⟨m+1,?_,?_,?_,?_,?_⟩
    · simp only [normalDelta,hd,show ¬ b₀ ≤ b+m*q from hb,decide_false,Bool.false_eq_true,↓reduceIte]
      ring
    all_goals dsimp only [r,e] at *; nlinarith

@[fun_prop] theorem poly_normalDelta : Poly (fun t : ℕ × ℤ × ℤ × ℤ × ℤ =>
    normalDelta t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) := by
  have hr : Poly (fun t : ℕ × ℤ × ℤ × ℤ × ℤ => ((t.2.1-t.2.2.2.1)%(t.1:ℤ)).toNat) :=
    Poly.modIntNat.comp (f := fun t : ℕ × ℤ × ℤ × ℤ × ℤ => (t.2.1-t.2.2.2.1,t.1)) (by fun_prop)
  unfold normalDelta
  dsimp only
  fun_prop

variable {α : Type} [Inhabited α] [DecidableEq α]
def normalizeEntry (q : ℕ) (base e : Entry α) : Entry α :=
  e.shift (normalDelta q e.start e.stop base.start base.stop)
def requestPath (U : List α) (base : Entry α) (E : List (Entry α)) : Walk α :=
  normalized U base (E.map (normalizeEntry U.length base))
def requestPool (U : List α) (E : List (Entry α)) : List (Walk α) :=
  E.map (fun b => requestPath U b E)
variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_normalizeEntry : Poly (fun t : ℕ × Entry α × Entry α => normalizeEntry t.1 t.2.1 t.2.2) := by
  unfold normalizeEntry
  have hd := poly_normalDelta.comp (f := fun t : ℕ × Entry α × Entry α =>
    (t.1,t.2.2.start,t.2.2.stop,t.2.1.start,t.2.1.stop)) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_requestPath : Poly (fun t : List α × Entry α × List (Entry α) => requestPath t.1 t.2.1 t.2.2) := by
  have hm : Poly (fun t : List α × Entry α × List (Entry α) => t.2.2.map (normalizeEntry t.1.length t.2.1)) := by
    apply BitCode.Poly.mapFn (f := fun t : (List α × Entry α × List (Entry α)) × Entry α => normalizeEntry t.1.1.length t.1.2.1 t.2)
    · exact poly_normalizeEntry.comp (f := fun t : (List α × Entry α × List (Entry α)) × Entry α =>
        (t.1.1.length,t.1.2.1,t.2)) (by fun_prop)
    · fun_prop
  unfold requestPath
  fun_prop
@[fun_prop] theorem poly_requestPool : Poly (fun t : List α × List (Entry α) => requestPool t.1 t.2) := by
  unfold requestPool
  apply BitCode.Poly.mapFn (f := fun t : (List α × List (Entry α)) × Entry α => requestPath t.1.1 t.2 t.1.2)
  · exact poly_requestPath.comp (f := fun t : (List α × List (Entry α)) × Entry α => (t.1.1,t.2,t.1.2)) (by fun_prop)
  · fun_prop
end Superstring.HostCode


namespace Superstring.PeriodWord
variable {α : Type} [Inhabited α]
@[simp] theorem shift_zero (U : List α) : shift U 0 = U := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [shift,window_eq,Hierarchical.textWord,List.getElem_ofFn,neg_zero,zero_add]
    simp only [text,Int.emod_eq_of_lt (by omega : (0:ℤ) ≤ i) (by omega : (i:ℤ) < U.length),Int.toNat_natCast,
      List.getElem?_eq_getElem hi',Option.getD_some]
end Superstring.PeriodWord

namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode
variable {α ι κ : Type} [Inhabited α] [DecidableEq α] {V : Set (List α)}

theorem requestPath_spec {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (hU : U.length = q) (hUt : PeriodWord.text U = A)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (I : List κ) (i₀ : κ) (hi₀ : i₀ ∈ I)
    (hmin : ∀ i ∈ I, (H (g i₀)).period ≤ (H (g i)).period)
    (hreq : ∀ i ∈ I, g i = g i₀ → (R i₀).stop ≤ (R i).stop) :
    let E := entryOf H g R W tag
    Runs V [] [] (requestPath U (E i₀) (I.map E)) ∧
      cost (requestPath U (E i₀) (I.map E)) ≤ q+(I.map (fun i => (H (g i)).period)).sum ∧
      textWord A (H (g i₀)).start (H (g i₀)).stop ∈ requestPath U (E i₀) (I.map E) ∧
      ∀ i ∈ I, textWord (H (g i)).text (H (g i)).start (R i).stop ∈ requestPath U (E i₀) (I.map E) := by
  classical
  let E := entryOf H g R W tag
  let z := g i₀
  have shifts (j : ι) : ∃ m : ℤ,
      normalDelta q (H j).start (H j).stop (H z).start (H z).stop = m*q ∧
      (H z).start ≤ (H j).start+m*q ∧ (H j).start+m*q ≤ (H z).start+q ∧
      (H z).stop ≤ (H j).stop+m*q ∧ (H j).stop+m*q ≤ (H z).stop+q :=
    normalDelta_spec D hq (H j).first_le (H j).le_last (H z).first_le (H z).le_last
  choose m hm hb using shifts
  have hmz : m z = 0 := by
    have hz := hm z
    rw [normalDelta_self] at hz
    have : (0:ℤ) < q := by omega
    nlinarith
  let H' := fun j => (H j).translate per (m j)
  let R' := fun i => (R i).translate per (m (g i))
  let W' := fun j => PeriodWord.shift (W j) (m j*q)
  let E' := entryOf H' g R' W' tag
  have hW' (j : ι) : (W' j).length = (H' j).period := by simp [W',H',HostedGroup.translate,hW]
  have hWt' (j : ι) : PeriodWord.text (W' j) = (H' j).text := by
    dsimp only [W']
    rw [PeriodWord.text_shift (by rw [hW]; exact (H j).positive),hWt]
    rfl
  have hbase : E' i₀ = E i₀ := by
    simp only [E',E,entryOf,H',R',W',HostedGroup.translate,HostedGroup.Request.translate,
      show g i₀ = z from rfl,hmz,zero_mul,PeriodWord.shift_zero,add_zero]
  have hmap (i : κ) : normalizeEntry U.length (E i₀) (E i) = E' i := by
    simp only [normalizeEntry,E,E',entryOf,Entry.start,Entry.stop,hU,show g i₀ = z from rfl,hm]
    rfl
  have hd : ∀ i j, i ≠ j → ∀ c, (H' i).text ≠ fun x => (H' j).text (x+c) := by
    intro i j hij c he
    apply different i j hij (m i*q+c-m j*q)
    funext x
    have hh := congrFun he (x+m i*q)
    change (H i).text (x+m i*q-m i*q) = (H j).text (x+m i*q+c-m j*q) at hh
    have hx : x+m i*q+c-m j*q = x+(m i*q+c-m j*q) := by omega
    simpa only [add_sub_cancel_right,hx] using hh
  have ho : ∀ i ∈ I,
      (H' (g i₀)).start ≤ (H' (g i)).start ∧ (H' (g i)).start ≤ (H' (g i₀)).start+q ∧
      (H' (g i₀)).stop ≤ (H' (g i)).stop ∧ (H' (g i)).stop ≤ (H' (g i₀)).stop+q := by
    intro i _
    simpa only [H',HostedGroup.translate,show g i₀ = z from rfl,hmz,zero_mul,add_zero] using hb (g i)
  have hrq : ∀ i ∈ I, g i = g i₀ → (R' i₀).stop ≤ (R' i).stop := by
    intro i hi hg
    have hh := hreq i hi hg
    change (R i₀).stop+m (g i₀)*q ≤ (R i).stop+m (g i)*q
    have hm' := congrArg m hg
    rw [hm']
    exact Int.add_le_add_right hh _
  obtain ⟨hr,hc,hb',hv⟩ := normalized_spec closed D hq per letters H' g R' W' tag htag U hU hUt
    hW' hWt' (fun j x => child_letters j (x-m j*q)) hd I i₀ hi₀ hmin hrq ho
  have hpath : requestPath U (E i₀) (I.map E) = normalized U (E' i₀) (I.map E') := by
    unfold requestPath
    rw [List.map_map,hbase]
    apply congrArg (normalized U (E i₀))
    apply List.map_congr_left
    intro i _
    exact hmap i
  change Runs V [] [] (requestPath U (E i₀) (I.map E)) ∧ _
  rw [hpath]
  refine ⟨hr,hc,?_,?_⟩
  · have ha : (H' (g i₀)).start = (H (g i₀)).start := by
      simp only [H',HostedGroup.translate,show g i₀ = z from rfl,hmz,zero_mul,add_zero]
    have hb₀ : (H' (g i₀)).stop = (H (g i₀)).stop := by
      simp only [H',HostedGroup.translate,show g i₀ = z from rfl,hmz,zero_mul,add_zero]
    change textWord A (H' (g i₀)).start (H' (g i₀)).stop ∈ normalized U (E' i₀) (I.map E') at hb'
    rwa [ha,hb₀] at hb'
  · intro i hi
    have hh := hv i hi
    have he : textWord (H' (g i)).text (H' (g i)).start (R' i).stop =
        textWord (H (g i)).text (H (g i)).start (R i).stop := by
      change textWord (fun x => (H (g i)).text (x-m (g i)*q))
        ((H (g i)).start+m (g i)*q) ((R i).stop+m (g i)*q) = _
      simpa only [sub_eq_add_neg,add_neg_cancel_right] using
        textWord_reindex (H (g i)).text (-(m (g i)*q))
          ((H (g i)).start+m (g i)*q) ((R i).stop+m (g i)*q)
    rwa [he] at hh
theorem requestPool_complete {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (hU : U.length = q) (hUt : PeriodWord.text U = A)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (I : List κ) (hne : I ≠ []) :
    ∃ P ∈ requestPool U (I.map (entryOf H g R W tag)),
      Runs V [] [] P ∧ cost P ≤ q+(I.map (fun i => (H (g i)).period)).sum ∧
      (∃ w ∈ D.Content, w ∈ P) ∧
      ∀ i ∈ I, ∃ w ∈ (R i).layer.Content, w ∈ P := by
  classical
  have hne' : I.toFinset.Nonempty := by
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil I hne
    exact ⟨i,List.mem_toFinset.mpr hi⟩
  obtain ⟨i₀,hi₀,hmin⟩ := I.toFinset.exists_min_image (fun i => (H (g i)).period) hne'
  let J := I.toFinset.filter (fun i => g i = g i₀)
  have hj₀ : i₀ ∈ J := by simp [J,hi₀]
  obtain ⟨i₁,hi₁,hr⟩ := J.exists_min_image (fun i => (R i).stop) ⟨i₀,hj₀⟩
  have hi₁I : i₁ ∈ I := List.mem_toFinset.mp (Finset.mem_filter.mp hi₁).1
  have he : g i₁ = g i₀ := (Finset.mem_filter.mp hi₁).2
  have hm : ∀ i ∈ I, (H (g i₁)).period ≤ (H (g i)).period := by
    intro i hi
    rw [he]
    exact hmin i (List.mem_toFinset.mpr hi)
  have hr' : ∀ i ∈ I, g i = g i₁ → (R i₁).stop ≤ (R i).stop := by
    intro i hi hg
    exact hr i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi,hg.trans he⟩)
  obtain ⟨hP,hc,hb,hv⟩ := requestPath_spec closed D hq per letters H g R W tag htag U hU hUt
    hW hWt child_letters different I i₁ hi₁I hm hr'
  refine ⟨_,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨i₁,hi₁I,rfl⟩,rfl⟩,hP,hc,?_,?_⟩
  · exact ⟨_,⟨_,_,(H (g i₁)).first_le,(H (g i₁)).le_last,rfl⟩,hb⟩
  · intro i hi
    exact ⟨_,⟨_,_,(R i).first_le,(R i).le_last,rfl⟩,hv i hi⟩
end Superstring.HostCode


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α ι : Type} [Inhabited α] [DecidableEq α]
abbrev LayerData (α : Type) := List α × List ℕ

def saturateAll (D : List (LayerData α)) (P : Walk α) : Walk α :=
  fill P (D.map (fun d => turn d.1 d.2))

theorem saturateAll_spec {V : Set (List α)} (closed : SubstringClosed V)
    (A : ι → ℤ → α) (p : ι → ℕ) (L : ∀ i, Layer V (A i) (p i))
    (D : ι → LayerData α) (I : List ι) (rep : ∀ i ∈ I, Represents (D i).1 (D i).2 (L i))
    (pos : ∀ i ∈ I, 0 < p i) (per : ∀ i ∈ I, Function.Periodic (A i) (p i : ℤ))
    {P : Walk α} {s t : List α} (hP : Runs V s t P)
    (touch : ∀ i ∈ I, ∃ w ∈ (L i).Content, w ∈ P) :
    Runs V s t (saturateAll (I.map D) P) ∧
      cost (saturateAll (I.map D) P) = cost P+(I.map p).sum ∧
      (∀ w ∈ P, w ∈ saturateAll (I.map D) P) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ saturateAll (I.map D) P := by
  have hturn i hi := turn_spec (rep i hi) closed (pos i hi) (per i hi)
  have hm : (I.map D).map (fun d => turn d.1 d.2) = I.map (fun i => turn (D i).1 (D i).2) := List.map_map ..
  obtain ⟨hF,hFc,hFv⟩ := fill_spec P (I.map (fun i => turn (D i).1 (D i).2)) hP
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ; exact ⟨_,(hturn i hi).1⟩)
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ
        obtain ⟨w,hw,hwP⟩ := touch i hi
        exact ⟨w,hwP,(hturn i hi).2.2 w hw⟩)
  unfold saturateAll
  rw [hm]
  refine ⟨hF,?_,fun w hw => (hFv w).mpr (Or.inl hw),?_⟩
  · rw [List.map_map] at hFc
    have hh : I.map (fun i => cost (turn (D i).1 (D i).2)) = I.map p :=
      List.map_congr_left (fun i hi => (hturn i hi).2.1)
    exact hFc.trans (congrArg (fun l : List ℕ => cost P+l.sum) hh)
  · intro i hi w hw
    exact (hFv w).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,(hturn i hi).2.2 w hw⟩)

variable [Coded α]
@[fun_prop] theorem poly_saturateAll : Poly (fun q : List (LayerData α) × Walk α => saturateAll q.1 q.2) := by
  unfold saturateAll
  have ht : Poly (fun D : List (LayerData α) => D.map (fun d => turn d.1 d.2)) := BitCode.Poly.map poly_turn
  fun_prop
end Superstring.LayerArray

end OAI
