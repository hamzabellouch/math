import Mathlib
import OAI.GroupTheory.PeriodicGroups.Algebra.WordAlgebra

namespace OAI

section
universe u v w
namespace SourceBurnside.HierarchyGrowth
open scoped BigOperators

def height (H D n : ℕ) : ℕ := H * D ^ n

def dimension (d k : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => d
  | n+1 => k * s n ^ k * dimension d k s n

def exponent (H D d k c n : ℕ) : ℕ :=
  d + k*n + k*c * ∑ i ∈ Finset.range n, height H D i

lemma height_succ (H D n : ℕ) : height H D (n+1) = D * height H D n := by
  simp [height, pow_succ]; ring

lemma exponent_succ (H D d k c n : ℕ) :
    exponent H D d k c (n+1) = k + c * height H D n * k + exponent H D d k c n := by
  simp [exponent, Finset.sum_range_succ]; ring

lemma dimension_bound (H D d k c : ℕ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) (n : ℕ) :
    dimension d k s n ≤ 2 ^ exponent H D d k c n := by
  induction n with
  | zero => simpa [dimension, exponent] using (Nat.lt_two_pow_self (n := d)).le
  | succ n ih =>
    have hk : k ≤ 2^k := (Nat.lt_two_pow_self (n := k)).le
    calc
      dimension d k s (n+1) = k * s n ^ k * dimension d k s n := rfl
      _ ≤ 2^k * (2 ^ (c * height H D n)) ^ k * 2 ^ exponent H D d k c n :=
        Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left (hs n) k)) ih
      _ = 2 ^ exponent H D d k c (n+1) := by
        simp only [← pow_mul, ← pow_add, exponent_succ]

lemma geometric_identity (H D n : ℕ) (hD : 1 ≤ D) :
    H + (D-1) * (∑ i ∈ Finset.range n, height H D i) = height H D n := by
  induction n with
  | zero => simp [height]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ← Nat.add_assoc, ih, height_succ]
    have hD' : D-1+1 = D := Nat.sub_add_cancel hD
    nlinarith

lemma source_choice (c k D : ℕ) (hD : 10*(c+1)*(k+1) < D) :
    4 ≤ D ∧ 4*k*c ≤ D-1 := by
  constructor
  · nlinarith
  · have hx : 4*k*c < D := by nlinarith
    omega

theorem stopping_index (H D d k c : ℕ) (s : ℕ → ℕ)
    (hH : 1 ≤ H) (hD : 10*(c+1)*(k+1) < D)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) :
    ∃ n, 400*k*(dimension d k s n)^2 < 2 ^ height H D n := by
  obtain ⟨hD4, hDcharge⟩ := source_choice c k D hD
  let L := 400*k
  let n := 2*L + 4*d + 4*k + 2
  have hn : n < 2^n := Nat.lt_two_pow_self
  have hnheight : n^2 < height H D n := by
    calc
      n^2 < (2^n)^2 := Nat.pow_lt_pow_left hn (by decide)
      _ = 4^n := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
      _ ≤ D^n := Nat.pow_le_pow_left hD4 n
      _ ≤ H*D^n := Nat.le_mul_of_pos_left _ hH
  have hfree : 2*L + 4*d + 4*k*n < height H D n := by
    have hnlarge : 2*L + 4*d + 4*k + 2 = n := rfl
    nlinarith
  have hcharge : 4*k*c*(∑ i ∈ Finset.range n, height H D i) ≤ height H D n := by
    have hi := geometric_identity H D n (by omega)
    have hm := Nat.mul_le_mul_right (∑ i ∈ Finset.range n, height H D i) hDcharge
    omega
  have hexp : L + 2 * exponent H D d k c n < height H D n := by
    unfold exponent
    nlinarith
  refine ⟨n, ?_⟩
  calc
    400*k*(dimension d k s n)^2 ≤ 2^L * (2 ^ exponent H D d k c n)^2 :=
      Nat.mul_le_mul (Nat.lt_two_pow_self (n := L)).le
        (Nat.pow_le_pow_left (dimension_bound H D d k c s hs n) 2)
    _ = 2 ^ (L + 2 * exponent H D d k c n) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ < 2 ^ height H D n := Nat.pow_lt_pow_right (by decide) hexp

end SourceBurnside.HierarchyGrowth

namespace SourceBurnside.WeightedTests

open scoped BigOperators
noncomputable section
open Classical

variable {Γ : Type u} [Fintype Γ] {R : Type v} [Semiring R]

def product {r : ℕ} (f : Γ → R) (v : Fin r → Γ) : R :=
  (List.ofFn (f ∘ v)).prod

def length {r : ℕ} (l : Γ → ℕ) (v : Fin r → Γ) : ℕ := ∑ i, l (v i)

omit [Fintype Γ] in
lemma length_ge (l : Γ → ℕ) (hl : ∀ c, 1 ≤ l c) {r : ℕ} (v : Fin r → Γ) :
    r ≤ length l v := by
  calc
    r = ∑ _i : Fin r, (1 : ℕ) := by simp
    _ ≤ ∑ i : Fin r, l (v i) := Finset.sum_le_sum (fun i _ => hl (v i))

lemma sum_product_eq_pow (f : Γ → R) (r : ℕ) :
    (∑ v : Fin r → Γ, product f v) = (∑ c, f c) ^ r := by
  induction r with
  | zero => simp [product]
  | succ r ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (r+1) => Γ)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, product, Function.comp_def,
      List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    simp only [product, Function.comp_def] at ih
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ih, pow_succ']

def lengthPolynomial (l : Γ → ℕ) (f : Γ → R) (n : ℕ) : Polynomial R :=
  ∑ r ∈ Finset.range (n+1), ∑ v : Fin r → Γ,
    if length l v = n then Polynomial.monomial r (product f v) else 0

lemma coefficient_lengthPolynomial (l : Γ → ℕ) (f : Γ → R) {n r : ℕ}
    (hr : r ≤ n) :
    (lengthPolynomial l f n).coeff r =
      ∑ v : Fin r → Γ, if length l v = n then product f v else 0 := by
  unfold lengthPolynomial
  simp only [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single r]
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  · intro b _ hbr
    apply Finset.sum_eq_zero
    intro v _
    split_ifs <;> simp [Polynomial.coeff_monomial, hbr]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))).elim

theorem nilpotent_of_eventually_zero_lengthPolynomial
    (l : Γ → ℕ) (hl : ∀ c, 1 ≤ l c) (f : Γ → R)
    (h : ∃ N, ∀ n, N ≤ n → lengthPolynomial l f n = 0) :
    IsNilpotent (∑ c, f c) := by
  obtain ⟨N, hN⟩ := h
  let r := N + 1
  let lens : Finset ℕ := Finset.univ.image (length (r := r) l)
  have hfiber : ∀ n ∈ lens,
      (∑ v : Fin r → Γ, if length l v = n then product f v else 0) = 0 := by
    intro n hn
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hn
    have hrn : r ≤ n := hv ▸ length_ge l hl v
    rw [← coefficient_lengthPolynomial l f hrn, hN n (by omega)]
    exact Polynomial.coeff_zero r
  refine ⟨r, ?_⟩
  rw [← sum_product_eq_pow f r]
  have hp := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := lens)
    (g := length (r := r) l) (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    (product f)
  rw [← hp]
  apply Finset.sum_eq_zero
  intro n hn
  simpa only [Finset.sum_filter] using hfiber n hn

end
end SourceBurnside.WeightedTests

namespace SourceBurnside.Cuts
open Classical
noncomputable section
variable {α : Type*}

def parse (cut : α → Prop) : List α → List α × List (List α)
  | [] => ([],[])
  | a::w =>
    let p := parse cut w
    if cut a then ([],(a::p.1)::p.2) else (a::p.1,p.2)

def NoCut (cut : α → Prop) (w : List α) : Prop := ∀ a ∈ w, ¬ cut a

def Interval (cut : α → Prop) (w : List α) : Prop :=
  ∃ a t, w=a::t ∧ cut a ∧ NoCut cut t

lemma parse_join (cut : α → Prop) (w : List α) :
    (parse cut w).1 ++ (parse cut w).2.flatten = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [parse]
    split <;> simpa only [List.nil_append, List.flatten_cons, List.cons_append] using
      congrArg (List.cons a) ih

lemma parse_prefix (cut : α → Prop) (w : List α) : NoCut cut (parse cut w).1 := by
  induction w with
  | nil => simp [parse,NoCut]
  | cons a w ih =>
    by_cases ha : cut a
    · simp [parse,ha,NoCut]
    · simp only [parse,ite_eq_right ha]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih x hx

lemma parse_intervals (cut : α → Prop) (w : List α) :
    ∀ t ∈ (parse cut w).2, Interval cut t := by
  induction w with
  | nil => simp [parse]
  | cons a w ih =>
    by_cases ha : cut a
    · simp only [parse,ite_eq_left ha]
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨a,(parse cut w).1,rfl,ha,parse_prefix cut w⟩
      · exact ih t ht
    · simpa only [parse,ite_eq_right ha] using ih

lemma parse_noCut_append (cut : α → Prop) (p w : List α) (hp : NoCut cut p) :
    parse cut (p++w) = (p++(parse cut w).1,(parse cut w).2) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht : NoCut cut p := fun x hx => hp x (by simp [hx])
    simp only [List.cons_append,parse,ih ht,ite_eq_right ha]

lemma parse_interval_append (cut : α → Prop) (t w : List α) (ht : Interval cut t) :
    parse cut (t++w) = ([],(t++(parse cut w).1)::(parse cut w).2) := by
  obtain ⟨a,p,rfl,ha,hp⟩ := ht
  simp only [List.cons_append,parse,parse_noCut_append cut p w hp,ite_eq_left ha]

lemma parse_intervals_flatten (cut : α → Prop) (ts : List (List α))
    (ht : ∀ t ∈ ts, Interval cut t) : parse cut ts.flatten = ([],ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have h0 := ht t (by simp)
    have h1 := ih (fun u hu => ht u (by simp [hu]))
    simp only [List.flatten_cons,parse_interval_append cut t _ h0,h1,List.append_nil]

theorem parse_language (cut : α → Prop) (p s : List α) (ts : List (List α))
    (hp : NoCut cut p) (hs : Interval cut s) (ht : ∀ t ∈ ts, Interval cut t) :
    parse cut (p++ts.flatten++s) = (p,ts++[s]) := by
  rw [List.append_assoc]
  have h := parse_intervals_flatten cut (ts++[s]) (by
    intro t hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ht t hm
    · simpa using (List.mem_singleton.mp hm) ▸ hs)
  simp only [List.flatten_append,List.flatten_singleton] at h
  rw [parse_noCut_append cut p (ts.flatten++s) hp,h]
  simp

theorem language_injective (cut : α → Prop)
    {p s p' s' : List α} {ts ts' : List (List α)}
    (hp : NoCut cut p) (hs : Interval cut s) (ht : ∀ t ∈ ts, Interval cut t)
    (hp' : NoCut cut p') (hs' : Interval cut s') (ht' : ∀ t ∈ ts', Interval cut t)
    (he : p++ts.flatten++s = p'++ts'.flatten++s') :
    p=p' ∧ ts=ts' ∧ s=s' := by
  have h := congrArg (parse cut) he
  rw [parse_language cut p s ts hp hs ht,parse_language cut p' s' ts' hp' hs' ht'] at h
  have hp0 := congrArg Prod.fst h
  have ht0 := congrArg Prod.snd h
  exact ⟨hp0,List.append_singleton_inj.mp ht0⟩

end
end SourceBurnside.Cuts
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax Cuts
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

def Token (S : Schedule q) (d : ℕ) (t : List (Cell q)) : Prop :=
  Cuts.Interval Cell.Cut t ∧ ∃b, b.Cut ∧ Survives S d (t++[b])
def fragmentBound (q : ℕ) := 12*(17*q+3)
lemma token_normal_form {t : List (Cell q)} (ht : Token S d t) (hd : d≤q) :
    ∃u : List (Fin d → ZMod 2), 1≤u.length ∧ u.length≤10 ∧
      t.length=(2*q+1)*u.length ∧ Reach S d t (encodeWord u) := by
  obtain ⟨⟨a,w,rfl,ha,hn⟩,b,hb,hw⟩ := ht
  exact hw.token_normalization ha hb hn hd
lemma token_length_le {t : List (Cell q)} (ht : Token S d t) : t.length≤fragmentBound q := by
  obtain ⟨⟨a,w,rfl,_,hn⟩,b,_,hw⟩ := ht
  exact cut_free_fragment_bound (hw.infix ⟨[],[b],by simp⟩) hn
lemma finite_tokens : {t : List (Cell q) | Token S d t}.Finite :=
  (List.finite_length_le (Cell q) (fragmentBound q)).subset (fun _ h => token_length_le h)
lemma flatten_member_infix {α : Type*} {v : List α} {vs : List (List α)} (hv : v∈vs) :
    v <:+: vs.flatten := by
  obtain ⟨p,s,rfl⟩ := List.mem_iff_append.mp hv
  exact ⟨p.flatten,s.flatten,by simp⟩
lemma token_of_adjacent {t s : List (Cell q)} (ht : Cuts.Interval Cell.Cut t)
    (hs : Cuts.Interval Cell.Cut s) (hw : Survives S d (t++s)) : Token S d t := by
  obtain ⟨b,w,rfl,hb,_⟩ := hs
  exact ⟨ht,b,hb,hw.infix ⟨[],w,by simp⟩⟩
lemma tokens_of_flatten {ts : List (List (Cell q))} {s : List (Cell q)}
    (hs : Cuts.Interval Cell.Cut s) (ht : ∀t∈ts,Cuts.Interval Cell.Cut t)
    (hw : Survives S d (ts.flatten++s)) : ∀t∈ts,Token S d t := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have htt := ht t (by simp)
    have hts := fun u hu => ht u (List.mem_cons_of_mem _ hu)
    have hwts : Survives S d (ts.flatten++s) := hw.infix ⟨t,[],by simp⟩
    have htok : Token S d t := by
      cases ts with
      | nil => exact token_of_adjacent htt hs (by simpa using hw)
      | cons u us =>
        apply token_of_adjacent htt (hts u (by simp))
        exact hw.infix ⟨[],us.flatten++s,by simp [List.append_assoc]⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact htok
    · exact ih hts hwts u hu

theorem Survives.token_decomposition {w : List (Cell q)} (hw : Survives S d w)
    (hlong : 2*fragmentBound q<w.length) :
    ∃p ts s, w=p++ts.flatten++s ∧ Cuts.NoCut Cell.Cut p ∧
      Cuts.Interval Cell.Cut s ∧ p.length≤fragmentBound q ∧ s.length≤fragmentBound q ∧
      ts≠[] ∧ ∀t∈ts,Token S d t := by
  generalize he : Cuts.parse Cell.Cut w = pr
  obtain ⟨p,vs⟩ := pr
  have hj := Cuts.parse_join Cell.Cut w
  have hp := Cuts.parse_prefix Cell.Cut w
  have ht := Cuts.parse_intervals Cell.Cut w
  rw [he] at hj hp ht
  dsimp only at hj hp ht
  cases vs using List.reverseRecOn with
  | nil =>
    simp only [List.flatten_nil,List.append_nil] at hj
    subst w
    have hb := cut_free_fragment_bound hw (fun c hc => hp c (List.mem_of_mem_tail hc))
    change p.length≤fragmentBound q at hb
    omega
  | append_singleton ts s =>
    simp only [List.flatten_append,List.flatten_singleton] at hj
    have hs := ht s (by simp)
    have hps : Survives S d p := hw.infix ⟨[],ts.flatten++s,by simpa using hj⟩
    have hss : Survives S d s := hw.infix ⟨p++ts.flatten,[],by simpa [List.append_assoc] using hj⟩
    have hpbound : p.length≤fragmentBound q :=
      cut_free_fragment_bound hps (fun c hc => hp c (List.mem_of_mem_tail hc))
    have hsbound : s.length≤fragmentBound q := by
      obtain ⟨a,v,rfl,_,hn⟩ := hs
      exact cut_free_fragment_bound hss hn
    have hwts : Survives S d (ts.flatten++s) := hw.infix ⟨p,[],by simpa using hj⟩
    refine ⟨p,ts,s,by simpa [List.append_assoc] using hj.symm,hp,hs,hpbound,hsbound,?_,?_⟩
    · intro he
      subst ts
      have hlen := congrArg List.length hj
      simp at hlen
      omega
    · exact tokens_of_flatten hs (fun t h => ht t (List.mem_append_left _ h)) hwts
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}
lemma Survives.palette_rank_mono {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) {i j : ℕ} (hi : i<w.length) (hj : j<w.length) (hij : i ≤ j) :
    w[i].paletteRank ≤ w[j].paletteRank := by
  rcases eq_or_lt_of_le hij with rfl|hl
  · rfl
  · have hc := (hw.palette_rank_chain hp).pairwise
    have HH := List.pairwise_iff_getElem.mp hc i j (by simpa) (by simpa) hl
    simpa using HH

lemma Survives.long_equal_rank {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) (hq : 16 ≤ q) (hql : q ≤ w.length) :
    ∃v : List (Cell q), v <:+: w  ∧  2 ≤ v.length  ∧  q ≤ 100*v.length  ∧
      ∀a∈v,∀b∈v,a.paletteRank=b.paletteRank := by
  let m := max 2 ((q+99)/100)
  have hm : 2 ≤ m := le_max_left _ _
  have hqm : q ≤ 100*m := by
    have hd := Nat.mod_add_div (q+99) 100
    have hr := Nat.mod_lt (q+99) (by decide : 0<100)
    have hl := le_max_right 2 ((q+99)/100)
    dsimp [m]; omega
  have h6 : 6*m<q := by
    have hd := Nat.mod_add_div (q+99) 100
    have hl := Nat.zero_le ((q+99)%100)
    dsimp [m]
    rcases le_total 2 ((q+99)/100) with h|h
    · rw [max_eq_right h]
      omega
    · rw [max_eq_left h]
      omega
  let f : Fin 7  →  Fin 6 := fun i =>
    ⟨(w[i.val*m]'(by have := i.isLt; nlinarith)).paletteRank,Cell.paletteRank_lt _⟩
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by decide)
  have hi : i.val*m<w.length := by have := i.isLt; nlinarith
  have hj : j.val*m<w.length := by have := j.isLt; nlinarith
  have he' : (w[i.val*m]'hi).paletteRank=(w[j.val*m]'hj).paletteRank := congrArg Fin.val he
  have hab : ∃a b : ℕ, ∃(ha : a<w.length) (hb : b<w.length), a<b ∧ m ≤ b+1-a ∧
      (w[a]'ha).paletteRank=(w[b]'hb).paletteRank := by
    rcases lt_or_gt_of_ne (show i.val≠j.val from fun h => hne (Fin.ext h)) with h|h
    · refine ⟨i.val*m,j.val*m,hi,hj,by nlinarith,?_,he'⟩
      have H : i.val*m+m ≤ j.val*m := by nlinarith
      omega
    · refine ⟨j.val*m,i.val*m,hj,hi,by nlinarith,?_,he'.symm⟩
      have H : j.val*m+m ≤ i.val*m := by nlinarith
      omega
  obtain ⟨a,b,ha,hb,hab,hml,heab⟩ := hab
  let v := (w.drop a).take (b+1-a)
  have hlen : v.length=b+1-a := by simp [v,List.length_take,List.length_drop]; omega
  have hv : v <:+: w := by
    refine ⟨w.take a,(w.drop a).drop (b+1-a),?_⟩
    simp only [v,List.append_assoc,List.take_append_drop]
  refine ⟨v,hv,by omega,by nlinarith,?_⟩
  have hval : ∀c∈v,c.paletteRank=(w[a]'(by omega)).paletteRank := by
    intro c hc
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hc
    have hk' : a+k ≤ b := by rw [hlen] at hk; omega
    have hwk : a+k<w.length := by omega
    have hvk : (v[k]'hk)=(w[a+k]'hwk) := by simp [v,List.getElem_take,List.getElem_drop]
    rw [hvk]
    have h1 := hw.palette_rank_mono hp (by omega : a<w.length) hwk (by omega : a ≤ a+k)
    have h2 := hw.palette_rank_mono hp hwk hb hk'
    omega
  intro c hc e he
  exact (hval c hc).trans (hval e he).symm

lemma Survives.equal_rank_eligible {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) (hn : 2 ≤ w.length)
    (hr : ∀a∈w,∀b∈w,a.paletteRank=b.paletteRank) :
    ∃c, ∀a∈w,a.eraseColor=c  ∧  a.HeadFree := by
  have hc : w.IsChain (fun a b => a.eraseColor=b.eraseColor  ∧  a.HeadFree  ∧  b.HeadFree) :=
    hw.chain.imp_of_mem_imp (by
      intro a b ha hb hab
      exact palette_equal_rank (hp a ha) (hp b hb) (hw.format ha) (hw.format hb) hab (hr a ha b hb))
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b w =>
      obtain ⟨hab,ht⟩ := List.isChain_cons_cons.mp hc
      refine ⟨a.eraseColor,?_⟩
      have hh : ∀c∈b::w,c.eraseColor=a.eraseColor  ∧  c.HeadFree := by
        have hb : b.eraseColor=a.eraseColor  ∧  b.HeadFree := ⟨hab.1.symm,hab.2.2⟩
        clear hp hw hr hn hc hab
        induction w generalizing b with
        | nil => simpa using hb
        | cons c w ih =>
          obtain ⟨hbc,hw⟩ := List.isChain_cons_cons.mp ht
          intro e he
          rcases List.mem_cons.mp he with rfl|he
          · exact hb
          · exact ih c hw ⟨hbc.1.symm.trans hb.1,hbc.2.2⟩ e he
      intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact ⟨rfl,hab.2.1⟩
      · exact hh c hc

theorem Survives.palette_long_eligible {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) (hq : 16 ≤ q) (hql : q ≤ w.length) :
    ∃v : List (Cell q),v <:+: w  ∧  2 ≤ v.length  ∧  q ≤ 100*v.length  ∧
      ∃c,∀a∈v,a.isPalette  ∧  a.eraseColor=c  ∧  a.HeadFree := by
  obtain ⟨v,hv,hn,hqv,hr⟩ := hw.long_equal_rank hp hq hql
  have hpv : ∀c∈v,c.isPalette := fun c hc => hp c (hv.sublist.subset hc)
  obtain ⟨c,hc⟩ := (hw.infix hv).equal_rank_eligible hpv hn hr
  exact ⟨v,hv,hn,hqv,c,fun a ha => ⟨hpv a ha,hc a ha⟩⟩
namespace StructuralBlock
variable (B : StructuralBlock q)
lemma palette_card_le (hw : Survives S d B.word) : q ≤ B.palette.length := by
  obtain ⟨p,c,hcores,hcp⟩ := B.core_ends
  have ht : q-1+1=q := by have := NeZero.pos q; omega
  have hwpal : Survives S d (c::B.palette++[B.stop]) :=
    hw.infix ⟨p,[],by simp [word,hcores,List.append_assoc]⟩
  have hc := hwpal.palette_all_colors hcp ht B.stop_position B.palette_nonempty B.palette_positions
  have hcard : (Finset.univ : Finset (Fin q))⊆(B.palette.map Cell.color).toFinset := by
    intro x _
    exact List.mem_toFinset.mpr (hc x)
  have hl := (Finset.card_le_card hcard).trans (List.toFinset_card_le _)
  simpa using hl
end StructuralBlock
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax Cuts
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}
lemma token_contains_block {t : List (Cell q)} (ht : Token S d t) :
    ∃B : StructuralBlock q, B.word <:+: t ∧ Survives S d B.word := by
  obtain ⟨hinterval,b,hb,hw⟩ := ht
  obtain ⟨a,v,rfl,ha,_⟩ := hinterval
  have hw' : Survives S d (a::v) := hw.infix ⟨[],[b],by simp⟩
  have hstruct : StructuralChain (a::v) := hw'.chain.imp (fun _ _ h => h.1.1)
  obtain ⟨bs,he⟩ := structural_decompose (a::v) hstruct (by simpa [StartsCore] using ha.1)
    (hw.before_cut_end hb).1
  cases bs with
  | nil => simp at he
  | cons B bs =>
    have hi : B.word <:+: a::v := ⟨[],bs.flatMap StructuralBlock.word,by simpa using he.symm⟩
    exact ⟨B,hi,hw'.infix hi⟩

lemma token_long_eligible {t : List (Cell q)} (ht : Token S d t) (hq : 16 ≤ q) :
    ∃v : List (Cell q),v <:+: t ∧ 2 ≤ v.length ∧ q ≤ 100*v.length ∧
      ∃c,∀a∈v,a.isPalette ∧ a.eraseColor=c ∧ a.HeadFree := by
  obtain ⟨B,hB,hw⟩ := token_contains_block ht
  have hpal : B.palette <:+: B.word := ⟨B.cores,[B.stop],rfl⟩
  obtain ⟨v,hv,hn,hqv,hall⟩ := (hw.infix hpal).palette_long_eligible B.palette_positions hq (B.palette_card_le hw)
  exact ⟨v,hv.trans (hpal.trans hB),hn,hqv,hall⟩

theorem Survives.long_eligible {w : List (Cell q)} (hw : Survives S d w) (hq : 16 ≤ q)
    (hlong : 2*fragmentBound q<w.length) :
    ∃v : List (Cell q),v <:+: w ∧ 2 ≤ v.length ∧ q ≤ 100*v.length ∧
      ∃c,∀a∈v,a.isPalette ∧ a.eraseColor=c ∧ a.HeadFree := by
  obtain ⟨p,ts,s,he,_,_,_,_,htn,ht⟩ := hw.token_decomposition hlong
  cases ts with
  | nil => contradiction
  | cons t ts =>
    obtain ⟨v,hv,hn,hqv,hall⟩ := token_long_eligible (ht t (by simp)) hq
    have htw : t <:+: w := ⟨p,ts.flatten++s,by simpa [List.append_assoc] using he.symm⟩
    exact ⟨v,hv.trans htw,hn,hqv,hall⟩
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma Survives.infix {v w : List (Raw h)} (hw : Survives hh S d w) (hi : v <:+: w) :
    Survives hh S d v := by
  obtain ⟨a,b,rfl⟩ := hi
  intro p z s hr hz
  exact hw (a++p) z (s++b) (by simpa [List.append_assoc] using reach_context hr a b) hz
lemma Survives.has_encoding (h4 : 4 ≤ h) {w : List (Raw h)} (hw : Survives hh S d w) :
    ∃v : List (Cell (2^h)),w=v.map encode ∧ FiniteTable.Survives S d v := by
  have H : ∀a∈w,∃c : Cell (2^h),a=encode c := by
    intro a ha
    obtain ⟨p,s,he⟩ := List.mem_iff_append.mp ha
    have haz : ¬unaryZero hh S d a := by
      apply hw p [a] s
      simpa [he] using (Relation.ReflTransGen.refl : Reach hh S d w w)
    cases hc : decode hh a with
    | none => exact (haz (by simp [unaryZero,hc])).elim
    | some c => exact ⟨c,(decode_eq_some_iff h4 a c).mp hc⟩
  have Hlist : ∃v : List (Cell (2^h)),w=v.map encode := by
    clear hw
    induction w with
    | nil => exact ⟨[],rfl⟩
    | cons a w ih =>
      obtain ⟨c,rfl⟩ := H a (by simp)
      obtain ⟨v,rfl⟩ := ih (fun b hb => H b (by simp [hb]))
      exact ⟨c::v,rfl⟩
  obtain ⟨v,rfl⟩ := Hlist
  exact ⟨v,rfl,(survives_encode_iff h4 v).mp hw⟩

def rawCut (hh : 0<h) (a : Raw h) : Prop := ∃c,decode hh a=some c ∧ c.Cut
lemma rawCut_encode (h4 : 4 ≤ h) (c : Cell (2^h)) : rawCut hh (encode c) ↔ c.Cut := by
  simp [rawCut,decode_encode h4]

def noncolor (c : Cell (2^h)) : Cell (2^h) := if c.isPalette then c.eraseColor else c
def fields (hh : 0<h) (a : Raw h) := (decode hh a).map noncolor
def eligibleFields (t : Option (Cell (2^h))) : Prop := ∃c,t=some c ∧ c.isPalette ∧ c.HeadFree
lemma fields_encode (h4 : 4 ≤ h) (c : Cell (2^h)) : fields hh (encode c)=some (noncolor c) := by
  simp [fields,decode_encode h4]
lemma erased_palette {q : ℕ} [NeZero q] (c : Cell q) (hp : c.isPalette) : c.eraseColor.isPalette := by
  obtain ⟨x,hx⟩ := hp
  exact ⟨0,rfl⟩
lemma erased_headfree {q : ℕ} [NeZero q] (c : Cell q) : c.eraseColor.HeadFree ↔ c.HeadFree := Iff.rfl
lemma Survives.long_uniform (h4 : 4 ≤ h) {w : List (Raw h)} (hw : Survives hh S d w)
    (hlong : 2*fragmentBound (2^h)<w.length) :
    ∃v : List (Raw h),v <:+: w ∧ 2 ≤ v.length ∧ 2^h ≤ 100*v.length ∧
      ∃t,eligibleFields t ∧ ∀a∈v,fields hh a=t := by
  obtain ⟨w',rfl,hw'⟩ := hw.has_encoding h4
  have hq : 16 ≤ 2^h := (show 16=2^4 from by norm_num) ▸ Nat.pow_le_pow_right (by decide) h4
  obtain ⟨v,hv,hn,hqv,c,hc⟩ := hw'.long_eligible hq (by simpa using hlong)
  have hvn : v≠[] := by intro h; simp [h] at hn
  obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil v hvn
  obtain ⟨hap,he,haf⟩ := hc a ha
  refine ⟨v.map encode,hv.map encode,by simpa,by simpa, some c,?_,?_⟩
  · exact ⟨c,rfl,he ▸ erased_palette a hap,(he ▸ (erased_headfree a).mpr haf)⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    rw [fields_encode h4,noncolor,ite_eq_left (hc a ha).1,(hc a ha).2.1]

def rawToken (_hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (t : List (Raw h)) : Prop :=
  ∃u : List (Cell (2^h)),FiniteTable.Token S d u ∧ t=u.map encode
lemma finite_rawTokens : {t : List (Raw h)|rawToken hh S d t}.Finite := by
  apply ((finite_tokens (S:=S) (d:=d)).image (List.map encode)).subset
  rintro t ⟨u,hu,rfl⟩
  exact ⟨u,hu,rfl⟩

lemma rawToken_interval (h4 : 4 ≤ h) {t : List (Raw h)} (ht : rawToken hh S d t) :
    Cuts.Interval (rawCut hh) t := by
  obtain ⟨u,hu,rfl⟩ := ht
  obtain ⟨a,v,rfl,ha,hn⟩ := hu.1
  refine ⟨encode a,v.map encode,rfl,(rawCut_encode h4 _).mpr ha,?_⟩
  intro c hc
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
  exact fun h => hn b hb ((rawCut_encode h4 _).mp h)
lemma rawToken_normalize (h4 : 4 ≤ h) {D : ℕ} (hd : 10000*(D*h) ≤ 2^h)
    {t : List (Raw h)} (ht : rawToken hh S (10000*(D*h)) t) :
    ∃u : List (Raw (D*h)),1 ≤ u.length ∧ u.length ≤ 10 ∧
      t.length=(2*(2^h)+1)*u.length ∧ Reach hh S (10000*(D*h)) t (SourceMachine.embedding h D u) := by
  obtain ⟨v,hv,rfl⟩ := ht
  obtain ⟨u,hn,hk,hlen,hr⟩ := token_normal_form hv hd
  refine ⟨u.map SourceMachine.bits,by simpa,by simpa,by simpa,?_⟩
  have hh := reach_encode h4 hr
  simpa [SourceMachine.embedding,List.map_map,Function.comp_def] using hh

theorem Survives.raw_token_decomposition (h4 : 4 ≤ h) {w : List (Raw h)} (hw : Survives hh S d w)
    (hlong : 2*fragmentBound (2^h)<w.length) :
    ∃p ts s, w=p++ts.flatten++s ∧ Cuts.NoCut (rawCut hh) p ∧
      Cuts.Interval (rawCut hh) s ∧ p.length ≤ fragmentBound (2^h) ∧ s.length ≤ fragmentBound (2^h) ∧
      ts≠[] ∧ ∀t∈ts,rawToken hh S d t := by
  obtain ⟨w',rfl,hw'⟩ := hw.has_encoding h4
  obtain ⟨p,ts,s,he,hp,hs,hpB,hsB,htn,ht⟩ := hw'.token_decomposition (by simpa using hlong)
  refine ⟨p.map encode,ts.map (List.map encode),s.map encode,?_,?_,?_,by simpa,by simpa,?_,?_⟩
  · simp [he,List.map_flatten]
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact fun h => hp a ha ((rawCut_encode h4 _).mp h)
  · obtain ⟨a,v,rfl,ha,hn⟩ := hs
    refine ⟨encode a,v.map encode,rfl,(rawCut_encode h4 _).mpr ha,?_⟩
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    exact fun h => hn b hb ((rawCut_encode h4 _).mp h)
  · simpa using htn
  · intro t ht'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht'
    exact ⟨u,ht u hu,rfl⟩
end
end SourceBurnside.FiniteTable.Codec

end

end OAI
