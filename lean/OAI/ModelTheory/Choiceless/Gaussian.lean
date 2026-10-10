import OAI.ModelTheory.Choiceless.Evaluation

namespace OAI

namespace CPTSeparation.Gaussian

abbrev Scalar := ZMod 3

structure Row (n : ℕ) where
  coeff : Fin n → Scalar
  rhs : Scalar

namespace Row

def satisfies {n} (r : Row n) (v : Fin n → Scalar) : Prop :=
  (∑ i, r.coeff i * v i) = r.rhs

def tail {n} (r : Row (n+1)) : Row n := ⟨fun i => r.coeff i.succ,r.rhs⟩

def reduce {n} (p r : Row (n+1)) : Row n :=
  ⟨fun i => r.coeff i.succ - (r.coeff 0 / p.coeff 0)*p.coeff i.succ,
    r.rhs - (r.coeff 0 / p.coeff 0)*p.rhs⟩

lemma satisfies_cons {n} (r : Row (n+1)) (x : Scalar) (v : Fin n → Scalar) :
    r.satisfies (Fin.cons x v) ↔
      r.coeff 0*x + (∑ i, r.coeff i.succ * v i) = r.rhs := by
  simp [satisfies,Fin.sum_univ_succ]

lemma tail_iff {n} (r : Row (n+1)) (h : r.coeff 0 = 0) (x : Scalar) (v : Fin n → Scalar) :
    r.satisfies (Fin.cons x v) ↔ r.tail.satisfies v := by
  rw [satisfies_cons,h]
  simp [satisfies,tail]

lemma pivot_solution {n} (p : Row (n+1)) (hp : p.coeff 0 ≠ 0) (v : Fin n → Scalar) :
    p.satisfies (Fin.cons ((p.rhs - ∑ i, p.coeff i.succ * v i)/p.coeff 0) v) := by
  rw [satisfies_cons]
  field_simp
  ring

lemma reduce_iff {n} (p r : Row (n+1)) (hp : p.coeff 0 ≠ 0)
    (x : Scalar) (v : Fin n → Scalar) (hpx : p.satisfies (Fin.cons x v)) :
    r.satisfies (Fin.cons x v) ↔ (p.reduce r).satisfies v := by
  rw [satisfies_cons] at hpx ⊢
  simp only [satisfies,reduce,sub_mul,Finset.sum_sub_distrib,
    mul_assoc,← Finset.mul_sum]
  have h : (r.coeff 0 / p.coeff 0)*p.coeff 0 = r.coeff 0 := div_mul_cancel₀ _ hp
  have heq : r.coeff 0*x + ∑ i, r.coeff i.succ*v i - r.rhs =
      (∑ i, r.coeff i.succ*v i) - (r.coeff 0/p.coeff 0)*(∑ i, p.coeff i.succ*v i) -
        (r.rhs-(r.coeff 0/p.coeff 0)*p.rhs) := by
    rw [← hpx]
    linear_combination -(x*h)
  exact (sub_eq_zero.symm.trans (iff_of_eq (congrArg (fun z => z = 0) heq))).trans sub_eq_zero

end Row

def Solvable {n} (rows : List (Row n)) : Prop := ∃ v, ∀ r ∈ rows, r.satisfies v

def pivot {n} (rows : List (Row (n+1))) : Option (Row (n+1)) :=
  rows.find? (fun r => r.coeff 0 != 0)

def solve : {n : ℕ} → List (Row n) → Bool
  | 0, rows => rows.all (fun r => r.rhs == 0)
  | _+1, rows => match pivot rows with
    | none => solve (rows.map Row.tail)
    | some p => solve (rows.map (Row.reduce p))

lemma pivot_some {n} {rows : List (Row (n+1))} {p : Row (n+1)} (h : pivot rows = some p) :
    p ∈ rows ∧ p.coeff 0 ≠ 0 := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

lemma pivot_none {n} {rows : List (Row (n+1))} (h : pivot rows = none) :
    ∀ r ∈ rows, r.coeff 0 = 0 := by
  simpa [pivot,List.find?_eq_none] using h

lemma solvable_tail {n} {rows : List (Row (n+1))} (h : pivot rows = none) :
    Solvable rows ↔ Solvable (rows.map Row.tail) := by
  have hz := pivot_none h
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun i => v i.succ,?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    have hv' : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; cases i using Fin.cases <;> rfl
    exact (Row.tail_iff s (hz s hs) (v 0) _).mp (hv' ▸ hv s hs)
  · rintro ⟨v,hv⟩
    refine ⟨Fin.cons 0 v,?_⟩
    intro r hr
    exact (Row.tail_iff r (hz r hr) 0 v).mpr (hv _ (List.mem_map_of_mem hr))

lemma solvable_reduce {n} {rows : List (Row (n+1))} {p : Row (n+1)}
    (h : pivot rows = some p) : Solvable rows ↔ Solvable (rows.map (Row.reduce p)) := by
  obtain ⟨hpm,hp⟩ := pivot_some h
  constructor
  · rintro ⟨v,hv⟩
    have hv' : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; cases i using Fin.cases <;> rfl
    refine ⟨fun i => v i.succ,?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact (Row.reduce_iff p s hp (v 0) _ (hv' ▸ hv p hpm)).mp (hv' ▸ hv s hs)
  · rintro ⟨v,hv⟩
    let x := (p.rhs - ∑ i, p.coeff i.succ * v i)/p.coeff 0
    refine ⟨Fin.cons x v,?_⟩
    intro r hr
    exact (Row.reduce_iff p r hp x v (Row.pivot_solution p hp v)).mpr
      (hv _ (List.mem_map_of_mem hr))

theorem solve_correct {n} (rows : List (Row n)) : solve rows = true ↔ Solvable rows := by
  induction n with
  | zero =>
    simp only [solve,List.all_eq_true,beq_iff_eq]
    constructor
    · intro h
      exact ⟨Fin.elim0,fun r hr => by simpa [Row.satisfies] using (h r hr).symm⟩
    · rintro ⟨v,hv⟩ r hr
      simpa [Row.satisfies] using (hv r hr).symm
  | succ n ih =>
    cases hp : pivot rows with
    | none => simpa only [solve,hp] using (ih (rows.map Row.tail)).trans (solvable_tail hp).symm
    | some p => simpa only [solve,hp] using (ih (rows.map (Row.reduce p))).trans (solvable_reduce hp).symm

namespace Row

def dense {n} (r : Row n) : Row n :=
  let a := Vector.ofFn r.coeff
  ⟨a.get,r.rhs⟩

@[simp] lemma dense_eq {n} (r : Row n) : r.dense = r := by
  cases r
  simp only [dense]
  congr 1
  funext i
  exact Vector.get_ofFn _ i

def reduceDense {n} (p r : Row (n+1)) : Row n :=
  let c := r.coeff 0 / p.coeff 0
  let a := Vector.ofFn (fun i : Fin n => r.coeff i.succ - c*p.coeff i.succ)
  ⟨a.get,r.rhs-c*p.rhs⟩

@[simp] lemma reduceDense_eq {n} (p r : Row (n+1)) : p.reduceDense r = p.reduce r := by
  simp only [reduceDense,reduce]
  congr 1
  funext i
  exact Vector.get_ofFn _ i

end Row

def metered : {n : ℕ} → List (Row n) → Bool × ℕ
  | 0, rows => (rows.all (fun r => r.rhs == 0),2*rows.length+1)
  | n+1, rows =>
    let next := match pivot rows with
      | none => metered (rows.map (fun (r : Row (n+1)) => r.tail.dense))
      | some p => metered (rows.map (Row.reduceDense p))
    (next.1, next.2 + (8*n+12)*rows.length+2)

@[simp] theorem metered_answer {n} (rows : List (Row n)) : (metered rows).1 = solve rows := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hp : pivot rows with
    | none => simp [metered,solve,hp,ih]
    | some p =>
      have he : p.reduceDense = p.reduce := funext (fun r => Row.reduceDense_eq p r)
      simp [metered,solve,hp,ih,he]

theorem metered_bound {n} (rows : List (Row n)) :
    (metered rows).2 ≤ 12*(rows.length+1)*(n+1)^2 := by
  induction n with
  | zero => simp [metered]; omega
  | succ n ih =>
    have hpoly : 12*(rows.length+1)*(n+1)^2+(8*n+12)*rows.length+2 ≤
        12*(rows.length+1)*(n+1+1)^2 := by nlinarith
    cases hp : pivot rows with
    | none =>
      have hi := ih (rows.map (fun (r : Row (n+1)) => r.tail.dense))
      simp only [List.length_map] at hi
      simp only [metered,hp]
      omega
    | some p =>
      have hi := ih (rows.map (Row.reduceDense p))
      simp only [List.length_map] at hi
      simp only [metered,hp]
      omega

theorem metered_correct {n} (rows : List (Row n)) :
    (metered rows).1 = true ↔ Solvable rows := by rw [metered_answer,solve_correct]

end CPTSeparation.Gaussian

namespace CPTSeparation.OrderedQuery

open Finset

variable {N : ℕ}

def coefficient (S : Data N) (y a : Fin N) : Scalar :=
  ∑ x, if S.rel .Ed x x ∧ S.rel .I a x then
    ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0 else 0

def incident (S : Data N) (t y : Fin N) : Bool :=
  (List.finRange N).any fun a => S.rel .Cf a a && S.rel .VB t a &&
    (List.finRange N).any fun x => S.rel .Ed x x && S.rel .I a x && S.rel .EB y x

def normalizationRow (S : Data N) (t : Fin N) : Gaussian.Row (N+N) := if S.rel .Cf t t then
  ⟨Fin.addCases (fun a => if S.rel .Cf a a && S.rel .VB t a then 1 else 0)
    (fun _ => 0),1⟩ else ⟨fun _ => 0,0⟩

def consistencyRow (S : Data N) (t y : Fin N) : Gaussian.Row (N+N) :=
  if S.rel .Cf t t && S.rel .Ed y y && incident S t y then
    ⟨Fin.addCases (fun a => if S.rel .Cf a a && S.rel .VB t a then -coefficient S y a else 0)
      (fun z => if z = y then 1 else 0),0⟩ else ⟨fun _ => 0,0⟩

def rows (S : Data N) : List (Gaussian.Row (N+N)) :=
  (List.finRange N).map (normalizationRow S) ++
    (List.finRange N).flatMap (fun t => (List.finRange N).map (consistencyRow S t))

def decideQuery (S : Data N) : Bool :=
  (Gaussian.metered ((rows S).map Gaussian.Row.dense)).1

lemma sum_subtype {A : Type} [Fintype A] [DecidableEq A] (p : A → Prop) [DecidablePred p]
    (f : A → Scalar) : (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

lemma coefficient_eq (S : Data N) (y : S.Edge) (a : S.Config) :
    coefficient S y a = S.coefficient y a := by
  unfold coefficient Input.coefficient
  rw [← sum_subtype (fun x => S.rel .Ed x x = true) (fun x => if S.rel .I a x then ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0 else 0)]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : S.rel .Ed x x = true <;> by_cases h' : S.rel .I a x = true <;> simp [h,h']

lemma incident_eq (S : Data N) (t : S.Config) (y : S.Edge) :
    incident S t y = true ↔ S.incident t y := by
  simp only [incident,List.any_eq_true,Bool.and_eq_true,List.mem_finRange,true_and,
    Input.incident]
  constructor
  · rintro ⟨a,⟨ha,hva⟩,x,⟨hx,hix⟩,hby⟩
    exact ⟨⟨a,ha⟩,hva,⟨x,hx⟩,hix,hby⟩
  · rintro ⟨a,hva,x,hix,hby⟩
    exact ⟨a,⟨a.property,hva⟩,x,⟨x.property,hix⟩,hby⟩

lemma row_zero (v : Fin (N+N) → Scalar) :
    (⟨fun _ => 0,0⟩ : Gaussian.Row (N+N)).satisfies v := by simp [Gaussian.Row.satisfies]

def left (v : Fin (N+N) → Scalar) (a : Fin N) := v (Fin.castAdd N a)

def right (v : Fin (N+N) → Scalar) (y : Fin N) := v (Fin.natAdd N y)

lemma normalization_satisfies (S : Data N) (t : Fin N) (v : Fin (N+N) → Scalar) :
    (normalizationRow S t).satisfies v ↔
      S.rel .Cf t t = true →
        (∑ a : S.Config, if S.rel .VB t a then left v a else 0) = 1 := by
  by_cases ht : S.rel .Cf t t = true
  · simp only [normalizationRow,ht,ite_true,Gaussian.Row.satisfies,Fin.sum_univ_add,
      Fin.addCases_left,Fin.addCases_right,zero_mul,Finset.sum_const_zero,add_zero,
      true_implies]
    have heq : (∑ a : Fin N, (if S.rel .Cf a a && S.rel .VB t a then (1:Scalar) else 0) * left v a) =
        ∑ a : S.Config, if S.rel .VB t a then left v a else 0 := by
      rw [← sum_subtype (fun a => S.rel .Cf a a = true) (fun a => if S.rel .VB t a then left v a else 0)]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : S.rel .Cf a a = true <;> by_cases hv : S.rel .VB t a = true <;> simp [ha,hv]
    exact (congrArg (fun z => z = 1) heq).to_iff
  · simp [normalizationRow,ht,Gaussian.Row.satisfies]

lemma consistency_satisfies (S : Data N) (t y : Fin N) (v : Fin (N+N) → Scalar) :
    (consistencyRow S t y).satisfies v ↔
      ∀ (ht : S.rel .Cf t t = true) (hy : S.rel .Ed y y = true),
        S.incident ⟨t,ht⟩ ⟨y,hy⟩ →
        right v y = ∑ a : S.Config, if S.rel .VB t a then left v a*S.coefficient ⟨y,hy⟩ a else 0 := by
  by_cases ht : S.rel .Cf t t = true
  · by_cases hy : S.rel .Ed y y = true
    · have hi := incident_eq S ⟨t,ht⟩ ⟨y,hy⟩
      by_cases hin : incident S t y = true
      · simp only [consistencyRow,ht,hy,hin,Bool.true_and,ite_true,
          Gaussian.Row.satisfies,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
        have hr : (∑ z : Fin N, (if z = y then (1:Scalar) else 0)*right v z) = right v y := by
          simp
        have hl : (∑ a : Fin N, (if S.rel .Cf a a && S.rel .VB t a then -coefficient S y a else 0)*left v a) =
            -(∑ a : S.Config, if S.rel .VB t a then left v a*S.coefficient ⟨y,hy⟩ a else 0) := by
          rw [← Finset.sum_neg_distrib]
          trans ∑ a : S.Config, (if S.rel .VB t a then -coefficient S y a else 0)*left v a
          · rw [← sum_subtype (fun a => S.rel .Cf a a = true) (fun a => (if S.rel .VB t a then -coefficient S y a else 0)*left v a)]
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : S.rel .Cf a a = true <;> by_cases hv : S.rel .VB t a = true <;> simp [ha,hv]
          · apply Finset.sum_congr rfl
            intro a _
            rw [coefficient_eq S ⟨y,hy⟩ a]
            by_cases hv : S.rel .VB t a = true <;> simp [hv,mul_comm]
        change (_ + _ = 0) ↔ _
        rw [show (∑ i : Fin N, (if i = y then (1:Scalar) else 0) * v (Fin.natAdd N i)) = right v y from hr]
        rw [show (∑ i : Fin N, (if S.rel .Cf i i && S.rel .VB t i then -coefficient S y i else 0) * v (Fin.castAdd N i)) = _ from hl]
        constructor
        · intro h _ _ _
          linear_combination h
        · intro h
          have hh := h True.intro True.intro (hi.mp hin)
          linear_combination hh
      · have hni : ¬ S.incident ⟨t,ht⟩ ⟨y,hy⟩ := fun h => hin (hi.mpr h)
        simp only [consistencyRow,ht,hy,Bool.true_and,hin,true_implies,hni,false_implies,iff_true]
        exact row_zero v
    · simp [consistencyRow,hy,Gaussian.Row.satisfies]
  · simp [consistencyRow,ht,Gaussian.Row.satisfies]

lemma norm_mem (S : Data N) (t : Fin N) : normalizationRow S t ∈ rows S := by
  apply List.mem_append_left
  exact List.mem_map_of_mem (List.mem_finRange t)

lemma consistency_mem (S : Data N) (t y : Fin N) : consistencyRow S t y ∈ rows S := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨t,List.mem_finRange t,List.mem_map_of_mem (List.mem_finRange y)⟩

theorem rows_solvable_iff (S : Data N) : Gaussian.Solvable (rows S) ↔ S.query := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun a => left v a,fun y => right v y,?_,?_⟩
    · intro t
      exact (normalization_satisfies S t v).mp (hv _ (norm_mem S t)) t.property
    · intro t y hinc
      exact (consistency_satisfies S t y v).mp (hv _ (consistency_mem S t y)) t.property y.property hinc
  · rintro ⟨lam,mu,hnorm,hcons⟩
    let l : Fin N → Scalar := fun a => if ha : S.rel .Cf a a = true then lam ⟨a,ha⟩ else 0
    let r : Fin N → Scalar := fun y => if hy : S.rel .Ed y y = true then mu ⟨y,hy⟩ else 0
    let v : Fin (N+N) → Scalar := Fin.addCases l r
    have hl (a : S.Config) : left v a = lam a := by simp [left,v,l,a.property]
    have hr (y : S.Edge) : right v y = mu y := by
      simp only [right,v,Fin.addCases_right]
      simp only [r,dite_eq_left y.property]
    refine ⟨v,?_⟩
    intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hrow
      apply (normalization_satisfies S t v).mpr
      intro ht
      simpa only [hl] using hnorm ⟨t,ht⟩
    · obtain ⟨t,ht,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hrow
      apply (consistency_satisfies S t y v).mpr
      intro ht hy hi
      rw [show right v y = mu ⟨y,hy⟩ from hr ⟨y,hy⟩]
      simpa only [hl] using hcons ⟨t,ht⟩ ⟨y,hy⟩ hi

theorem decideQuery_correct (S : Data N) : decideQuery S = true ↔ S.query := by
  simp only [decideQuery,Gaussian.metered_answer,Gaussian.solve_correct]
  have he : (rows S).map Gaussian.Row.dense = rows S := by
    have hf : Gaussian.Row.dense (n := N+N) = id := funext Gaussian.Row.dense_eq
    rw [hf,List.map_id]
  rw [he,rows_solvable_iff]

theorem rows_length (S : Data N) : (rows S).length = N+N*N := by
  simp [rows,List.length_flatMap]

theorem elimination_operations (S : Data N) :
    (Gaussian.metered ((rows S).map Gaussian.Row.dense)).2 ≤ 96*(N+1)^4 := by
  have h := Gaussian.metered_bound ((rows S).map Gaussian.Row.dense)
  simp only [List.length_map,rows_length] at h
  have hr : N+N*N+1 ≤ 2*(N+1)^2 := by nlinarith
  have hc : N+N+1 ≤ 2*(N+1) := by omega
  calc
    _ ≤ 12*(N+N*N+1)*(N+N+1)^2 := h
    _ ≤ 12*(2*(N+1)^2)*(2*(N+1))^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 12 hr) (Nat.pow_le_pow_left hc 2)
    _ = _ := by ring

end CPTSeparation.OrderedQuery

namespace CPTSeparation.SerialGaussian

structure Row (n : ℕ) where
  coeff : List Scalar
  length_eq : coeff.length = n
  rhs : Scalar

def Row.decode {n} (r : Row n) : Gaussian.Row n :=
  ⟨fun i => r.coeff[i.val]'(by rw [r.length_eq]; exact i.isLt),r.rhs⟩

def Row.encode {n} (r : Gaussian.Row n) : Row n :=
  ⟨List.ofFn r.coeff,by simp,r.rhs⟩

def Row.head {n} (r : Row (n+1)) : Scalar := r.coeff.headD 0

def Row.tail {n} (r : Row (n+1)) : Row n :=
  ⟨r.coeff.tail,by simp [r.length_eq],r.rhs⟩

def Row.reduce {n} (p r : Row (n+1)) : Row n :=
  let c := r.head / p.head
  ⟨List.zipWith (fun x y => x-c*y) r.coeff.tail p.coeff.tail,
    by simp [r.length_eq,p.length_eq],r.rhs-c*p.rhs⟩

def pivot {n} (rows : List (Row (n+1))) : Option (Row (n+1)) :=
  rows.find? (fun r => r.head != 0)

def solve : {n : ℕ} → List (Row n) → Bool
  | 0,rows => rows.all (fun r => r.rhs == 0)
  | _+1,rows => match pivot rows with
    | none => solve (rows.map Row.tail)
    | some p => solve (rows.map (Row.reduce p))

@[simp] theorem Row.decode_encode {n} (r : Gaussian.Row n) : (Row.encode r).decode = r := by
  cases r
  simp only [Row.encode,Row.decode,List.getElem_ofFn]

@[simp] theorem Row.head_decode {n} (r : Row (n+1)) : r.head = r.decode.coeff 0 := by
  rcases r with ⟨l,h,b⟩
  cases l with
  | nil => simp at h
  | cons a l => rfl

@[simp] theorem Row.decode_tail {n} (r : Row (n+1)) : r.tail.decode = r.decode.tail := by
  apply congrArg₂ Gaussian.Row.mk
  · funext i
    simp [Row.decode,Row.tail]
  · rfl

@[simp] theorem Row.decode_reduce {n} (p r : Row (n+1)) :
    (p.reduce r).decode = p.decode.reduce r.decode := by
  apply congrArg₂ Gaussian.Row.mk
  · funext i
    simp [Row.decode,Row.reduce,List.getElem_zipWith,Row.head_decode]
  · simp [Row.decode,Row.reduce,Row.head_decode]

@[simp] theorem pivot_decode {n} (rows : List (Row (n+1))) :
    Gaussian.pivot (rows.map Row.decode) = (pivot rows).map Row.decode := by
  simp only [Gaussian.pivot,pivot,List.find?_map]
  congr 2
  funext r
  simp []

theorem solve_decode {n} (rows : List (Row n)) :
    solve rows = Gaussian.solve (rows.map Row.decode) := by
  induction n with
  | zero => simp [solve,Gaussian.solve,Row.decode,Function.comp_def]
  | succ n ih =>
    cases hp : pivot rows with
    | none => simp [solve,Gaussian.solve,pivot_decode,hp,ih,List.map_map,Function.comp_def]
    | some p => simp [solve,Gaussian.solve,pivot_decode,hp,ih,List.map_map,Function.comp_def]

def payload {n} (rows : List (Row n)) : List (Option Scalar) :=
  rows.flatMap (fun r => r.coeff.map some ++ [some r.rhs,none])

theorem payload_length {n} (rows : List (Row n)) :
    (payload rows).length = rows.length*(n+2) := by
  induction rows with
  | nil => simp [payload]
  | cons r rs ih =>
    simp only [payload,List.flatMap_cons,List.length_append,List.length_map,
      r.length_eq,List.length_cons,List.length_nil] at *
    rw [Nat.add_mul]
    omega

def queryRows {N} (S : OrderedQuery.Data N) : List (Row (N+N)) :=
  (OrderedQuery.rows S).map Row.encode

theorem queryRows_correct {N} (S : OrderedQuery.Data N) :
    solve (queryRows S) = true ↔ S.query := by
  rw [solve_decode]
  have hd : Gaussian.Row.dense (n := N+N) = id := funext Gaussian.Row.dense_eq
  simpa [queryRows,List.map_map,Function.comp_def,OrderedQuery.decideQuery,
    Gaussian.metered_answer,hd] using OrderedQuery.decideQuery_correct S

theorem query_payload_size {N} (S : OrderedQuery.Data N) :
    (payload (queryRows S)).length ≤ 2*(N+1)^3 := by
  rw [payload_length]
  simp only [queryRows,List.length_map,OrderedQuery.rows_length]
  have he : (N+N*N)*(N+N+2) = 2*N*(N+1)^2 := by ring
  rw [he]
  calc
    2*N*(N+1)^2 ≤ 2*(N+1)*(N+1)^2 := by gcongr; omega
    _ = 2*(N+1)^3 := by ring

theorem reduce_payload_size {n} (p : Row (n+1)) (rows : List (Row (n+1))) :
    (payload (rows.map (Row.reduce p))).length ≤ (payload rows).length := by
  simp only [payload_length,List.length_map]
  gcongr
  omega

theorem tail_payload_size {n} (rows : List (Row (n+1))) :
    (payload (rows.map Row.tail)).length ≤ (payload rows).length := by
  simp only [payload_length,List.length_map]
  gcongr
  omega

end CPTSeparation.SerialGaussian

namespace CPTSeparation.OrderedQuery

def symbolIndex : Symbol → Fin 8
  | .Ed => 0 | .Cf => 1 | .EB => 2 | .VB => 3 | .I => 4
  | .Z δ => ⟨5+δ.val,by have := δ.val_lt; omega⟩

@[simp] theorem indexSymbol_symbolIndex (r : Symbol) : indexSymbol (symbolIndex r) = r := by
  cases r with
  | Ed => decide
  | Cf => decide
  | EB => decide
  | VB => decide
  | I => decide
  | Z δ => fin_cases δ <;> decide

@[simp] theorem symbolIndex_indexSymbol (i : Fin 8) : symbolIndex (indexSymbol i) = i := by
  fin_cases i <;> decide

def symbolEquiv : Symbol ≃ Fin 8 :=
  ⟨symbolIndex,indexSymbol,indexSymbol_symbolIndex,symbolIndex_indexSymbol⟩

variable {N : ℕ}

def cellIndex (r : Symbol) (a b : Fin N) : Fin (8*(N*N)) :=
  finProdFinEquiv (symbolIndex r,finProdFinEquiv (a,b))

@[simp] theorem cellValue_index (S : Data N) (r : Symbol) (a b : Fin N) :
    cellValue S (cellIndex r a b) = S.rel r a b := by
  simp [cellValue,cellIndex]

def tableDecode (N : ℕ) (w : List Bool) : Data N :=
  ⟨fun r a b => (w[(cellIndex r a b).val]?).getD false⟩

@[simp] theorem tableDecode_tableBits (S : Data N) : tableDecode N (tableBits S) = S := by
  cases S with
  | mk rel =>
    apply congrArg Input.mk
    funext r a b
    simp [tableBits,cellValue_index]

abbrev Alphabet := Option Bool

def encode (S : OrderedInput) : List Alphabet :=
  List.replicate S.1 none ++ some false :: (tableBits S.2).map some

def decode (w : List Alphabet) : OrderedInput :=
  let N := w.count none
  ⟨N,tableDecode N ((w.drop (N+1)).map (fun b => b.getD false))⟩

@[simp] theorem tableBits_length (S : Data N) : (tableBits S).length = 8*(N*N) := by
  simp [tableBits]

@[simp] theorem encode_size (S : OrderedInput) : (encode S).count none = S.1 := by
  simp only [encode,List.count_append,List.count_replicate,List.count_cons]
  have h : List.count none ((tableBits S.2).map some) = 0 :=
    List.count_eq_zero_of_not_mem (by simp)
  simp [h]

@[simp] theorem decode_encode (S : OrderedInput) : decode (encode S) = S := by
  rcases S with ⟨N,S⟩
  have htail : (encode ⟨N,S⟩).drop (N+1) = (tableBits S).map some := by
    simp [encode,List.drop_append]
  unfold decode
  rw [encode_size]
  change (⟨N,tableDecode N _⟩ : OrderedInput) = ⟨N,S⟩
  apply congrArg (Sigma.mk N)
  rw [htail,List.map_map]
  change tableDecode N ((tableBits S).map id) = S
  rw [List.map_id]
  exact tableDecode_tableBits S

theorem encode_injective : Function.Injective encode := by
  intro S T h
  simpa only [decode_encode] using congrArg decode h

@[simp] theorem encode_length (S : OrderedInput) :
    (encode S).length = S.1+1+8*(S.1*S.1) := by simp [encode]; omega

def encoding : Computability.Encoding OrderedInput Alphabet :=
  ⟨encode,fun w => some (decode w),fun S => by simp⟩

def answer (S : OrderedInput) : Bool := decideQuery S.2

theorem answer_correct (S : OrderedInput) : answer S = true ↔ S.2.query :=
  decideQuery_correct S.2

end CPTSeparation.OrderedQuery

end OAI
