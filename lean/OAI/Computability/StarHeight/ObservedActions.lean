import OAI.Computability.StarHeight.BoundarySnapshots

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uS uK uC uM2 uS2 uM3
universe uS3 uP uP2 uP3 uP4 uP5 uP6 uP7
universe uP8 uAlphabet2 uT uP9 uC2 uAlphabet3 uT2 uP10
universe uC3 uAlphabet4 uM4 uU uK2

namespace ObservedMain

open WordIntervals BoundarySnapshot SplitMetadata ClockAffine

variable {Alphabet : Type uAlphabet} {M : Type uM} {S : Type uS} {K : Type uK} {C : Type uC} [Monoid M] [Field K] [AddCommGroup S] [Module K S]
    {g B : ℕ}

variable (T : FreeMonoid Alphabet →* M) (ρ : M → (S →ₗ[K] S))
    (β : M → M → (Fin g → M) → S)

def Certificate (tag : MainTag M S g B) : Prop :=
  ∀ a, productTable ρ tag.A tag.C (insert tag.j tag.entries a) tag.input +
    β tag.A tag.C (insert tag.j tag.entries a) = tag.output

structure Prefix (tag : MainTag M S g B) (f : ℤ → Alphabet) (s : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop where
  present : ∀ i, i.val ≤ tag.j.val → search i ≠ none
  initial : product T f s (positions search 0) = tag.A
  earlier : ∀ i : {i : Fin g // i ≠ tag.j}, i.val < tag.j →
    product T f (positions search i.val.castSucc) (positions search i.val.succ) = tag.entries i
  certificate : Certificate ρ β tag

structure Suffix (tag : MainTag M S g B) (f : ℤ → Alphabet) (b : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop where
  present : ∀ i, tag.j.val < i.val → search i ≠ none
  final : product T f (positions search (Fin.last g)) b = tag.C
  later : ∀ i : {i : Fin g // i ≠ tag.j}, tag.j < i.val →
    product T f (positions search i.val.castSucc) (positions search i.val.succ) = tag.entries i

lemma pair_present {tag : MainTag M S g B} {f : ℤ → Alphabet} {s b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : Prefix T ρ β tag f s search)
    (hq : Suffix T tag f b search) : ∀ i, search i ≠ none := by
  intro i
  by_cases hi : i.val ≤ tag.j.val
  · exact hp.present i hi
  · exact hq.present i (by omega)

lemma pair_entries {tag : MainTag M S g B} {f : ℤ → Alphabet} {s b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : Prefix T ρ β tag f s search)
    (hq : Suffix T tag f b search) :
    ∀ i : {i : Fin g // i ≠ tag.j},
      product T f (positions search i.val.castSucc) (positions search i.val.succ) = tag.entries i := by
  intro i
  rcases lt_or_gt_of_ne i.property with hi | hi
  · exact hp.earlier i hi
  · exact hq.later i hi

lemma pair_sound {tag : MainTag M S g B} {f : ℤ → Alphabet} {s b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : Prefix T ρ β tag f s search)
    (hq : Suffix T tag f b search) (hm : Present search s b) :
    ρ (actual T f s b search).product tag.input +
      (match (actual T f s b search).boundaries with
        | none => 0
        | some a => β a.A a.C a.entries) = tag.output := by
  have hf := factors_positions T f hm
  let d : Fin g → M := fun i => product T f (positions search i.castSucc) (positions search i.succ)
  have hentries : tag.entries = fun i => d i.val := by
    funext i
    exact (pair_entries T ρ β hp hq i).symm
  have hprod := (actual T f s b search).product_eq _ hf
  rw [hp.initial,hq.final] at hprod hf
  change ρ (actual T f s b search).product tag.input +
    (match factors T f s b search with | none => 0 | some a => β a.A a.C a.entries) = _
  rw [hf,hprod]
  change productTable ρ tag.A tag.C d tag.input + β tag.A tag.C d = _
  have hh := hp.certificate (d tag.j)
  simpa only [hentries,insert_actual] using hh

lemma available (f : ℤ → Alphabet) (s b : ℤ) (search : Fin (g+1) → Option ℤ)
    (hm : Present search s b) (u : Fin B) (x : S)
    (hβ : ∀ A C, ShiftTableProperty g (productTable ρ A C) (β A C)) :
    ∃ tag : MainTag M S g B, tag.u = u ∧ tag.input = x ∧
      Prefix T ρ β tag f s search ∧ Suffix T tag f b search ∧
      tag.output = ρ (actual T f s b search).product x +
        (match (actual T f s b search).boundaries with
          | none => 0
          | some a => β a.A a.C a.entries) := by
  let A := product T f s (positions search 0)
  let C' := product T f (positions search (Fin.last g)) b
  let d : Fin g → M := fun i => product T f (positions search i.castSucc) (positions search i.succ)
  obtain ⟨j,hj⟩ := certificate_available (productTable ρ A C') (β A C') (hβ A C') d x
  let tag : MainTag M S g B := ⟨j,u,A,C',fun i => d i.val,x,
    productTable ρ A C' d x + β A C' d⟩
  have hp : ∀ i, search i ≠ none := by
    obtain ⟨p,hp,_,_,_⟩ := hm
    intro i hi
    rw [hp i] at hi
    cases hi
  have hpre : Prefix T ρ β tag f s search :=
    ⟨fun i _ => hp i,rfl,fun _ _ => rfl,hj⟩
  have hsuf : Suffix T tag f b search := ⟨fun i _ => hp i,rfl,fun _ _ => rfl⟩
  exact ⟨tag,rfl,rfl,hpre,hsuf,(pair_sound T ρ β hpre hsuf hm).symm⟩

end ObservedMain

namespace SplitMetadata

open scoped BigOperators

variable {M : Type uM2} {S : Type uS2} [Fintype M] [Fintype S]

def tagCoefficient (M : Type uM3) (S : Type uS3) [Fintype M] [Fintype S] (g : ℕ) : ℕ :=
  Fintype.card S ^ 2 *
    (g * Fintype.card M ^ (g+1) + (g+1)*Fintype.card M)

lemma mainTag_card (g B : ℕ) (hg : 0 < g) :
    Fintype.card (MainTag M S g B) =
      B * Fintype.card S ^ 2 * g * Fintype.card M ^ (g+1) := by
  classical
  let e : MainTag M S g B ≃
      (Σ j : Fin g, Fin B × M × M × Omitted M g j × S × S) :=
    ⟨fun t => ⟨t.j, t.u,t.A,t.C,t.entries,t.input,t.output⟩,
      fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2⟩,
      fun t => by cases t; rfl, fun t => by cases t; rfl⟩
  have hc (j : Fin g) : Fintype.card {i : Fin g // i ≠ j} = g-1 := by
    simpa only [Fintype.card_fin,Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin g => i=j)
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin,Omitted,Fintype.card_fun,hc,
    Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have he : g+1 = (g-1)+2 := by omega
  rw [he,pow_add,pow_two]
  ring

lemma periodicTag_card (g B : ℕ) :
    Fintype.card (PeriodicTag M S g B) = B * Fintype.card S ^ 2 * (g+1) * Fintype.card M := by
  let e : PeriodicTag M S g B ≃ Fin (g+1) × Fin B × M × S × S :=
    ⟨fun t => (t.j,t.u,t.prefixProduct,t.input,t.output),
      fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2⟩,
      fun t => by cases t; rfl, fun t => by cases t; rfl⟩
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_fin]
  ring

lemma tag_card (g B : ℕ) (hg : 0 < g) :
    Fintype.card (Tag M S g B) = B * tagCoefficient M S g := by
  simp only [Tag,Fintype.card_sum,mainTag_card g B hg,periodicTag_card,tagCoefficient]
  ring

lemma tagCoefficient_pos (g : ℕ) [Nonempty M] [Nonempty S] :
    0 < tagCoefficient M S g := by
  have hM : 0 < Fintype.card M := Fintype.card_pos
  have hS : 0 < Fintype.card S := Fintype.card_pos
  dsimp [tagCoefficient]
  positivity

lemma exists_copies (g κ : ℕ) [Nonempty M] [Nonempty S] (hg : 0 < g) :
    ∃ μ : ℕ, 0 < μ ∧
      20 * (10000000 * Real.log
        (2 * Fintype.card (Tag M S g (20*(κ*μ+1)^3))) + 4*(g+1)) + 10 < μ := by
  have hD := tagCoefficient_pos (M := M) (S := S) g
  obtain ⟨μ,hμ,hbound⟩ := ScheduleCopies.exists_log_polynomial (κ : ℝ)
    (40 * tagCoefficient M S g) 200000000 (80*(g+1)+10)
    (by positivity) (by positivity) (by norm_num)
  refine ⟨μ,hμ,?_⟩
  rw [tag_card g _ hg]
  push_cast
  have he : (2:ℝ) * (20*((κ:ℝ)*μ+1)^3 * tagCoefficient M S g) =
      40 * tagCoefficient M S g * ((κ:ℝ)*μ+1)^3 := by ring
  rw [he]
  linarith

end SplitMetadata

namespace SourceSchedule

open scoped BigOperators

@[instance_reducible] noncomputable def blockOrder {P : Type uP} [Fintype P] {g : ℕ} (label : P → Fin g) :
    LinearOrder P :=
  LinearOrder.lift' (fun p => toLex (label p,(Fintype.equivFin P) p)) (by
    intro a b he
    have hh := congrArg (fun x => (ofLex x).2) he
    exact (Fintype.equivFin P).injective hh)

lemma block_lt {P : Type uP2} [Fintype P] {g : ℕ} (label : P → Fin g)
    {a b : P} (hab : label a < label b) :
    @LT.lt P (blockOrder label).toLT a b :=
  Prod.Lex.left _ _ hab

noncomputable def absoluteBound {P : Type uP3} [Fintype P] (p : P → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (p i).natAbs)

lemma abs_le_absoluteBound {P : Type uP4} [Fintype P] (p : P → ℤ) (i : P) :
    |p i| ≤ (absoluteBound p : ℤ) := by
  have hh : (p i).natAbs ≤ absoluteBound p :=
    Finset.le_sup (f := fun i => (p i).natAbs) (Finset.mem_univ i)
  simpa only [Int.natCast_natAbs] using (show ((p i).natAbs : ℤ) ≤ absoluteBound p by exact_mod_cast hh)

lemma difference_bound {P : Type uP5} [Fintype P] (p : P → ℤ) (i j : P) :
    |p i-p j| ≤ 2 * (absoluteBound p : ℤ)+1 := by
  exact (abs_sub _ _).trans (by linarith [abs_le_absoluteBound p i,abs_le_absoluteBound p j])

noncomputable def innerD {P : Type uP6} [Fintype P] (p : P → ℤ) (w₀ : ℕ) : ℕ :=
  10*(2*(2*absoluteBound p+1)+2*w₀+5)+1

lemma innerD_ge {P : Type uP7} [Fintype P] (p : P → ℤ) (w₀ : ℕ) : 2 ≤ innerD p w₀ := by
  dsimp [innerD]
  omega

lemma innerD_bound {P : Type uP8} [Fintype P] (p : P → ℤ) (w₀ : ℕ) :
    10*(2*(2*(absoluteBound p : ℤ)+1)+2*w₀+5) < innerD p w₀ := by
  simp only [innerD,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

structure Early {Alphabet : Type uAlphabet2} {T : Type uT} {P : Type uP9} {C : Type uC2} [Fintype T] [Fintype P] [Fintype C]
    {g' : ℕ} (clock : RobustClock.Specification T P C) (B size : ℕ)
    (label : P → Fin g') (reserved : P → ℤ) where
  R : ℕ
  p : P → ℤ
  β : Fin (g'+1) → ℤ
  denominator : C → ℕ
  numerator : C → ℕ
  R_pos : 0 < R
  reserved_eq : ∀ i, p i % B = reserved i % B
  p_pos : ∀ i, 0 < p i
  separated : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
    (2*(B*R)+2 : ℤ) < |(p i-p j)-(p i'-p j')|
  separated_zero : ∀ i j, i ≠ j → (2*(B*R)+2 : ℤ) < |p i-p j|
  β_zero : β 0 = 0
  β_strict : StrictMono β
  block : ∀ i, β (label i).castSucc < p i ∧ p i < β (label i).succ
  prime : ∀ c, Nat.Prime (denominator c)
  den_injective : Function.Injective denominator
  den_large : ∀ c, max B (max (innerD p (B*R)) size.factorial) < denominator c
  num_bounds : ∀ c, 1 ≤ numerator c ∧ numerator c < denominator c
  approximate : ∀ i, dist
    (PeriodicClock.speedMap (fun c => (numerator c : ℝ)/denominator c) (p i)) (clock.v i) < clock.η
  net : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a<R ∧ dist
    (PeriodicClock.speedMap (fun c => (numerator c : ℝ)/denominator c) (a*B)) v < clock.ρ
  rule : LocalMarkers.Rule Alphabet (innerD p (B*R)) (3*(innerD p (B*R))^2+1)
  inner : IntegerSchedules.Inner B (∏c,denominator c) R size (innerD p (B*R))
    (3*(innerD p (B*R))^2+1) rule.r (2*(absoluteBound p : ℤ)+1)

lemma exists_early {Alphabet : Type uAlphabet3} {T : Type uT2} {P : Type uP10} {C : Type uC3} [Fintype Alphabet] [Fintype T]
    [Fintype P] [Fintype C] {g' : ℕ} (clock : RobustClock.Specification T P C)
    (B size : ℕ) (hB : 0 < B) (label : P → Fin g') (honto : Function.Surjective label)
    (reserved : P → ℤ) : Nonempty (Early (Alphabet := Alphabet) clock B size label reserved) := by
  classical
  let : LinearOrder P := blockOrder label
  obtain ⟨R,p,n,a,hR,hp,hspread,hn,hna,hpert,hnet⟩ :=
    ScheduleClock.exists_ordered_stencil_clock clock B hB reserved
      (fun p w₀ => max B (max (innerD p w₀) size.factorial))
  have hK : (0 : ℤ) ≤ 2*(B*R)+2 := by positivity
  have hp' : ∀ i, (2*(B*R)+2 : ℤ) < p i := fun i => (hp i).2
  have hpos : ∀ i, 0 < p i := fun i => hK.trans_lt (hp' i)
  obtain ⟨β,hβ₀,hβ,hblock⟩ := SpacedStencil.exists_boundaries label p honto hpos (by
    intro i j hij
    have hh := hspread i j (block_lt label hij)
    have hi := hpos i
    omega)
  obtain ⟨rule⟩ := LocalMarkers.nonempty_rule (Alphabet := Alphabet)
    (d := innerD p (B*R)) (K := 3*(innerD p (B*R))^2+1)
    (innerD_ge p (B*R)) (by omega)
  obtain ⟨inner⟩ := IntegerSchedules.exists_inner B (∏c,n c) R size
    (innerD p (B*R)) (3*(innerD p (B*R))^2+1) rule.r
    (2*(absoluteBound p : ℤ)+1) hB
  exact ⟨⟨R,p,β,n,a,hR,fun i => (hp i).1,hpos,
    fun _ _ _ _ hij hkl hne => SpacedStencil.ordered_differences hK hp' hspread hij hkl hne,
    fun _ _ hij => SpacedStencil.nonzero_differences hK hp' hspread hij,
    hβ₀,hβ,hblock,fun c => (hna c).1,hn,fun c => (hna c).2.1,
    fun c => (hna c).2.2,hpert,hnet,rule,inner⟩⟩

end SourceSchedule

namespace ObservedInner

open WordIntervals SplitMetadata

variable {Alphabet : Type uAlphabet4} {M : Type uM4} {U : Type uU} {K : Type uK2} [Monoid M] [Field K]
  [AddCommGroup U] [Module K U] {g : ℕ}

def table (ψ : M → (U →ₗ[K] U)) (d : Fin g → M) : U →ₗ[K] U :=
  ψ (List.ofFn d).prod

variable (T : FreeMonoid Alphabet →* M)
  (β : (M → (U →ₗ[K] U)) → (Fin g → M) → U)

def Certificate (kind : Kind M U K g) : Prop :=
  ∀ a, table kind.hypothetical (insert kind.j kind.entries a) kind.input +
    β kind.hypothetical (insert kind.j kind.entries a) = kind.output

structure Prefix (kind : Kind M U K g) (f : ℤ → Alphabet)
    (boundary : Fin (g+1) → ℤ) : Prop where
  earlier : ∀ i : {i : Fin g // i ≠ kind.j}, i.val < kind.j →
    product T f (boundary i.val.castSucc) (boundary i.val.succ) = kind.entries i
  certificate : Certificate β kind

structure Suffix (kind : Kind M U K g) (f : ℤ → Alphabet)
    (boundary : Fin (g+1) → ℤ) (ψ : M → (U →ₗ[K] U)) : Prop where
  later : ∀ i : {i : Fin g // i ≠ kind.j}, kind.j < i.val →
    product T f (boundary i.val.castSucc) (boundary i.val.succ) = kind.entries i
  hypothetical_eq : ψ = kind.hypothetical

lemma prefix_congr {kind : Kind M U K g} {f f' : ℤ → Alphabet}
    {boundary : Fin (g+1) → ℤ} {k : ℤ} (hm : Monotone boundary)
    (hk : boundary kind.j.castSucc ≤ k)
    (he : LocalMarkers.AgreesOn f f' (boundary 0) k)
    (hp : Prefix T β kind f boundary) : Prefix T β kind f' boundary := by
  refine ⟨?_,hp.certificate⟩
  intro i hi
  rw [← hp.earlier i hi]
  apply product_congr T (hm (Fin.castSucc_le_succ i.val))
  intro x hx hx'
  exact (he x ((hm (Fin.zero_le _)).trans hx) (hx'.trans_le ((hm (by
    change i.val.val + 1 ≤ kind.j.val
    exact hi)).trans hk))).symm

lemma suffix_congr {kind : Kind M U K g} {f f' : ℤ → Alphabet}
    {boundary : Fin (g+1) → ℤ} {k : ℤ} {ψ : M → (U →ₗ[K] U)}
    (hm : Monotone boundary) (hk : k ≤ boundary kind.j.succ)
    (he : LocalMarkers.AgreesOn f f' k (boundary (Fin.last g)))
    (hq : Suffix T kind f boundary ψ) : Suffix T kind f' boundary ψ := by
  refine ⟨?_,hq.hypothetical_eq⟩
  intro i hi
  rw [← hq.later i hi]
  apply product_congr T (hm (Fin.castSucc_le_succ i.val))
  intro x hx hx'
  exact (he x ((hk.trans (hm (by change kind.j.val + 1 ≤ i.val.val; exact hi))).trans hx)
    (hx'.trans_le (hm (Fin.le_last _)))).symm

lemma pair_sound {kind : Kind M U K g} {f : ℤ → Alphabet}
    {boundary : Fin (g+1) → ℤ} {ψ : M → (U →ₗ[K] U)}
    (hp : Prefix T β kind f boundary) (hq : Suffix T kind f boundary ψ) :
    let d := fun i : Fin g => product T f (boundary i.castSucc) (boundary i.succ)
    table ψ d kind.input + β ψ d = kind.output := by
  let d := fun i : Fin g => product T f (boundary i.castSucc) (boundary i.succ)
  have he : kind.entries = fun i => d i.val := by
    funext i
    rcases lt_or_gt_of_ne i.property with hi | hi
    · exact (hp.earlier i hi).symm
    · exact (hq.later i hi).symm
  have hh := hp.certificate (d kind.j)
  rw [he,insert_actual] at hh
  simpa only [hq.hypothetical_eq] using hh

lemma available (f : ℤ → Alphabet) (boundary : Fin (g+1) → ℤ)
    (ψ : M → (U →ₗ[K] U)) (x : U)
    (hβ : ShiftTableProperty g (table ψ) (β ψ)) :
    ∃ kind : Kind M U K g, kind.input = x ∧
      Prefix T β kind f boundary ∧ Suffix T kind f boundary ψ ∧
      kind.output = table ψ
        (fun i => product T f (boundary i.castSucc) (boundary i.succ)) x +
        β ψ (fun i => product T f (boundary i.castSucc) (boundary i.succ)) := by
  let d := fun i : Fin g => product T f (boundary i.castSucc) (boundary i.succ)
  obtain ⟨j,hj⟩ := certificate_available (table ψ) (β ψ) hβ d x
  let kind : Kind M U K g := ⟨j,x,table ψ d x + β ψ d,fun i => d i.val,ψ⟩
  exact ⟨kind,rfl,⟨fun _ _ => rfl,hj⟩,⟨fun _ _ => rfl,rfl⟩,rfl⟩

lemma linear_part (f : ℤ → Alphabet) (boundary : Fin (g+1) → ℤ)
    (hm : Monotone boundary) (ψ : M → (U →ₗ[K] U)) :
    table ψ (fun i => product T f (boundary i.castSucc) (boundary i.succ)) =
      ψ (product T f (boundary 0) (boundary (Fin.last g))) := by
  exact congrArg ψ (product_chain T f boundary hm)

end ObservedInner

end GeneralizedStarHeight

end OAI
