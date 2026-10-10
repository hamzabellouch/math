import OAI.LinearAlgebra.MatrixState.QuarterRoot
import OAI.RepresentationTheory.RowColumn.SignedWords

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Nat
namespace RowColumn.WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- All transporters between two words are exactly the independent bijections
between corresponding color fibres. -/
def transporterEquiv (a b : S → A) :
    {p : Equiv.Perm S // ∀ x, b (p x) = a x} ≃
      (∀ c : A, {x : S // a x = c} ≃ {x : S // b x = c}) where
  toFun p c :=
    { toFun := fun x => ⟨p.1 x.1, (p.2 x.1).trans x.2⟩
      invFun := fun y => ⟨p.1.symm y.1, by
        have h := p.2 (p.1.symm y.1)
        rw [Equiv.apply_symm_apply] at h
        exact h.symm.trans y.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  invFun f := ⟨(Equiv.sigmaFiberEquiv a).symm |>.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv b)), fun x => (f (a x) ⟨x,rfl⟩).2⟩
  left_inv := by intro p; apply Subtype.ext; ext x; rfl
  right_inv := by
    intro f
    funext c
    apply Equiv.ext
    rintro ⟨x,rfl⟩
    apply Subtype.ext
    rfl

lemma card_transporters (a b : S → A) (he : counts a = counts b) :
    Fintype.card {p : Equiv.Perm S // ∀ x, b (p x) = a x} =
      ∏ c : A, (Fintype.card {x : S // a x = c})! := by
  rw [Fintype.card_congr (transporterEquiv a b), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  have hc : Fintype.card {x : S // a x = c} = Fintype.card {x : S // b x = c} :=
    congrArg (fun f : A → Fin (Fintype.card S + 1) => (f c).val) he
  let e := Fintype.equivOfCardEq hc
  let ee : ({x : S // a x = c} ≃ {x : S // b x = c}) ≃
      Equiv.Perm {x : S // a x = c} :=
    { toFun := fun f => f.trans e.symm
      invFun := fun g => g.trans e
      left_inv := by intro f; ext x; simp
      right_inv := by intro g; ext x; simp }
  rw [Fintype.card_congr ee, Fintype.card_perm]

/-- Orbit-stabilizer with all factors explicit. It is the exact multinomial
cardinality needed for the finite postselection probability. -/
lemma type_card_factorial (a : S → A) :
    Fintype.card {b : S → A // counts b = counts a} *
      (∏ c : A, (Fintype.card {x : S // a x = c})!) = (Fintype.card S)! := by
  let e : Equiv.Perm S ≃
      Σ b : {b : S → A // counts b = counts a},
        {p : Equiv.Perm S // ∀ x, b.1 (p x) = a x} :=
    { toFun := fun p =>
        ⟨⟨(fun x => a (p.symm x)), by
          funext c
          apply Fin.ext
          exact Fintype.card_congr
            { toFun := fun x => ⟨p.symm x.1,x.2⟩
              invFun := fun x => ⟨p x.1,by simpa using x.2⟩
              left_inv := by intro x; apply Subtype.ext; simp
              right_inv := by intro x; apply Subtype.ext; simp }⟩,
          ⟨p,fun x => by simp⟩⟩
      invFun := fun z => z.2.1
      left_inv := by intro p; rfl
      right_inv := by
        rintro ⟨⟨b,hb⟩,p,hp⟩
        have he : (fun x => a (p.symm x)) = b := by
          funext x
          have h := hp (p.symm x)
          simpa using h.symm
        cases he
        rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_perm, Fintype.card_sigma] at hc
  have hn (b : {b : S → A // counts b = counts a}) :
      Fintype.card {p : Equiv.Perm S // ∀ x, b.1 (p x) = a x} =
        ∏ c : A, (Fintype.card {x : S // a x = c})! :=
    card_transporters a b.1 b.2.symm
  simp_rw [hn] at hc
  simpa using hc.symm

end RowColumn.WordOrbits

namespace RowColumn.WordOrbits
open scoped BigOperators Classical Nat

lemma factorial_le_factorial_mul_pow {b a : ℕ} (h : b ≤ a) :
    a.factorial ≤ b.factorial * a^(a-b) := by
  induction a,h using Nat.le_induction with
  | base => simp
  | succ a ha ih =>
    rw [Nat.factorial_succ, show a+1-b = (a-b)+1 by omega, pow_succ]
    calc
      (a+1)*a.factorial ≤ (a+1)*(b.factorial*a^(a-b)) := Nat.mul_le_mul_left _ ih
      _ ≤ (a+1)*(b.factorial*(a+1)^(a-b)) := by gcongr; omega
      _ = _ := by ring

lemma factorial_mode (a b : ℕ) : a^b * a.factorial ≤ a^a * b.factorial := by
  rcases le_total a b with h | h
  · have hh := Nat.factorial_mul_pow_sub_le_factorial h
    calc
      a^b * a.factorial = a^a * (a.factorial * a^(b-a)) := by
        calc
          _ = a^(a+(b-a)) * a.factorial := by rw [Nat.add_sub_of_le h]
          _ = _ := by rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hh
  · have hh := factorial_le_factorial_mul_pow h
    calc
      a^b * a.factorial ≤ a^b * (b.factorial * a^(a-b)) := Nat.mul_le_mul_left _ hh
      _ = a^a * b.factorial := by
        calc
          _ = a^(b+(a-b)) * b.factorial := by rw [pow_add]; ring
          _ = _ := by rw [Nat.add_sub_of_le h]

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] in
lemma prod_by_counts {M : Type*} [CommMonoid M] (w : S → A) (f : A → M) :
    (∏ x : S, f (w x)) = ∏ c : A, f c ^ (counts w c).val := by
  rw [← Fintype.prod_fiberwise w]
  apply Finset.prod_congr rfl
  intro c _
  simp only [counts]
  simp only [show ∀ x : {x : S // w x = c}, f (w x.1) = f c from fun x => congrArg f x.2]
  simp

omit [DecidableEq S] in
lemma sum_counts (w : S → A) : ∑ c : A, (counts w c).val = Fintype.card S := by
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv w)).symm.trans (by rw [Fintype.card_sigma]; rfl) |>.symm

/-- Under its own empirical product distribution, a type is a mode among
all types. This gives a polynomial lower bound without Stirling or entropy. -/
lemma empirical_type_mode (a b : S → A) :
    Fintype.card {w : S → A // counts w = counts b} *
      (∏ c : A, (counts a c).val ^ (counts b c).val) ≤
    Fintype.card {w : S → A // counts w = counts a} *
      (∏ c : A, (counts a c).val ^ (counts a c).val) := by
  have h := Finset.prod_le_prod (fun c (_ : c ∈ Finset.univ) =>
    factorial_mode (counts a c).val (counts b c).val)
  simp only [Finset.prod_mul_distrib] at h
  have ha := type_card_factorial a
  have hb := type_card_factorial b
  change _ * (∏ c : A, (counts a c).val !) = _ at ha
  change _ * (∏ c : A, (counts b c).val !) = _ at hb
  have hp : 0 < (∏ c : A, (counts a c).val !) * (∏ c : A, (counts b c).val !) := by
    exact Nat.mul_pos (Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
      (Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
  apply (Nat.mul_le_mul_right_iff hp).mp
  calc
    _ = (Fintype.card S)! * ((∏ c, (counts a c).val ^ (counts b c).val) *
        ∏ c, (counts a c).val !) := by rw [← hb]; ring
    _ ≤ (Fintype.card S)! * ((∏ c, (counts a c).val ^ (counts a c).val) *
        ∏ c, (counts b c).val !) := Nat.mul_le_mul_left _ h
    _ = _ := by rw [← ha]; ring

end RowColumn.WordOrbits

namespace RowColumn.WordOrbits
open scoped BigOperators Classical Nat
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def typeMass (a : S → A) (q : A → Fin (Fintype.card S + 1)) : ℕ :=
  Fintype.card {w : S → A // counts w = q} * ∏ c, (counts a c).val ^ (q c).val

lemma typeMass_le_mode (a : S → A) (q : A → Fin (Fintype.card S + 1)) :
    typeMass a q ≤ typeMass a (counts a) := by
  by_cases hn : Nonempty {w : S → A // counts w = q}
  · obtain ⟨w,hw⟩ := hn
    rw [← hw]
    exact empirical_type_mode a w
  · let : IsEmpty {w : S → A // counts w = q} := not_nonempty_iff.mp hn
    simp [typeMass]

lemma sum_typeMass (a : S → A) :
    (∑ q : A → Fin (Fintype.card S+1), typeMass a q) =
      (Fintype.card S)^(Fintype.card S) := by
  have he (q : A → Fin (Fintype.card S+1)) : typeMass a q =
      ∑ w : {w : S → A // counts w = q}, ∏ x : S, (counts a (w.1 x)).val := by
    have hh (w : {w : S → A // counts w = q}) :
        (∏ x : S, (counts a (w.1 x)).val) = ∏ c : A, (counts a c).val ^ (q c).val := by
      rw [prod_by_counts w.1 (fun c => (counts a c).val), w.2]
    simp only [hh, Finset.sum_const, Finset.card_univ, smul_eq_mul, typeMass]
  simp_rw [he]
  rw [Fintype.sum_fiberwise counts (fun w : S → A => ∏ x : S, (counts a (w x)).val),
    ← Fintype.prod_sum (fun (_ : S) (c : A) => (counts a c).val)]
  simp only [sum_counts, Finset.prod_const, Finset.card_univ]

/-- Elementary finite postselection mass bound: an empirical type has at
least the inverse number of possible occupation tables. -/
lemma empirical_mass_lower (a : S → A) :
    (Fintype.card S)^(Fintype.card S) ≤
      (Fintype.card S+1)^(Fintype.card A) * typeMass a (counts a) := by
  rw [← sum_typeMass a]
  have hh := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => typeMass_le_mode a q)
  simpa using hh

end RowColumn.WordOrbits

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def empiricalAmplitude (a : S → A) (c : A) : ℂ :=
  Real.sqrt ((counts a c).val / (Fintype.card S : ℝ))

def tensorVector (z : A → ℂ) (w : S → A) : ℂ := ∏ x : S, z (w x)

omit [DecidableEq S] [Fintype A] in
lemma normSq_empiricalAmplitude (a : S → A) (c : A) :
    Complex.normSq (empiricalAmplitude a c) =
      (counts a c).val / (Fintype.card S : ℝ) := by
  simp only [empiricalAmplitude, Complex.normSq_ofReal]
  exact Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [DecidableEq S] in
lemma empiricalAmplitude_normalized (a : S → A) (hn : 0 < Fintype.card S) :
    (∑ c : A, Complex.normSq (empiricalAmplitude a c)) = 1 := by
  simp only [normSq_empiricalAmplitude, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_counts]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hn)

omit [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma normSq_tensorVector (z : A → ℂ) (w : S → A) :
    Complex.normSq (tensorVector z w) = ∏ x : S, Complex.normSq (z (w x)) := by
  exact map_prod Complex.normSq _ _

omit [DecidableEq S] in
lemma normSq_empirical_tensor (a : S → A) :
    Complex.normSq (tensorVector (empiricalAmplitude a) a) =
      (∏ c : A, ((counts a c).val : ℝ)^(counts a c).val) /
        (Fintype.card S : ℝ)^(Fintype.card S) := by
  rw [normSq_tensorVector]
  simp_rw [normSq_empiricalAmplitude]
  rw [Finset.prod_div_distrib, prod_by_counts a (fun c => ((counts a c).val : ℝ))]
  simp

lemma empirical_type_probability (a : S → A) (hn : 0 < Fintype.card S) :
    1 ≤ ((Fintype.card S+1)^(Fintype.card A) : ℕ) *
      ((Fintype.card {w : S → A // counts w = counts a} : ℝ) *
        Complex.normSq (tensorVector (empiricalAmplitude a) a)) := by
  have hh := empirical_mass_lower a
  rw [normSq_empirical_tensor]
  have hden : 0 < (Fintype.card S : ℝ)^Fintype.card S := by positivity
  rw [← mul_div_assoc, ← mul_div_assoc, le_div_iff₀ hden, one_mul]
  dsimp only [typeMass] at hh
  exact_mod_cast hh

end RowColumn.Postselection


noncomputable section
open scoped BigOperators Classical
namespace RowColumn.Postselection
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

abbrev CountIndex (A : Type*) (n : ℕ) := A → Fin (n+1)
abbrev Phases (A : Type*) (n : ℕ) := A → ZMod (n+1)

def countCharacter (q : CountIndex A n) : AddChar (Phases A n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom
    { toFun := fun θ => ∑ c, ((q c).val : ZMod (n+1)) * θ c
      map_zero' := by simp
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib] }

@[simp] lemma countCharacter_single (q : CountIndex A n) (a : A) :
    countCharacter q (Pi.single a 1) = ZMod.stdAddChar ((q a).val : ZMod (n+1)) := by
  simp [countCharacter, Pi.single_apply]

lemma countCharacter_injective : Function.Injective (countCharacter (A := A) (n := n)) := by
  intro q r h
  funext a
  have he := congrArg (fun f : AddChar (Phases A n) ℂ => f (Pi.single a 1)) h
  simp only [countCharacter_single] at he
  have hc := ZMod.injective_stdAddChar he
  change ((q a).val : ZMod (n+1)) = (r a).val at hc
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (q a).isLt,
    Nat.mod_eq_of_lt (r a).isLt] at hc
  exact Fin.ext hc

lemma character_orthogonality (q r : CountIndex A n) :
    (∑ θ : Phases A n, countCharacter q θ * (starRingEnd ℂ) (countCharacter r θ)) =
      if q = r then (Fintype.card (Phases A n) : ℂ) else 0 := by
  have he (θ : Phases A n) : (countCharacter q - countCharacter r) θ =
      countCharacter q θ * (starRingEnd ℂ) (countCharacter r θ) := by
    rw [AddChar.sub_apply, AddChar.map_neg_eq_inv,
      Complex.inv_eq_conj ((countCharacter r).norm_apply θ)]
  simp_rw [← he]
  rw [AddChar.sum_eq_ite]
  simp only [sub_eq_zero, countCharacter_injective.eq_iff]

/-- Finite exact phase integration: order n+1 resolves every occupation
vector with entries in 0,...,n, with no analytical Haar integral. -/
lemma phase_parseval (f : CountIndex A n → ℂ) :
    (∑ θ : Phases A n, Complex.normSq (∑ q, countCharacter q θ * f q)) =
      (Fintype.card (Phases A n) : ℝ) * ∑ q, Complex.normSq (f q) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj, map_sum, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  have he (θ : Phases A n) (q r : CountIndex A n) :
      (countCharacter q θ * f q) * ((starRingEnd ℂ) (countCharacter r θ) *
        (starRingEnd ℂ) (f r)) =
      (countCharacter q θ * (starRingEnd ℂ) (countCharacter r θ)) *
        (f q * (starRingEnd ℂ) (f r)) := by ring
  simp_rw [he]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, character_orthogonality]
  simp [ite_mul]

lemma phase_single_bound (f : CountIndex A n → ℂ) (q : CountIndex A n) :
    (Fintype.card (Phases A n) : ℝ) * Complex.normSq (f q) ≤
      ∑ θ : Phases A n, Complex.normSq (∑ r, countCharacter r θ * f r) := by
  rw [phase_parseval]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ q)

end RowColumn.Postselection
namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits

lemma normSq_sum_mul_le {I : Type*} [Fintype I] (v x : I → ℂ) :
    Complex.normSq (∑ i, v i * x i) ≤
      (∑ i, Complex.normSq (v i)) * ∑ i, Complex.normSq (x i) := by
  have hh : ‖∑ i, v i * x i‖ ≤ ∑ i, ‖v i‖ * ‖x i‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => v i * x i)
  calc
    Complex.normSq (∑ i, v i * x i) = ‖∑ i, v i * x i‖^2 := (Complex.sq_norm _).symm
    _ ≤ (∑ i, ‖v i‖ * ‖x i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ ≤ (∑ i, ‖v i‖^2) * ∑ i, ‖x i‖^2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by simp only [Complex.sq_norm]

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

abbrev Types := CountIndex A (Fintype.card S)
def typeSize (q : Types (S := S) (A := A)) := Fintype.card {w : S → A // counts w = q}
def typeSum (x : (S → A) → ℂ) (q : Types (S := S) (A := A)) : ℂ :=
  ∑ w : {w : S → A // counts w = q}, x w.1

def typeAverage (x : (S → A) → ℂ) (w : S → A) : ℂ :=
  typeSum x (counts w) / (typeSize (counts w) : ℂ)

def typeRepresentative (a₀ : S → A) (q : Types (S := S) (A := A)) : S → A :=
  if h : Nonempty {w : S → A // counts w = q} then h.some.1 else a₀

omit [DecidableEq S] [Fintype A] in
lemma representative_counts (a₀ : S → A) (q : Types (S := S) (A := A))
    (h : Nonempty {w : S → A // counts w = q}) :
    counts (typeRepresentative a₀ q) = q := by
  simp only [typeRepresentative, dite_eq_left h]
  exact h.some.2

lemma typeAverage_pair (v x : (S → A) → ℂ)
    (hv : ∀ a b, counts a = counts b → v a = v b) :
    (∑ w : S → A, v w * typeAverage x w) = ∑ w : S → A, v w * x w := by
  rw [← Fintype.sum_fiberwise counts (fun w : S → A => v w * typeAverage x w),
    ← Fintype.sum_fiberwise counts (fun w : S → A => v w * x w)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hn : Nonempty {w : S → A // counts w = q}
  · obtain ⟨a,ha⟩ := hn
    have hc : (typeSize q : ℂ) ≠ 0 := by
      have hn : 0 < typeSize q := Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩
      exact_mod_cast Nat.ne_of_gt hn
    have he (w : {w : S → A // counts w = q}) : v w.1 = v a := hv _ _ (w.2.trans ha.symm)
    simp only [typeAverage, he,
      show ∀ w : {w : S → A // counts w = q}, counts w.1 = q from fun w => w.2]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    change (typeSize q : ℂ) * (v a * (typeSum x q / typeSize q)) = v a * typeSum x q
    field_simp
  · let : IsEmpty {w : S → A // counts w = q} := not_nonempty_iff.mp hn
    simp

lemma typeAverage_normSq (x : (S → A) → ℂ) :
    (∑ w : S → A, Complex.normSq (typeAverage x w)) =
      ∑ q : Types (S := S) (A := A), Complex.normSq (typeSum x q) / typeSize q := by
  rw [← Fintype.sum_fiberwise counts (fun w : S → A => Complex.normSq (typeAverage x w))]
  apply Finset.sum_congr rfl
  intro q _
  simp only [typeAverage,
    show ∀ w : {w : S → A // counts w = q}, counts w.1 = q from fun w => w.2,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (typeSize q : ℝ) * Complex.normSq (typeSum x q / (typeSize q : ℂ)) = _
  rw [Complex.normSq_div]
  have he : Complex.normSq (typeSize q : ℂ) = (typeSize q : ℝ)^2 := by simp [Complex.normSq_apply]; ring
  rw [he]
  by_cases hh : typeSize q = 0
  · simp [hh]
  · have hc : (typeSize q : ℝ) ≠ 0 := by exact_mod_cast hh
    field_simp

lemma invariant_vector_bound (v x : (S → A) → ℂ)
    (hv : ∀ a b, counts a = counts b → v a = v b) :
    Complex.normSq (∑ w, v w * x w) ≤
      (∑ w, Complex.normSq (v w)) *
        ∑ q : Types (S := S) (A := A), Complex.normSq (typeSum x q) / typeSize q := by
  rw [← typeAverage_pair v x hv, ← typeAverage_normSq]
  exact normSq_sum_mul_le v (typeAverage x)

end RowColumn.Postselection

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits

lemma char_sum {I G : Type*} [AddCommMonoid G] (ψ : AddChar G ℂ)
    (s : Finset I) (f : I → G) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp only [Finset.sum_cons, Finset.prod_cons, ψ.map_add_eq_mul, ih]

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def typeAmplitude (z : A → ℂ) (q : Types (S := S) (A := A)) : ℂ :=
  ∏ c, z c ^ (q c).val

omit [DecidableEq S] in
lemma tensorVector_by_counts (z : A → ℂ) (w : S → A) :
    tensorVector z w = typeAmplitude z (counts w) := prod_by_counts w z

def twistedAmplitude (a : S → A) (θ : Phases A (Fintype.card S)) (c : A) : ℂ :=
  empiricalAmplitude a c * ZMod.stdAddChar (θ c)

omit [DecidableEq S] in
lemma twistedAmplitude_normalized (a : S → A) (hn : 0 < Fintype.card S)
    (θ : Phases A (Fintype.card S)) :
    (∑ c : A, Complex.normSq (twistedAmplitude a θ c)) = 1 := by
  have hc (c : A) : Complex.normSq (ZMod.stdAddChar (θ c)) = 1 := by
    rw [← Complex.sq_norm, AddChar.norm_apply]; norm_num
  simp only [twistedAmplitude, Complex.normSq_mul, hc, mul_one]
  exact empiricalAmplitude_normalized a hn

omit [DecidableEq S] [DecidableEq A] in
lemma countCharacter_eq_prod (q : Types (S := S) (A := A)) (θ : Phases A (Fintype.card S)) :
    countCharacter q θ = ∏ c, ZMod.stdAddChar (θ c) ^ (q c).val := by
  change ZMod.stdAddChar (∑ c, ((q c).val : ZMod (Fintype.card S + 1)) * θ c) = _
  rw [char_sum]
  apply Finset.prod_congr rfl
  intro c _
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

omit [DecidableEq S] in
lemma tensorVector_twisted (a w : S → A) (θ : Phases A (Fintype.card S)) :
    tensorVector (twistedAmplitude a θ) w =
      countCharacter (counts w) θ * typeAmplitude (empiricalAmplitude a) (counts w) := by
  change (∏ x : S, empiricalAmplitude a (w x) * ZMod.stdAddChar (θ (w x))) = _
  rw [Finset.prod_mul_distrib, prod_by_counts w (empiricalAmplitude a),
    prod_by_counts w (fun c => ZMod.stdAddChar (θ c)), ← countCharacter_eq_prod]
  exact mul_comm _ _

lemma twisted_pair (a : S → A) (θ : Phases A (Fintype.card S)) (x : (S → A) → ℂ) :
    (∑ w, tensorVector (twistedAmplitude a θ) w * x w) =
      ∑ q : Types (S := S) (A := A),
        countCharacter q θ * (typeAmplitude (empiricalAmplitude a) q * typeSum x q) := by
  simp_rw [tensorVector_twisted]
  rw [← Fintype.sum_fiberwise counts (fun w : S → A =>
    countCharacter (counts w) θ * typeAmplitude (empiricalAmplitude a) (counts w) * x w)]
  apply Finset.sum_congr rfl
  intro q _
  simp only [show ∀ w : {w : S → A // counts w = q}, counts w.1 = q from fun w => w.2]
  rw [← Finset.mul_sum]
  exact mul_assoc _ _ _

lemma type_phase_bound (a : S → A) (x : (S → A) → ℂ) :
    (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      (Complex.normSq (tensorVector (empiricalAmplitude a) a) *
        Complex.normSq (typeSum x (counts a))) ≤
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w, tensorVector (twistedAmplitude a θ) w * x w) := by
  simp_rw [twisted_pair]
  have hh := phase_single_bound (fun q : Types (S := S) (A := A) =>
    typeAmplitude (empiricalAmplitude a) q * typeSum x q) (counts a)
  simpa only [Complex.normSq_mul, tensorVector_by_counts] using hh

lemma type_representative_bound (a₀ : S → A) (hn : 0 < Fintype.card S)
    (x : (S → A) → ℂ) (q : Types (S := S) (A := A)) :
    Complex.normSq (typeSum x q) / typeSize q ≤
      ((Fintype.card S+1)^(Fintype.card A) : ℕ) /
        (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w, tensorVector (twistedAmplitude (typeRepresentative a₀ q) θ) w * x w) := by
  by_cases he : Nonempty {w : S → A // counts w = q}
  · let a := typeRepresentative a₀ q
    have ha : counts a = q := representative_counts a₀ q he
    have hp := empirical_type_probability a hn
    have ht := type_phase_bound a x
    rw [ha] at ht
    change 1 ≤ ((Fintype.card S+1)^(Fintype.card A) : ℕ) *
      ((typeSize (counts a) : ℝ) * Complex.normSq (tensorVector (empiricalAmplitude a) a)) at hp
    rw [ha] at hp
    have hq : (0 : ℝ) < typeSize q := by
      exact_mod_cast Fintype.card_pos_iff.mpr he
    have hP : (0 : ℝ) < Fintype.card (Phases A (Fintype.card S)) := by
      exact_mod_cast Fintype.card_pos
    have ha0 := Complex.normSq_nonneg (tensorVector (empiricalAmplitude a) a)
    have hx0 := Complex.normSq_nonneg (typeSum x q)
    have hD0 : (0 : ℝ) ≤ ((Fintype.card S+1)^(Fintype.card A) : ℕ) := Nat.cast_nonneg _
    rw [div_le_iff₀ hq]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hP]
    nlinarith [mul_le_mul_of_nonneg_right hp hx0,
      mul_le_mul_of_nonneg_left ht (mul_nonneg hD0 (le_of_lt hq))]
  · let : IsEmpty {w : S → A // counts w = q} := not_nonempty_iff.mp he
    have hx : typeSum x q = 0 := by simp [typeSum]
    rw [hx, Complex.normSq_zero, zero_div]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

/-- Exact finite symmetric-vector postselection, with a polynomial cost
in the slot number and alphabet size. Every mixture vector is a normalized
identical-slot tensor power; the construction is explicit and finite. -/
theorem symmetric_postselection (a₀ : S → A) (hn : 0 < Fintype.card S)
    (v x : (S → A) → ℂ) (hv : ∀ a b, counts a = counts b → v a = v b) :
    Complex.normSq (∑ w, v w * x w) ≤
      (∑ w, Complex.normSq (v w)) *
      (((Fintype.card S+1)^(Fintype.card A) : ℕ) /
        (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := A),
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w, tensorVector (twistedAmplitude (typeRepresentative a₀ q) θ) w * x w)) := by
  apply (invariant_vector_bound v x hv).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun q _ => type_representative_bound a₀ hn x q)

end RowColumn.Postselection

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- Truncating purification letters preserves positivity after partial trace.
It is how the postselection mixture is constrained to even one-slot states. -/
def truncateAmplitude (good : A → Prop) [DecidablePred good] (z : A → ℂ) : A → ℂ :=
  fun c => if good c then z c else 0

omit [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma tensorVector_truncate (good : A → Prop) [DecidablePred good]
    (z : A → ℂ) (w : S → A) :
    tensorVector (truncateAmplitude good z) w =
      if ∀ i, good (w i) then tensorVector z w else 0 := by
  by_cases h : ∀ i, good (w i)
  · simp [tensorVector, truncateAmplitude, h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [truncateAmplitude, hi])

omit [DecidableEq S] in
lemma truncated_twisted_subnormalized (good : A → Prop) [DecidablePred good]
    (a : S → A) (hn : 0 < Fintype.card S) (θ : Phases A (Fintype.card S)) :
    (∑ c, Complex.normSq (truncateAmplitude good (twistedAmplitude a θ) c)) ≤ 1 := by
  rw [← twistedAmplitude_normalized a hn θ]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : good c
  · simp [truncateAmplitude, hc]
  · simpa [truncateAmplitude, hc] using Complex.normSq_nonneg (twistedAmplitude a θ c)

/-- Symmetric postselection retaining a prescribed alphabet support. In the
application good(c,e) means that the physical and auxiliary parities agree,
so the resulting Gram states are block diagonal. -/
theorem supported_symmetric_postselection (a₀ : S → A) (hn : 0 < Fintype.card S)
    (good : A → Prop) [DecidablePred good] (v x : (S → A) → ℂ)
    (hv : ∀ a b, counts a = counts b → v a = v b)
    (hsupp : ∀ w, ¬ (∀ i, good (w i)) → v w = 0) :
    Complex.normSq (∑ w, v w * x w) ≤
      (∑ w, Complex.normSq (v w)) *
      (((Fintype.card S+1)^(Fintype.card A) : ℕ) /
        (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := A),
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w,
          tensorVector (truncateAmplitude good (twistedAmplitude (typeRepresentative a₀ q) θ)) w * x w)) := by
  let y : (S → A) → ℂ := fun w => if ∀ i, good (w i) then x w else 0
  have he (w : S → A) : v w * y w = v w * x w := by
    by_cases hw : ∀ i, good (w i)
    · simp [y, hw]
    · simp [y, hw, hsupp w hw]
  have ht (z : A → ℂ) (w : S → A) :
      tensorVector z w * y w = tensorVector (truncateAmplitude good z) w * x w := by
    rw [tensorVector_truncate]
    by_cases hw : ∀ i, good (w i) <;> simp [y, hw]
  have hh := symmetric_postselection a₀ hn v y hv
  simpa only [he, ht] using hh

end RowColumn.Postselection
namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def pairWordsEquiv : (S → C × C) ≃ (S → C) × (S → C) where
  toFun a := (fun i => (a i).1, fun i => (a i).2)
  invFun w := fun i => (w.1 i,w.2 i)
  left_inv := by intro a; rfl
  right_inv := by intro w; rfl

def purificationVector (B : (S → C) → (S → C) → ℂ) (a : S → C × C) : ℂ :=
  B (fun i => (a i).1) (fun i => (a i).2)

def purificationTest (x : (S → C) → ℂ) (v : S → C) (a : S → C × C) : ℂ :=
  if (fun i => (a i).2) = v then x (fun i => (a i).1) else 0

def productPurifier (z : C × C → ℂ) (w v : S → C) : ℂ := ∏ i : S, z (w i,v i)

def purifierQuadratic (B : (S → C) → (S → C) → ℂ) (x : (S → C) → ℂ) : ℝ :=
  ∑ v : S → C, Complex.normSq (∑ w : S → C, B w v * x w)

def purifierTrace (B : (S → C) → (S → C) → ℂ) : ℝ :=
  ∑ w : S → C, ∑ v : S → C, Complex.normSq (B w v)

lemma purification_pair (B : (S → C) → (S → C) → ℂ) (x : (S → C) → ℂ) (v : S → C) :
    (∑ a : S → C × C, purificationVector B a * purificationTest x v a) =
      ∑ w : S → C, B w v * x w := by
  calc
    _ = ∑ p : (S → C) × (S → C), B p.1 p.2 * (if p.2 = v then x p.1 else 0) :=
      Fintype.sum_equiv pairWordsEquiv _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp [mul_ite]

omit [DecidableEq C] in
lemma purification_normSq (B : (S → C) → (S → C) → ℂ) :
    (∑ a : S → C × C, Complex.normSq (purificationVector B a)) = purifierTrace B := by
  calc
    _ = ∑ p : (S → C) × (S → C), Complex.normSq (B p.1 p.2) :=
      Fintype.sum_equiv pairWordsEquiv _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

lemma productPurifier_pair (z : C × C → ℂ) (x : (S → C) → ℂ) (v : S → C) :
    (∑ a : S → C × C, tensorVector z a * purificationTest x v a) =
      ∑ w : S → C, productPurifier z w v * x w := by
  exact purification_pair (productPurifier z) x v

omit [DecidableEq S] [Fintype C] in
lemma purification_invariant (B : (S → C) → (S → C) → ℂ)
    (hB : ∀ (p : Equiv.Perm S) (w v : S → C),
      B (fun i => w (p i)) (fun i => v (p i)) = B w v)
    (a b : S → C × C) (he : counts a = counts b) :
    purificationVector B a = purificationVector B b := by
  obtain ⟨p,hp⟩ := same_counts_permutation a b he
  have h₁ : (fun i => (a i).1) = fun i => (b (p i)).1 := by
    funext i; exact congrArg Prod.fst (hp i).symm
  have h₂ : (fun i => (a i).2) = fun i => (b (p i)).2 := by
    funext i; exact congrArg Prod.snd (hp i).symm
  change B (fun i => (a i).1) (fun i => (a i).2) = _
  rw [h₁,h₂]
  exact hB p (fun i => (b i).1) (fun i => (b i).2)

/-- Explicit positive identical-slot domination at the purification level.
The matrix factor is symmetric under actual slot permutations and has the
specified letter support. This is the quantitative local-state dependency
of the occupied-board main, not an assumed main overlap estimate. -/
theorem matrix_postselection (a₀ : S → C × C) (hn : 0 < Fintype.card S)
    (good : C × C → Prop) [DecidablePred good]
    (B : (S → C) → (S → C) → ℂ)
    (hB : ∀ (p : Equiv.Perm S) (w v : S → C),
      B (fun i => w (p i)) (fun i => v (p i)) = B w v)
    (hsupp : ∀ w v, ¬ (∀ i, good (w i,v i)) → B w v = 0)
    (x : (S → C) → ℂ) :
    purifierQuadratic B x ≤ purifierTrace B *
      (((Fintype.card S+1)^(Fintype.card (C × C)) : ℕ) /
        (Fintype.card (Phases (C × C) (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := C × C),
      ∑ θ : Phases (C × C) (Fintype.card S),
        purifierQuadratic (productPurifier
          (truncateAmplitude good (twistedAmplitude (typeRepresentative a₀ q) θ))) x) := by
  have hv := purification_invariant B hB
  have hs (a : S → C × C) (ha : ¬ ∀ i, good (a i)) : purificationVector B a = 0 := by
    exact hsupp _ _ ha
  have hh (v : S → C) := supported_symmetric_postselection a₀ hn good
    (purificationVector B) (purificationTest x v) hv hs
  simp_rw [purification_pair, purification_normSq, productPurifier_pair] at hh
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hh v)
  change purifierQuadratic B x ≤ _ at hsum
  apply hsum.trans_eq
  simp only [Finset.mul_sum, purifierQuadratic]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]

end RowColumn.Postselection

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I]

lemma sqrt_commute (A T : Matrix I I ℂ) (_ : A.PosSemidef) (h : Commute A T) :
    Commute (CFC.sqrt A) T := by
  rw [CFC.sqrt_eq_cfc]
  exact h.cfc_nnreal _

lemma commute_perm_iff (A : Matrix I I ℂ) (p : Equiv.Perm I) :
    Commute A (p.permMatrix ℂ) ↔ ∀ i j, A (p i) (p j) = A i j := by
  change A * p.permMatrix ℂ = p.permMatrix ℂ * A ↔ _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  constructor
  · intro h i j
    have hh := congrArg (fun M : Matrix I I ℂ => M i (p j)) h
    simpa using hh.symm
  · intro h
    ext i j
    exact (h i (p.symm j)).symm.trans (by simp)

lemma sqrt_permutation_invariant (A : Matrix I I ℂ) (hA : A.PosSemidef)
    (p : Equiv.Perm I) (h : ∀ i j, A (p i) (p j) = A i j) :
    ∀ i j, CFC.sqrt A (p i) (p j) = CFC.sqrt A i j :=
  (commute_perm_iff _ p).mp (sqrt_commute A _ hA ((commute_perm_iff A p).mpr h))

lemma commute_diagonal_iff (A : Matrix I I ℂ) (d : I → ℂ) :
    Commute A (Matrix.diagonal d) ↔ ∀ i j, A i j * d j = d i * A i j := by
  change _ = _ ↔ _
  constructor
  · intro h i j
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrArg (fun M : Matrix I I ℂ => M i j) h
  · intro h; ext i j; simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

lemma sqrt_block_supported [DecidableEq J] (b : I → J)
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (h : ∀ i j, b i ≠ b j → A i j = 0) :
    ∀ i j, b i ≠ b j → CFC.sqrt A i j = 0 := by
  intro i j hij
  let d : I → ℂ := fun k => if b k = b i then 1 else 0
  have hc : Commute A (Matrix.diagonal d) := by
    apply (commute_diagonal_iff A d).mpr
    intro k l
    by_cases he : b k = b l
    · simp [d, he, mul_comm]
    · simp [h k l he]
  have hs := (commute_diagonal_iff (CFC.sqrt A) d).mp (sqrt_commute A _ hA hc) i j
  simpa [d, Ne.symm hij] using hs.symm

/-- Bilinear-coordinate quadratic form. Complex conjugation is placed in the
second coordinate, matching the purification formulas used below. -/
def quadratic (A : Matrix I I ℂ) (x : I → ℂ) : ℝ :=
  (∑ i, ∑ j, A i j * x i * star (x j)).re

def factorQuadratic (B : Matrix I I ℂ) (x : I → ℂ) : ℝ :=
  ∑ v, Complex.normSq (∑ w, B w v * x w)

lemma normSq_eq_re (z : ℂ) : Complex.normSq z = (z * star z).re := by
  rw [Complex.star_def, Complex.mul_conj]
  rfl

omit [DecidableEq I] in
lemma factorQuadratic_eq (B : Matrix I I ℂ) (x : I → ℂ) :
    factorQuadratic B x = quadratic (B * B.conjTranspose) x := by
  simp only [factorQuadratic, quadratic, Matrix.mul_apply, Matrix.conjTranspose_apply,
    normSq_eq_re, star_sum, star_mul, Complex.re_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  ring

lemma sqrt_factorQuadratic (A : Matrix I I ℂ) (hA : A.PosSemidef) (x : I → ℂ) :
    factorQuadratic (CFC.sqrt A) x = quadratic A x := by
  rw [factorQuadratic_eq, (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq,
    CFC.sqrt_mul_sqrt_self A hA.nonneg]

lemma sqrt_trace (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    (∑ w, ∑ v, Complex.normSq (CFC.sqrt A w v)) = A.trace.re := by
  have hs : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have he : CFC.sqrt A * (CFC.sqrt A).conjTranspose = A := by
    rw [hs, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  conv_rhs => rw [← he]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  exact normSq_eq_re _

end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def tensorMatrix (M : S → Matrix C C ℂ) : Matrix (S → C) (S → C) ℂ :=
  fun w v => ∏ i, M i (w i) (v i)

omit [DecidableEq C] in
lemma tensorMatrix_mul (A B : S → Matrix C C ℂ) :
    tensorMatrix A * tensorMatrix B = tensorMatrix (fun i => A i * B i) := by
  ext w v
  simp only [tensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i : S => fun c : C => A i (w i) c * B i c (v i))).symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma tensorMatrix_star (A : S → Matrix C C ℂ) :
    (tensorMatrix A).conjTranspose = tensorMatrix (fun i => (A i).conjTranspose) := by
  ext w v
  simp [tensorMatrix, Matrix.conjTranspose_apply, star_prod]

omit [DecidableEq C] in
lemma tensorMatrix_trace (A : S → Matrix C C ℂ) :
    (tensorMatrix A).trace = ∏ i, (A i).trace := by
  simp only [tensorMatrix, Matrix.trace, Matrix.diag]
  exact (Fintype.prod_sum (fun i : S => fun c : C => A i c c)).symm

omit [DecidableEq S] [Fintype C] in
lemma tensorMatrix_one : tensorMatrix (fun _ : S => (1 : Matrix C C ℂ)) = 1 := by
  ext w v
  by_cases he : w = v
  · subst v; simp [tensorMatrix]
  · have hn : ∃ i, w i ≠ v i := Function.ne_iff.mp he
    obtain ⟨i,hi⟩ := hn
    rw [Matrix.one_apply_ne he]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

lemma tensorMatrix_posSemidef (A : S → Matrix C C ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensorMatrix A).PosSemidef := by
  let B := fun i => CFC.sqrt (A i)
  have hb (i : S) : (B i).conjTranspose * B i = A i := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A i))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ (hA i).nonneg
  have he : (tensorMatrix B).conjTranspose * tensorMatrix B = tensorMatrix A := by
    rw [tensorMatrix_star, tensorMatrix_mul]
    simp_rw [hb]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def letterMatrix (z : C × C → ℂ) : Matrix C C ℂ := fun c d => z (c,d)

/-- A purification letter z is an actual one-slot substate after partial trace. -/
def gramState (z : C × C → ℂ) : Matrix C C ℂ :=
  letterMatrix z * (letterMatrix z).conjTranspose

omit [DecidableEq C] in
lemma gramState_posSemidef (z : C × C → ℂ) : (gramState z).PosSemidef := by
  have hh := Matrix.posSemidef_conjTranspose_mul_self
    (letterMatrix z).conjTranspose
  simpa only [Matrix.conjTranspose_conjTranspose, gramState] using hh

omit [DecidableEq C] in
lemma gramState_trace (z : C × C → ℂ) :
    (gramState z).trace.re = ∑ p : C × C, Complex.normSq (z p) := by
  rw [Fintype.sum_prod_type]
  simp only [gramState, letterMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [Complex.star_def, Complex.mul_conj]
  rfl

omit [DecidableEq C] in
lemma gramState_parity_supported (odd : C → Prop) [DecidablePred odd]
    (z : C × C → ℂ) (hz : ∀ c d, ¬ (odd c ↔ odd d) → z (c,d) = 0)
    (c d : C) (hc : ¬ (odd c ↔ odd d)) : gramState z c d = 0 := by
  simp only [gramState, Matrix.mul_apply, letterMatrix, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : odd c ↔ odd e
  · have hd : ¬ (odd d ↔ odd e) := fun h => hc (he.trans h.symm)
    simp [hz d e hd]
  · simp [hz c e he]

end RowColumn.MatrixState

namespace RowColumn.Postselection
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open MatrixState WordOrbits
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def reindexWord (p : Equiv.Perm S) : Equiv.Perm (S → C) where
  toFun w := fun i => w (p i)
  invFun w := fun i => w (p.symm i)
  left_inv := by intro w; ext i; simp
  right_inv := by intro w; ext i; simp

omit [DecidableEq C] in
lemma productPurifier_quadratic (z : C × C → ℂ) (x : (S → C) → ℂ) :
    purifierQuadratic (productPurifier z) x =
      quadratic (tensorMatrix (fun _ : S => gramState z)) x := by
  change factorQuadratic (tensorMatrix (fun _ : S => letterMatrix z)) x = _
  rw [factorQuadratic_eq, tensorMatrix_star, tensorMatrix_mul]
  rfl

def localAmplitude (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := C × C)) (θ : Phases (C × C) (Fintype.card S)) : C × C → ℂ :=
  truncateAmplitude (fun p : C × C => odd p.1 ↔ odd p.2)
    (twistedAmplitude (typeRepresentative a₀ q) θ)

def localState (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := C × C)) (θ : Phases (C × C) (Fintype.card S)) : Matrix C C ℂ :=
  gramState (localAmplitude a₀ odd q θ)

omit [DecidableEq S] in
lemma localState_positive (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := C × C)) (θ : Phases (C × C) (Fintype.card S)) :
    (localState a₀ odd q θ).PosSemidef := gramState_posSemidef _

omit [DecidableEq S] in
lemma localState_trace_le_one (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (hn : 0 < Fintype.card S)
    (q : Types (S := S) (A := C × C)) (θ : Phases (C × C) (Fintype.card S)) :
    (localState a₀ odd q θ).trace.re ≤ 1 := by
  rw [localState, gramState_trace]
  exact truncated_twisted_subnormalized _ _ hn _

omit [DecidableEq S] in
lemma localState_even (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := C × C)) (θ : Phases (C × C) (Fintype.card S))
    (c d : C) (hp : ¬ (odd c ↔ odd d)) : localState a₀ odd q θ c d = 0 := by
  apply gramState_parity_supported odd _ _ c d hp
  intro c d h
  simp [localAmplitude, truncateAmplitude, h]

/-- Quantitative positive mixture of genuine even identical-slot states for a
PSD matrix invariant under unsigned slot permutations and supported on physical
parity blocks. The polynomial includes only the explicitly finite type count;
no structural duality or postselection axiom is assumed. -/
theorem positive_state_postselection (a₀ : S → C × C) (hn : 0 < Fintype.card S)
    (odd : C → Prop) [DecidablePred odd] (A : Matrix (S → C) (S → C) ℂ)
    (hA : A.PosSemidef)
    (hinv : ∀ (p : Equiv.Perm S) (w v : S → C),
      A (fun i => w (p i)) (fun i => v (p i)) = A w v)
    (hsupp : ∀ w v, ¬ (∀ i, odd (w i) ↔ odd (v i)) → A w v = 0)
    (x : (S → C) → ℂ) :
    quadratic A x ≤ A.trace.re *
      (((Fintype.card S+1)^(Fintype.card (C × C)) : ℕ) /
        (Fintype.card (Phases (C × C) (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := C × C),
      ∑ θ : Phases (C × C) (Fintype.card S),
        quadratic (tensorMatrix (fun _ : S => localState a₀ odd q θ)) x) := by
  let B : Matrix (S → C) (S → C) ℂ := CFC.sqrt A
  have hi (p : Equiv.Perm S) (w v : S → C) :
      B (fun i => w (p i)) (fun i => v (p i)) = B w v :=
    sqrt_permutation_invariant A hA (reindexWord p) (hinv p) w v
  have hz (w v : S → C) (hh : ¬ ∀ i, odd (w i) ↔ odd (v i)) : B w v = 0 := by
    apply sqrt_block_supported (fun u : S → C => fun i => odd (u i)) A hA
      (fun u v he => hsupp u v (fun ht => he (funext fun i => propext (ht i)))) w v
    intro he
    exact hh (fun i => Iff.of_eq (congrFun he i))
  have h := matrix_postselection a₀ hn (fun p : C × C => odd p.1 ↔ odd p.2)
    B hi hz x
  change factorQuadratic B x ≤ _ at h
  change factorQuadratic (CFC.sqrt A) x ≤ _ at h
  rw [sqrt_factorQuadratic A hA] at h
  have ht : purifierTrace B = A.trace.re := sqrt_trace A hA
  rw [ht] at h
  simpa only [productPurifier_quadratic, localState, localAmplitude] using h

end RowColumn.Postselection

end
end
end
end
end

end OAI
