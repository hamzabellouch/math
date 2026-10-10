import OAI.Analysis.MarkovType.FiniteCharts
import OAI.Analysis.MarkovType.FiniteCoupling
import OAI.Analysis.MarkovType.FiniteProbability
import OAI.Analysis.MarkovType.MarkedChains
import Mathlib.Data.Fintype.Prod

namespace OAI

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

universe u v

namespace FiniteCoupling

variable {A : Type u} [Fintype A] {p : A → ℝ}

def eventMass (k : FiniteCoupling p p) (G : A → A → Prop) : ℝ :=
  ∑ a, ∑ b, if G a b then k.weight a b else 0

theorem eventMass_nonneg (k : FiniteCoupling p p) (G : A → A → Prop) :
    0 ≤ k.eventMass G := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact k.nonneg a b
  · exact le_rfl

theorem eventMass_compl (k : FiniteCoupling p p) (hpsum : ∑ a, p a = 1)
    (G : A → A → Prop) : k.eventMass (fun a b => ¬ G a b) = 1 - k.eventMass G := by
  have hsum : k.eventMass (fun a b => ¬ G a b) + k.eventMass G = 1 := by
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ a, ∑ b, k.weight a b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hab : G a b <;> simp [hab]
      _ = 1 := by simp only [k.row_sum, hpsum]
  linarith

theorem eventMass_average (k l : FiniteCoupling p p) (G : A → A → Prop) :
    (k.average l).eventMass G = (k.eventMass G + l.eventMass G) / 2 := by
  have hpoint (a b : A) :
      (if G a b then (k.weight a b + l.weight a b) / 2 else 0) =
        ((if G a b then k.weight a b else 0) +
          (if G a b then l.weight a b else 0)) / 2 := by
    by_cases h : G a b <;> simp [h]
  simp only [eventMass, average, hpoint]
  simp only [Finset.sum_div, Finset.sum_add_distrib, add_div]

theorem eventMass_transpose (k : FiniteCoupling p p) (G H : A → A → Prop)
    (hGH : ∀ a b, G a b ↔ H b a) :
    k.transpose.eventMass G = k.eventMass H := by
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [transpose, hGH b a]

end FiniteCoupling

def symmetrizeFiniteCouplings {A : Type u} {L : Type v} [Fintype A]
    {p : A → ℝ} (inv : L → L) (Γ : ∀ _s : L, FiniteCoupling p p)
    (s : L) : FiniteCoupling p p :=
  (Γ s).average (Γ (inv s)).transpose

theorem symmetrizeFiniteCouplings_reverse {A : Type u} {L : Type v} [Fintype A]
    {p : A → ℝ} (inv : L → L) (hinv : Function.Involutive inv)
    (Γ : ∀ _s : L, FiniteCoupling p p) (s : L) (a b : A) :
    (symmetrizeFiniteCouplings inv Γ (inv s)).weight b a =
      (symmetrizeFiniteCouplings inv Γ s).weight a b := by
  simp only [symmetrizeFiniteCouplings, FiniteCoupling.average,
    FiniteCoupling.transpose, hinv s, add_comm]

theorem symmetrizeFiniteCouplings_good {A : Type u} {L : Type v} [Fintype A]
    {p : A → ℝ} (inv : L → L) (Γ : ∀ _s : L, FiniteCoupling p p)
    (G : L → A → A → Prop) (hrev : ∀ s a b, G s a b ↔ G (inv s) b a)
    {ε : ℝ} (hgood : ∀ s, 1 - ε ≤ (Γ s).eventMass (G s)) (s : L) :
    1 - ε ≤ (symmetrizeFiniteCouplings inv Γ s).eventMass (G s) := by
  rw [symmetrizeFiniteCouplings, FiniteCoupling.eventMass_average,
    FiniteCoupling.eventMass_transpose _ (G s) (G (inv s)) (hrev s)]
  linarith [hgood s, hgood (inv s)]

def chartTransportDomain (Λ : Finset ℝ) (h : ℝ ≃o ℝ) : Finset ℝ :=
  Λ.filter (fun x => h x ∈ Λ)

def chartTransportDomainSource (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    ↥(chartTransportDomain Λ h) ↪o ↥Λ where
  toFun x := ⟨h (x : ℝ), (Finset.mem_filter.mp x.property).2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact h.injective (congrArg Subtype.val hxy)
  map_rel_iff' := by
    intro x y
    exact h.le_iff_le

def chartTransportDomainTarget (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    ↥(chartTransportDomain Λ h) ↪o ↥Λ where
  toFun x := ⟨(x : ℝ), (Finset.mem_filter.mp x.property).1⟩
  inj' := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : ↥Λ => (z : ℝ)) hxy)
  map_rel_iff' := Iff.rfl

def chartTransportSourceTuple (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    Fin (chartTransportDomain Λ h).card ↪o ↥Λ :=
  ((chartTransportDomain Λ h).orderIsoOfFin rfl).toOrderEmbedding.trans
    (chartTransportDomainSource Λ h)

def chartTransportTargetTuple (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    Fin (chartTransportDomain Λ h).card ↪o ↥Λ :=
  ((chartTransportDomain Λ h).orderIsoOfFin rfl).toOrderEmbedding.trans
    (chartTransportDomainTarget Λ h)

theorem chart_good_iff_transport_tuple {Λ : Finset ℝ} {B : ℕ}
    (h : ℝ ≃o ℝ) (C C' : Chart Λ B) :
    Chart.Good h C C' ↔
      (chartTransportSourceTuple Λ h).trans C =
        (chartTransportTargetTuple Λ h).trans C' := by
  constructor
  · intro hg
    apply DFunLike.ext
    intro i
    let x := (chartTransportDomain Λ h).orderIsoOfFin rfl i
    exact (hg ⟨(x : ℝ), (Finset.mem_filter.mp x.property).1⟩
      (Finset.mem_filter.mp x.property).2).symm
  · intro heq x hx
    let d : ↥(chartTransportDomain Λ h) :=
      ⟨(x : ℝ), Finset.mem_filter.mpr ⟨x.property, hx⟩⟩
    let i := ((chartTransportDomain Λ h).orderIsoOfFin rfl).symm d
    have hd : (chartTransportDomain Λ h).orderIsoOfFin rfl i = d :=
      ((chartTransportDomain Λ h).orderIsoOfFin rfl).apply_symm_apply d
    have hi := congrArg (fun F : Fin (chartTransportDomain Λ h).card ↪o Fin B => F i) heq
    change C (chartTransportDomainSource Λ h ((chartTransportDomain Λ h).orderIsoOfFin rfl i)) =
      C' (chartTransportDomainTarget Λ h ((chartTransportDomain Λ h).orderIsoOfFin rfl i)) at hi
    rw [hd] at hi
    exact hi.symm

def preliminaryChartCoupling {Λ : Finset ℝ} {B : ℕ}
    (ν : FiniteLaw (Chart Λ B)) (h : ℝ ≃o ℝ) :
    FiniteCoupling ν.mass ν.mass :=
  maximalFeatureCoupling ν.mass ν.mass
    (fun C => (chartTransportSourceTuple Λ h).trans C)
    (fun C => (chartTransportTargetTuple Λ h).trans C)
    ν.mass_nonneg ν.mass_nonneg ν.sum_mass ν.sum_mass

theorem preliminaryChartCoupling_good_mass {Λ : Finset ℝ} {B : ℕ}
    (ν : FiniteLaw (Chart Λ B)) (h : ℝ ≃o ℝ) :
    (preliminaryChartCoupling ν h).eventMass (Chart.Good h) =
      1 - finiteTotalVariation
        (finitePushforward ν.mass (fun C => (chartTransportSourceTuple Λ h).trans C))
        (finitePushforward ν.mass (fun C => (chartTransportTargetTuple Λ h).trans C)) := by
  simp only [FiniteCoupling.eventMass, chart_good_iff_transport_tuple,
    preliminaryChartCoupling]
  exact maximalFeatureCoupling_matching_mass _ _ _ _
    ν.mass_nonneg ν.mass_nonneg ν.sum_mass ν.sum_mass

abbrev PositiveMassSupport {A : Type u} [Fintype A] (ν : FiniteLaw A) :=
  {a : A // 0 < ν.mass a}

theorem mass_zero_outside_positive_support {A : Type u} [Fintype A]
    (ν : FiniteLaw A) {a : A} (ha : ¬ 0 < ν.mass a) : ν.mass a = 0 :=
  le_antisymm (le_of_not_gt ha) (ν.mass_nonneg a)

theorem sum_positive_support {A : Type u} [Fintype A] (ν : FiniteLaw A)
    (f : A → ℝ) (hf : ∀ a, ¬ 0 < ν.mass a → f a = 0) :
    ∑ a : PositiveMassSupport ν, f a = ∑ a, f a := by
  exact (Finset.sum_congr_set {a | 0 < ν.mass a} f (fun a => f a)
    (fun _ _ => rfl) hf).symm

def positiveSupportLaw {A : Type u} [Fintype A] (ν : FiniteLaw A) :
    FiniteLaw (PositiveMassSupport ν) where
  mass a := ν.mass a
  mass_nonneg a := ν.mass_nonneg a
  sum_mass := by
    rw [sum_positive_support ν ν.mass (fun a ha => mass_zero_outside_positive_support ν ha)]
    exact ν.sum_mass

def restrictPositiveCoupling {A : Type u} [Fintype A] (ν : FiniteLaw A)
    (k : FiniteCoupling ν.mass ν.mass) :
    FiniteCoupling (positiveSupportLaw ν).mass (positiveSupportLaw ν).mass where
  weight a b := k.weight a b
  nonneg a b := k.nonneg a b
  row_sum a := by
    rw [sum_positive_support ν (fun b => k.weight a b)
      (fun b hb => k.weight_eq_zero_of_col a (mass_zero_outside_positive_support ν hb))]
    exact k.row_sum a
  col_sum b := by
    rw [sum_positive_support ν (fun a => k.weight a b)
      (fun a ha => k.weight_eq_zero_of_row (mass_zero_outside_positive_support ν ha) b)]
    exact k.col_sum b

theorem restrictPositiveCoupling_eventMass {A : Type u} [Fintype A]
    (ν : FiniteLaw A) (k : FiniteCoupling ν.mass ν.mass) (G : A → A → Prop) :
    (restrictPositiveCoupling ν k).eventMass (fun a b => G a b) = k.eventMass G := by
  unfold FiniteCoupling.eventMass
  change (∑ a : PositiveMassSupport ν, ∑ b : PositiveMassSupport ν,
    if G a b then k.weight a b else 0) = _
  calc
    _ = ∑ a : PositiveMassSupport ν, ∑ b : A, if G a b then k.weight a b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply sum_positive_support ν (fun b : A => if G (a : A) b then k.weight (a : A) b else 0)
      intro b hb
      rw [k.weight_eq_zero_of_col a (mass_zero_outside_positive_support ν hb)]
      simp
    _ = ∑ a : A, ∑ b : A, if G a b then k.weight a b else 0 := by
      apply sum_positive_support ν (fun a : A => ∑ b : A, if G a b then k.weight a b else 0)
      intro a ha
      have hzero := k.weight_eq_zero_of_row (mass_zero_outside_positive_support ν ha)
      simp only [hzero, ite_self, Finset.sum_const_zero]

abbrev UniformCouplingEdge (A : Type u) (L : Type v) := A × L × A

def uniformCouplingChain {A : Type u} {L : Type v} [Fintype A] [Fintype L]
    [Nonempty L] (ν : FiniteLaw A) (hν : ∀ a, 0 < ν.mass a)
    (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b) :
    FiniteMarkedChain A (UniformCouplingEdge A L) where
  π := ν.mass
  π_nonneg := ν.mass_nonneg
  sum_π := ν.sum_mass
  src e := e.1
  tgt e := e.2.2
  rev e := (e.2.2, inv e.2.1, e.1)
  rev_rev e := by rcases e with ⟨a,s,b⟩; simp only [hinv s]
  src_rev _ := rfl
  tgt_rev _ := rfl
  q e := (couplings e.2.1).weight e.1 e.2.2 / ((Fintype.card L : ℝ) * ν.mass e.1)
  q_nonneg e := div_nonneg ((couplings e.2.1).nonneg e.1 e.2.2)
    (mul_nonneg (Nat.cast_nonneg _) (ν.mass_nonneg e.1))
  sum_q a := by
    have hcard : (Fintype.card L : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0)
    have ha : ν.mass a ≠ 0 := ne_of_gt (hν a)
    simp only [Fintype.sum_prod_type]
    simp_rw [Finset.sum_ite_irrel]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    simp_rw [← Finset.sum_div, (couplings _).row_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  balance e := by
    rcases e with ⟨a,s,b⟩
    have ha : ν.mass a ≠ 0 := ne_of_gt (hν a)
    have hb : ν.mass b ≠ 0 := ne_of_gt (hν b)
    rw [hrev s a b]
    field_simp

theorem uniformCouplingChain_edge_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (e : UniformCouplingEdge A L) :
    (uniformCouplingChain ν hν inv hinv couplings hrev).π e.1 *
      (uniformCouplingChain ν hν inv hinv couplings hrev).q e =
        (couplings e.2.1).weight e.1 e.2.2 / (Fintype.card L : ℝ) := by
  change ν.mass e.1 * ((couplings e.2.1).weight e.1 e.2.2 /
    ((Fintype.card L : ℝ) * ν.mass e.1)) = _
  have ha := ne_of_gt (hν e.1)
  field_simp

theorem uniformCouplingChain_letter_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (a : A) (s : L) :
    (∑ b, (uniformCouplingChain ν hν inv hinv couplings hrev).q (a,s,b)) =
      (Fintype.card L : ℝ)⁻¹ := by
  change (∑ b, (couplings s).weight a b / ((Fintype.card L : ℝ) * ν.mass a)) = _
  rw [← Finset.sum_div, (couplings s).row_sum]
  have ha := ne_of_gt (hν a)
  field_simp

theorem uniformCouplingChain_marked_letter_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (a : A) (s : L) :
    (∑ e : UniformCouplingEdge A L, if e.1 = a ∧ e.2.1 = s then
      (uniformCouplingChain ν hν inv hinv couplings hrev).q e else 0) =
        (Fintype.card L : ℝ)⁻¹ := by
  classical
  simp only [Fintype.sum_prod_type]
  simp_rw [show ∀ (x : A) (t : L) (y : A),
      (if x = a ∧ t = s then (uniformCouplingChain ν hν inv hinv couplings hrev).q (x,t,y) else 0) =
      (if x = a then if t = s then
        (uniformCouplingChain ν hν inv hinv couplings hrev).q (x,t,y) else 0 else 0) from
    fun x t y => by by_cases hx : x = a <;> by_cases ht : t = s <;> simp [hx, ht]]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
  exact uniformCouplingChain_letter_mass ν hν inv hinv couplings hrev a s

theorem uniformCouplingChain_good_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (G : L → A → A → Prop) {ε : ℝ}
    (hgood : ∀ s, 1 - ε ≤ (couplings s).eventMass (G s)) :
    1 - ε ≤ ∑ e : UniformCouplingEdge A L, if G e.2.1 e.1 e.2.2 then
      (uniformCouplingChain ν hν inv hinv couplings hrev).π e.1 *
        (uniformCouplingChain ν hν inv hinv couplings hrev).q e else 0 := by
  have hcard : 0 < (Fintype.card L : ℝ) := by exact_mod_cast Fintype.card_pos
  simp_rw [uniformCouplingChain_edge_mass]
  have hsum : (∑ e : UniformCouplingEdge A L, if G e.2.1 e.1 e.2.2 then
      (couplings e.2.1).weight e.1 e.2.2 / (Fintype.card L : ℝ) else 0) =
      (∑ s, (couplings s).eventMass (G s)) / (Fintype.card L : ℝ) := by
    simp only [Fintype.sum_prod_type, FiniteCoupling.eventMass]
    rw [Finset.sum_comm]
    have hpoint (s : L) (a b : A) :
        (if G s a b then (couplings s).weight a b / (Fintype.card L : ℝ) else 0) =
        (if G s a b then (couplings s).weight a b else 0) / (Fintype.card L : ℝ) := by
      by_cases h : G s a b <;> simp [h]
    simp_rw [hpoint, ← Finset.sum_div]
  rw [hsum, le_div_iff₀ hcard]
  have hle := Finset.sum_le_sum (fun (s : L) (_ : s ∈ Finset.univ) => hgood s)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hle

def reversibleChartCoupling {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    (ν : FiniteLaw (Chart Λ B)) (inv : L → L) (h : L → ℝ ≃o ℝ)
    (s : L) : FiniteCoupling ν.mass ν.mass :=
  symmetrizeFiniteCouplings inv (fun t => preliminaryChartCoupling ν (h t)) s

theorem reversibleChartCoupling_good {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    (ν : FiniteLaw (Chart Λ B)) (inv : L → L) (h : L → ℝ ≃o ℝ)
    (hh : ∀ s, h (inv s) = (h s).symm) {ε : ℝ}
    (hTV : ∀ s, finiteTotalVariation
      (finitePushforward ν.mass (fun C => (chartTransportSourceTuple Λ (h s)).trans C))
      (finitePushforward ν.mass (fun C => (chartTransportTargetTuple Λ (h s)).trans C)) < ε)
    (s : L) :
    1 - ε ≤ (reversibleChartCoupling ν inv h s).eventMass (Chart.Good (h s)) := by
  apply symmetrizeFiniteCouplings_good inv (fun t => preliminaryChartCoupling ν (h t))
    (fun t => Chart.Good (h t))
  · intro t C C'
    rw [hh t]
    exact Chart.good_symm_iff (h t) C C'
  · intro t
    rw [preliminaryChartCoupling_good_mass]
    exact sub_le_sub_left (le_of_lt (hTV t)) 1

def chartTransportChain {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ) :
    FiniteMarkedChain (PositiveMassSupport ν) (UniformCouplingEdge (PositiveMassSupport ν) L) :=
  uniformCouplingChain (positiveSupportLaw ν) (fun C => C.property) inv hinv
    (fun s => restrictPositiveCoupling ν (reversibleChartCoupling ν inv h s))
    (fun s C C' => symmetrizeFiniteCouplings_reverse inv hinv
      (fun t => preliminaryChartCoupling ν (h t)) s C C')

theorem chartTransportChain_good_mass {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (hh : ∀ s, h (inv s) = (h s).symm) {ε : ℝ}
    (hTV : ∀ s, finiteTotalVariation
      (finitePushforward ν.mass (fun C => (chartTransportSourceTuple Λ (h s)).trans C))
      (finitePushforward ν.mass (fun C => (chartTransportTargetTuple Λ (h s)).trans C)) < ε) :
    1 - ε ≤ ∑ e : UniformCouplingEdge (PositiveMassSupport ν) L,
      if Chart.Good (h e.2.1) e.1.val e.2.2.val then
        (chartTransportChain ν inv hinv h).π e.1 *
          (chartTransportChain ν inv hinv h).q e else 0 := by
  refine uniformCouplingChain_good_mass (positiveSupportLaw ν) (fun C => C.property)
    inv hinv (fun s => restrictPositiveCoupling ν (reversibleChartCoupling ν inv h s))
    (fun s C C' => symmetrizeFiniteCouplings_reverse inv hinv
      (fun t => preliminaryChartCoupling ν (h t)) s C C')
    (fun s C C' => Chart.Good (h s) C.val C'.val) ?_
  intro s
  rw [restrictPositiveCoupling_eventMass]
  exact reversibleChartCoupling_good ν inv h hh hTV s

theorem chartTransportChain_marked_letter_mass {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (C : PositiveMassSupport ν) (s : L) :
    (∑ e : UniformCouplingEdge (PositiveMassSupport ν) L,
      if e.1 = C ∧ e.2.1 = s then (chartTransportChain ν inv hinv h).q e else 0) =
      (Fintype.card L : ℝ)⁻¹ := by
  refine Eq.trans ?_
    (uniformCouplingChain_marked_letter_mass (positiveSupportLaw ν) (fun D => D.property)
      inv hinv (fun t => restrictPositiveCoupling ν (reversibleChartCoupling ν inv h t))
      (fun t D D' => symmetrizeFiniteCouplings_reverse inv hinv
        (fun v => preliminaryChartCoupling ν (h v)) t D D') C s)
  apply Finset.sum_congr rfl
  intro e _
  by_cases hevent : e.1 = C ∧ e.2.1 = s
  · simp only [ite_eq_left hevent, chartTransportChain]
  · simp only [ite_eq_right hevent]

theorem chartTransportChain_reverse_ne {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (hfree : ∀ s, inv s ≠ s)
    (h : L → ℝ ≃o ℝ) (e : UniformCouplingEdge (PositiveMassSupport ν) L) :
    (chartTransportChain ν inv hinv h).rev e ≠ e := by
  intro heq
  exact hfree e.2.1 (congrArg (fun d => d.2.1) heq)

end MarkovSuperreflexivity

end

end OAI
