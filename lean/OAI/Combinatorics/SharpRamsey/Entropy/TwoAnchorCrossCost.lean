import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.PoissonLaw

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section PairWitnesses
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
section AnchorGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]
omit [Fintype ι] [DecidableEq κ] [DecidableEq H] in
theorem two_anchor_cross_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S T : Finset ι) (lineSet : H → Finset ι) (N₂ : ℕ)
    (hN : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun H => d ∈ lineSet H ∧ e ∈ lineSet H)).card ≤ N₂) :
    (∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
      if x.direction ≠ y.direction then x.cost rate * y.cost rate *
        (Finset.univ.filter (fun H => x.direction ∈ lineSet H ∧ y.direction ∈ lineSet H)).card
      else 0) ≤
      (N₂ : ℝ) * (C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ)) *
        (C.card + Fintype.card κ * ∑ i ∈ T, (rate i : ℝ)) := by
  classical
  calc
    _ ≤ ∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
        x.cost rate * y.cost rate * N₂ := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      split_ifs with hxy
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (x.cost_nonneg rate) (y.cost_nonneg rate))
        exact_mod_cast hN x.direction y.direction hxy
      · exact mul_nonneg (mul_nonneg (x.cost_nonneg rate) (y.cost_nonneg rate)) (Nat.cast_nonneg _)
    _ = (N₂ : ℝ) * (∑ x : AnchorChoice C S, x.cost rate) *
        (∑ y : AnchorChoice C T, y.cost rate) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (sum_anchor_cost_le rate C S) (Nat.cast_nonneg _)
      · exact sum_anchor_cost_le rate C T
      · exact Finset.sum_nonneg (fun x _ => x.cost_nonneg rate)
      · positivity

omit [Fintype ι] [DecidableEq κ] [DecidableEq H] in

lemma one_anchor_subtype_sum (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S : Finset ι) (lineSet : H → Finset ι) :
    (∑ x : AnchorChoice C S, ∑ _h : {h : H // x.direction ∈ lineSet h}, x.cost rate) =
      ∑ x : AnchorChoice C S, x.cost rate *
        (Finset.univ.filter (fun h => x.direction ∈ lineSet h)).card := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
    Fintype.card_subtype]

omit [Fintype ι] [DecidableEq κ] [DecidableEq H] in
lemma two_anchor_subtype_sum (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S T : Finset ι) (lineSet : H → Finset ι) :
    (∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
      ∑ _h : {h : H // x.direction ≠ y.direction ∧
        x.direction ∈ lineSet h ∧ y.direction ∈ lineSet h}, x.cost rate * y.cost rate) =
      ∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
        if x.direction ≠ y.direction then x.cost rate * y.cost rate *
          (Finset.univ.filter (fun h => x.direction ∈ lineSet h ∧ y.direction ∈ lineSet h)).card
        else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x.direction ≠ y.direction <;>
    simp [hxy, Fintype.card_subtype, mul_comm]

end AnchorGeometry

end PairWitnesses

end SharpRamseyFive.StaticCertificates

open scoped BigOperators
namespace SharpRamseyFive.CertificateEnumeration

universe u v
variable {S : Type u} {A : Type v}

def Word (A : Type v) : ℕ → Type v
  | 0 => PUnit
  | n + 1 => A × Word A n

instance flat_HighMomentRecovered_4 [Fintype A] (n : ℕ) : Fintype (Word A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (A × Word A n))

def finish (next : S → A → S) : {n : ℕ} → S → Word A n → S
  | 0, s, _ => s
  | _ + 1, s, w => finish next (next s w.1) w.2

noncomputable def pathWeight (next : S → A → S) (cost : S → A → ℝ) :
    {n : ℕ} → S → Word A n → ℝ
  | 0, _, _ => 1
  | _ + 1, s, w => cost s w.1 * pathWeight next cost (next s w.1) w.2

def charge (c : A → ℤ) : {n : ℕ} → Word A n → ℤ
  | 0, _ => 0
  | _ + 1, w => c w.1 + charge c w.2

lemma pathWeight_nonneg (next : S → A → S) (cost : S → A → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) {n : ℕ} (s : S) (w : Word A n) :
    0 ≤ pathWeight next cost s w := by
  induction n generalizing s with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hc s w.1) (ih _ w.2)

theorem sum_pathWeight_le [Fintype A] (next : S → A → S) (cost : S → A → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ s, (∑ a, cost s a) ≤ M) (n : ℕ) (s : S) :
    (∑ w : Word A n, pathWeight next cost s w) ≤ M ^ n := by
  induction n generalizing s with
  | zero =>
    let : Unique (Word A 0) := inferInstanceAs (Unique PUnit)
    simp [pathWeight]
  | succ n ih =>
    change (∑ w : A × Word A n, cost s w.1 *
      pathWeight next cost (next s w.1) w.2) ≤ M ^ (n + 1)
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ a, cost s a * ∑ w : Word A n, pathWeight next cost (next s a) w := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ a, cost s a * M ^ n := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (ih (next s a)) (hc s a)
      _ = (∑ a, cost s a) * M ^ n := by rw [Finset.sum_mul]
      _ ≤ M * M ^ n := mul_le_mul_of_nonneg_right (hrow s) (pow_nonneg hM n)
      _ = _ := (pow_succ' M n).symm

lemma reweighted_path (next : S → A → S) (cost : S → A → ℝ)
    (c : A → ℤ) (b : ℝ) (hb : b ≠ 0) {n : ℕ} (s : S) (w : Word A n) :
    pathWeight next (fun s a => cost s a * b ^ c a) s w =
      pathWeight next cost s w * b ^ charge c w := by
  induction n generalizing s with
  | zero => simp [pathWeight, charge]
  | succ n ih =>
    simp only [pathWeight, charge, ih, zpow_add₀ hb]
    ring

theorem constrained_path_sum_le [Fintype A] (next : S → A → S)
    (cost : S → A → ℝ) (hc : ∀ s a, 0 ≤ cost s a)
    (c : A → ℤ) (b M : ℝ) (hb : 1 ≤ b) (hM : 0 ≤ M)
    (hrow : ∀ s, (∑ a, cost s a * b ^ c a) ≤ M)
    (n : ℕ) (s : S) (valid : Word A n → Prop) [DecidablePred valid]
    (hvalid : ∀ w, valid w → 0 ≤ charge c w) :
    (∑ w : Word A n, if valid w then pathWeight next cost s w else 0) ≤ M ^ n := by
  classical
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  calc
    _ ≤ ∑ w : Word A n, pathWeight next (fun s a => cost s a * b ^ c a) s w := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with hv
      · rw [reweighted_path next cost c b hb0.ne']
        apply le_mul_of_one_le_right (pathWeight_nonneg next cost hc s w)
        exact one_le_zpow₀ hb (hvalid w hv)
      · exact pathWeight_nonneg next _
          (fun s a => mul_nonneg (hc s a) (zpow_nonneg hb0.le _)) s w
    _ ≤ _ := sum_pathWeight_le next _
      (fun s a => mul_nonneg (hc s a) (zpow_nonneg hb0.le _)) M hM hrow n s

lemma root_charge_nonneg (r s : ℕ) (h : 10 * r ≤ r + s) :
    0 ≤ (s : ℤ) - 8 * r := by omega

section Dependent
variable (C : S → Type v) (step : (s : S) → C s → S)

def DWord : ℕ → S → Type v
  | 0, _ => PUnit
  | n + 1, s => (a : C s) × DWord n (step s a)

instance flat_HighMomentRecovered_5 [∀ s, Fintype (C s)] (n : ℕ) (s : S) : Fintype (DWord C step n s) := by
  induction n generalizing s with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((a : C s) × DWord C step n (step s a)))

def dFinish : {n : ℕ} → (s : S) → DWord C step n s → S
  | 0, s, _ => s
  | _ + 1, s, w => dFinish (step s w.1) w.2

noncomputable def dWeight (cost : (s : S) → C s → ℝ) :
    {n : ℕ} → (s : S) → DWord C step n s → ℝ
  | 0, _, _ => 1
  | _ + 1, s, w => cost s w.1 * dWeight cost (step s w.1) w.2

def dCharge (c : (s : S) → C s → ℤ) :
    {n : ℕ} → (s : S) → DWord C step n s → ℤ
  | 0, _, _ => 0
  | _ + 1, s, w => c s w.1 + dCharge c (step s w.1) w.2

lemma dWeight_nonneg (cost : (s : S) → C s → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) {n : ℕ} (s : S) (w : DWord C step n s) :
    0 ≤ dWeight C step cost s w := by
  induction n generalizing s with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hc s w.1) (ih _ w.2)

theorem sum_dWeight_le [∀ s, Fintype (C s)] (cost : (s : S) → C s → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ s, (∑ a, cost s a) ≤ M) (n : ℕ) (s : S) :
    (∑ w : DWord C step n s, dWeight C step cost s w) ≤ M ^ n := by
  induction n generalizing s with
  | zero =>
    let : Unique (DWord C step 0 s) := inferInstanceAs (Unique PUnit)
    simp [dWeight]
  | succ n ih =>
    change (∑ w : (a : C s) × DWord C step n (step s a), cost s w.1 *
      dWeight C step cost (step s w.1) w.2) ≤ M ^ (n + 1)
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ a, cost s a * ∑ w : DWord C step n (step s a),
          dWeight C step cost (step s a) w := by simp only [Finset.mul_sum]
      _ ≤ ∑ a, cost s a * M ^ n := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (ih (step s a)) (hc s a)
      _ = (∑ a, cost s a) * M ^ n := by rw [Finset.sum_mul]
      _ ≤ M * M ^ n := mul_le_mul_of_nonneg_right (hrow s) (pow_nonneg hM n)
      _ = _ := (pow_succ' M n).symm

lemma dReweighted (cost : (s : S) → C s → ℝ)
    (c : (s : S) → C s → ℤ) (b : ℝ) (hb : b ≠ 0)
    {n : ℕ} (s : S) (w : DWord C step n s) :
    dWeight C step (fun s a => cost s a * b ^ c s a) s w =
      dWeight C step cost s w * b ^ dCharge C step c s w := by
  induction n generalizing s with
  | zero => simp [dWeight, dCharge]
  | succ n ih =>
    simp only [dWeight, dCharge, ih, zpow_add₀ hb]
    ring

theorem constrained_dSum_le [∀ s, Fintype (C s)] (cost : (s : S) → C s → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) (c : (s : S) → C s → ℤ)
    (b M : ℝ) (hb : 1 ≤ b) (hM : 0 ≤ M)
    (hrow : ∀ s, (∑ a, cost s a * b ^ c s a) ≤ M)
    (n : ℕ) (s : S) (valid : DWord C step n s → Prop) [DecidablePred valid]
    (hvalid : ∀ w, valid w → 0 ≤ dCharge C step c s w) :
    (∑ w : DWord C step n s, if valid w then dWeight C step cost s w else 0) ≤ M ^ n := by
  classical
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  calc
    _ ≤ ∑ w : DWord C step n s,
        dWeight C step (fun s a => cost s a * b ^ c s a) s w := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with hv
      · rw [dReweighted C step cost c b hb0.ne']
        apply le_mul_of_one_le_right (dWeight_nonneg C step cost hc s w)
        exact one_le_zpow₀ hb (hvalid w hv)
      · exact dWeight_nonneg C step _
          (fun s a => mul_nonneg (hc s a) (zpow_nonneg hb0.le _)) s w
    _ ≤ _ := sum_dWeight_le C step _
      (fun s a => mul_nonneg (hc s a) (zpow_nonneg hb0.le _)) M hM hrow n s

end Dependent

end SharpRamseyFive.CertificateEnumeration

namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

abbrev State (V H D B : Type*) := (V → H) × Finset (B × D)

variable (lines : H → Finset D)

abbrev RootChoice := V × H
abbrev OneChoice (s : State V H D B) :=
  (_v : V) × (u : V) × (x : AnchorChoice s.2 (lines (s.1 u))) ×
    {h : H // x.direction ∈ lines h}
abbrev TwoChoice (s : State V H D B) :=
  (_v : V) × (u : V) × (w : V) ×
    (x : AnchorChoice s.2 (lines (s.1 u))) ×
    (y : AnchorChoice s.2 (lines (s.1 w))) ×
    {h : H // x.direction ≠ y.direction ∧ x.direction ∈ lines h ∧ y.direction ∈ lines h}
abbrev PairDirections (s : State V H D B) (h h' : H) :=
  (lines h ∩ lines h') \ dictionary s.2
abbrev PairChoice (K : ℕ) (s : State V H D B) :=
  (_v : V) × (_u : V) × (h : H) × (h' : {h' : H // h' ≠ h}) ×
    (T : {T : Finset B // T ∈ (Finset.univ : Finset B).powersetCard K}) ×
      (T.val → PairDirections lines s h h'.val)
abbrev Action (K : ℕ) (s : State V H D B) :=
  RootChoice (V := V) (H := H) ⊕ OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s

noncomputable instance actionFintype (K : ℕ) (s : State V H D B) :
    Fintype (Action lines K s) := by
  letI : Fintype (RootChoice (V := V) (H := H)) := inferInstance
  letI : Fintype (OneChoice lines s) := inferInstance
  letI : Fintype (TwoChoice lines s) := inferInstance
  letI : Fintype (PairChoice lines K s) := inferInstance
  exact inferInstanceAs (Fintype (RootChoice (V := V) (H := H) ⊕
    OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s))

noncomputable def oneCost (rate : D → ℝ≥0) (denom : ℝ)
    (s : State V H D B) (c : OneChoice lines s) : ℝ :=
  c.2.2.1.cost rate / denom
noncomputable def twoCost (rate : D → ℝ≥0) (denom : ℝ)
    (s : State V H D B) (c : TwoChoice lines s) : ℝ :=
  c.2.2.2.1.cost rate * c.2.2.2.2.1.cost rate / denom
noncomputable def pairCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ)
    (s : State V H D B) (c : PairChoice lines K s) : ℝ :=
  weight (fun p : B × D => rate p.2)
    (witnessRequirements c.2.2.2.2.1.val
      (PairDirections lines s c.2.2.1 c.2.2.2.1.val) c.2.2.2.2.2) / denom ^ 2

noncomputable def anchorBudget (_rate : D → ℝ≥0) (s : State V H D B) (mass : ℝ) : ℝ :=
  s.2.card + Fintype.card B * mass

omit [Fintype   V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D] [DecidableEq B] in
lemma anchorBudget_nonneg (rate : D → ℝ≥0) (s : State V H D B)
    (mass : ℝ) (hmass : 0 ≤ mass) : 0 ≤ anchorBudget rate s mass := by
  unfold anchorBudget
  positivity

omit [DecidableEq V] in
omit [DecidableEq H] in
omit [Fintype D] [DecidableEq B] in

theorem sum_oneCost_le (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (s : State V H D B) (mass : ℝ)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (N₁ : ℕ) (hN : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁) :
    (∑ c : OneChoice lines s, oneCost lines rate denom s c) ≤
      Fintype.card V ^ 2 * (N₁ : ℝ) * anchorBudget rate s mass / denom := by
  classical
  simp only [OneChoice, oneCost, Fintype.sum_sigma]
  simp only [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hd
  calc
    _ ≤ ∑ _v : V, ∑ _u : V, (N₁ : ℝ) * anchorBudget rate s mass := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      rw [one_anchor_subtype_sum]
      apply (one_anchor_geometric_cost rate s.2 (lines (s.1 u)) lines N₁ hN).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmass (s.1 u)) (Nat.cast_nonneg _))
    _ = _ := by simp [pow_two, anchorBudget]; ring

omit [DecidableEq V] [DecidableEq H] in
omit [Fintype D] [DecidableEq B] in

theorem sum_twoCost_le (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (s : State V H D B) (mass : ℝ) (hm0 : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (N₂ : ℕ) (hN : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂) :
    (∑ c : TwoChoice lines s, twoCost lines rate denom s c) ≤
      Fintype.card V ^ 3 * (N₂ : ℝ) * anchorBudget rate s mass ^ 2 / denom := by
  classical
  simp only [TwoChoice, twoCost, Fintype.sum_sigma]
  simp only [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hd
  calc
    _ ≤ ∑ _v : V, ∑ _u : V, ∑ _w : V,
        (N₂ : ℝ) * anchorBudget rate s mass ^ 2 := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro w _
      rw [two_anchor_subtype_sum]
      apply (two_anchor_cross_cost rate s.2 (lines (s.1 u)) (lines (s.1 w)) lines N₂ hN).trans
      have ha (j : V) : (s.2.card : ℝ) + Fintype.card B *
          ∑ d ∈ lines (s.1 j), (rate d : ℝ) ≤ anchorBudget rate s mass :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmass (s.1 j)) (Nat.cast_nonneg _))
      rw [pow_two, ← mul_assoc]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (ha u) (Nat.cast_nonneg _)
      · exact ha w
      · positivity
      · exact mul_nonneg (Nat.cast_nonneg _) (anchorBudget_nonneg rate s mass hm0)
    _ = _ := by simp; ring

noncomputable def pairMoment (rate : D → ℝ≥0) (K : ℕ) : ℝ :=
  ∑ h : H, ∑ h' : {h' : H // h' ≠ h},
    ((Fintype.card B : ℝ) * ∑ d ∈ lines h ∩ lines h'.val, (rate d : ℝ)) ^ K

omit [Fintype D] [DecidableEq B] in
lemma pairMoment_nonneg (rate : D → ℝ≥0) (K : ℕ) :
    0 ≤ pairMoment (B := B) lines rate K := by
  unfold pairMoment
  positivity

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma sum_pair_choices_le (rate : D → ℝ≥0) (K : ℕ) (s : State V H D B) (h h' : H) :
    (∑ T : {T : Finset B // T ∈ (Finset.univ : Finset B).powersetCard K},
      ∑ f : T.val → PairDirections lines s h h',
        weight (fun p : B × D => rate p.2)
          (witnessRequirements T.val (PairDirections lines s h h') f)) ≤
      ((Fintype.card B : ℝ) * ∑ d ∈ lines h ∩ lines h', (rate d : ℝ)) ^ K := by
  classical
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard K)
    (fun T : Finset B => ∑ f : T → PairDirections lines s h h',
      weight (fun p : B × D => rate p.2)
        (witnessRequirements T (PairDirections lines s h h') f))]
  apply (pair_certificate_weight_le rate (PairDirections lines s h h') K).trans
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (by intro d _ _; exact (rate d).coe_nonneg)

omit [DecidableEq V] in
omit [Fintype D] in

theorem sum_pairCost_le (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ)
    (s : State V H D B) :
    (∑ c : PairChoice lines K s, pairCost lines rate denom K s c) ≤
      Fintype.card V ^ 2 * pairMoment (B := B) lines rate K / denom ^ 2 := by
  classical
  simp only [PairChoice, pairCost, Fintype.sum_sigma]
  simp only [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ∑ _v : V, ∑ _u : V, pairMoment (B := B) lines rate K := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      unfold pairMoment
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro h' _
      exact sum_pair_choices_le lines rate K s h h'.val
    _ = _ := by simp [pow_two]; ring

end SharpRamseyFive.WeightedPrograms
end

end OAI
