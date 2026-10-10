import OAI.NumberTheory.TotientAsymptotic.Arithmetic

namespace OAI

/-!
The published inverse-fiber input and its arithmetic consequences.

`FordFiberPropagation d` is the single-seed specialization of the construction
in Kevin Ford, *The distribution of totients*, Ramanujan Journal 2 (1998),
67--151, arXiv:1104.3264v2 (2013), Section 5, equations (5.10)--(5.19),
and the explicit full-fiber statement in Section 7.3, p. 39.

`PPTBoundedFiberPropagation d` additionally retains the bounded multiplier
ratio from Pollack--Pomerance--Treviño, *Sets of monotonicity for Euler's
totient function*, Ramanujan Journal 30 (2013), 379--398, Lemma 4.1,
specialized to the same seed in both positions and D = d, together with
Ford's Theorem 1 to replace its scale Z(x) by V(x).  The lower-bound
constant may depend on d; the absolute bound in the published lemma is
weakened here to an existential constant for this fixed seed.

These are explicit hypotheses, not axioms.  The conclusions below count
large least-preimage ratios; they do not assert the companion asymptotic.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def FullFiber (d b : ℕ) : Prop :=
  ∀ n : ℕ, (0 < n ∧ n.totient = d*b.totient) ↔
    ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m

def FordFiberPropagation (d : ℕ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ᶠ x : ℝ in atTop,
    0 < x ∧ ∃ S : Finset ℕ, η * V x ≤ (S.card : ℝ) ∧
      ∀ b ∈ S, 0 < b ∧ ((d*b.totient : ℕ) : ℝ) ≤ x ∧ FullFiber d b

def PPTBoundedFiberPropagation (d : ℕ) : Prop :=
  ∃ η K : ℝ, 0 < η ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
    0 < x ∧ ∃ S : Finset ℕ, η * V x ≤ (S.card : ℝ) ∧
      ∀ b ∈ S, 0 < b ∧ ((d*b.totient : ℕ) : ℝ) ≤ x ∧
        FullFiber d b ∧ (b : ℝ) / b.totient ≤ K

def highRatioCount (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ k*v < ell v).card : ℝ)

def boundedHighRatioCount (k : ℕ) (C x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ k*v < ell v ∧ (ell v : ℝ) / v ≤ C).card : ℝ)

lemma isTotient_of_fullFiber {d b : ℕ} (hd : IsTotient d)
    (hfull : FullFiber d b) : IsTotient (d*b.totient) := by
  have he := ell_spec hd
  exact ⟨b*ell d, (hfull _).mpr ⟨ell d, he.1, he.2, rfl⟩⟩

lemma fullFiber_seed_inequality {d b k : ℕ} (hd : IsTotient d)
    (hb : 0 < b) (hseed : k*d < ell d) (hfull : FullFiber d b) :
    k*(d*b.totient) < ell (d*b.totient) := by
  have hratio := ratio_le_of_full_fiber hd hb rfl hfull
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (isTotient_pos hd)
  have hvpos : (0 : ℝ) < ((d*b.totient : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (isTotient_pos hd) (Nat.totient_pos.mpr hb)
  have hseed' : (k : ℝ) < (ell d : ℝ) / d := by
    apply (lt_div_iff₀ hdpos).mpr
    exact_mod_cast hseed
  have hvalue := (lt_div_iff₀ hvpos).mp (hseed'.trans_le hratio)
  exact_mod_cast hvalue

lemma card_fullFibers_le_highRatioCount {d k : ℕ} (hd : IsTotient d)
    (hseed : k*d < ell d) (S : Finset ℕ) (x : ℝ)
    (hS : ∀ b ∈ S, 0 < b ∧ ((d*b.totient : ℕ) : ℝ) ≤ x ∧ FullFiber d b) :
    (S.card : ℝ) ≤ highRatioCount k x := by
  classical
  have hinj : Set.InjOn (fun b : ℕ => d*b.totient) (S : Set ℕ) := by
    intro b hb c hc heq
    exact mul_totient_injective_of_full_fibers hd (hS b hb).1 (hS c hc).1
      (hS b hb).2.2 (hS c hc).2.2 heq
  have hsubset : S.image (fun b => d*b.totient) ⊆
      (Finset.Icc 1 ⌊x⌋₊).filter (fun v => IsTotient v ∧ k*v < ell v) := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hbpos, hbsize, hbfull⟩ := hS b hb
    have hvt := isTotient_of_fullFiber hd hbfull
    refine Finset.mem_filter.mpr ⟨?_, hvt, fullFiber_seed_inequality hd hbpos hseed hbfull⟩
    exact Finset.mem_Icc.mpr ⟨isTotient_pos hvt, Nat.le_floor hbsize⟩
  unfold highRatioCount
  apply Nat.cast_le.mpr
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsubset

/-- A single large least-preimage ratio propagates to a positive fraction of
the distinct totients, conditional on Ford's published full-fiber input. -/
theorem positive_proportion_highRatio_of_ford {d k : ℕ} (hd : IsTotient d)
    (hseed : k*d < ell d) (hford : FordFiberPropagation d) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ x : ℝ in atTop, η * V x ≤ highRatioCount k x := by
  obtain ⟨η, hη, hprop⟩ := hford
  refine ⟨η, hη, ?_⟩
  filter_upwards [hprop] with x hx
  obtain ⟨_, S, hcard, hS⟩ := hx
  exact hcard.trans (card_fullFibers_le_highRatioCount hd hseed S x hS)

lemma pptBoundedFiberPropagation_implies_ford {d : ℕ}
    (hppt : PPTBoundedFiberPropagation d) : FordFiberPropagation d := by
  obtain ⟨η, K, hη, _, hprop⟩ := hppt
  refine ⟨η, hη, ?_⟩
  filter_upwards [hprop] with x hx
  obtain ⟨hx, S, hcard, hS⟩ := hx
  exact ⟨hx, S, hcard, fun b hb =>
    ⟨(hS b hb).1, (hS b hb).2.1, (hS b hb).2.2.1⟩⟩

lemma fullFiber_ratio_eq {d b : ℕ} (hd : IsTotient d) (hb : 0 < b)
    (hfull : FullFiber d b) :
    (ell (d*b.totient) : ℝ) / ((d*b.totient : ℕ) : ℝ) =
      ((ell d : ℝ) / d) * ((b : ℝ) / b.totient) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (isTotient_pos hd).ne'
  have hb0 : (b.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hb).ne'
  rw [ell_eq_mul_of_full_fiber hd hb hfull]
  push_cast
  field_simp

lemma card_fullFibers_le_boundedHighRatioCount {d k : ℕ} (hd : IsTotient d)
    (hseed : k*d < ell d) (S : Finset ℕ) (K x : ℝ)
    (hS : ∀ b ∈ S, 0 < b ∧ ((d*b.totient : ℕ) : ℝ) ≤ x ∧
      FullFiber d b ∧ (b : ℝ) / b.totient ≤ K) :
    (S.card : ℝ) ≤ boundedHighRatioCount k (K * ((ell d : ℝ) / d)) x := by
  classical
  have hinj : Set.InjOn (fun b : ℕ => d*b.totient) (S : Set ℕ) := by
    intro b hb c hc heq
    exact mul_totient_injective_of_full_fibers hd (hS b hb).1 (hS c hc).1
      (hS b hb).2.2.1 (hS c hc).2.2.1 heq
  have hsubset : S.image (fun b => d*b.totient) ⊆
      (Finset.Icc 1 ⌊x⌋₊).filter (fun v =>
        IsTotient v ∧ k*v < ell v ∧ (ell v : ℝ) / v ≤ K * ((ell d : ℝ) / d)) := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hbpos, hbsize, hbfull, hbK⟩ := hS b hb
    have hvt := isTotient_of_fullFiber hd hbfull
    refine Finset.mem_filter.mpr ⟨?_, hvt,
      fullFiber_seed_inequality hd hbpos hseed hbfull, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨isTotient_pos hvt, Nat.le_floor hbsize⟩
    · rw [fullFiber_ratio_eq hd hbpos hbfull, mul_comm K]
      exact mul_le_mul_of_nonneg_left hbK (zero_le_one.trans (one_le_ell_ratio hd))
  unfold boundedHighRatioCount
  apply Nat.cast_le.mpr
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsubset

/-- PPT Lemma 4.1 supplies a bounded interval of positive ratios directly,
without an additional tightness hypothesis about arbitrary totients. -/
theorem positive_proportion_boundedHighRatio_of_ppt {d k : ℕ} (hd : IsTotient d)
    (hseed : k*d < ell d) (hppt : PPTBoundedFiberPropagation d) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      η * V x ≤ boundedHighRatioCount k C x := by
  obtain ⟨η, K, hη, hK, hprop⟩ := hppt
  refine ⟨η, K * ((ell d : ℝ) / d), hη,
    mul_pos hK (zero_lt_one.trans_le (one_le_ell_ratio hd)), ?_⟩
  filter_upwards [hprop] with x hx
  obtain ⟨_, S, hcard, hS⟩ := hx
  exact hcard.trans (card_fullFibers_le_boundedHighRatioCount hd hseed S K x hS)

end TotientAsymptotic

end

end OAI
