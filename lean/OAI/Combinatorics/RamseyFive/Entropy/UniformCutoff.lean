import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PublicDecoder
import OAI.Combinatorics.RamseyFive.Decoding.ReverseCap

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

noncomputable def uniformCutoff (q : ℝ) (C W : Finset A) (n : ℕ) : ℕ :=
  ⌈q/((9:ℝ)/10*((C.card:ℝ)/W.card)^n)⌉₊

omit [Fintype A] in
lemma uniformCutoff_pos (q : ℝ) (hq : 0 < q) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (n : ℕ) :
    0 < uniformCutoff q C W n := by
  have hc : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hw : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
  apply Nat.ceil_pos.mpr
  positivity

omit [Fintype A] in
lemma uniformCutoff_bound (q : ℝ) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (n : ℕ) :
    q ≤ (9:ℝ)/10*((C.card:ℝ)/W.card)^n*uniformCutoff q C W n := by
  have hc : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hw : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hp : (0:ℝ) < (9:ℝ)/10*((C.card:ℝ)/W.card)^n := by positivity
  have hh := (div_le_iff₀ hp).mp (Nat.le_ceil (q/((9:ℝ)/10*((C.card:ℝ)/W.card)^n)))
  simpa only [mul_comm,uniformCutoff] using hh

theorem uniform_cutoff_failure (q : ℝ) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W) (n : ℕ)
    (E : Finset (Fin n→A)) (hsource : ∀row∈E,∀i,row i∈C)
    (hE : (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) E) :
    map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
      (firstAccepted E (n := uniformCutoff q C W n)) none ≤ Real.exp (-q) :=
  uniform_table_failure C W hC hW hCW n _ E hsource hE q (uniformCutoff_bound q C W hC hW n)

lemma ceil_ratio_log (q a : ℝ) (hq : 1 ≤ q) (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log (⌈q/a⌉₊:ℝ) ≤ Real.log (2*q)-Real.log a := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hx : 1 ≤ q/a := (le_div_iff₀ ha).mpr (by simpa using ha1.trans hq)
  have hcpos : (0:ℝ) < ⌈q/a⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (div_pos hqpos ha)
  have hh : (⌈q/a⌉₊:ℝ) ≤ (2*q)/a := by
    have ht := Nat.ceil_lt_add_one (div_pos hqpos ha).le
    have he : 2*(q/a)=(2*q)/a := by ring
    linarith
  have hl := Real.log_le_log hcpos hh
  rwa [Real.log_div (by positivity : (2*q:ℝ) ≠ 0) ha.ne'] at hl

omit [Fintype A] in
theorem uniformCutoff_log (q : ℝ) (hq : 1 ≤ q) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W) (n : ℕ) :
    Real.log (uniformCutoff q C W n) ≤
      Real.log (2*q)-Real.log ((9:ℝ)/10)+(n:ℝ)*Real.log ((W.card:ℝ)/C.card) := by
  have hc : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hw : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hratio : (C.card:ℝ)/W.card ≤ 1 := (div_le_one hw).mpr (by exact_mod_cast Finset.card_le_card hCW)
  have hpow := pow_le_one₀ (n := n) (by positivity : (0:ℝ) ≤ (C.card:ℝ)/W.card) hratio
  have hh := ceil_ratio_log q ((9:ℝ)/10*((C.card:ℝ)/W.card)^n) hq (by positivity) (by nlinarith)
  change Real.log (uniformCutoff q C W n) ≤ _ at hh
  rw [Real.log_mul (by norm_num : (9:ℝ)/10 ≠ 0) (by positivity),Real.log_pow,
    Real.log_div hc.ne' hw.ne'] at hh
  rw [Real.log_div hw.ne' hc.ne']
  linarith

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoreSearchCost (S U : Finset (ℙ K V)) (P τ : ℝ) : ℝ :=
  Real.log ((U.card:ℝ)/S.card)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4)

noncomputable def scoreCutoff (S U : Finset (ℙ K V)) (P τ : ℝ) : ℕ :=
  ⌈(Nat.card K:ℝ)*Real.exp (scoreSearchCost S U P τ)⌉₊

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreSearchCost_nonneg (S U : Finset (ℙ K V)) (hS : S.Nonempty)
    (hSU : S⊆U) (P τ : ℝ) (hP : 0≤P) (hτ : 0≤τ) :
    0 ≤ scoreSearchCost S U P τ := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hs).mpr (by simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
  unfold scoreSearchCost
  exact add_nonneg (mul_nonneg (Real.log_nonneg hr) (by positivity))
    (add_nonneg (by positivity) (Real.log_nonneg (by norm_num)))

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreCutoff_pos (S U : Finset (ℙ K V)) (P τ : ℝ) : 0<scoreCutoff S U P τ := by
  apply Nat.ceil_pos.mpr
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  positivity

omit [FiniteDimensional K V] in
theorem score_public_implementation (U S : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (L₀ : ℝ≥0)
    (P τ M : ℝ) (hP : 0≤P) (hτ : 0≤τ)
    (hprob : Real.exp (-8*P*τ)/4≤
      (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
        (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))) :
    let N := scoreCutoff S U P τ
    let Good := ambientSuccess S (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ ∧
    (Measure.pi (fun _ : Fin N=>scheduleMeasure
      (fun i=>if i∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
       {t | firstIndex Good t=none}≤Real.exp (-(Nat.card K:ℝ)) ∧
    ∀(t : Fin N→Fin R→ℙ K V→ℕ) (i : Fin N),firstIndex Good t=some i →
      ∃z≤E.card, (sampleCount (t i):ℝ)≤2*(Nat.card K:ℝ)*P ∧
        ((publicDecoded U rawO b z (t i)).card:ℝ)≤M ∧
        (9/10:ℝ)*S.card≤(((publicDecoded U rawO b z (t i))∩S).card:ℝ) := by
  dsimp only
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hA := scoreSearchCost_nonneg S U hS hSU P τ hP hτ
  have hexp : Real.exp (-(8*P*τ+Real.log 4))=Real.exp (-8*P*τ)/4 := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 4),Real.exp_log (by norm_num : (0:ℝ)<4)]
    congr 1; ring_nf
  have hmean : (fun _ : S=>(L₀*(Nat.card K:ℝ≥0))/(S.card:ℝ≥0))=
      (fun _ : S=>L₀*pointStrength S) := by
    funext x
    simp only [pointStrength,mul_div_assoc]
  have hh := enclosure_search_failure S U hS hSU (L₀*(Nat.card K:ℝ≥0)) R
    (2*(Nat.card K:ℝ)*P) (8*P*τ+Real.log 4) (Nat.card K:ℝ) (by positivity)
    (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))
    (by intro ω hω;exact hω.1) (by rw [hmean,hexp];exact hprob)
  have hcost : Real.log ((U.card:ℝ)/S.card)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4)=scoreSearchCost S U P τ := by
    unfold scoreSearchCost;ring
  refine ⟨?_,hh,?_⟩
  · have hl := FiniteEntropy.ceil_ratio_log (Nat.card K:ℝ) (Real.exp (-scoreSearchCost S U P τ)) hq
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
    rw [Real.log_exp,sub_neg_eq_add] at hl
    simpa only [scoreCutoff,Real.exp_neg,div_inv_eq_mul] using hl
  · intro t i hi
    exact public_table_decodes U S hSU O rawO hO b E R _ M _ t hi

end SharpRamseyFive.ScoreGeometry

end OAI
