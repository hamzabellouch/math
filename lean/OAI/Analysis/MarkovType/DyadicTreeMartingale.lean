import OAI.Analysis.MarkovType.FiniteDyadicMartingale
import OAI.Analysis.MarkovType.DyadicTree
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [sectionNormedAddCommGroupE : NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem dyadicLaw_expect_snoc {n : ℕ} (f : DyadicWord (n + 1) → ℝ) :
    (dyadicLaw (n + 1)).expect f = (dyadicLaw n).expect
      (fun α => (f (Fin.snoc α true) + f (Fin.snoc α false)) / 2) := by
  classical
  unfold FiniteLaw.expect
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
    (fun ω => (dyadicLaw (n + 1)).mass ω * f ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  change (dyadicLaw (n + 1)).mass (Fin.snoc α true) * f (Fin.snoc α true) +
      (dyadicLaw (n + 1)).mass (Fin.snoc α false) * f (Fin.snoc α false) = _
  simp only [dyadicLaw_mass, pow_succ]
  ring

theorem FiniteLaw.vexpect_const {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (x : E) :
    μ.vexpect (fun _ => x) = x := by
  rw [FiniteLaw.vexpect, ← Finset.sum_smul, μ.sum_mass, one_smul]

theorem dyadicLaw_vexpect_snoc {n : ℕ} (f : DyadicWord (n + 1) → E) :
    (dyadicLaw (n + 1)).vexpect f = (dyadicLaw n).vexpect
      (fun α => (2 : ℝ)⁻¹ • (f (Fin.snoc α true) + f (Fin.snoc α false))) := by
  classical
  unfold FiniteLaw.vexpect
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
    (fun ω => (dyadicLaw (n + 1)).mass ω • f ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  change (dyadicLaw (n + 1)).mass (Fin.snoc α true) • f (Fin.snoc α true) +
      (dyadicLaw (n + 1)).mass (Fin.snoc α false) • f (Fin.snoc α false) = _
  simp only [dyadicLaw_mass, pow_succ]
  module

namespace DyadicTree

def branch : DyadicTree E → Bool → DyadicTree E
  | leaf x, _ => leaf x
  | node t s, b => if b then t else s

def splitCoefficient : DyadicTree E → E
  | leaf _ => 0
  | node t s => (2 : ℝ)⁻¹ • (root t - root s)

def descendant (t : DyadicTree E) : (n : ℕ) → DyadicWord n → DyadicTree E
  | 0, _ => t
  | n + 1, α => branch (descendant t n (Fin.init α)) (α (Fin.last n))

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
@[simp] theorem descendant_zero [NormedAddCommGroup E] [NormedSpace ℝ E] (t : DyadicTree E) (α : DyadicWord 0) :
    descendant t 0 α = t := rfl

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
@[simp] theorem descendant_snoc [NormedAddCommGroup E] [NormedSpace ℝ E] (t : DyadicTree E) (n : ℕ)
    (α : DyadicWord n) (b : Bool) :
    descendant t (n + 1) (Fin.snoc α b) = branch (descendant t n α) b := by
  simp only [descendant, Fin.init_snoc, Fin.snoc_last]

theorem root_branch (t : DyadicTree E) (b : Bool) :
    root (branch t b) = root t + dyadicSign b • splitCoefficient t := by
  cases t <;> cases b <;> simp [branch, splitCoefficient, dyadicSign] <;> module

theorem root_branch_average (t : DyadicTree E) :
    (2 : ℝ)⁻¹ • (root (branch t true) + root (branch t false)) = root t := by
  cases t with
  | leaf x => simp only [branch, root_leaf]; module
  | node t s => rfl

omit sectionNormedSpaceℝE in
theorem moment_branch_average [NormedSpace ℝ E] (t : DyadicTree E) (p : ℝ) :
    (moment p (branch t true) + moment p (branch t false)) / 2 = moment p t := by
  cases t with
  | leaf x => simp only [branch, moment_leaf]; ring
  | node t s => rfl

theorem energy_branch_average {p : ℝ} (hp : 0 < p) (t : DyadicTree E) :
    (energy p (branch t true) + energy p (branch t false)) / 2 +
      ‖splitCoefficient t‖ ^ p = energy p t := by
  cases t with
  | leaf x => simp [branch, splitCoefficient, Real.zero_rpow hp.ne']
  | node t s => rfl

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
theorem full_branch [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {t : DyadicTree E} (h : Full (n + 1) t) (b : Bool) :
    Full n (branch t b) := by
  cases t with
  | leaf x => exact h.elim
  | node t s =>
      cases b with
      | false => exact h.2
      | true => exact h.1

theorem full_descendant {n k : ℕ} {t : DyadicTree E} (h : Full (n + k) t)
    (α : DyadicWord n) : Full k (descendant t n α) := by
  induction n generalizing k with
  | zero => simpa only [Nat.zero_add, descendant] using h
  | succ n ih =>
      apply full_branch
      apply ih (k := k + 1)
      convert h using 1 ; omega

theorem moment_full_zero {t : DyadicTree E} (h : Full 0 t) (p : ℝ) :
    moment p t = ‖root t‖ ^ p := by
  cases t with
  | leaf x => rfl
  | node t s => exact h.elim

theorem energy_full_zero {t : DyadicTree E} (h : Full 0 t) (p : ℝ) :
    energy p t = 0 := by
  cases t with
  | leaf x => rfl
  | node t s => exact h.elim

theorem vexpect_root_descendant (t : DyadicTree E) (n : ℕ) :
    (dyadicLaw n).vexpect (fun α => root (descendant t n α)) = root t := by
  induction n with
  | zero => exact FiniteLaw.vexpect_const (dyadicLaw 0) (root t)
  | succ n ih =>
      rw [dyadicLaw_vexpect_snoc]
      simp only [descendant_snoc, root_branch_average]
      exact ih

theorem expect_moment_descendant (t : DyadicTree E) (n : ℕ) (p : ℝ) :
    (dyadicLaw n).expect (fun α => moment p (descendant t n α)) = moment p t := by
  induction n with
  | zero => exact FiniteLaw.expect_const (dyadicLaw 0) (moment p t)
  | succ n ih =>
      rw [dyadicLaw_expect_snoc]
      simp only [descendant_snoc, moment_branch_average]
      exact ih

theorem expected_energy_step {p : ℝ} (hp : 0 < p) (t : DyadicTree E) (n : ℕ) :
    (dyadicLaw (n + 1)).expect (fun α => energy p (descendant t (n + 1) α)) +
      (dyadicLaw n).expect (fun α => ‖splitCoefficient (descendant t n α)‖ ^ p) =
      (dyadicLaw n).expect (fun α => energy p (descendant t n α)) := by
  rw [dyadicLaw_expect_snoc]
  simp only [descendant_snoc, FiniteLaw.expect]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← mul_add, energy_branch_average hp]

theorem energy_telescope {p : ℝ} (hp : 0 < p) (t : DyadicTree E) (n : ℕ) :
    (dyadicLaw n).expect (fun α => energy p (descendant t n α)) +
      (∑ j : Fin n, (dyadicLaw j.val).expect
        (fun α => ‖splitCoefficient (descendant t j.val α)‖ ^ p)) = energy p t := by
  induction n with
  | zero => simp [descendant, FiniteLaw.expect_const]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hstep := expected_energy_step hp t n
      linarith

def coefficients (N : ℕ) (t : DyadicTree E) : DyadicAtom N → E
  | .inl _ => root t
  | .inr ⟨j, α⟩ => splitCoefficient (descendant t j.val α)

@[simp] theorem coefficients_root (N : ℕ) (t : DyadicTree E) :
    dyadicRoot (coefficients N t) = root t := rfl

@[simp] theorem coefficients_prefix (N : ℕ) (t : DyadicTree E) (j : Fin N)
    (α : DyadicWord j.val) :
    dyadicCoefficient (coefficients N t) j α = splitCoefficient (descendant t j.val α) := rfl

theorem process_coefficients {N n : ℕ} (hn : n ≤ N) (t : DyadicTree E)
    (ω : DyadicWord N) :
    dyadicProcess (coefficients N t) n ω = root (descendant t n (dyadicPrefix ω n hn)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hprev : n ≤ N := Nat.le_of_lt hnN
      simp only [dyadicProcess, dite_eq_left hnN, ih hprev]
      change root (descendant t n (dyadicPrefix ω n hprev)) +
        dyadicSign (ω ⟨n, hnN⟩) • splitCoefficient
          (descendant t n (dyadicPrefix ω n hprev)) = _
      rw [descendant, root_branch]
      rfl

theorem synthesis_coefficients (N : ℕ) (t : DyadicTree E) (ω : DyadicWord N) :
    dyadicSynthesis N (coefficients N t) ω = root (descendant t N ω) := by
  change dyadicProcess (coefficients N t) N ω = _
  rw [process_coefficients (Nat.le_refl N)]
  rfl

theorem process_eq_descendant_average {N n : ℕ} (hn : n ≤ N) (t : DyadicTree E)
    (ω : DyadicWord N) :
    dyadicProcess (coefficients N t) n ω =
      (dyadicLaw (N - n)).vexpect (fun β => root
        (descendant (descendant t n (dyadicPrefix ω n hn)) (N - n) β)) := by
  rw [vexpect_root_descendant, process_coefficients hn]

theorem synthesis_moment {N : ℕ} {t : DyadicTree E} (h : Full N t) (p : ℝ) :
    finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N (coefficients N t)) = moment p t := by
  have hfull (α : DyadicWord N) : Full 0 (descendant t N α) :=
    full_descendant (k := 0) (by simpa only [Nat.add_zero] using h) α
  calc
    _ = (dyadicLaw N).expect (fun α => moment p (descendant t N α)) := by
      unfold finiteMoment FiniteLaw.expect
      apply Finset.sum_congr rfl
      intro α _
      simp only [synthesis_coefficients, moment_full_zero (hfull α)]
    _ = moment p t := expect_moment_descendant t N p

theorem coefficients_energy {N : ℕ} {t : DyadicTree E} (h : Full N t)
    {p : ℝ} (hp : 0 < p) :
    (∑ j : Fin N, finiteMoment (dyadicLaw N).mass p
      (dyadicIncrement (coefficients N t) j)) = energy p t := by
  have hz : (dyadicLaw N).expect (fun α => energy p (descendant t N α)) = 0 := by
    have hzero : (fun α : DyadicWord N => energy p (descendant t N α)) = fun _ => 0 := by
      funext α
      exact energy_full_zero
        (full_descendant (k := 0) (by simpa only [Nat.add_zero] using h) α) p
    rw [hzero, FiniteLaw.expect_const]
  simpa only [dyadicIncrement_moment, coefficients_prefix, hz, zero_add] using
    energy_telescope hp t N

theorem coefficients_inputMoment {N : ℕ} {t : DyadicTree E} (h : Full N t)
    {p : ℝ} (hp : 0 < p) :
    finiteMoment dyadicInputWeight p (coefficients N t) = ‖root t‖ ^ p + energy p t := by
  rw [dyadicInputMoment, coefficients_root, coefficients_energy h hp]

theorem exists_dyadic_model (t : DyadicTree E) {p : ℝ} (hp : 0 < p) :
    ∃ (N : ℕ) (φ : DyadicAtom N → E),
      dyadicRoot φ = root t ∧
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) = moment p t ∧
      (∑ j : Fin N, finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ j)) = energy p t := by
  let N := height t
  let u := pad N t
  have hu : Full N u := pad_full N t (Nat.le_refl _)
  refine ⟨N, coefficients N u, ?_, ?_, ?_⟩
  · exact root_pad N t
  · rw [synthesis_moment hu, moment_pad]
  · rw [coefficients_energy hu hp, energy_pad hp]

end DyadicTree
end MarkovSuperreflexivity

end

end OAI
