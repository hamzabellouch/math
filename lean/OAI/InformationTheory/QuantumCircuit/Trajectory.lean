import OAI.InformationTheory.QuantumCircuit.Localization
import OAI.InformationTheory.QuantumCircuit.Physical

namespace OAI

/-! Excitation tails and regular trajectories of shallow quantum circuits. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

abbrev State (N : ℕ) := EuclideanSpace ℂ (Word N)

def act {N : ℕ} (A : Operator N) (ψ : State N) : State N :=
  Matrix.toEuclideanCLM (n := Word N) (𝕜 := ℂ) A ψ

@[simp] lemma act_mul {N : ℕ} (A B : Operator N) (ψ : State N) :
    act (A * B) ψ = act A (act B ψ) := by
  simp [act, map_mul]

@[simp] lemma act_one {N : ℕ} (ψ : State N) : act (1 : Operator N) ψ = ψ := by
  simp [act]

@[simp] lemma act_zero {N : ℕ} (ψ : State N) : act (0 : Operator N) ψ = 0 := by
  simp [act]

lemma act_add {N : ℕ} (A B : Operator N) (ψ : State N) :
    act (A + B) ψ = act A ψ + act B ψ := by simp [act, map_add]

lemma act_sub {N : ℕ} (A B : Operator N) (ψ : State N) :
    act (A - B) ψ = act A ψ - act B ψ := by simp [act, map_sub]

lemma act_norm_le {N : ℕ} (A : Operator N) (ψ : State N) :
    ‖act A ψ‖ ≤ ‖A‖ * ‖ψ‖ := (Matrix.toEuclideanCLM (n := Word N) (𝕜 := ℂ) A).le_opNorm ψ

lemma act_norm_le_of_contraction {N : ℕ} (A : Operator N) (hA : ‖A‖ ≤ 1)
    (ψ : State N) : ‖act A ψ‖ ≤ ‖ψ‖ :=
  (act_norm_le A ψ).trans (by simpa using mul_le_mul_of_nonneg_right hA (norm_nonneg ψ))

lemma act_unitary_norm {N : ℕ} {U : Operator N} (hU : U ∈ unitary (Operator N))
    (ψ : State N) : ‖act U ψ‖ = ‖ψ‖ := by
  apply le_antisymm
  · exact act_norm_le_of_contraction U (by simpa using (CStarRing.norm_coe_unitary ⟨U, hU⟩).le) ψ
  · calc
      ‖ψ‖ = ‖act (star U) (act U ψ)‖ := by
        rw [← act_mul, Unitary.star_mul_self_of_mem hU, act_one]
      _ ≤ ‖act U ψ‖ := act_norm_le_of_contraction (star U)
        (by simpa using (CStarRing.norm_coe_unitary ⟨U, hU⟩).le) _

lemma projection_action_tail_bound {N : ℕ} (A : Count N) (Q : Operator N)
    (ψ : State N) (r R δ : ℝ) (hδ : 0 ≤ δ) (hψ : ‖ψ‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hloc : ‖A.high R * Q * A.low r‖ ≤ δ)
    (htail : ‖act (A.high r) ψ‖ ≤ δ) :
    ‖act (A.high R) (act Q ψ)‖ ≤ δ + δ := by
  have hsplit : A.high R * Q = A.high R * Q * A.low r +
      (A.high R * Q) * A.high r := by
    dsimp [Count.low]; noncomm_ring
  rw [← act_mul, hsplit, act_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (act_norm_le _ _).trans ((mul_le_mul_of_nonneg_right hloc
      (norm_nonneg _)).trans (by simpa using mul_le_mul_of_nonneg_left hψ hδ))
  · rw [act_mul]
    exact (act_norm_le_of_contraction _
      (norm_mul_le_one (IsStarProjection.norm_le _ (A.high_projection R)) hQ) _).trans htail

def HasExcitationTails (m : ℕ → ℕ) (A : ∀ ν, Count (m ν))
    (ψ : ∀ ν, State (m ν)) (b : ℝ) : Prop :=
  ∀ h p : ℝ, b < h → h < 1 → 0 < p → p < h →
    ∀ᶠ ν in atTop,
      ‖act ((A ν).high ((m ν : ℝ) ^ h)) (ψ ν)‖ ≤ Real.exp (-((m ν : ℝ) ^ p))

theorem excitation_tail_transport (d : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (U : ∀ ν, Operator (m ν))
    (hU : ∀ ν, IsCircuit d (U ν)) (A B : ∀ ν, Count (m ν))
    (ψ : ∀ ν, State (m ν)) (hψ : ∀ ν, ‖ψ ν‖ ≤ 1)
    {b : ℝ} (hb : 0 ≤ b) (htail : HasExcitationTails m A ψ b) :
    HasExcitationTails m A
      (fun ν => act (conjugate (U ν) (B ν).zero) (ψ ν)) b := by
  intro h p hbh hh hp hph
  obtain ⟨v, hv, hvh⟩ := exists_between (max_lt hbh hph)
  have hbv : b < v := (le_max_left _ _).trans_lt hv
  have hpv : p < v := (le_max_right _ _).trans_lt hv
  obtain ⟨a, hva, hah⟩ := exists_between hvh
  have ha : 0 ≤ a := hb.trans (hbv.trans hva).le
  have hloc := hm.eventually (uniform_low_propagation
    (fun s t hs hst => uniform_localization d s t hs hst) ha
    (hp.trans hpv).le hah hvh)
  have hsmall := htail a v (hbv.trans hva) (hah.trans hh) (hp.trans hpv) hva
  have hcost := hm.eventually (eventually_exp_power_gap hpv hpv (hp.trans hpv)
    2 1 1 0 (by norm_num) (by norm_num))
  filter_upwards [hloc, hsmall, hcost] with ν hloc hsmall hcost
  have hQ : ‖conjugate (U ν) (B ν).zero‖ ≤ 1 := IsStarProjection.norm_le _
    (conjugate_projection (hU ν).mem_unitary (B ν).zero_projection)
  exact (projection_action_tail_bound (A ν) _ (ψ ν) _ _ _ (Real.exp_pos _).le
    (hψ ν) hQ (hloc (U ν) (hU ν) (A ν) (B ν)) hsmall).trans
    (by simpa only [zero_mul, zero_sub, one_mul, ← two_mul] using hcost)

end QAC

namespace QAC

inductive AnalyticLayer (N : ℕ) where
  | local (L : LocalLayer N)
  | reflection (R : ReflectionLayer N)

namespace AnalyticLayer

def matrix {N : ℕ} : AnalyticLayer N → Operator N
  | .local L => localMatrix L
  | .reflection R => reflectionMatrix R

lemma isCircuit {N : ℕ} (a : AnalyticLayer N) : IsCircuit 1 a.matrix := by
  cases a with
  | «local» L => exact (show IsCircuit 0 (localMatrix L) from ⟨L, rfl⟩).succ
  | reflection R =>
    refine ⟨1, R, (fun _ => 1), ?_, ?_⟩
    · exact ⟨fun _ => 1, tensorMatrix_one.symm⟩
    · simp [matrix, localMatrix]

end AnalyticLayer

def evolution {N : ℕ} : List (AnalyticLayer N) → Operator N
  | [] => 1
  | a :: l => evolution l * a.matrix

lemma evolution_append {N : ℕ} (a b : List (AnalyticLayer N)) :
    evolution (a ++ b) = evolution b * evolution a := by
  induction a with
  | nil => simp [evolution]
  | cons x a ih => simp [evolution, ih, mul_assoc]

lemma evolution_isCircuit {N : ℕ} (l : List (AnalyticLayer N)) :
    IsCircuit l.length (evolution l) := by
  induction l with
  | nil => exact ⟨fun _ => 1, tensorMatrix_one.symm⟩
  | cons a l ih => simpa [evolution] using ih.mul a.isCircuit

def jointTest {N : ℕ} : List (Count N) → Count N
  | [] => Count.empty
  | A :: l => A.join (jointTest l)

def RegularTrajectory (m : ℕ → ℕ) (l : ∀ ν, List (AnalyticLayer (m ν)))
    (ψ : ∀ ν, State (m ν)) : Prop :=
  ∀ b h p : ℝ, 0 ≤ b → b < h → h < 1 → 0 < p → p < h →
    ∀ᶠ ν in atTop, ∀ j R, (l ν)[j]? = some (.reflection R) →
      ∀ S : List (Count (m ν)), S.Sublist R.gates → (S.length : ℝ) ≤ (m ν : ℝ) ^ b →
        ‖act ((jointTest S).high ((m ν : ℝ) ^ h))
          (act (evolution ((l ν).take j)) (ψ ν))‖ ≤ Real.exp (-((m ν : ℝ) ^ p))

def projectedInput {N : ℕ} (l : List (AnalyticLayer N)) (B : Count N) (ψ : State N) :
    State N := act (star (evolution l) * B.zero * evolution l) ψ

lemma projectedInput_at_cut {N : ℕ} (l : List (AnalyticLayer N))
    (B : Count N) (ψ : State N) (j : ℕ) :
    act (evolution (l.take j)) (projectedInput l B ψ) =
      act (conjugate (star (evolution (l.drop j))) B.zero)
        (act (evolution (l.take j)) ψ) := by
  have hU := (evolution_isCircuit (l.take j)).mem_unitary
  have heq : evolution l = evolution (l.drop j) * evolution (l.take j) := by
    rw [← evolution_append, List.take_append_drop]
  simp only [projectedInput, ← act_mul, heq, star_mul, conjugate, star_star]
  congr 1
  calc
    _ = (evolution (l.take j) * star (evolution (l.take j))) *
        star (evolution (l.drop j)) * B.zero * evolution (l.drop j) *
        evolution (l.take j) := by noncomm_ring
    _ = _ := by rw [Unitary.mul_star_self_of_mem hU, one_mul]

theorem regular_projection_insertion (d : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (l : ∀ ν, List (AnalyticLayer (m ν)))
    (hl : ∀ ν, (l ν).length ≤ d) (ψ : ∀ ν, State (m ν))
    (hψ : ∀ ν, ‖ψ ν‖ ≤ 1) (hreg : RegularTrajectory m l ψ)
    (B : ∀ ν, Count (m ν)) :
    RegularTrajectory m l (fun ν => projectedInput (l ν) (B ν) (ψ ν)) := by
  intro b h p hb hbh hh hp hph
  obtain ⟨v, hv, hvh⟩ := exists_between (max_lt hbh hph)
  have hbv : b < v := (le_max_left _ _).trans_lt hv
  have hpv : p < v := (le_max_right _ _).trans_lt hv
  obtain ⟨a, hva, hah⟩ := exists_between hvh
  have ha : 0 ≤ a := hb.trans (hbv.trans hva).le
  have hloc := hm.eventually (uniform_low_propagation
    (fun s t hs hst => uniform_localization d s t hs hst) ha
    (hp.trans hpv).le hah hvh)
  have hsmall := hreg b a v hb (hbv.trans hva) (hah.trans hh) (hp.trans hpv) hva
  have hcost := hm.eventually (eventually_exp_power_gap hpv hpv (hp.trans hpv)
    2 1 1 0 (by norm_num) (by norm_num))
  filter_upwards [hloc, hsmall, hcost] with ν hloc hsmall hcost
  intro j R hj S hS hsize
  rw [projectedInput_at_cut]
  let A := jointTest S
  let Q := conjugate (star (evolution ((l ν).drop j))) (B ν).zero
  let ξ := act (evolution ((l ν).take j)) (ψ ν)
  have hξ : ‖ξ‖ ≤ 1 := by
    rw [show ‖ξ‖ = ‖ψ ν‖ from act_unitary_norm
      (evolution_isCircuit ((l ν).take j)).mem_unitary _]
    exact hψ ν
  have hU : IsCircuit d (star (evolution ((l ν).drop j))) :=
    (evolution_isCircuit ((l ν).drop j)).star_mem.mono
      (by simpa only [List.length_drop] using (Nat.sub_le (l ν).length j).trans (hl ν))
  have hQ : ‖Q‖ ≤ 1 := IsStarProjection.norm_le _
    (conjugate_projection hU.mem_unitary (B ν).zero_projection)
  exact (projection_action_tail_bound A Q ξ _ _ _ (Real.exp_pos _).le hξ hQ
    (hloc _ hU A (B ν)) (hsmall j R hj S hS hsize)).trans
    (by simpa only [zero_mul, zero_sub, one_mul, ← two_mul] using hcost)

end QAC

end

end OAI
