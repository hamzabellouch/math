import OAI.Probability.InvariantIsing.Spectral.Spectral
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-!
The inverse Cauchy transform of a finite alphabet always lies strictly
above its largest atom. This supplies existence, as well as uniqueness,
for the resolvent used by the finite-alphabet cavity construction.
-/

noncomputable section

open scoped BigOperators
open Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuousOn_finiteResolvent (ρ eig : ι → ℝ) (s : Set ℝ)
    (hs : ∀ b ∈ s, ∀ a, eig a < b) :
    ContinuousOn (finiteResolvent ρ eig) s := by
  unfold finiteResolvent
  apply continuousOn_finsetSum
  intro a _
  exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    (fun b hb => ne_of_gt (sub_pos.mpr (hs b hb a)))

/-- Existence and uniqueness above an upper edge carrying positive mass. -/
theorem exists_unique_finiteResolvent_solution {ρ eig : ι → ℝ} {a₀ : ι} {x : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (ha₀ : 0 < ρ a₀) (he : ∀ a, eig a ≤ eig a₀) (hx : 0 < x) :
    ∃! b : ℝ, (∀ a, eig a < b) ∧ finiteResolvent ρ eig b = x := by
  let lo := eig a₀ + ρ a₀ / (2 * x)
  let hi := lo + 1 / x
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hdist : 0 < ρ a₀ / (2 * x) := div_pos ha₀ (by positivity)
  have helo : eig a₀ < lo := by dsimp [lo]; linarith
  have hlohi : lo < hi := by dsimp [hi]; linarith [one_div_pos.mpr hx]
  have hEiglo : ∀ a, eig a < lo := fun a => (he a).trans_lt helo
  have hsingle : ρ a₀ / (lo - eig a₀) = 2 * x := by
    dsimp [lo]
    field_simp [ne_of_gt ha₀]
    ring
  have hxlo : x ≤ finiteResolvent ρ eig lo := by
    have hterm : ρ a₀ / (lo - eig a₀) ≤ finiteResolvent ρ eig lo :=
      Finset.single_le_sum (fun a _ => div_nonneg (hρ a) (sub_pos.mpr (hEiglo a)).le)
        (Finset.mem_univ a₀)
    rw [hsingle] at hterm
    linarith
  have hhiedge : eig a₀ < hi := helo.trans hlohi
  have hupper := finiteResolvent_le hρ hρsum he hhiedge
  have hxhi : finiteResolvent ρ eig hi ≤ x := by
    apply hupper.trans
    have hhidist : 1 / x ≤ hi - eig a₀ := by dsimp [hi, lo]; linarith
    have h := one_div_le_one_div_of_le (one_div_pos.mpr hx) hhidist
    simpa using h
  have hcont : ContinuousOn (finiteResolvent ρ eig) (Icc lo hi) :=
    continuousOn_finiteResolvent ρ eig _ (fun b hb a => (hEiglo a).trans_le hb.1)
  obtain ⟨b, hb, hbx⟩ := intermediate_value_Icc' hlohi.le hcont ⟨hxhi, hxlo⟩
  have hbEig : ∀ a, eig a < b := fun a => (hEiglo a).trans_le hb.1
  refine ⟨b, ⟨hbEig, hbx⟩, ?_⟩
  intro c hc
  exact finiteResolvent_solution_unique hρ hρsum hc.1 hbEig hc.2 hbx

/-- In particular every finite spectral probability law with positive masses
has an uncapped inverse at every positive argument. -/
theorem exists_unique_finiteResolvent_of_pos {ρ eig : ι → ℝ} {x : ℝ}
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (hx : 0 < x) :
    ∃! b : ℝ, (∀ a, eig a < b) ∧ finiteResolvent ρ eig b = x := by
  classical
  obtain ⟨a, _⟩ := exists_pos_spectral_weight (fun a => (hρ a).le) hρsum
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨a, Finset.mem_univ a⟩
  obtain ⟨a₀, _, he⟩ := Finset.exists_max_image Finset.univ eig hnonempty
  exact exists_unique_finiteResolvent_solution (fun a => (hρ a).le) hρsum
    (hρ a₀) (fun a => he a (Finset.mem_univ a)) hx

end InvariantIsing

end

end OAI
