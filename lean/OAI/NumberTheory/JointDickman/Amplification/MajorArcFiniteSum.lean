import OAI.NumberTheory.JointDickman.Amplification.MajorArcUnfolding
import OAI.NumberTheory.JointDickman.Probability.LiftedResidueSum

namespace OAI

/-! # The finite major-arc identity for the actual Fourier integrand -/

namespace JointDickman
open Filter MeasureTheory Set Function Finset
open scoped Topology

def positiveDenominators (N : ℕ) : Finset ℕ+ :=
  (range (N+1)).subtype (fun n => 0 < n)

theorem mem_positiveDenominators (N : ℕ) (q : ℕ+) :
    q ∈ positiveDenominators N ↔ (q : ℕ) ≤ N := by
  exact (Finset.mem_subtype (p := fun n : ℕ => 0 < n) (s := range (N+1)) (a := q)).trans
    (by simp only [Finset.mem_range,Nat.lt_succ_iff]; rfl)

theorem tsum_denominator_cutoff (N : ℕ) (G : ℕ+ → ℂ) :
    (∑' q : ℕ+, if (q : ℝ) ≤ (N : ℝ) then G q else 0) =
      ∑ q ∈ positiveDenominators N, G q := by
  classical
  calc
    _ = ∑ q ∈ positiveDenominators N, if (q : ℝ) ≤ (N : ℝ) then G q else 0 := by
      apply tsum_eq_sum
      intro q hq
      have hn : ¬ (q : ℕ) ≤ N := by simpa [mem_positiveDenominators] using hq
      have hr : ¬ (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
      simp [hr]
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      have hr : (q : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (mem_positiveDenominators N q).mp hq
      rw [ite_eq_left hr]

theorem majorArc_finite_sum :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ F : ℝ → ℂ, Continuous F → Periodic F 1 →
      (∫ x in majorArcRegion B j X, F x) =
        ∑ q ∈ positiveDenominators (B^12), ∑ h : ZMod (j*(q : ℕ)),
          if h.val.Coprime (q : ℕ) then
            ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
              (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), F x
          else 0 := by
  filter_upwards [majorArc_unfolded] with B hB
  intro X hX hlog j hj F hF hp
  let : NeZero j := hj
  rw [hB X hX hlog j hj F hF hp]
  have hsum : (fun q : ℕ+ => ∑ u : (ZMod (q : ℕ))ˣ, ∑ t : Fin j,
      if (q : ℝ) ≤ (B : ℝ)^12 then
        ∫ x in
          ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j-((B : ℝ)^13/X)/j)..
          ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j+((B : ℝ)^13/X)/j), F x
      else 0) =
      (fun q : ℕ+ => if (q : ℝ) ≤ ((B^12 : ℕ) : ℝ) then
        ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
          ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
            (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), F x
        else 0 else 0) := by
    funext q
    simp only [Nat.cast_pow]
    split_ifs with hq
    · have hd : ((B : ℝ)^13/X)/j = (B : ℝ)^13/(j*X) := by rw [div_div,mul_comm X]
      simp_rw [hd]
      exact sum_lifted_locations j (q : ℕ) (fun c =>
        ∫ x in c-(B : ℝ)^13/(j*X)..c+(B : ℝ)^13/(j*X), F x)
    · simp
  rw [hsum,tsum_denominator_cutoff]

end JointDickman

end OAI
