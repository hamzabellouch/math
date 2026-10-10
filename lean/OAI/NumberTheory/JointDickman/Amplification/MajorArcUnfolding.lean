import OAI.NumberTheory.JointDickman.Amplification.LiftedRationalEquiv
import OAI.NumberTheory.JointDickman.Counting.ArcWindowUnfolding
import OAI.NumberTheory.JointDickman.Amplification.MajorArcPartition

namespace OAI

/-! # Unfolding the rational major-arc partition into its finitely many lifts -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

theorem scaled_arc_window {j : ℝ} (hj : 0 < j) (c D x k : ℝ) :
    |-j*x-(-j*(c-k))| ≤ D ↔ c-D/j ≤ k+x ∧ k+x ≤ c+D/j := by
  rw [show -j*x-(-j*(c-k)) = j*(c-(k+x)) by ring,
    abs_mul, abs_of_pos hj, mul_comm, ← le_div_iff₀ hj, abs_le]
  constructor <;> rintro ⟨hL,hU⟩ <;> constructor <;> linarith

theorem rationalArcPiece_lifted (B j : ℕ) [NeZero j] (X : ℝ)
    (q : ℕ+) (u : (ZMod (q : ℕ))ˣ) (t : Fin j) (k : ℤ) :
    rationalArcPiece B j X (liftedRationalEquiv j ⟨q,u,t,k⟩) =
      if (q : ℝ) ≤ (B : ℝ)^12 then
        {x : ℝ | x ∈ Ioc 0 1 ∧
          (((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j-((B : ℝ)^13/X)/j ≤ k+x ∧
          k+x ≤ (((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j+((B : ℝ)^13/X)/j}
      else ∅ := by
  have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne j)
  ext x
  simp only [rationalArcPiece,mem_ofPred_eq,liftedRationalEquiv_den,
    liftedRationalEquiv_cast,scaled_arc_window hj]
  split_ifs with hq <;> simp [hq]

theorem rationalArc_lifted_sum (B j : ℕ) [NeZero j] {X : ℝ} (hX : 0 < X)
    (q : ℕ+) (u : (ZMod (q : ℕ))ˣ) (t : Fin j)
    {F : ℝ → ℂ} (hF : Continuous F) (hp : Periodic F 1) :
    (∑' k : ℤ, ∫ x in rationalArcPiece B j X (liftedRationalEquiv j ⟨q,u,t,k⟩), F x) =
      if (q : ℝ) ≤ (B : ℝ)^12 then
        ∫ x in
          ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j-((B : ℝ)^13/X)/j)..
          ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j+((B : ℝ)^13/X)/j), F x
      else 0 := by
  simp_rw [rationalArcPiece_lifted]
  split_ifs with hq
  · apply periodic_closed_windows hF hp
    have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne j)
    have hd : 0 ≤ ((B : ℝ)^13/X)/j := div_nonneg
      (div_nonneg (pow_nonneg (Nat.cast_nonneg B) _) hX.le) hj.le
    linarith
  · simp

theorem rationalArc_integral_summable :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ F : ℝ → ℂ, Continuous F →
        Summable (fun r : ℚ => ∫ x in rationalArcPiece B j X r, F x) := by
  filter_upwards [rationalArcPiece_pairwise] with B hB
  intro X hX hlog j F hF
  apply (hasSum_integral_iUnion (rationalArcPiece_measurable B j X)
    (hB X hX hlog j) ?_).summable
  apply ((hF.intervalIntegrable (μ := volume) 0 1).1).mono_set
  intro x hx
  obtain ⟨r,hr⟩ := mem_iUnion.mp hx
  exact hr.1

/-- All translates, including arcs through zero, combine into exactly j lifts
of each reduced coefficient fraction. -/
theorem majorArc_unfolded :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ F : ℝ → ℂ, Continuous F → Periodic F 1 →
      (∫ x in majorArcRegion B j X, F x) =
        ∑' q : ℕ+, ∑ u : (ZMod (q : ℕ))ˣ, ∑ t : Fin j,
          if (q : ℝ) ≤ (B : ℝ)^12 then
            ∫ x in
              ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j-((B : ℝ)^13/X)/j)..
              ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j+((B : ℝ)^13/X)/j), F x
          else 0 := by
  filter_upwards [majorArc_integral_sum,rationalArc_integral_summable] with B hB hsB
  intro X hX hlog j hj F hF hp
  let : NeZero j := hj
  rw [hB X hX hlog j F hF, ← (liftedRationalEquiv j).tsum_eq]
  have hs := (hsB X hX hlog j F hF).comp_injective (liftedRationalEquiv j).injective
  dsimp only [Function.comp_def] at hs
  rw [hs.tsum_sigma]
  apply tsum_congr
  intro q
  rw [(hs.sigma_factor q).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro u _
  rw [((hs.sigma_factor q).prod_factor u).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro t _
  exact rationalArc_lifted_sum B j hX q u t hF hp

end JointDickman

end OAI
