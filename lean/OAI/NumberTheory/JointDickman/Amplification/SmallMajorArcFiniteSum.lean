import OAI.NumberTheory.JointDickman.Amplification.TruncatedMajorRegion
import OAI.NumberTheory.JointDickman.Amplification.MajorArcFiniteSum

namespace OAI

/-! # The finite residue identity with a small-denominator cutoff -/

namespace JointDickman
open Filter MeasureTheory Set Function Finset
open scoped Topology

theorem smallMajorArc_hasSum :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j Q : ℕ, ∀ F : ℝ → ℂ, Continuous F →
      HasSum (fun r : ℚ => if r.den ≤ Q then ∫ x in rationalArcPiece B j X r, F x else 0)
        (∫ x in smallMajorArcRegion B j X Q, F x) := by
  filter_upwards [rationalArcPiece_pairwise] with B hB
  intro X hX hlog j Q F hF
  let S : ℚ → Set ℝ := fun r => if r.den ≤ Q then rationalArcPiece B j X r else ∅
  have hm (r : ℚ) : MeasurableSet (S r) := by
    dsimp [S]
    split_ifs
    · exact rationalArcPiece_measurable B j X r
    · exact MeasurableSet.empty
  have hd : Pairwise (Disjoint on S) := by
    intro r s hrs
    change Disjoint (S r) (S s)
    dsimp [S]
    split_ifs
    · exact hB X hX hlog j hrs
    all_goals simp
  have hi : IntegrableOn F (⋃ r, S r) := by
    apply ((hF.intervalIntegrable (μ := volume) 0 1).1).mono_set
    intro x hx
    obtain ⟨r,hr⟩ := mem_iUnion.mp hx
    dsimp [S] at hr
    split_ifs at hr
    · exact hr.1
    · exact hr.elim
  have h := hasSum_integral_iUnion hm hd hi
  have he : (fun r : ℚ => ∫ x in S r, F x) =
      fun r => if r.den ≤ Q then ∫ x in rationalArcPiece B j X r, F x else 0 := by
    funext r
    dsimp [S]
    split_ifs <;> simp
  rw [he] at h
  exact h

theorem smallMajorArc_finite_sum :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ F : ℝ → ℂ, Continuous F → Periodic F 1 →
      (∫ x in smallMajorArcRegion B j X Q, F x) =
        ∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
          ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
            ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
              (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), F x
          else 0 else 0 := by
  filter_upwards [smallMajorArc_hasSum] with B hB
  intro X hX hlog j hj Q F hF hp
  let : NeZero j := hj
  have hh := hB X hX hlog j Q F hF
  rw [← hh.tsum_eq,← (liftedRationalEquiv j).tsum_eq]
  have hs := hh.summable.comp_injective (liftedRationalEquiv j).injective
  dsimp only [Function.comp_def] at hs
  rw [hs.tsum_sigma]
  have heq : (fun q : ℕ+ => ∑' p : (ZMod (q : ℕ))ˣ × (Fin j × ℤ),
      if (liftedRationalEquiv j ⟨q,p⟩).den ≤ Q then
        ∫ x in rationalArcPiece B j X (liftedRationalEquiv j ⟨q,p⟩), F x else 0) =
      (fun q : ℕ+ => if (q : ℝ) ≤ ((B^12 : ℕ) : ℝ) then
        if (q : ℕ) ≤ Q then
          ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
            ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
              (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), F x
          else 0 else 0 else 0) := by
    funext q
    rw [(hs.sigma_factor q).tsum_prod,tsum_fintype]
    have hinner (u : (ZMod (q : ℕ))ˣ) :
        (∑' p : Fin j × ℤ, if (liftedRationalEquiv j ⟨q,u,p⟩).den ≤ Q then
          ∫ x in rationalArcPiece B j X (liftedRationalEquiv j ⟨q,u,p⟩), F x else 0) =
        ∑ t : Fin j, if (q : ℕ) ≤ Q then
          if (q : ℝ) ≤ (B : ℝ)^12 then
            ∫ x in
              ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j-((B : ℝ)^13/X)/j)..
              ((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j+((B : ℝ)^13/X)/j), F x
          else 0 else 0 := by
      rw [((hs.sigma_factor q).prod_factor u).tsum_prod,tsum_fintype]
      apply sum_congr rfl
      intro t _
      simp only [liftedRationalEquiv_den]
      by_cases hq : (q : ℕ) ≤ Q
      · simpa only [ite_eq_left hq] using rationalArc_lifted_sum B j hX q u t hF hp
      · simp [hq]
    simp_rw [hinner]
    simp only [Nat.cast_pow]
    have hwidth : ((B : ℝ)^13/X)/j = (B : ℝ)^13/(j*X) := by rw [div_div,mul_comm X]
    by_cases hqQ : (q : ℕ) ≤ Q
    · simp only [ite_eq_left hqQ]
      by_cases hqB : (q : ℝ) ≤ (B : ℝ)^12
      · simp only [ite_eq_left hqB,hwidth]
        exact sum_lifted_locations j (q : ℕ) (fun c =>
          ∫ x in c-(B : ℝ)^13/(j*X)..c+(B : ℝ)^13/(j*X), F x)
      · simp [hqB]
    · simp [hqQ]
  rw [heq,tsum_denominator_cutoff]

end JointDickman

end OAI
