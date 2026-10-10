import OAI.NumberTheory.DirichletL.Detector.EulerHolomorphic
import OAI.NumberTheory.DirichletL.Detector.NormalProduct

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection
local notation "O" => ActualEisensteinCubic.O

def primeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(363/200:ℝ))

def principalLocal (eta : HeckeFamily.Character) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase eta (primaryGenerator P.val))
    (HeckeFamily.elementCoeff eta (primaryGenerator P.val)) 1 s 1 (1/6)

def principalCorrection (eta : HeckeFamily.Character) (S : Finset (Ideal O)) (s : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val ∉ S}, principalLocal eta P.val s

lemma primeDefectBound_nonneg (P : PrimeIdeal) : 0 ≤ primeDefectBound P := by
  unfold primeDefectBound
  positivity

lemma primeDefectBound_summable : Summable primeDefectBound := by
  have h : Summable (fun P : PrimeIdeal => ‖CubicEisenstein.fullIdealWeight ((363/200:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm ((363/200:ℝ):ℂ) (by norm_num)).comp_injective
      Subtype.val_injective
  apply (h.mul_left 240).congr
  intro P
  unfold primeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

lemma principalLocal_bound (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (s : ℂ) (hs : 7/8 < s.re) :
    ‖principalLocal eta P s-1‖ ≤ primeDefectBound P := by
  apply unramifiedClosed_second_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · simp
  · exact hs.le
  · norm_num
  · norm_num

lemma principalLocal_analytic (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | 7/8 < s.re} := by
  apply principalClosed_analytic
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _

theorem exists_uniform_principal_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ (S : Finset (Ideal O)),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
        ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero primeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans (le_max_right _ _)
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) h
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => primeDefectBound P.val) :=
    primeDefectBound_summable.subtype _
  have hsmall : (∑' P : T, primeDefectBound P.val) ≤ 1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => primeDefectBound_nonneg P.val) (fun _ => le_rfl)
      hsum (primeDefectBound_summable.subtype _)
  have hhalf (P : T) : primeDefectBound P.val ≤ 1/2 := by
    have hterm := Summable.le_tsum hsum P (fun Q _ => primeDefectBound_nonneg Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => primeDefectBound P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principalLocal_analytic eta P.val (hnorm P))
      (fun P s hs => principalLocal_bound eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => primeDefectBound P.val) hsum
      (fun P => principalLocal_bound eta P.val (hnorm P) s hs) hhalf hsmall

def smallPrimeSet (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le N).toFinset.filter Prime

lemma mem_smallPrimeSet (N : ℕ) (P : PrimeIdeal) :
    P.val ∈ smallPrimeSet N ↔ Ideal.absNorm P.val ≤ N := by
  simp [smallPrimeSet, P.property]

theorem exists_principal_correction (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
      ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_principal_cutoff
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbeEuler
end

end OAI
