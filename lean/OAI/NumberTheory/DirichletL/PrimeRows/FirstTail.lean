import OAI.NumberTheory.DirichletL.PrimeRows.Product
import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRegion

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

def firstPrimeDefectBound (eps : ℝ) (P : PrimeIdeal) : ℝ :=
  240*(P.val.absNorm : ℝ)^(-1-min eps (1/50:ℝ))

theorem firstPrimeDefectBound_nonneg (eps : ℝ) (P : PrimeIdeal) :
    0≤firstPrimeDefectBound eps P := by unfold firstPrimeDefectBound; positivity

theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
    Summable (firstPrimeDefectBound eps) := by
  have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    have hm : 0<min eps (1/50:ℝ) := lt_min heps (by norm_num)
    linarith
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
  unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp only [Complex.neg_re,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  congr 2
  ring

structure FirstTail (eps : ℝ) (S : Finset (Ideal O)) : Prop where
  positive : 0<eps
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤P.val.absNorm
  small : (∑' P : {P : PrimeIdeal // P.val∉S},firstPrimeDefectBound eps P.val)≤1/6

theorem FirstTail.summable {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val) :=
  (firstPrimeDefectBound_summable eps h.positive).subtype _

theorem FirstTail.half {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S)
    (P : {P : PrimeIdeal // P.val∉S}) : firstPrimeDefectBound eps P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>firstPrimeDefectBound_nonneg eps Q.val)
  linarith [h.small]

theorem exists_first_cutoff (eps : ℝ) (heps : 0<eps) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset (Ideal O),
      (∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S) → FirstTail eps S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (firstPrimeDefectBound eps))).2
    (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>P.val.absNorm))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>P.val.absNorm) hm).trans
      (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  refine ⟨heps,?_,?_⟩
  · intro P hP
    have hn : ¬P.val.absNorm≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>firstPrimeDefectBound_nonneg eps P.val) (fun _=>le_rfl)
      ((firstPrimeDefectBound_summable eps heps).subtype _)
      ((firstPrimeDefectBound_summable eps heps).subtype _)

theorem exists_both_source_exclusions (eps : ℝ) (heps : 0<eps)
    (S₀ : Finset (Ideal O)) (hp : ∀P∈S₀,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S₀) :
    ∃S : Finset (Ideal O),S₀⊆S ∧ SourceExclusions S ∧ FirstTail eps S := by
  obtain ⟨N₁,hN₁,hcut₁⟩ := exists_uniform_global_cutoff
  obtain ⟨N₂,hN₂,hcut₂⟩ := exists_first_cutoff eps heps
  let N := max N₁ N₂
  let S := S₀∪smallPrimeSet N
  have hpS : ∀P∈S,Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  have hcut : ∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S := by
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
  refine ⟨S,Finset.subset_union_left,⟨hpS,hbad.trans Finset.subset_union_left,?_⟩,?_⟩
  · exact hcut₁ S (fun P hP=>hcut P (hP.trans (le_max_left _ _)))
  · exact hcut₂ S (fun P hP=>hcut P (hP.trans (le_max_right _ _)))

end SevenEighths.ProbeHighRowFamily

end

end OAI
