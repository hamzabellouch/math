import OAI.NumberTheory.TotientAsymptotic.LocalExceptionalResidualMass
import OAI.NumberTheory.TotientAsymptotic.LocalResidualWitness
import OAI.NumberTheory.TotientAsymptotic.LocalSuffixFamily
import OAI.NumberTheory.TotientAsymptotic.PPTSeedNormality

namespace OAI

/-! Apply the exceptional estimates to the actual distinct suffix values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localWitnessNonnormal (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) : Finset ℕ :=
  R.filter (fun r => ∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p)

def localWitnessSquare (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) : Finset ℕ :=
  R.filter (fun r => ∃ p : ℕ,p.Prime ∧ localNormalityScale h<p ∧
    (p^2 ∣ F r ∨ p^2 ∣ (F r).totient))

def localWitnessRegular (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) : Finset ℕ :=
  R \ (localWitnessNonnormal R F h ∪ localWitnessSquare R F h)

lemma local_regular_witness_properties {R : Finset ℕ} {F : ℕ → ℕ} {h r : ℕ}
    (hr : r ∈ localWitnessRegular R F h) :
    r∈R ∧ (∀ p : ℕ,p.Prime → p ∣ F r → IsNormalPrime (localNormalityScale h) p) ∧
      SquarefreeAbove (F r) (localNormalityScale h) ∧
      SquarefreeAbove (F r).totient (localNormalityScale h) := by
  classical
  obtain ⟨hr,hnot⟩ := Finset.mem_sdiff.mp hr
  have hn : r ∉ localWitnessNonnormal R F h := fun h => hnot (Finset.mem_union_left _ h)
  have hs : r ∉ localWitnessSquare R F h := fun h => hnot (Finset.mem_union_right _ h)
  refine ⟨hr,?_,?_,?_⟩
  · intro p hp hdiv
    by_contra hbad
    exact hn (Finset.mem_filter.mpr ⟨hr,p,hp,hdiv,hbad⟩)
  · intro p hp hlarge hdiv
    exact hs (Finset.mem_filter.mpr ⟨hr,p,hp,hlarge,Or.inl hdiv⟩)
  · intro p hp hlarge hdiv
    exact hs (Finset.mem_filter.mpr ⟨hr,p,hp,hlarge,Or.inr hdiv⟩)

lemma local_residual_mass_partition (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) :
    (∑ r ∈ R,(r.totient:ℝ)⁻¹) ≤
      (∑ r ∈ localWitnessNonnormal R F h,(r.totient:ℝ)⁻¹)+
      (∑ r ∈ localWitnessSquare R F h,(r.totient:ℝ)⁻¹)+
      (∑ r ∈ localWitnessRegular R F h,(r.totient:ℝ)⁻¹) := by
  classical
  let N := localWitnessNonnormal R F h
  let S := localWitnessSquare R F h
  let f := fun r : ℕ => (r.totient:ℝ)⁻¹
  have hsub : N∪S ⊆ R := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit := Finset.sum_sdiff (f:=f) hsub
  have hunion := Finset.sum_union_inter (s₁:=N) (s₂:=S) (f:=f)
  have hpos : 0 ≤ ∑ r ∈ N∩S,f r := Finset.sum_nonneg (fun r _ => by dsimp [f]; positivity)
  change (∑ r ∈ R,f r) ≤ (∑ r ∈ N,f r)+(∑ r ∈ S,f r)+(∑ r ∈ R\(N∪S),f r)
  linarith only [hsplit,hunion,hpos]

lemma local_residual_card_partition (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) :
    R.card ≤ (localWitnessNonnormal R F h).card+(localWitnessSquare R F h).card+
      (localWitnessRegular R F h).card := by
  classical
  let N := localWitnessNonnormal R F h
  let S := localWitnessSquare R F h
  have hsub : N∪S ⊆ R := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  have hunion := Finset.card_union_le N S
  change R.card ≤ N.card+S.card+(R\(N∪S)).card
  omega

lemma localNormalityScale_tendsto : Tendsto localNormalityScale atTop atTop :=
  Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    ((tendsto_pow_atTop (by decide : 4≠0)).comp tendsto_natCast_atTop_atTop))

theorem local_bad_suffix_exception_data {c : ℝ} (hc : 0 < c)
    (d q : ℕ) (hd : 0 < d) (hqpos : 0 < q) (hq : q.totient=d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ i : Fin (m x-H),
      let R := localBadSuffixValues x c d L H i
      let h := m x-i.val
      ∃ F : ℕ → ℕ,Set.InjOn F (R : Set ℕ) ∧
        (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
          largestPrimeFactor (F r) ≠ largestPrimeFactor r) ∧
        (∑ r ∈ localWitnessNonnormal R F h,(r.totient:ℝ)⁻¹) ≤ rho^h ∧
        (∑ r ∈ localWitnessSquare R F h,(r.totient:ℝ)⁻¹) ≤ rho^h := by
  classical
  obtain ⟨A,hA,hvalues⟩ := local_bad_suffix_value_bounds hc d hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hA' : 0 < A+Real.log d+2 := by
    have := Real.log_nonneg hd1
    linarith
  have hn := local_nonnormal_residual_mass (half_pos hc) hA' d q L hd
  have hs := local_square_residual_mass (half_pos hc) hA' d L hd
  have hseed := localNormalityScale_tendsto.eventually
    (ppt_seed_prime_factors_eventually_normal hqpos)
  obtain ⟨h₀,hh₀⟩ := eventually_atTop.mp (hn.and (hs.and hseed))
  filter_upwards [hvalues L,eventually_ge_atTop h₀] with H hH hH0
  filter_upwards [hH] with x hx
  intro i
  let R := localBadSuffixValues x c d L H i
  let h := m x-i.val
  have hHi : H ≤ h := by have := i.isLt; dsimp [h]; omega
  obtain ⟨hn,hs,hseed⟩ := hh₀ h (hH0.trans hHi)
  have hR (r) (hr : r∈R) := local_bad_suffix_normality i hr
  obtain ⟨F,hinj,hF,hbranch⟩ := local_bad_residual_witness hd hqpos hq R
    (fun r hr => (hR r hr).1)
  have hval (r) (hr : r∈R) : ∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
      (c/2)*(rho^h)⁻¹ ≤ B p ∧ ((d*r.totient:ℕ):ℝ) ≤
        Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L h)) := by
    obtain ⟨hu,p,hp,hpv,hgeo⟩ := hx i r hr
    exact ⟨p,hp,hpv,hgeo,hu⟩
  refine ⟨F,hinj,hF,?_,?_⟩
  · apply hn R (localWitnessNonnormal R F h) F (Finset.filter_subset _ _)
      (fun r hr => hval r (Finset.mem_filter.mp hr).1)
      (fun r hr => (hR r hr).2) hseed hbranch
      (fun _ hr => (Finset.mem_filter.mp hr).2)
      (fun r hr => ⟨(hF r (Finset.mem_filter.mp hr).1).1,
        (hF r (Finset.mem_filter.mp hr).1).2.1⟩)
  · apply hs (localWitnessSquare R F h) F (hinj.mono (Finset.filter_subset _ _))
      (fun r hr => hval r (Finset.mem_filter.mp hr).1)
      (fun r hr => ⟨(hF r (Finset.mem_filter.mp hr).1).1,
        (hF r (Finset.mem_filter.mp hr).1).2.1⟩)
      (fun _ hr => (Finset.mem_filter.mp hr).2)

end TotientAsymptotic

end

end OAI
