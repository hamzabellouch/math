import OAI.NumberTheory.TotientAsymptotic.LocalNormalityMass
import OAI.NumberTheory.TotientAsymptotic.LocalPrimeSupport
import OAI.NumberTheory.TotientAsymptotic.GeometricPrefixMass

namespace OAI

/-! The actual two-index normality exclusion in the local candidate grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localAbnormalTuples (x c : ℝ) (L H : ℕ)
    (i j : Fin (m x-H)) : Finset (Fin (m x-H) → ℕ) :=
  (gridPrimeTuples (localPrimeGrid x c L (m x-H))).filter
    (fun p => ¬IsNormalPrime (localNormalityScale (m x-i.val)) (p j))

theorem local_normality_layer_mass {c : ℝ} (hc : 0 < c) :
    ∃ A C D : ℝ,0 < A ∧ 0 < C ∧ 0 < D ∧
    ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ i j : Fin (m x-H),i ≤ j →
      let h := m x-i.val
      let U := localPrimeHeight A L h
      (∑ p ∈ localAbnormalTuples x c L H i j,reciprocalShiftWeight p) ≤
        C*G x (m x-H)*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6)*
          (D*(2*U+2))^(m x-H-i.val-1) := by
  obtain ⟨A,hA,hsupport⟩ := local_prime_suffix_support hc
  obtain ⟨C₀,hC₀,hprefix⟩ := geometric_initial_mass_le_base (half_pos hc)
  obtain ⟨E,hE,hexcept⟩ := local_non_normal_prime_mass
  obtain ⟨D,hD,htotal⟩ := candidate_total_prime_mass
  refine ⟨A,C₀*E,D,hA,mul_pos hC₀ hE,hD,?_⟩
  intro L
  filter_upwards [hsupport L,hprefix,head_limited_prime_coordinates hc] with H hH hpref hcoords
  filter_upwards [hH,hpref,hcoords,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hsup hpre hco hm hB
  intro i j hij
  dsimp only
  let N := m x-H
  let h := m x-i.val
  let U := localPrimeHeight A L h
  let Q := localAbnormalTuples x c L H i j
  have hU : 2 ≤ U := localPrimeHeight_ge_two hA.le L h
  have hi : i.val ≤ N := Nat.le_of_lt i.isLt
  let k : Fin (N-i.val) := ⟨j.val-i.val,by have := j.isLt; omega⟩
  have hmem (p) (hp : p ∈ Q) : p ∈ gridPrimeTuples (localPrimeGrid x c L N) :=
    (Finset.mem_filter.mp hp).1
  have hheadmem (p) (hp : p ∈ Q) : p ∈ gridPrimeTuples (headLimitedPrimeGrid x c N) := by
    obtain ⟨b,hb,hp⟩ := Finset.mem_biUnion.mp (hmem p hp)
    exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hp⟩
  have hq (p) (hp : p ∈ Q) : (∀ l,(p l).Prime) ∧
      primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) (c/2) := by
    have hh := hco N (Nat.sub_add_cancel hm) p (hheadmem p hp)
    exact ⟨hh.1,hh.2.1⟩
  have hsp (p) (hp : p ∈ Q) (l : Fin (N-i.val)) :
      primeFinal p i.val l ∈ Nat.primesLE (discardPrimeBound U) := by
    apply hsup N (Nat.sub_add_cancel hm) p (hmem p hp) i
      ⟨i.val+l.val,by have := l.isLt; omega⟩
    show i.val ≤ i.val+l.val
    omega
  have hbad (p) (hp : p ∈ Q) :
      primeFinal p i.val k ∈ nonNormalPrimes (localNormalityScale h) (discardPrimeBound U) := by
    apply Finset.mem_filter.mpr
    refine ⟨hsp p hp k,?_⟩
    have he : primeFinal p i.val k=p j := by
      apply congrArg p
      apply Fin.ext
      change i.val+(j.val-i.val)=j.val
      omega
    rw [he]
    exact (Finset.mem_filter.mp hp).2
  have hmass := prime_mass_one_exception hi Q k _ _ hsp hbad
  have hpm := hpre N i.val (Nat.sub_add_cancel hm) hi Q hq
  have hem := hexcept h U hU
  have htm := htotal U hU
  have hright : (∑ p ∈ Q,reciprocalShiftWeight p) ≤
      (C₀*G x N)*(E*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6))*
        (D*(2*U+2))^(N-i.val-1) := by
    apply hmass.trans
    apply mul_le_mul
    · exact mul_le_mul hpm hem (Finset.sum_nonneg (fun _ _ => by positivity))
        (mul_nonneg hC₀.le (G_pos hB _).le)
    · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) htm _
    · positivity
    · exact mul_nonneg (mul_nonneg hC₀.le (G_pos hB _).le) (by positivity)
  convert hright using 1
  ring

end TotientAsymptotic

end

end OAI
