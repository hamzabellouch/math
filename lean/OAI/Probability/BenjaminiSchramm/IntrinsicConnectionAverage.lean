import OAI.Probability.BenjaminiSchramm.IntrinsicConnection

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsic_sphere_interval_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x z : V) (m n : ℕ) :
    (∑ j ∈ Finset.Icc (m+1) n, law p (intrinsicSphereEvent G x z j)) ≤
      law p (longConnectionEvent G x z m) := by
  have hdisj : (↑(Finset.Icc (m+1) n) : Set ℕ).PairwiseDisjoint (intrinsicSphereEvent G x z) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro ω ⟨_,hi⟩ ⟨_,hj⟩
    exact hij (hi.symm.trans hj)
  rw [←measure_biUnion_finset hdisj (fun j hj => measurableSet_intrinsicSphereEvent G hloc x z j
    (by have h := (Finset.mem_Icc.mp hj).1; omega))]
  apply measure_mono
  intro ω hω
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hji,hz⟩ := Set.mem_iUnion.mp hj
  exact ⟨hz.1,((Nat.le_succ m).trans (Finset.mem_Icc.mp hji).1).trans_eq hz.2.symm⟩

theorem longConnection_interval_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x y : V) (m n : ℕ) :
    (n-m : ℕ) * law p (longConnectionEvent G x y n) ≤
      ∑' z, law p (longConnectionEvent G x z m) * law p {ω | Conn G ω z y} := by
  have havg := Finset.sum_le_sum (s := Finset.Icc (m+1) n) (fun j hj => longConnection_sphere_bound G hloc p x y n j
    (by have h := (Finset.mem_Icc.mp hj).1; omega) (Finset.mem_Icc.mp hj).2)
  have hcard : (Finset.Icc (m+1) n).card = n-m := by rw [Nat.card_Icc]; omega
  calc
    _ = ∑ j ∈ Finset.Icc (m+1) n, law p (longConnectionEvent G x y n) := by
      simp only [Finset.sum_const,nsmul_eq_mul,hcard]
    _ ≤ ∑ j ∈ Finset.Icc (m+1) n,
        ∑' z, law p (intrinsicSphereEvent G x z j) * law p {ω | Conn G ω z y} := havg
    _ = ∑' z, ∑ j ∈ Finset.Icc (m+1) n,
        law p (intrinsicSphereEvent G x z j) * law p {ω | Conn G ω z y} :=
      (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
    _ = ∑' z, (∑ j ∈ Finset.Icc (m+1) n, law p (intrinsicSphereEvent G x z j)) *
        law p {ω | Conn G ω z y} := by simp only [Finset.sum_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum (fun z => mul_le_mul'
      (intrinsic_sphere_interval_sum_le G hloc p x z m n) le_rfl)

theorem longConnection_power_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (M k : ℕ) (x y : V) :
    (M : ℝ≥0∞)^k * law p (longConnectionEvent G x y (k*M)) ≤
      ennMatrixCoeff (T^(k+1)) x y := by
  have hpos := hT.positiveRealMatrix G p T
  induction k generalizing x y with
  | zero =>
    rw [pow_zero,one_mul,Nat.zero_mul,pow_one,hT.ennMatrixCoeff G p T]
    apply measure_mono
    intro ω hω
    exact hω.1
  | succ k ih =>
    have hrec := longConnection_interval_bound G hloc p x y (k*M) ((k+1)*M)
    have hsub : (k+1)*M-k*M = M := by rw [Nat.add_mul]; omega
    rw [hsub] at hrec
    calc
      _ = (M : ℝ≥0∞)^k * (M * law p (longConnectionEvent G x y ((k+1)*M))) := by rw [pow_succ,mul_assoc]
      _ ≤ (M : ℝ≥0∞)^k * ∑' z, law p (longConnectionEvent G x z (k*M)) * law p {ω | Conn G ω z y} :=
        mul_le_mul' le_rfl hrec
      _ = ∑' z, ((M : ℝ≥0∞)^k * law p (longConnectionEvent G x z (k*M))) * law p {ω | Conn G ω z y} := by
        rw [←ENNReal.tsum_mul_left]
        simp only [mul_assoc]
      _ ≤ ∑' z, ennMatrixCoeff (T^(k+1)) x z * ennMatrixCoeff T z y := by
        apply ENNReal.tsum_le_tsum
        intro z
        rw [hT.ennMatrixCoeff G p T]
        exact mul_le_mul' (ih x z) le_rfl
      _ = _ := by
        rw [←ennMatrixCoeff_mul (hpos.pow (k+1)) hpos,←pow_succ]

end Percolation.BenjaminiSchramm

end OAI
