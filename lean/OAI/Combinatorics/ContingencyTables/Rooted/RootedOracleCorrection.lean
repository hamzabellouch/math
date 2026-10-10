import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleDensity
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleJointLaw

namespace OAI

/-! # Exact population correction for the computed-root completion count

Integer bins and their executable interval draws are the existing
physical bins.  Only their positive density weights change with the
explicit root selector.  All normalizer identities are finite sums.
-/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GridBoundary
open CompanionOracleDensity (dimension index pull binWidth height integerPoint integerBin integerFiber
  assignmentCount ownFiber_positive assignmentCount_positive integerFiber_nonempty)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def gridWeight (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ :=
  V A S C a z (realCorner v)

lemma gridWeight_positive (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    0<gridWeight A S C a z v := DenseWeights.binWeight_pos _ _ _

lemma density_at_integer (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    rho A S C a z (integerPoint A C f)=
      (2:ℝ)^(-(a*C/height A C)*RootedLiteralCount.actualPenalty A S
        (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
        (freeTable A.small A.T A.b f)
        (RootedPhysicalCompletion.solved A S (ForestScaledPenalty.rowCounts A z)
          (ForestScaledPenalty.columnCounts A z) (fun i j => (freeTable A.small A.T A.b f i j:ℤ)))) := by
  unfold rho DenseWeights.density D
  rw [CompanionOracleDensity.pull_integerPoint]
  have hp := RootedScaledPenalty.penalty_at_integer A S C (binWidth A C)
    (CompanionOracleDensity.binWidth_positive A C hC) z f
  have hr : (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))=
      ForestScaledPenalty.rowCounts A z := rfl
  have hc : (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))=
      ForestScaledPenalty.columnCounts A z := rfl
  rw [hr,hc] at hp
  rw [hp]
  congr 1
  ring

lemma sum_density_integer (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) :
    (∑ f : FreeIndex A.small A.T A.b,rho A S C a z (integerPoint A C f))=
      RootedCountIdentification.h A S (a*C/height A C) z := by
  unfold RootedCountIdentification.h
  apply Finset.sum_congr rfl
  intro f _
  exact density_at_integer A S C a hC z f

noncomputable def binSum (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) : ℝ :=
  ∑ v : Grid (I := Fin (dimension A)) K,gridWeight A S C a z v

lemma binSum_positive (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) : 0<binSum A S C a z K := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact Finset.sum_pos (fun _ _ => gridWeight_positive _ _ _ _ _ _) Finset.univ_nonempty

noncomputable def correctedMass (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) : ℝ :=
  gridWeight A S C a z (integerBin A K hK f)/binSum A S C a z K/
    (integerFiber A K hK (integerBin A K hK f)).card

noncomputable def correction (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) : ℝ :=
  ((K:ℝ)^dimension A*(integerFiber A K hK (integerBin A K hK f)).card/assignmentCount A)*
    rho A S C a z (integerPoint A C f)/gridWeight A S C a z (integerBin A K hK f)

lemma correctedMass_nonnegative (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) :
    0≤ correctedMass A S C a z K hK f := by
  unfold correctedMass
  exact div_nonneg (div_nonneg (gridWeight_positive _ _ _ _ _ _).le
    (binSum_positive _ _ _ _ _ _ hK).le) (Nat.cast_nonneg _)

theorem correction_bounds (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0<K) (hW : 100*A.d*K≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (f : FreeIndex A.small A.T A.b) :
    1/8≤ correction A S C a z K hK f ∧ correction A S C a z K hK f≤4 := by
  let v := integerBin A K hK f
  have hpQ := CompanionOracleDensity.actual_population_bounds A K hK hW v
  have hp : (1/2:ℝ)≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A≤2 := by
    constructor
    · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.2
  have hdist : ∀ i,|realCorner v i-integerPoint A C f i|≤1 := by
    intro i
    simpa only [abs_sub_comm] using CompanionOracleDensity.integerPoint_distance A C K hK hB f i
  have hb := bin_comparison A S C a hC ha haH z (realCorner v) (integerPoint A C f) hdist
  have hw := gridWeight_positive A S C a z v
  have hr : (1/4:ℝ)≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v ∧
      rho A S C a z (integerPoint A C f)/gridWeight A S C a z v≤2 := by
    constructor
    · apply (le_div_iff₀ hw).mpr
      simpa only [gridWeight,div_eq_mul_inv,mul_comm,one_mul] using hb.1
    · exact (div_le_iff₀ hw).mpr (by simpa only [gridWeight] using hb.2)
  have he : correction A S C a z K hK f=
      ((K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)*
        (rho A S C a z (integerPoint A C f)/gridWeight A S C a z v) := by
    unfold correction
    ring
  rw [he]
  constructor
  · have hh := mul_le_mul hp.1 hr.1 (by norm_num : (0:ℝ)≤1/4) (by linarith :
        0≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)
    norm_num at hh ⊢
    exact hh
  · have hh := mul_le_mul hp.2 hr.2 (by linarith [hr.1] :
        0≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v)
      (by norm_num : (0:ℝ)≤2)
    norm_num at hh ⊢
    exact hh

lemma corrected_mass_product (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) :
    correctedMass A S C a z K hK f*correction A S C a z K hK f=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A S C a z K))*
        rho A S C a z (integerPoint A C f) := by
  have hw := (gridWeight_positive A S C a z (integerBin A K hK f)).ne'
  have hf : ((integerFiber A K hK (integerBin A K hK f)).card:ℝ)≠0 := by
    exact_mod_cast (ownFiber_positive A K hK f).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  have hz := (binSum_positive A S C a z K hK).ne'
  unfold correctedMass correction
  field_simp [hw,hf,hc,hz]

theorem corrected_expectation (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) (K : ℕ) (hK : 0<K) :
    (∑ f : FreeIndex A.small A.T A.b,
      correctedMass A S C a z K hK f*correction A S C a z K hK f)=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A S C a z K))*
        RootedCountIdentification.h A S (a*C/height A C) z := by
  simp_rw [corrected_mass_product]
  rw [←Finset.mul_sum,sum_density_integer A S C a hC]

theorem correctedMass_total (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (hW : 100*A.d*K≤ A.W) :
    (∑ f : FreeIndex A.small A.T A.b,correctedMass A S C a z K hK f)=1 := by
  have hbin (v : Grid (I := Fin (dimension A)) K) :
      (∑ f : FreeIndex A.small A.T A.b,if integerBin A K hK f=v then
        correctedMass A S C a z K hK f else 0)=gridWeight A S C a z v/binSum A S C a z K := by
    have hc : ((integerFiber A K hK v).card:ℝ)≠0 := by
      exact_mod_cast (Finset.card_pos.mpr (integerFiber_nonempty A K hK hW v)).ne'
    have hz := (binSum_positive A S C a z K hK).ne'
    calc
      _=∑ f : FreeIndex A.small A.T A.b,if integerBin A K hK f=v then
          gridWeight A S C a z v/binSum A S C a z K/(integerFiber A K hK v).card else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf : integerBin A K hK f=v <;> simp only [correctedMass,hf,ite_true,ite_false]
      _=∑ f∈integerFiber A K hK v,gridWeight A S C a z v/binSum A S C a z K/
          (integerFiber A K hK v).card := by simp only [integerFiber,Finset.sum_filter]
      _=_ := by rw [Finset.sum_const,nsmul_eq_mul]; field_simp [hc,hz]
  calc
    _=∑ v : Grid (I := Fin (dimension A)) K,∑ f : FreeIndex A.small A.T A.b,
        if integerBin A K hK f=v then correctedMass A S C a z K hK f else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      simp
    _=∑ v : Grid (I := Fin (dimension A)) K,gridWeight A S C a z v/binSum A S C a z K :=
      Finset.sum_congr rfl (fun v _ => hbin v)
    _=1 := by rw [←Finset.sum_div]; exact div_self (binSum_positive A S C a z K hK).ne'

noncomputable def ratioObservable (A : Instance I J) (S : Selection A.T) (C : ℝ)
    (a : ℕ) (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ :=
  gridWeight A S C (a+1) z v/gridWeight A S C a z v

noncomputable def ratioMean (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (a : ℕ) (z : View A → ℕ) (K : ℕ) : ℝ :=
  ∑ v : Grid (I := Fin (dimension A)) K,
    (gridWeight A S C a z v/binSum A S C a z K)*ratioObservable A S C a z v

lemma ratioMean_eq (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (a : ℕ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) :
    ratioMean A S C a z K=binSum A S C (a+1) z K/binSum A S C a z K := by
  unfold ratioMean binSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  have hv := (gridWeight_positive A S C a z v).ne'
  have hz := (binSum_positive A S C a z K hK).ne'
  unfold ratioObservable
  change (gridWeight A S C a z v/binSum A S C a z K)*
    (gridWeight A S C (a+1) z v/gridWeight A S C a z v)=
      gridWeight A S C (a+1) z v/binSum A S C a z K
  field_simp [hv,hz]

lemma binSum_zero (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (z : View A → ℕ) (K : ℕ) : binSum A S C 0 z K=(K:ℝ)^dimension A := by
  simp only [binSum,gridWeight,V,DenseWeights.binWeight,zero_div,zero_mul,Int.floor_zero,
    Int.cast_zero,neg_zero,Real.rpow_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,CompanionOracleDensity.oracle_grid_card,Nat.cast_pow]

lemma ratio_telescope (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (j : ℕ) :
    (∏ a∈Finset.range j,ratioMean A S C a z K)=binSum A S C j z K/(K:ℝ)^dimension A := by
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  induction j with
  | zero => simp only [Finset.range_zero,Finset.prod_empty,Nat.cast_zero,binSum_zero,div_self hp]
  | succ j ih =>
    rw [Finset.prod_range_succ,ih,ratioMean_eq A S C j z K hK]
    have hz := (binSum_positive A S C j z K hK).ne'
    push_cast
    field_simp [hp,hz]

theorem oracle_telescope (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (K : ℕ) (hK : 0<K) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ a∈Finset.range j,ratioMean A S C a z K)*
      (∑ f : FreeIndex A.small A.T A.b,
        correctedMass A S C j z K hK f*correction A S C j z K hK f)=
      RootedCountIdentification.h A S ((j:ℝ)*C/height A C) z := by
  rw [ratio_telescope A S C z K hK j,corrected_expectation A S C j hC z K hK]
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  have hz := (binSum_positive A S C j z K hK).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  field_simp [hp,hz,hc]

end ContingencyTables.RootedOracleDensity

end OAI
