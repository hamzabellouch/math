import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleFibres

namespace OAI

/-! # Normalization of the actual bin-then-integer sampling law -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma sum_by_bins {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (bin : X → Y) (g : X → ℝ) :
    (∑ y : Y,∑ x : X,if bin x=y then g x else 0)=∑ x,g x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

private lemma total_of_bin_sums {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (bin : X → Y) (g : X → ℝ) (p : Y → ℝ)
    (h : ∀ y,(∑ x : X,if bin x=y then g x else 0)=p y)
    (hp : ∑ y,p y=1) : ∑ x,g x=1 := by
  calc
    _ = ∑ y : Y,∑ x : X,if bin x=y then g x else 0 := (sum_by_bins bin g).symm
    _ = ∑ y,p y := Finset.sum_congr rfl (fun y _ => h y)
    _ = 1 := hp

theorem correctedMass_nonnegative (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    0 ≤ correctedMass A C a z K hK f := by
  unfold correctedMass
  exact div_nonneg
    (div_nonneg (DenseWeights.binWeight_pos _ _ _).le (binSum_positive A C a z K hK).le)
    (Nat.cast_nonneg _)

private lemma correctedMass_fiber_sum (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) :
      (∑ f : FreeIndex A.small A.T A.b,
        if integerBin A K hK f=v then correctedMass A C a z K hK f else 0)=
      gridWeight A C a z v/binSum A C a z K := by
    have hc : ((integerFiber A K hK v).card:ℝ)≠0 := by
      exact_mod_cast (Finset.card_pos.mpr (integerFiber_nonempty A K hK hW v)).ne'
    have hZ := (binSum_positive A C a z K hK).ne'
    calc
      _ = ∑ f : FreeIndex A.small A.T A.b, if integerBin A K hK f=v then
          gridWeight A C a z v/binSum A C a z K/(integerFiber A K hK v).card else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf : integerBin A K hK f=v
        · simp only [correctedMass,hf,ite_true]
        · simp only [hf,ite_false]
      _ = ∑ f∈integerFiber A K hK v,
          gridWeight A C a z v/binSum A C a z K/(integerFiber A K hK v).card := by
        simp only [integerFiber,Finset.sum_filter]
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        field_simp [hc,hZ]

/-- Choosing a stationary bin and then an exactly uniform integer point
in that bin defines a probability law on the actual free assignments. -/
theorem correctedMass_total (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) :
    (∑ f : FreeIndex A.small A.T A.b,correctedMass A C a z K hK f)=1 := by
  apply total_of_bin_sums (integerBin A K hK) (correctedMass A C a z K hK)
    (fun v => gridWeight A C a z v/binSum A C a z K)
    (correctedMass_fiber_sum A C a z K hK hW)
  rw [←Finset.sum_div]
  exact div_self (binSum_positive A C a z K hK).ne'

lemma integerPoint_distance (A : Instance I J) (C : ℝ) (K : ℕ) (hK : 0 < K)
    (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    ∀ i,|integerPoint A C f i-realCorner (integerBin A K hK f) i| ≤ 1 := by
  intro i
  let t := index A i
  let N := freeRange A t
  let x := (f t).val
  have hq : (0:ℚ) ≤ (K:ℚ)*x/N := by positivity
  have hlo : (FairBits.scale K N x:ℚ) ≤ (K:ℚ)*x/N := Nat.floor_le hq
  have hhi : (K:ℚ)*x/N < (FairBits.scale K N x:ℚ)+1 := Nat.lt_floor_add_one _
  have hloR : (FairBits.scale K N x:ℝ) ≤ (K:ℝ)*x/N := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div] using (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR : (K:ℝ)*x/N < (FairBits.scale K N x:ℝ)+1 := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr hhi
  have hN : (N:ℝ)=(A.b t.val.1 t.val.2:ℝ)+1 := by simp [N,freeRange]
  change |binWidth A C*(f t).val/((A.b t.val.1 t.val.2:ℝ)+1)-
    (FairBits.scale K N (f t).val:ℝ)| ≤ 1
  rw [←hB,←hN]
  change |(K:ℝ)*x/N-(FairBits.scale K N x:ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The correction variable is uniformly bounded, independently of the
success event and of the number of integers in a bin. -/
theorem correction_bounds (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (f : FreeIndex A.small A.T A.b) :
    1/8 ≤ correction A C a z K hK f ∧ correction A C a z K hK f ≤ 4 := by
  let v := integerBin A K hK f
  have hpQ := actual_population_bounds A K hK hW v
  have hp : (1/2:ℝ) ≤ (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ≤ 2 := by
    constructor
    · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.2
  have hdist : ∀ i,|realCorner v i-integerPoint A C f i| ≤ 1 := by
    intro i
    simpa only [abs_sub_comm] using integerPoint_distance A C K hK hB f i
  have hb := bin_comparison A C a hC ha haH z (realCorner v) (integerPoint A C f) hdist
  have hw : 0 < gridWeight A C a z v := DenseWeights.binWeight_pos _ _ _
  have hr : (1/4:ℝ) ≤ rho A C a z (integerPoint A C f)/gridWeight A C a z v ∧
      rho A C a z (integerPoint A C f)/gridWeight A C a z v ≤ 2 := by
    constructor
    · apply (le_div_iff₀ hw).mpr
      simpa only [gridWeight,div_eq_mul_inv,mul_comm,one_mul] using hb.1
    · exact (div_le_iff₀ hw).mpr (by simpa only [gridWeight] using hb.2)
  have he : correction A C a z K hK f=
      ((K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)*
        (rho A C a z (integerPoint A C f)/gridWeight A C a z v) := by
    unfold correction
    ring
  rw [he]
  constructor
  · have hh := mul_le_mul hp.1 hr.1 (by norm_num : (0:ℝ) ≤ 1/4) (by linarith :
        0 ≤ (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)
    norm_num at hh ⊢
    exact hh
  · have hh := mul_le_mul hp.2 hr.2 (by linarith [hr.1] :
        0 ≤ rho A C a z (integerPoint A C f)/gridWeight A C a z v)
      (by norm_num : (0:ℝ) ≤ 2)
    norm_num at hh ⊢
    exact hh

end

end ContingencyTables.CompanionOracleDensity

end OAI
