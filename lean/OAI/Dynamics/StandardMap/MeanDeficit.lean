import OAI.Dynamics.StandardMap.DoublingPointwise

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def torusIterMeasurableEquiv (k : ℝ) (a : ℤ) : Torus ≃ᵐ Torus where
  toEquiv := (torusStep k)^a
  measurable_toFun := (continuous_torusIter k a).measurable
  measurable_invFun := by
    have hh := (continuous_torusIter k (-a)).measurable
    simpa only [torusIter,zpow_neg,Equiv.Perm.inv_def] using hh
lemma integral_torusIter (k : ℝ) (a : ℤ) (f : Torus → ℝ) :
    (∫ z, f (torusIter k a z) ∂area)=∫ z, f z ∂area :=
  (measurePreserving_torusIter k a).integral_comp (torusIterMeasurableEquiv k a).measurableEmbedding f
lemma integrable_productDistance (k : ℝ) (hk : 0 ≤ k) (i j : ℤ) :
    Integrable (fun z => productDistance k z i j) area :=
  (continuous_productDistance k hk i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma continuous_wingDefect (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : Continuous (fun z => wingDefect k z n) :=
  continuous_const.sub ((continuous_productDistance k hk 0 (-(n:ℤ))).min (continuous_productDistance k hk 0 (n:ℤ)))
lemma continuous_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : Continuous (fun z => cancellationLoss k z n) :=
  ((continuous_productDistance k hk 0 (-(n:ℤ))).add (continuous_productDistance k hk 0 (n:ℤ))).sub
    (continuous_productDistance k hk (-(n:ℤ)) (n:ℤ))
noncomputable def meanDeficit (k : ℝ) (n : ℕ) : ℝ :=
  1-(∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ)
lemma integral_productDistance_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    0 ≤ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ∧ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ≤ (n:ℝ) := by
  refine ⟨integral_nonneg (fun z => productDistance_nonneg k hk z 0 (n:ℤ)),?_⟩
  have hh := integral_mono (integrable_productDistance k hk 0 (n:ℤ)) (integrable_const (n:ℝ)) (fun z => by simpa using productDistance_le k hk z 0 (n:ℤ))
  simpa only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using hh
lemma meanDeficit_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) : 0 ≤ meanDeficit k n ∧ meanDeficit k n ≤ 1 := by
  obtain ⟨h0,h1⟩ := integral_productDistance_bounds k hk n
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hdiv : (∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ) ≤ 1 := (div_le_one hnp).mpr h1
  have hdiv0 := div_nonneg h0 hnp.le
  unfold meanDeficit; constructor <;> linarith
lemma integral_distance_shift (k : ℝ) (i j a : ℤ) :
    (∫ z,productDistance k z (i+a) (j+a) ∂area)=∫ z,productDistance k z i j ∂area := by
  calc
    _ = ∫ z,productDistance k (torusIter k a z) i j ∂area := by simp only [productDistance_shift]
    _ = _ := by convert! integral_torusIter k a (fun z => productDistance k z i j) using 1
lemma integral_wing_left (k : ℝ) (n : ℕ) :
    (∫ z, productDistance k z 0 (-(n:ℤ)) ∂area)=∫ z, productDistance k z 0 (n:ℤ) ∂area := by
  simp_rw [productDistance_symm k _ 0 (-(n:ℤ))]
  convert integral_distance_shift k 0 (n:ℤ) (-(n:ℤ)) using 1 ; simp
lemma integral_wingDefect_le (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,wingDefect k z n ∂area) ≤ 2*(n:ℝ)*meanDeficit k n := by
  have hbd (z : Torus) : wingDefect k z n ≤ ((n:ℝ)-productDistance k z 0 (-(n:ℤ)))+((n:ℝ)-productDistance k z 0 (n:ℤ)) := by
    have hl := productDistance_le k hk z 0 (-(n:ℤ))
    have hr := productDistance_le k hk z 0 (n:ℤ)
    simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hl hr
    unfold wingDefect
    rcases le_total (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hL := (integrable_const (n:ℝ)).sub (integrable_productDistance k hk 0 (-(n:ℤ)))
  have hR := (integrable_const (n:ℝ)).sub (integrable_productDistance k hk 0 (n:ℤ))
  have hh := integral_mono ((continuous_wingDefect k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hL.add hR) hbd
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  have hsum : (∫ z, ((n:ℝ)-productDistance k z 0 (-(n:ℤ)))+((n:ℝ)-productDistance k z 0 (n:ℤ)) ∂area)=
      (∫ z, ((n:ℝ)-productDistance k z 0 (-(n:ℤ))) ∂area)+(∫ z, ((n:ℝ)-productDistance k z 0 (n:ℤ)) ∂area) := by
    convert! integral_add hL hR using 1
  have hsub (i : ℤ) : (∫ z, ((n:ℝ)-productDistance k z 0 i) ∂area)=(n:ℝ)-(∫ z,productDistance k z 0 i ∂area) := by
    calc
      _ = (∫ _z : Torus, (n:ℝ) ∂area)-(∫ z,productDistance k z 0 i ∂area) := by
        convert! integral_sub (integrable_const (n:ℝ)) (integrable_productDistance k hk 0 i) using 1
      _ = _ := by simp
  rw [hsum,hsub,hsub,integral_wing_left] at hh
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold meanDeficit
  field_simp [hn0] at *
  nlinarith
lemma integral_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,cancellationLoss k z n ∂area)=2*(n:ℝ)*(meanDeficit k (n+n)-meanDeficit k n) := by
  have hL := integrable_productDistance k hk 0 (-(n:ℤ))
  have hR := integrable_productDistance k hk 0 (n:ℤ)
  have hT := integrable_productDistance k hk (-(n:ℤ)) (n:ℤ)
  have ht : (∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area)=∫ z,productDistance k z 0 ((n+n:ℕ):ℤ) ∂area := by
    convert integral_distance_shift k 0 ((n+n:ℕ):ℤ) (-(n:ℤ)) using 1 ; push_cast ; ring_nf
  have hsum : (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ)) ∂area)+(∫ z,productDistance k z 0 (n:ℤ) ∂area) := by
    convert! integral_add hL hR using 1
  have hsub : (∫ z,cancellationLoss k z n ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)-(∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area) := by
    convert! integral_sub (hL.add hR) hT using 1
  rw [hsub,hsum,integral_wing_left,ht]
  unfold meanDeficit
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp [hn0]; ring
lemma meanDeficit_doubling_mono (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n ≤ meanDeficit k (n+n) := by
  have hh : 0 ≤ ∫ z,cancellationLoss k z n ∂area := integral_nonneg fun z => (cancellationLoss_bounds k hk z n).1
  rw [integral_cancellationLoss k hk n hn] at hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  nlinarith
end StandardMapEntropy

end OAI
