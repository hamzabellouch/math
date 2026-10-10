import Mathlib
import OAI.NumberTheory.PrimePackets.OrbitProbability

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
namespace PrimeDegreePackets

 

lemma prime_dvd_card_padic_module (p : ℕ) [hp : Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module (PadicInt p) A] [Finite A] [Nontrivial A] :
    p ∣ Nat.card A := by
  by_contra h
  have hu : IsUnit (Nat.card A : PadicInt p) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.out.coprime_iff_not_dvd.mpr h
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  apply hx
  apply hu.smul_left_cancel.mp
  simpa only [smul_zero, Nat.cast_smul_eq_nsmul] using card_nsmul_eq_zero' (x := x)

lemma prime_le_cardQuot (p : ℕ) [Fact p.Prime]
    {A : Type*} [AddCommGroup A] [Module (PadicInt p) A]
    (L : Submodule (PadicInt p) A) [Finite (A ⧸ L)] (hL : L ≠ ⊤) :
    p ≤ L.cardQuot := by
  have : Nontrivial (A ⧸ L) := Submodule.Quotient.nontrivial_iff.mpr hL
  rw [Submodule.cardQuot_apply]
  exact Nat.le_of_dvd Nat.card_pos (prime_dvd_card_padic_module p (A ⧸ L))

end PrimeDegreePackets


namespace PrimeDegreePackets
universe v

lemma ennreal_tsum_fintype_prod {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞),
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f
    simp
  · intro α _ ih κ f
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

 

lemma local_weight_product_factorization {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (P d : ∀ i, κ i → ℝ≥0∞) (s : ℝ) :
    (∑' k : ∀ i, κ i, (∏ i, P i (k i)) * (∏ i, (d i (k i)) ^ s)) =
      ∏ i, ∑' k : κ i, P i k * d i k ^ s := by
  simp_rw [← Finset.prod_mul_distrib]
  exact ennreal_tsum_fintype_prod κ (fun i x => P i x * d i x ^ s)

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set
open scoped Pointwise

lemma unit_contains_probability {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace G] [MeasurableInv G] (ν : Measure G) [ν.IsInvInvariant]
    (L : Set X) (x : X) :
    ν {u : G | x ∈ u • L} = ν {u : G | u • x ∈ L} := by
  have hset : {u : G | x ∈ u • L} = ({u : G | u • x ∈ L})⁻¹ := by
    ext u
    simp only [mem_ofPred_eq, mem_smul_set_iff_inv_smul_mem, Set.mem_inv]
  rw [hset, ← Measure.inv_apply, Measure.inv_eq_self]

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 
def localProductConstant (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (localMajorant_product_le n ε hε).choose

lemma localProductConstant_pos (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < localProductConstant n ε hε :=
  (localMajorant_product_le n ε hε).choose_spec.1

lemma localProductConstant_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (S : Finset ℕ) (q : ℝ) (hS : ∀ p ∈ S, 1 ≤ p)
    (hq : (∏ p ∈ S, (p : ℝ)) ≤ q) :
    (∏ p ∈ S, localMajorant n p) ≤ localProductConstant n ε hε * q ^ ε :=
  (localMajorant_product_le n ε hε).choose_spec.2 S q hS hq

section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

def localIndexProduct : ℕ := ∏ p, (L p).cardQuot

def packetLocalWeight (k : ∀ p, ι p → ℕ) : ℝ≥0∞ :=
  ∏ p, localShellProbability (R p) (ν p) (L p) (k p)

def packetLocalNorm (k : ∀ p, ι p → ℕ) : ℝ≥0∞ :=
  ∏ p, shellNorm (R p) (k p)

include μ in
 
theorem global_local_weight_sum
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i))) :
    (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k /
      packetLocalNorm S ι R k) =
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ * ∏ p, (localZinv (R p))⁻¹ := by
  have hfactor := local_weight_product_factorization (fun p : S => ι p → ℕ)
    (fun p k => localShellProbability (R p) (ν p) (L p) k)
    (fun p k => shellNorm (R p) k) (-1)
  have hid : (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k /
      packetLocalNorm S ι R k) =
      ∏ p, ∑' k : ι p → ℕ, localShellProbability (R p) (ν p) (L p) k /
        shellNorm (R p) k := by
    unfold packetLocalWeight packetLocalNorm
    simp only [div_eq_mul_inv, ← ENNReal.rpow_neg_one]
    simpa only [ENNReal.prod_rpow_of_ne_top (fun p _ => shellNorm_ne_top (R p) _) (-1)] using hfactor
  rw [hid]
  simp_rw [local_weight_sum _ (μ _) (ν _) _ _ (hL _), div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [localIndexProduct, Nat.cast_prod]
  exact (ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))).symm

include μ in
 

theorem global_local_weight_moment
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i)))
    (hproper : ∀ p, L p ≠ ⊤)
    (hsat : ∀ p, Ideal.span (L p : Set (∀ i, R p i)) = ⊤)
    (e f : ∀ p, ι p → ℕ) (he0 : ∀ p i, 0 < e p i) (hf0 : ∀ p i, 0 < f p i)
    (he : ∀ p i, addVal (R p i) (algebraMap (PadicInt p.val) (R p i) p.val) = e p i)
    (hcard : ∀ p i, Nat.card (IsLocalRing.ResidueField (R p i)) = p.val ^ f p i)
    (hdegree : ∀ p, ∑ i, f p i * e p i = n) :
    (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k *
      packetLocalNorm S ι R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (localIndexProduct S ι R L : ℝ) ^ ε) := by
  have hnum (p : S) : Fintype.card (ι p) ≤ n := by
    rw [← hdegree p, ← Finset.card_univ]
    calc
      _ = ∑ _i : ι p, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.mul_pos (hf0 p i) (he0 p i))
  have hpq (p : S) : p.val ≤ (L p).cardQuot := prime_le_cardQuot p.val (L p) (hproper p)
  have hprod : (∏ p ∈ S, (p : ℝ)) ≤ (localIndexProduct S ι R L : ℝ) := by
    rw [← Finset.prod_coe_sort S, localIndexProduct, Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun p _ => by exact_mod_cast hpq p)
  have hmajor := localProductConstant_bound n ε hε S (localIndexProduct S ι R L : ℝ)
    (fun p hp => (show Fact p.Prime from inferInstanceAs (Fact (⟨p, hp⟩ : S).val.Prime)).out.one_le)
    hprod
  have hfactor := local_weight_product_factorization (fun p : S => ι p → ℕ)
    (fun p k => localShellProbability (R p) (ν p) (L p) k)
    (fun p k => shellNorm (R p) k) (1 / (2 * (n : ℝ)) - 1)
  unfold packetLocalWeight packetLocalNorm
  have hid : (∑' k : ∀ p, ι p → ℕ,
      (∏ p, localShellProbability (R p) (ν p) (L p) (k p)) *
        (∏ p, shellNorm (R p) (k p)) ^ (1 / (2 * (n : ℝ)) - 1)) =
      ∏ p, ∑' k : ι p → ℕ, localShellProbability (R p) (ν p) (L p) k *
        shellNorm (R p) k ^ (1 / (2 * (n : ℝ)) - 1) := by
    simpa only [ENNReal.prod_rpow_of_ne_top (fun p _ => shellNorm_ne_top (R p) _) _] using hfactor
  rw [hid]
  calc
    _ ≤ ∏ p : S, ((L p).cardQuot : ℝ≥0∞)⁻¹ * ENNReal.ofReal (localMajorant n p.val) := by
      apply Finset.prod_le_prod
      intro p _
      apply (local_weight_moment (R p) (μ p) (ν p) p.val (L p) (hL p) (hsat p)
        (e p) (f p) (he0 p) (hf0 p) (he p) (hcard p) n hn (hdegree p)).trans
      apply mul_le_mul_right
      exact localEulerFactor_le_majorant (R p) p.val n (Fact.out : p.val.Prime).one_lt
        (f p) (hf0 p) (hcard p) (hnum p)
    _ = (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∏ p ∈ S, localMajorant n p) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      · rw [localIndexProduct, Nat.cast_prod]
        exact (ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))).symm
      · rw [← Finset.prod_coe_sort S]
        exact (ENNReal.ofReal_prod_of_nonneg (fun p _ =>
          localMajorant_nonneg n p.val (Fact.out : p.val.Prime).one_le)).symm
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal hmajor) _

end
end PrimeDegreePackets


namespace PrimeDegreePackets

 

lemma reciprocal_norm_tail_le {α : Type*} (w d : α → ℝ≥0∞)
    (hd0 : ∀ i, d i ≠ 0) (hdt : ∀ i, d i ≠ ∞)
    (T : ℝ≥0∞) (s : ℝ) (hs : 0 ≤ s) :
    (∑' i, if T < d i then w i / d i else 0) ≤
      T ^ (-s) * ∑' i, w i * d i ^ (s - 1) := by
  classical
  calc
    _ ≤ ∑' i, T ^ (-s) * (w i * d i ^ (s - 1)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      split_ifs with h
      · have hp : d i ^ (-s) ≤ T ^ (-s) := by
          simp only [ENNReal.rpow_neg, ENNReal.inv_le_inv]
          exact ENNReal.rpow_le_rpow h.le hs
        calc
          w i / d i = d i ^ (-s) * (w i * d i ^ (s - 1)) := by
            rw [mul_left_comm, ← ENNReal.rpow_add _ _ (hd0 i) (hdt i)]
            simp [show -s + (s - 1) = -1 by ring, ENNReal.rpow_neg_one, div_eq_mul_inv]
          _ ≤ _ := mul_le_mul_left hp _
      · exact bot_le
    _ = _ := ENNReal.tsum_mul_left

 

lemma reciprocal_norm_tail_of_moment {α : Type*} (w d : α → ℝ≥0∞)
    (hd0 : ∀ i, d i ≠ 0) (hdt : ∀ i, d i ≠ ∞)
    (q Q C : ℝ≥0∞) (hQ0 : Q ≠ 0) (hQt : Q ≠ ∞) (hqQ : q ≤ Q)
    (s : ℝ) (hs : 0 < s)
    (hm : (∑' i, w i * d i ^ (s - 1)) ≤ q⁻¹ * C * q ^ (s / 16)) :
    (∑' i, if Q ^ (1 / 8 : ℝ) < d i then w i / d i else 0) ≤
      q⁻¹ * C * Q ^ (-s / 16) := by
  classical
  calc
    _ ≤ (Q ^ (1 / 8 : ℝ)) ^ (-s) * ∑' i, w i * d i ^ (s - 1) :=
      reciprocal_norm_tail_le w d hd0 hdt _ s hs.le
    _ ≤ (Q ^ (1 / 8 : ℝ)) ^ (-s) * (q⁻¹ * C * q ^ (s / 16)) :=
      mul_le_mul_right hm _
    _ ≤ (Q ^ (1 / 8 : ℝ)) ^ (-s) * (q⁻¹ * C * Q ^ (s / 16)) := by
      exact mul_le_mul_right (mul_le_mul_right (ENNReal.rpow_le_rpow hqQ (by positivity)) _) _
    _ = q⁻¹ * C * Q ^ (-s / 16) := by
      rw [← ENNReal.rpow_mul, mul_left_comm,
        ← ENNReal.rpow_add _ _ hQ0 hQt]
      congr 2
      ring

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

omit [∀ p : S, Fact p.val.Prime] [∀ p i, Algebra (PadicInt p.val) (R p i)]
  [∀ p i, BorelSpace (R p i)] [∀ p i, SecondCountableTopology (R p i)]
  [∀ p, BorelSpace (∀ i, R p i)ˣ]
  [∀ p i, MeasurableSpace (R p i)] [∀ p, MeasurableSpace (∀ i, R p i)ˣ] in
lemma packetLocalNorm_ne_zero (k : ∀ p, ι p → ℕ) : packetLocalNorm S ι R k ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => shellNorm_ne_zero (R p) (k p))

omit [∀ p : S, Fact p.val.Prime] [∀ p i, Algebra (PadicInt p.val) (R p i)]
  [∀ p i, IsTopologicalRing (R p i)] [∀ p i, CompactSpace (R p i)]
  [∀ p i, T2Space (R p i)] [∀ p i, BorelSpace (R p i)]
  [∀ p i, SecondCountableTopology (R p i)] [∀ p, BorelSpace (∀ i, R p i)ˣ]
  [∀ p i, TopologicalSpace (R p i)] [∀ p i, MeasurableSpace (R p i)]
  [∀ p, MeasurableSpace (∀ i, R p i)ˣ] in
lemma packetLocalNorm_ne_top (k : ∀ p, ι p → ℕ) : packetLocalNorm S ι R k ≠ ∞ := by
  exact ENNReal.prod_ne_top (fun p _ => shellNorm_ne_top (R p) (k p))

include μ in
 

theorem global_local_weight_tail
    (hn : 0 < n)
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i)))
    (hproper : ∀ p, L p ≠ ⊤)
    (hsat : ∀ p, Ideal.span (L p : Set (∀ i, R p i)) = ⊤)
    (e f : ∀ p, ι p → ℕ) (he0 : ∀ p i, 0 < e p i) (hf0 : ∀ p i, 0 < f p i)
    (he : ∀ p i, addVal (R p i) (algebraMap (PadicInt p.val) (R p i) p.val) = e p i)
    (hcard : ∀ p i, Nat.card (IsLocalRing.ResidueField (R p i)) = p.val ^ f p i)
    (hdegree : ∀ p, ∑ i, f p i * e p i = n)
    (Q : ℝ) (hQ : 0 < Q) (hqQ : (localIndexProduct S ι R L : ℝ) ≤ Q) :
    let s : ℝ := 1 / (2 * (n : ℝ))
    let hε : 0 < s / 16 := by dsimp [s]; positivity
    (∑' k : ∀ p, ι p → ℕ, if ENNReal.ofReal Q ^ (1 / 8 : ℝ) < packetLocalNorm S ι R k
      then packetLocalWeight S ι R ν L k / packetLocalNorm S ι R k else 0) ≤
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n (s / 16) hε) *
        ENNReal.ofReal Q ^ (-s / 16) := by
  dsimp only
  let s : ℝ := 1 / (2 * (n : ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have hε : 0 < s / 16 := by positivity
  apply reciprocal_norm_tail_of_moment (packetLocalWeight S ι R ν L)
    (packetLocalNorm S ι R) (packetLocalNorm_ne_zero S ι R)
    (packetLocalNorm_ne_top S ι R) (localIndexProduct S ι R L : ℝ≥0∞)
    (ENNReal.ofReal Q) (ENNReal.ofReal (localProductConstant n (s / 16) hε))
    (by simpa using hQ) ENNReal.ofReal_ne_top
    (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hqQ) s hs
  have H := global_local_weight_moment n S ι R μ ν L hn (s / 16) hε
    hL hproper hsat e f he0 hf0 he hcard hdegree
  convert H using 1
  rw [ENNReal.ofReal_mul (localProductConstant_pos n (s / 16) hε).le,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) hε.le,
    ENNReal.ofReal_natCast]
  exact mul_assoc _ _ _

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory NumberField IsDiscreteValuationRing
open scoped ENNReal Pointwise nonZeroDivisors

 

def modelUnitProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) : Measure Rˣ :=
  (localUnitHaarProbability (K := K) p).map (Units.mapEquiv E.toMulEquiv)

lemma modelUnitProbability_isProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) (hE : Continuous E) :
    IsProbabilityMeasure (modelUnitProbability p E) := by
  apply (Measure.isProbabilityMeasure_map_iff
    (Units.continuous_map hE).measurable.aemeasurable).mpr
  infer_instance

lemma modelUnitProbability_isHaar {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) (hE : Continuous E) :
    (modelUnitProbability p E).IsHaarMeasure := by
  exact Measure.isHaarMeasure_map_of_isFiniteMeasure (localUnitHaarProbability p)
    (Units.mapEquiv E.toMulEquiv).toMonoidHom (Units.continuous_map hE)
    (Units.mapEquiv E.toMulEquiv).surjective

lemma smul_normalized_mem_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (u : completedMaximalOrder (K := K) p) (z : (completedMaximalOrder (K := K) p)ˣ) :
    (u : LocalAlgebra p K) ∈ ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
      normalizedLocalModule M p ↔ z⁻¹ • u ∈ integralNormalizedModule M p := by
  let v : (LocalAlgebra p K)ˣ :=
    Units.map (completedMaximalOrder (K := K) p).val.toMonoidHom z
  change (u : LocalAlgebra p K) ∈ v • (normalizedLocalModule M p : Set (LocalAlgebra p K)) ↔ _
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

 

lemma actual_containment_eq_model_orbit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R)
    (hE : Continuous E) (hEs : Continuous E.symm)
    (u : completedMaximalOrder (K := K) p) :
    localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
      (u : LocalAlgebra p K) ∈ ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
        normalizedLocalModule M p} =
      orbitContainmentProbability (modelUnitProbability p E) (modelLocalModule M p E) (E u) := by
  rw [orbitContainmentProbability_eq_measure _ _ (modelLocalModule_open M hn p E hEs).measurableSet]
  have hm : Measurable (Units.mapEquiv E.toMulEquiv) :=
    (Units.continuous_map (f := E.toMonoidHom) hE).measurable
  have hset : MeasurableSet {z : Rˣ | z • E u ∈ modelLocalModule M p E} :=
    (modelLocalModule_open M hn p E hEs).measurableSet.preimage (measurable_id.smul_const _)
  change _ = (modelUnitProbability p E) {z : Rˣ | z • E u ∈ modelLocalModule M p E}
  unfold modelUnitProbability
  rw [Measure.map_apply hm hset]
  have he : (Units.mapEquiv E.toMulEquiv) ⁻¹' {z : Rˣ | z • E u ∈ modelLocalModule M p E} =
      {z : (completedMaximalOrder (K := K) p)ˣ | z • u ∈ integralNormalizedModule M p} := by
    ext z
    change E (z : completedMaximalOrder (K := K) p) * E u ∈
      (integralNormalizedModule M p).map E.toLinearMap ↔ _
    rw [← map_mul E]
    rw [Submodule.mem_map_equiv]
    change E.symm (E ((z : completedMaximalOrder (K := K) p) * u)) ∈
      integralNormalizedModule M p ↔ _
    rw [E.symm_apply_apply]
    rfl
  rw [he]
  have hi := Measure.measure_preimage_inv (localUnitHaarProbability (K := K) p)
    {z : (completedMaximalOrder (K := K) p)ˣ | z • u ∈ integralNormalizedModule M p}
  rw [← hi]
  congr 1
  ext z
  exact smul_normalized_mem_iff M p u z

lemma integral_idealLocalGenerator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    (idealLocalGenerator p J : LocalAlgebra p K) ∈ completedMaximalOrder (K := K) p := by
  have hle := completedFractionalIdeal_mono p hJ
  apply hle
  rw [idealLocalGenerator_spec]
  simpa using Submodule.smul_mem_pointwise_smul
    (1 : LocalAlgebra p K) (idealLocalGenerator p J : LocalAlgebra p K)
    (completedMaximalOrder (K := K) p).toSubmodule (completedMaximalOrder (K := K) p).one_mem

lemma nonZeroDivisor_component_ne_zero {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Nontrivial (R i)] {x : ∀ i, R i}
    (hx : x ∈ nonZeroDivisors (∀ i, R i)) (i : ι) : x i ≠ 0 := by
  classical
  intro hi
  have hzero : x * Pi.single i 1 = 0 := by
    funext j
    by_cases hij : j = i
    · subst j; simp [hi]
    · simp [Pi.single_eq_of_ne hij]
  have H := congrFun (hx.1 _ hzero) i
  simp at H

lemma model_generator_components_ne_zero {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Nontrivial (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, R i)
    (v : (LocalAlgebra p K)ˣ) (hv : (v : LocalAlgebra p K) ∈ completedMaximalOrder (K := K) p)
    (i : ι) : E ⟨v,hv⟩ i ≠ 0 := by
  have hu : (⟨v,hv⟩ : completedMaximalOrder (K := K) p) ∈
      nonZeroDivisors (completedMaximalOrder (K := K) p) :=
    mem_nonZeroDivisors_of_injective (f := (completedMaximalOrder (K := K) p).val)
      Subtype.val_injective v.isUnit.mem_nonZeroDivisors
  apply nonZeroDivisor_component_ne_zero (i := i)
  rw [← MulEquivClass.map_nonZeroDivisors E]
  exact ⟨⟨v,hv⟩,hu,rfl⟩

 

theorem localIdealWeight_eq_model_shell {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, Algebra (PadicInt p) (R i)] [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)] [∀ i, SecondCountableTopology (R i)] [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, R i)
    (hE : Continuous E) (hEs : Continuous E.symm)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    localIdealWeight M p J = localShellProbability R (modelUnitProbability p E)
      (modelLocalModule M p E)
      (fun i => (addVal (R i) (E ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩ i)).toNat) := by
  let u : completedMaximalOrder (K := K) p :=
    ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩
  let k : ι → ℕ := fun i => (addVal (R i) (E u i)).toNat
  let := modelUnitProbability_isProbability p E hE
  let := modelUnitProbability_isHaar p E hE
  have hxu : E u ∈ productDVRShell R k := by
    intro i
    exact (ENat.natCast_toNat (addVal_eq_top_iff.not.mpr
      (model_generator_components_ne_zero p E _ _ i))).symm
  obtain ⟨z,hz⟩ := productDVRShell_transitive R k
    (productDVRShell_nonempty R k).choose_spec hxu
  change localIdealWeight M p J = orbitContainmentProbability (modelUnitProbability p E)
    (modelLocalModule M p E) (productDVRShell_nonempty R k).choose
  rw [localIdealWeight, actual_containment_eq_model_orbit M hn p E hE hEs u, ← hz]
  exact orbitContainmentProbability_smul (modelUnitProbability p E)
    (modelLocalModule M p E : Set (∀ i, R i)) _ z

end PrimeDegreePackets
end
end

end OAI
