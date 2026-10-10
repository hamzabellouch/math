import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlagReplacement

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open scoped BigOperators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open PolynomialFlagReplacementFinite MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def leftRows (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x : PairKey h k → ZMod b) : Fiber h k r → ZMod b :=
  fun i => eval₂ (Int.castRingHom _) x (leftFlag h k hs ks i.val)

def rightRows (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x : PairKey h k → ZMod b) : Fiber h k r → ZMod b :=
  fun i => eval₂ (Int.castRingHom _) x (rightFlag h k hs ks i.val)

def unitKernel (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) : ℝ := by
  classical
  exact if (∀ i j : Fiber h k r, minorFlag h k hs ks i.val j.val=0) ∧
      (∃ i : Fiber h k r, leftFlag h k hs ks i.val≠0 ∧ rightFlag h k hs ks i.val≠0)
    then (((b-1:ℕ):ℝ))⁻¹ else 0

def mixedKernel (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) : ℝ := by
  classical
  exact if (∀ i j : Fiber h k r, minorFlag h k hs ks i.val j.val=0) ∧
      (∃ i : Fiber h k r, leftFlag h k hs ks i.val≠0)
    then (b:ℝ)⁻¹ else 0

@[simp] theorem unitKernel_old_prime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k) :
    unitKernel h k hs ks r (prime h k r)=HistoryPairPolynomialKernel.unitKernel h k hs ks r := rfl

@[simp] theorem mixedKernel_old_prime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k) :
    mixedKernel h k hs ks r (prime h k r)=HistoryPairPolynomialKernel.mixedKernel h k hs ks r := rfl

def NoAccidentalFlags (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x : PairKey h k → ZMod b) : Prop :=
  ∀ j : Index h k r, eval₂ (Int.castRingHom _) x (polynomial h k hs ks r j)=0 ↔
    polynomial h k hs ks r j=0

theorem minors_zero_iff (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) [Fact b.Prime] (x : PairKey h k → ZMod b) :
    PrimeLineFamilies.AllMinorsZero (leftRows h k hs ks r b x) (rightRows h k hs ks r b x) ↔
      ∀ i j : Fiber h k r, eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val)=0 := by
  simp only [PrimeLineFamilies.AllMinorsZero,PrimeLineFamilies.minor,leftRows,rightRows,
    minorFlag,ClearedCoefficientFlags.minor,eval₂_sub,eval₂_mul,leftFlag,rightFlag]

theorem probability_eq_unitKernel (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) [Fact b.Prime]
    (x : PairKey h k → ZMod b) (hx : NoAccidentalFlags h k hs ks r b x) :
    PrimeLineFamilies.probability b (leftRows h k hs ks r b x) (rightRows h k hs ks r b x) =
      unitKernel h k hs ks r b := by
  classical
  have hl i := hx (.inl (i,false))
  have hr i := hx (.inl (i,true))
  have hm i j := hx (.inr (i,j))
  simp only [polynomial] at hl hr hm
  rw [PrimeLineFamilies.probability_eq_flags,minors_zero_iff]
  simp only [PrimeLineFamilies.AllZero,leftRows,rightRows,ne_eq,hl,hr,hm,
    HistoryPairPolynomialKernel.polynomial_family_nonzero h k hs ks hroot r,ite_false,unitKernel]

theorem probability_eq_mixedKernel (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) [Fact b.Prime]
    (x : PairKey h k → ZMod b) (hx : NoAccidentalFlags h k hs ks r b x) :
    PrimeMixedLineFamilies.probability b (leftRows h k hs ks r b x) (rightRows h k hs ks r b x) =
      mixedKernel h k hs ks r b := by
  classical
  have hl i := hx (.inl (i,false))
  have hr i := hx (.inl (i,true))
  have hm i j := hx (.inr (i,j))
  simp only [polynomial] at hl hr hm
  have hm' : PrimeMixedLineFamilies.AllMinorsZero
      (leftRows h k hs ks r b x) (rightRows h k hs ks r b x) ↔
      ∀ i j : Fiber h k r, eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val)=0 :=
    minors_zero_iff h k hs ks r b x
  rw [PrimeMixedLineFamilies.probability_eq_flags,hm']
  simp only [PrimeMixedLineFamilies.AllZero,leftRows,rightRows,ne_eq,hl,hr,hm,
    HistoryPairPolynomialKernel.polynomial_family_nonzero h k hs ks hroot r,ite_false,mixedKernel]

theorem unit_probability_bounds {ι : Type*} (b : ℕ) [Fact b.Prime] (a c : ι → ZMod b) :
    0 ≤ PrimeLineFamilies.probability b a c ∧ PrimeLineFamilies.probability b a c ≤ 1 := by
  classical
  have hh : (((b-1:ℕ):ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ b-1 by have := (Fact.out : b.Prime).two_le; omega))
  rw [PrimeLineFamilies.probability_eq_flags]
  split_ifs <;> constructor <;> first | exact hh | norm_num

theorem mixed_probability_bounds {ι : Type*} (b : ℕ) [Fact b.Prime] (a c : ι → ZMod b) :
    0 ≤ PrimeMixedLineFamilies.probability b a c ∧ PrimeMixedLineFamilies.probability b a c ≤ 1 := by
  classical
  have hh : (b:ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : b.Prime).one_lt.le)
  rw [PrimeMixedLineFamilies.probability_eq_flags]
  split_ifs <;> constructor <;> first | exact hh | norm_num

theorem unitKernel_bounds (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) :
    0 ≤ unitKernel h k hs ks r b ∧ unitKernel h k hs ks r b ≤ 1 := by
  have hh : (((b-1:ℕ):ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ b-1 by have := hb.two_le; omega))
  unfold unitKernel
  split_ifs <;> constructor <;> first | exact hh | norm_num

theorem mixedKernel_bounds (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) :
    0 ≤ mixedKernel h k hs ks r b ∧ mixedKernel h k hs ks r b ≤ 1 := by
  have hh : (b:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hb.one_lt.le)
  unfold mixedKernel
  split_ifs <;> constructor <;> first | exact hh | norm_num

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
