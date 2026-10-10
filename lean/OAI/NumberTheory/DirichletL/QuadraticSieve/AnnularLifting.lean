import OAI.NumberTheory.DirichletL.GaussSum.GlobalScales

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel

def squarefreeHighRange (M K : ℝ) : Finset (Ideal O) :=
  (idealRange M).filter (fun I => K<(Ideal.absNorm I:ℝ))

def annularLift (M K : ℝ) (I : squarefreeHighRange M K) : Ideal O :=
  liftedRow M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1.1
    (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).2

theorem annularLift_injective (M K : ℝ) : Function.Injective (annularLift M K) := by
  intro I J h
  have he := congrArg squarefreePart h
  apply Subtype.ext
  simpa only [annularLift,
    liftedRow_squarefreePart M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp (Finset.mem_filter.mp J.property).1).1] using he

theorem annularLift_properties (M K : ℝ) (I : squarefreeHighRange M K) :
    Supported (annularLift M K I) ∧ K<(Ideal.absNorm (squarefreePart (annularLift M K I)):ℝ) ∧
      M<(Ideal.absNorm (annularLift M K I):ℝ) ∧ (Ideal.absNorm (annularLift M K I):ℝ)≤49*M := by
  have hi := mem_idealRange.mp (Finset.mem_filter.mp I.property).1
  have hn := liftedRow_bounds M I.val hi.1.1 hi.2
  refine ⟨liftedRow_supported M I.val hi.1 hi.2,?_,hn⟩
  simpa only [annularLift,liftedRow_squarefreePart M I.val hi.1] using (Finset.mem_filter.mp I.property).2

theorem annularLift_row_sum (M N K : ℝ) (I : squarefreeHighRange M K)
    (a : idealRange N → ℂ)
    (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑J : idealRange N, quadraticRow J.val (primaryGenerator (annularLift M K I))*a J) =
      ∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J := by
  apply Finset.sum_congr rfl
  intro J _
  by_cases hz : a J=0
  · simp only [hz,mul_zero]
  · rw [annularLift,liftedRow_character M I.val
      (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1 _ J.val
      (mem_idealRange.mp J.property).1 (hcop J hz)]

lemma exists_lifted_annular_scale (M x : ℝ) (hM : 0<M) (hx : M<x) (hupper : x≤49*M) :
    ∃j : Fin 7, ((2:ℝ)^j.val*M)/2≤x ∧ x≤(2:ℝ)^j.val*M := by
  have hratio : 1≤x/M := (le_div_iff₀ hM).mpr (by linarith)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hratioU : x/M≤49 := (div_le_iff₀ hM).mpr hupper
  have hk : k<6 := by
    by_contra hn
    have h6 : 6≤k := by omega
    have hp : (2:ℝ)^6≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) h6
    norm_num at hp
    linarith
  refine ⟨⟨k+1,by omega⟩,?_,?_⟩
  · have hl := (le_div_iff₀ hM).mp hlo
    simpa only [pow_succ,mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hl
  · exact ((div_lt_iff₀ hM).mp hhi).le

lemma sum_injective_mask_le {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (hf : Function.Injective f) (S : Finset (Ideal O))
    (v : Ideal O → ℝ) (hv : ∀I, 0≤v I) :
    (∑i, if f i∈S then v (f i) else 0)≤∑I∈S,v I := by
  classical
  rw [←Finset.sum_filter]
  rw [←Finset.sum_image (f := v) (g := f) (by intro i hi j hj he; exact hf he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hi).2
  · intro I hI hnot
    exact hv I

theorem squarefreeHigh_energy_le_annuli (M N K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K a := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hE (I : Ideal O) : 0≤E I := sq_nonneg _
  have hlift :
      (∑I : squarefreeHighRange M K, E I.val) = ∑I : squarefreeHighRange M K, E (annularLift M K I) := by
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [E]
    rw [annularLift_row_sum M N K I a hcop]
  change (∑I : squarefreeHighRange M K, E I.val)≤_
  rw [hlift]
  have hpoint (I : squarefreeHighRange M K) : E (annularLift M K I) ≤
      ∑j : Fin 7, if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := by
    have hp := annularLift_properties M K I
    obtain ⟨j,hjlo,hjhi⟩ := exists_lifted_annular_scale M _ hM hp.2.2.1 hp.2.2.2
    have hMj : 0<(2:ℝ)^j.val*M := by positivity
    have hm : annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K :=
      mem_highKernelRange.mpr ⟨hp.1,by linarith,hp.2.1⟩
    have hw : annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)=1 := by
      apply QuadraticInitialBound.annularSieveBump_eq_one
      · exact (le_div_iff₀ hMj).mpr (by linarith)
      · exact (div_le_one hMj).mpr hjhi
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0)
      (fun j _ => by split_ifs; exact mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE _); exact le_rfl)
      (Finset.mem_univ j)
    simpa only [hm,ite_true,hw,one_mul] using hh
  calc
    _ ≤ ∑I : squarefreeHighRange M K, ∑j : Fin 7,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑j : Fin 7, ∑I : squarefreeHighRange M K,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [annularHighEnergy,Finset.sum_coe_sort (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)]
      exact sum_injective_mask_le (annularLift M K) (annularLift_injective M K)
        (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)
        (fun I => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE I))

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction

def liftingDivisibleColumns (N : ℝ) : Finset (idealRange N) :=
  Finset.univ.filter (fun J => liftingPrime∣J.val)

def liftingQuotientColumn (N : ℝ) (J : liftingDivisibleColumns N) : idealRange N :=
  ⟨idealQuotient liftingPrime J.val.val, by
    have hd := (Finset.mem_filter.mp J.property).2
    have hj := mem_idealRange.mp J.val.property
    refine mem_idealRange.mpr ⟨admissible_idealQuotient hj.1 hd,?_⟩
    have hn := idealQuotient_norm_le liftingPrime_prime.ne_zero hd N hj.2
    rw [liftingPrime_norm] at hn
    have hN : 0≤N := (Nat.cast_nonneg _).trans hj.2
    exact hn.trans (by norm_num; linarith)⟩

theorem liftingQuotientColumn_injective (N : ℝ) : Function.Injective (liftingQuotientColumn N) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact idealQuotient_injective_on liftingPrime
    (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2 (congrArg Subtype.val h)

def liftingFreeCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  fun J => if liftingPrime∣J.val then 0 else a J

def liftingDividedCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  extendByZero Finset.univ (liftingQuotientColumn N) (fun J : liftingDivisibleColumns N => a J.val)

theorem liftingFreeCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingFreeCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  apply ideals_coprime_of_relprime
  apply liftingPrime_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hJ (by simp only [liftingFreeCoefficient,hd,ite_true])

theorem liftingDividedCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingDividedCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  classical
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have hdiv := (Finset.mem_filter.mp I.property).2
  have hsf : Squarefree (liftingPrime*idealQuotient liftingPrime I.val.val) := by
    rw [idealQuotient_mul hdiv]
    exact (mem_idealRange.mp I.val.property).1.2.1
  exact ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hsf).1

theorem liftingDividedCoefficient_row_sum (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) =
      ∑J : liftingDivisibleColumns N, quadraticRow (idealQuotient liftingPrime J.val.val) z*a J.val := by
  simpa only [liftingDividedCoefficient,liftingQuotientColumn] using
    extendByZero_matrix Finset.univ (liftingQuotientColumn N)
      (fun J : liftingDivisibleColumns N => a J.val) (fun (_ : Unit) J => quadraticRow J.val z) ()

theorem liftingCoefficient_row_split (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*a J) =
      (∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J) +
      quadraticRow liftingPrime z*(∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) := by
  rw [liftingDividedCoefficient_row_sum,Finset.mul_sum,
    Finset.sum_coe_sort (liftingDivisibleColumns N)
      (fun J => quadraticRow liftingPrime z*(quadraticRow (idealQuotient liftingPrime J.val) z*a J))]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val
  · simp only [hd,ite_true,liftingFreeCoefficient,mul_zero,zero_add]
    rw [quadraticRow_divisor_factor J.val liftingPrime (mem_idealRange.mp J.property).1 hd z]
    ring
  · simp only [hd,ite_false,liftingFreeCoefficient,add_zero]

theorem liftingCoefficient_energy (N : ℝ) (a : idealRange N → ℂ) :
    (∑J : idealRange N, ‖liftingFreeCoefficient N a J‖^2) +
      (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2) = ∑J, ‖a J‖^2 := by
  have he := extendByZero_energy Finset.univ (liftingQuotientColumn N)
    (fun J : liftingDivisibleColumns N => a J.val) (liftingQuotientColumn_injective N).injOn
  change (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2)=
    ∑J : liftingDivisibleColumns N, ‖a J.val‖^2 at he
  rw [he,Finset.sum_coe_sort (liftingDivisibleColumns N) (fun J => ‖a J‖^2)]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val <;>
    simp only [liftingFreeCoefficient,hd,ite_true,ite_false,norm_zero,zero_pow (by decide : 2≠0),zero_add,add_zero]

theorem liftingCoefficient_row_energy (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    ‖∑J : idealRange N, quadraticRow J.val z*a J‖^2 ≤
      2*(‖∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J‖^2 +
        ‖∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J‖^2) := by
  rw [liftingCoefficient_row_split]
  let u := ∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J
  let v := ∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J
  change ‖u+quadraticRow liftingPrime z*v‖^2≤2*(‖u‖^2+‖v‖^2)
  have hp : ‖quadraticRow liftingPrime z*v‖≤‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hn : ‖u+quadraticRow liftingPrime z*v‖≤‖u‖+‖v‖ := by
    linarith [norm_add_le u (quadraticRow liftingPrime z*v)]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem liftingFreeCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N X (liftingFreeCoefficient N a) := by
  intro J hJ
  have hj : a J≠0 := by
    intro hz
    exact hJ (by simp only [liftingFreeCoefficient,hz,ite_self])
  exact ha J hj

theorem liftingDividedCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N (X/7) (liftingDividedCoefficient N a) := by
  classical
  intro J hJ
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have he : liftingDividedCoefficient N a (liftingQuotientColumn N I)=a I.val :=
    extendByZero_apply_image _ _ _ (liftingQuotientColumn_injective N).injOn I (Finset.mem_univ I)
  have hn : a I.val≠0 := by rwa [he] at hJ
  have hs := ha I.val hn
  change (X/7)/2<(Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ) ∧
    (Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ)≤X/7
  rw [idealQuotient_norm_eq liftingPrime I.val.val liftingPrime_prime.ne_zero
    (Finset.mem_filter.mp I.property).2,liftingPrime_norm]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

theorem coefficientOnShell_zero_or_scale (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : (∀J, a J=0) ∨ 1≤X := by
  classical
  by_cases h : ∀J, a J=0
  · exact Or.inl h
  · push Not at h
    obtain ⟨J,hJ⟩ := h
    have hnorm : 1≤(Ideal.absNorm J.val:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => (mem_idealRange.mp J.property).1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact Or.inr (hnorm.trans (ha J hJ).2)

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator

def ballQuadraticEnergy (M N : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑I : idealRange M, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2

theorem ballQuadraticEnergy_low_high (M N K : ℝ) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      ∑I : squarefreeHighRange M K, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2 := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hs : (idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K) ⊆ idealRange K := by
    intro I hI
    exact mem_idealRange.mpr ⟨(mem_idealRange.mp (Finset.mem_filter.mp hI).1).1,(Finset.mem_filter.mp hI).2⟩
  have hlo : (∑I∈(idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K), E I) ≤
      sieveNorm K N*(∑J, ‖a J‖^2) := by
    calc
      _ ≤ ∑I∈idealRange K,E I := Finset.sum_le_sum_of_subset_of_nonneg hs (fun I hI hnot => sq_nonneg _)
      _ = ballQuadraticEnergy K N a := (Finset.sum_coe_sort (idealRange K) E).symm
      _ ≤ _ := FiniteSieveOperator.energy_bound (matrix K N) a
  change (∑I : idealRange M,E I.val)≤_+(∑I : squarefreeHighRange M K,E I.val)
  rw [Finset.sum_coe_sort (idealRange M) E,
    ←Finset.sum_filter_add_sum_filter_not (idealRange M) (fun I => (Ideal.absNorm I:ℝ)≤K) E]
  rw [Finset.sum_coe_sort (squarefreeHighRange M K) E]
  simp only [not_le,squarefreeHighRange]
  linarith

theorem ballQuadraticEnergy_lifted_annuli (M N K : ℝ) (hM : 0<M) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryGenerator I.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith

end

open ActualEisensteinCubic CompletedGauss

theorem ballQuadraticEnergy_mono {M M' N : ℝ} (hM : M≤M') (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a≤ballQuadraticEnergy M' N a := by
  unfold ballQuadraticEnergy
  rw [Finset.sum_coe_sort (idealRange M)
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2),
    Finset.sum_coe_sort (idealRange M')
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (idealRange_mono hM) (fun I hI hnot => sq_nonneg _)

theorem ballQuadraticEnergy_coefficientAtScale (M N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀J, a J≠0 → (Ideal.absNorm J.val:ℝ)≤X) :
    ballQuadraticEnergy M N a=ballQuadraticEnergy M X (coefficientAtScale N X a) := by
  unfold ballQuadraticEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem ballQuadraticEnergy_column_shells (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M N (dyadicColumnCoefficient N lengthScale hNL j a) := by
  simpa only [one_mul,ballQuadraticEnergy] using
    weighted_energy_column_shells N lengthScale hNL
      (fun I : idealRange M => fun J : idealRange N => quadraticRow J.val (primaryGenerator I.val))
      (fun _ => (1:ℝ)) (fun _ => by norm_num) a

theorem ballQuadraticEnergy_column_shells_at_scale (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M ((2:ℝ)^j.val)
        (coefficientAtScale N ((2:ℝ)^j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (ballQuadraticEnergy_column_shells M N lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact ballQuadraticEnergy_coefficientAtScale M N _ _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

theorem columnDyadicLength_scale_upper (N : ℝ) (hN : 1≤N) :
    (2:ℝ)^columnDyadicLength N≤2*N := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0≤Real.log N/Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  calc
    _ = (2:ℝ)^((columnDyadicLength N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ)^(Real.log N/Real.log 2+1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2*N := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      have he : (2:ℝ)^(Real.log N/Real.log 2)=N :=
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [he,mul_comm]

theorem columnDyadicScale_bounds (N : ℝ) (hN : 1≤N) (j : Fin (columnDyadicLength N+1)) :
    1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤2*N := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  exact (pow_le_pow_right₀ (by norm_num) (by omega : j.val≤columnDyadicLength N)).trans
    (columnDyadicLength_scale_upper N hN)

end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem gcdPool_admissible {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀j, Admissible (cols j)) (D : Ideal O) (hD : D∈gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact admissible_of_dvd (hcols j) (GCDMonoid.gcd_dvd_left _ _)

theorem annularHighEnergy_gcd_reduction (M N K H : ℝ) (hN : 1≤N) (hH : 0<H)
    (ε : ℝ) (hε : 0<ε) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ 16*((∑c : EisensteinEPrimaryPhase.Coord,
      ∑D∈(gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H),
        ‖annularRayGcdBlock M N K D c a‖) +
      highKernelNorm (2*M) (N/H) K*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε H hH
    (fun I : highKernelRange (2*M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2*M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.annularSieveBump.nonneg,QuadraticInitialBound.annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy,annularRayGcdBlock,one_mul] using h

theorem HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_gcd_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  classical
  let S := (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H)
  have hb (D : Ideal O) (hD : D∈S) (c : EisensteinEPrimaryPhase.Coord) :
      ‖annularRayGcdBlock M N K D c a‖ ≤
        (C/6)*∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D hadm.1 (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0≤∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 by positivity)
    change _ ≤ C*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hbound
    have hn : ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖=6*‖annularRayGcdBlock M N K D c a‖ := by
      rw [norm_mul]
      norm_num
    rw [hn] at hh
    change _≤_*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hh
    nlinarith
  have hs := gcdRaySupport_weighted_sum_bound ε hε S (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) a N (C/6) (by positivity)
    (fun J hJ => (mem_idealRange.mp J.property).2)
    (fun D c => ‖annularRayGcdBlock M N K D c a‖) hb
  have hNH : 1≤N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_gcd_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hsupp := (supportConstant_pos ε hε).le
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/6)*(divisorConstant ε hε*N^ε)*∑J,‖a J‖^2 +
      (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
        (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
      gcongr
    _ = _ := by ring

end

section

def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q^2/(r/q)^η

theorem cutoffRescaleCoefficient_eq (C η r q : ℝ) (hr : 0<r) (hq : 0<q) :
    cutoffRescaleCoefficient C η r q=C*r^(1-η)*q^(2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r^η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q^η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp

theorem cutoffRescaleCoefficient_bounds (C η r q : ℝ)
    (hC : 0≤C) (hη : 0≤η) (hη1 : η≤1) (hr : 1≤r) (hr64 : r≤64) (hq : 1≤q) (hq7 : q≤7) :
    C≤cutoffRescaleCoefficient C η r q ∧ cutoffRescaleCoefficient C η r q≤21952*C := by
  rw [cutoffRescaleCoefficient_eq C η r q (by linarith) (by linarith)]
  have hrlo : 1≤r^(1-η) := Real.one_le_rpow hr (by linarith)
  have hqlo : 1≤q^(2+η) := Real.one_le_rpow hq (by linarith)
  have hrup : r^(1-η)≤r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr (show 1-η≤1 by linarith)
  have hqup : q^(2+η)≤q^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hq (show 2+η≤(3:ℝ) by linarith)
  constructor
  · calc
      C = C*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ C*r*q^3 := by gcongr
      _ ≤ C*64*7^3 := by gcongr
      _ = _ := by ring

theorem selectedPoissonK_rescale (C M X η r q : ℝ)
    (hM : 0<M) (hX : 0<X) (hr : 0<r) (hq : 0<q) :
    selectedPoissonK (cutoffRescaleCoefficient C η r q) (r*M) (X/q) η =
      selectedPoissonK C M X η := by
  unfold selectedPoissonK selectedPoissonT cutoffRescaleCoefficient
  have he : (r*M)*(X/q)=(r/q)*(M*X) := by ring
  rw [he,Real.mul_rpow (by positivity : 0≤r/q) (by positivity : 0≤M*X)]
  have hp : (r/q)^η≠0 := (Real.rpow_pos_of_pos (by positivity) η).ne'
  field_simp

end

open scoped BigOperators Classical

def largeGcdThreshold (α N : ℝ) : ℝ := N^(1-1/α)

theorem largeGcdThreshold_quotient_power (α N : ℝ) (hα : α≠0) (hN : 0<N) :
    (N/largeGcdThreshold α N)^α=N := by
  have he : N/largeGcdThreshold α N=N^(1/α) := by
    rw [show 1/α=1-(1-1/α) by ring,Real.rpow_sub hN,Real.rpow_one]
    rfl
  rw [he,←Real.rpow_mul hN.le]
  field_simp
  rw [Real.rpow_one]

theorem largeGcdThreshold_bounds (α N : ℝ) (hα1 : 1≤α) (hα2 : α≤2) (hN : 4≤N) :
    1≤largeGcdThreshold α N ∧ largeGcdThreshold α N≤N/2 := by
  have hα : 0<α := by linarith
  have hN0 : 0<N := by linarith
  have ha : 0≤1-1/α := by
    have hi : 1/α≤1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α≤(1/2:ℝ) := by
    have hi : (1/2:ℝ)≤1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeGcdThreshold α N ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩

theorem high_kernel_chosen_scale (M N K : ℝ) (hM : 0<M) (_hN : 0<N) (hK : 0<K)
    (hcut : N^2/M≤K) : Real.sqrt ((2*M)/K)*N≤2*M := by
  have hNK : N^2≤M*K := by
    have h := (div_le_iff₀ hM).mp hcut
    nlinarith
  let s := Real.sqrt ((2*M)/K)
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hs : s^2*K=2*M := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hK.ne']
  have hb : s^2*N^2≤2*M^2 := by
    calc
      _ ≤ s^2*(M*K) := mul_le_mul_of_nonneg_left hNK (sq_nonneg s)
      _ = (s^2*K)*M := by ring
      _ = _ := by rw [hs]; ring
  change s*N≤2*M
  nlinarith [sq_nonneg (s*N)]

theorem chosen_large_gcd_main (α M N K : ℝ) (hα : α≠0)
    (hM : 0<M) (hN : 0<N) (hK : 0<K) (hcut : N^2/M≤K) :
    2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α≤4*M := by
  rw [largeGcdThreshold_quotient_power α N hα hN]
  linarith [high_kernel_chosen_scale M N K hM hN hK hcut]

theorem chosen_large_gcd_full (α deltaLoss C M N K : ℝ) (hα1 : 1≤α) (hα2 : α≤2)
    (hδ : 0≤deltaLoss) (hC : 0≤C) (hM : 0<M) (hN : 4≤N) (hK : 0<K)
    (hcut : N^2/M≤K) :
    C*((2*M)*(N/largeGcdThreshold α N))^deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α) ≤
        (4*C*2^deltaLoss)*(M*N)^deltaLoss*M := by
  have hh := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hH : 0<largeGcdThreshold α N := by linarith
  have hN0 : 0<N := by linarith
  have hp : ((2*M)*(N/largeGcdThreshold α N))^deltaLoss≤(2*(M*N))^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_gcd_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N))^deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; ring

end CanonicalQuadraticSieve

end

end OAI
