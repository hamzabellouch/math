import OAI.NumberTheory.Jacobsthal.Estimates.SourceRootReference

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosStoppedReferenceUpper
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.ReferenceDifferentiation

theorem log_near_two_upper {s : ℝ} (hs : 2 ≤ s) :
    Real.log (s-1) ≤ 1/10+(10/11)*(s-21/10) := by
  have hpos : 0 < s-1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpos (by norm_num : (0:ℝ)<11/10))
  rw [Real.log_div (ne_of_gt hpos) (by norm_num : (11/10:ℝ)≠0)] at hlog
  have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<11/10)
  linarith

theorem parent_benchmark_le_32 {s : ℝ} (hs : 2 ≤ s) (hu : s ≤ 218/100) :
    parentBenchmark .even s ≤ 32/100 := by
  rw [parent_even_eq_starting (by linarith : s ≤ 4)]
  unfold startingExtension
  have hlog := log_near_two_upper hs
  have hnonneg : 0 ≤ Real.log (s-1) := Real.log_nonneg (by linarith)
  have hA : sieveA ≤ 4 := by
    unfold sieveA
    linarith [ErdosPositiveReference.exp_gamma_lt_two]
  have hm := mul_le_mul_of_nonneg_right hA hnonneg
  apply (div_le_iff₀ (by linarith : 0<s)).mpr
  nlinarith

end ErdosStoppedReferenceUpper

end

section

namespace ErdosStoppedReferenceUpper
open _root_.Filter
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceAdmission ReferencePruning ReferenceProductsBasics ReferenceMertens
open ReferenceSourcePrimeSets ReferenceSourceDecomposition ReferenceDifferentiation
open ErdosPrimeInputs.MertensStrong

noncomputable def strictEuler (P : ℝ) : ℝ := availableProduct 0 P false

theorem strict_euler_split {w P : ℝ} (hw : 0 ≤ w) (hP : w < P) :
    primeProduct w*availableProduct w P false=strictEuler P := by
  classical
  have hP0 : 0 ≤ P := hw.trans hP.le
  have he : availablePrimes 0 P false = Nat.primesLE ⌊w⌋₊ ∪ availablePrimes w P false := by
    ext p
    simp only [Finset.mem_union,availablePrimes_membership hP0,Bool.false_eq_true,ite_false,Nat.mem_primesLE,
      Nat.le_floor_iff hw]
    constructor
    · rintro ⟨hp,_hp0,hpP⟩
      by_cases hpw : (p:ℝ) ≤ w
      · exact Or.inl ⟨hpw,hp⟩
      · exact Or.inr ⟨hp,lt_of_not_ge hpw,hpP⟩
    · rintro (⟨hpw,hp⟩|⟨hp,hwp,hpP⟩)
      · exact ⟨hp,by exact_mod_cast hp.pos,hpw.trans_lt hP⟩
      · exact ⟨hp,by exact_mod_cast hp.pos,hpP⟩
  have hd : Disjoint (Nat.primesLE ⌊w⌋₊) (availablePrimes w P false) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpa
    have hlo := ((availablePrimes_membership hP0 false p).mp hpa).2.1
    have hhi := (Nat.le_floor_iff hw).mp (Nat.mem_primesLE.mp hp).1
    linarith
  simp only [primeProduct_eq_survivor,strictEuler,availableProduct]
  rw [he]
  exact (Finset.prod_union hd).symm

theorem moving_finite_reference_upper (K : ℝ) (hK : 0 < K) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ w B : ℝ,w₀ ≤ w → B₀ ≤ B →
      B ≤ K*(Real.log w)^2 → ∀ z : Node,
      z.side=.even → 2 ≤ z.ratio → z.ratio ≤ 218/100 → Consistent z → z.cutoff=B →
      sourceReference w z ≤ (321/1000)*referenceProduct w B z.closed := by
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := MovingLocalReference.moving_local_reference K (1/1000) hK (by norm_num)
  refine ⟨B₀,w₀,hB₀,hw₀,?_⟩
  intro w B hw hB hscale z hi hlo hhi hcons hcut
  have herr := h w B hw hB hscale z hi (by linarith) (by linarith) hcons hcut
  have hf := parent_benchmark_le_32 hlo hhi
  have hquot : sourceReference w z/referenceProduct w B z.closed ≤ 321/1000 := by
    linarith [(abs_le.mp herr).2]
  exact (div_le_iff₀ (availableProduct_pos w (w^B) z.closed)).mp hquot

theorem moving_vertex_reference_upper (K : ℝ) (hK : 0 < K) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ w B J : ℝ,w₀ ≤ w → B₀ ≤ B →
      B ≤ K*(Real.log w)^2 → 0 ≤ J → ∀ v : StoppedCountVertex.Vertex,
      v.node.side=.even → 2 ≤ v.node.ratio → v.node.ratio ≤ 218/100 →
      Consistent v.node → v.node.cutoff=B → v.node.closed=false →
      v.available=sourcePrimes w B false → v.scale=J*primeProduct w →
      StoppedCountVertex.referenceValue w v ≤ (321/1000)*J*strictEuler (w^B) := by
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := moving_finite_reference_upper K hK
  refine ⟨max B₀ 2,w₀,hB₀.trans_le (le_max_left _ _),hw₀,?_⟩
  intro w B J hw hB hscale hJ v hi hlo hhi hcons hcut hclosed hav hmu
  have hB' : B₀ ≤ B := (le_max_left _ _).trans hB
  have hB2 : 2 ≤ B := (le_max_right _ _).trans hB
  have hw1 : 1 < w := hw₀.trans_le hw
  have hw0 : 0 < w := by linarith
  have hwp : w < w^B := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hw1 (show (1:ℝ)<B by linarith)
  have href := h w B hw hB' hscale v.node hi hlo hhi hcons hcut
  rw [hclosed] at href
  have hmu0 : 0 ≤ J*primeProduct w := mul_nonneg hJ (actual_primeProduct_pos w).le
  have hs := mul_le_mul_of_nonneg_left href hmu0
  have he : StoppedCountVertex.referenceValue w v=(J*primeProduct w)*sourceReference w v.node := by
    simp only [StoppedCountVertex.referenceValue,sourceReference,hav,hmu,hcut,hclosed]
  rw [he]
  calc
    _ ≤ (J*primeProduct w)*((321/1000)*referenceProduct w B false) := hs
    _ = (321/1000)*J*(primeProduct w*availableProduct w (w^B) false) := by
      unfold referenceProduct
      ring
    _ = _ := by rw [strict_euler_split hw0.le hwp]

theorem strict_euler_le_closed {P : ℝ} (hP : 100 ≤ P) :
    strictEuler P ≤ (51/50)*primeProduct P := by
  have hclosed : availableProduct 0 P true=primeProduct P := by
    rw [closed_product_ratio (by norm_num : (0:ℝ)≤0) (by linarith : (0:ℝ)≤P)]
    have hz : primeProduct 0=1 := by
      norm_num [primeProduct_eq_survivor,survivorProduct]
    rw [hz,div_one]
  have he := endpoint_relative_bound (a:=0) (by linarith : 2≤P)
  rw [hclosed] at he
  have hrec : 2/P ≤ 1/50 := (div_le_iff₀ (by linarith : 0<P)).mpr (by linarith)
  have hquot : strictEuler P/primeProduct P ≤ 51/50 := by
    unfold strictEuler
    linarith [(abs_le.mp he).2]
  exact (div_le_iff₀ (actual_primeProduct_pos P)).mp hquot

theorem reference_strict_to_closed {R J P : ℝ} (hJ : 0 ≤ J) (hP : 100 ≤ P)
    (hR : R ≤ (321/1000)*J*strictEuler P) :
    R ≤ (33/100)*J*primeProduct P := by
  have hE := strict_euler_le_closed hP
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ (321/1000:ℝ)*J by positivity)
  have hnonneg : 0 ≤ J*primeProduct P := mul_nonneg hJ (actual_primeProduct_pos P).le
  nlinarith

end ErdosStoppedReferenceUpper

end

end Erdos970

end OAI
