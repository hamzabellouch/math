import Mathlib
import OAI.Geometry.BallPacking.Toric.CubicRadialFamilyExtension

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
section
variable {ι : Type*} [Fintype ι]

theorem radialProbability_nonneg {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (p : Radial.Plane) (x : BaseCurve) (i : ι) :
    0≤radialProbability k D m p x i :=
  Radial.selected_nonneg (fun j => coefficientNorm_pos (D j) (m j) x) h0 p i

theorem radialProbability_sum {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (p : Radial.Plane) (x : BaseCurve) :
    ∑ i,radialProbability k D m p x i=1 :=
  Radial.selected_sum (fun j => coefficientNorm_pos (D j) (m j) x) h0 p

theorem radialProbability_mean {A B : ℕ} (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (x : BaseCurve) :
    ∑ i,radialProbability Radial.latticeIndex D m p x i • trapezoidWeight A B i=
      planeVector p.1 p.2 :=
  Radial.trapezoid_selected_mean hAB (fun j => coefficientNorm_pos (D j) (m j) x) hp

end
section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem reducedEndRegularPrimitive_norm_le (w : ι → MomentPlane) (D m : ι → ℕ)
    (c : ℝ) (p : MomentPlane) (ε : EndIndex) (y : Plane) {M : ℝ}
    (hM : ∀ i,‖weightedRegularEndPrimitive (D i) (m i) ε c y‖≤M) :
    ‖reducedEndRegularPrimitive w D m c p ε y‖≤M := by
  apply (norm_sum_le _ _).trans
  have hq (i : ι) : 0<reducedEndProbability w D m p ε y i :=
    reducedProbability_pos w D m p _ _
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (hq _)]
  exact probability_weighted_le
    (fun i => (reducedProbability_pos w D m p (infinityDiffeomorph (parameters 0) ε y) i).le)
    (reducedProbability_sum w D m p _) hM

 omit [Nonempty ι] in
 theorem exists_regularCoefficient_log_bound (D m : ι → ℕ) {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion) :
    ∃ M : ℝ,0≤M ∧ ∀ (i : ι) (ε : EndIndex) y,y∈radialAnnulus 0 R →
      |Real.log (regularCoefficientNorm (D i) (m i) ε y)|≤M := by
  have hc : ContinuousOn (fun y : Plane => fun j : ι × EndIndex =>
      Real.log (regularCoefficientNorm (D j.1) (m j.1) j.2 y)) (radialAnnulus 0 R) := by
    apply continuousOn_pi.mpr
    intro j y hy
    have hRy : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hy.2
    exact ((regularCoefficientNorm_contDiffAt (D j.1) (m j.1) j.2 hRy).continuousAt.log
      (regularCoefficientNorm_pos _ _ _ _).ne').continuousWithinAt
  obtain ⟨M,hM⟩ := (radialAnnulus_compact 0 R).exists_bound_of_continuousOn hc
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro i ε y hy
  exact (show |Real.log (regularCoefficientNorm (D i) (m i) ε y)|≤
      ‖fun j : ι × EndIndex => Real.log (regularCoefficientNorm (D j.1) (m j.1) j.2 y)‖ from
      (norm_le_pi_norm (fun j : ι × EndIndex => Real.log (regularCoefficientNorm (D j.1) (m j.1) j.2 y))
        (i,ε))).trans ((hM y hy).trans (le_max_right _ _))

 omit [Nonempty ι] in
 theorem exists_regularPrimitive_bound (D m : ι → ℕ) (c : ℝ) {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion) :
    ∃ M : ℝ,0≤M ∧ ∀ (i : ι) (ε : EndIndex) y,y∈radialAnnulus 0 R →
      ‖weightedRegularEndPrimitive (D i) (m i) ε c y‖≤M := by
  have hc : ContinuousOn (fun y : Plane => fun j : ι × EndIndex =>
      weightedRegularEndPrimitive (D j.1) (m j.1) j.2 c y) (radialAnnulus 0 R) := by
    apply continuousOn_pi.mpr
    intro j y hy
    have hRy : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hy.2
    exact (weightedRegularEndPrimitive_contDiffAt _ _ _ _ hRy).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := (radialAnnulus_compact 0 R).exists_bound_of_continuousOn hc
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro i ε y hy
  exact (norm_le_pi_norm (fun j : ι × EndIndex =>
      weightedRegularEndPrimitive (D j.1) (m j.1) j.2 c y) (i,ε)).trans
    ((hM y hy).trans (le_max_right _ _))

end
section

variable {ι : Type*} [Fintype ι]

theorem radialEndRegularPrimitive_norm_le {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane) (ε : EndIndex) (y : Plane) {M : ℝ}
    (hM : ∀ i,‖weightedRegularEndPrimitive (D i) (m i) ε c y‖≤M) :
    ‖radialEndRegularPrimitive k D m c p ε y‖≤M := by
  apply (norm_sum_le _ _).trans
  have hq (i : ι) : 0≤radialEndProbability k D m p ε y i :=
    radialProbability_nonneg h0 D m p _ _
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hq _)]
  exact probability_weighted_le
    (fun i => radialProbability_nonneg h0 D m p (infinityDiffeomorph (parameters 0) ε y) i)
    (radialProbability_sum h0 D m p _) hM

end

 def limitingEndOrder (D S : ℝ) (p : MomentPlane) (ε : EndIndex) : ℝ :=
  if ε 0 then (if ε 1 then D-3*(p 0+p 1) else D-3*(p 0+p 1)-markedHeight S p)
  else (if ε 1 then D-3*(p 0+p 1)-markedHeight S p else 0)

 theorem probability_affine_degree {ι : Type*} [Fintype ι] {w : ι → MomentPlane}
    {q : ι → ℝ} {p : MomentPlane} (hs : ∑ i,q i=1) (he : ∑ i,q i • w i=p) (D C : ℝ) :
    (∑ i,q i*(D-C*((w i) 0+(w i) 1)))=D-C*(p 0+p 1) := by
  have hcoord (j : Fin 2) : ∑ i,q i*(w i) j=p j := by
    simpa using congrArg (fun z : MomentPlane => z j) he
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp_rw [mul_left_comm (q _) C]
  rw [←Finset.mul_sum,←Finset.mul_sum,←Finset.sum_mul,hs,one_mul,hcoord 0,hcoord 1]

 theorem reducedEndProbability_regularized {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (p : MomentPlane) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    reducedEndProbability (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) p ε y=
      selected (trapezoidWeight A B) (fun k =>
        regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y/
          (radiusSq y)^(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε)) p := by
  unfold reducedEndProbability reducedProbability
  have he : (fun k : TrapezoidWeight A B => coefficientNorm (cubicDegree D k) (cubicMarkedOrder S k)
      (infinityDiffeomorph (parameters 0) ε y))=(fun k => regularCoefficientNorm (cubicDegree D k)
      (cubicMarkedOrder S k) ε y/(radiusSq y)^(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε)) := by
    funext k
    exact coefficientNorm_eq_regular_div (cubicMarked_lt_degree hB hS k).le
      (cubicMarked_twice_complement hB hS k) ε hy hR
  rw [he]

 theorem reducedEndResidue_error {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : MomentPlane} (hp : p∈openTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (ht : 0<radiusSq y) (ht1 : radiusSq y<1) {M : ℝ} (hM : 0≤M)
    (hlog : ∀ k : TrapezoidWeight A B,|Real.log (regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y)|≤M)
    (c : ℝ) :
    |reducedEndResidue (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p ε y-
      c*limitingEndOrder D S p ε|≤
      |c| * ((2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y))) := by
  have hs := trapezoidWeight_surrounds hAB hp
  have hb : 0≤(2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)) :=
    div_nonneg (by positivity) (neg_pos.mpr (Real.log_neg ht ht1)).le
  have he : reducedEndResidue (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p ε y=
      c*(∑ k,reducedEndProbability (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) p ε y k*
        (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)) := by
    simp only [reducedEndResidue,weightedEndResidue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have hsum := reducedProbability_sum (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) p
    (infinityDiffeomorph (parameters 0) ε y)
  have hmean := reducedProbability_mean (cubicDegree D) (cubicMarkedOrder S) hs
    (infinityDiffeomorph (parameters 0) ε y)
  have hmarked (hn : ∀ k,(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)=
      (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-markedHeight S (trapezoidWeight A B k)) :
      |(∑ k,reducedEndProbability (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) p ε y k*
        (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ))-
        ((D:ℝ)-3*(p 0+p 1)-markedHeight S p)|≤
        (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)) := by
    rw [reducedEndProbability_regularized hB hS p ε hy hR]
    exact selected_marked_error hA hS0 hAB hSB
      (fun k => regularCoefficientNorm_pos _ _ _ _) hlog ht ht1 hn hp
  cases h0 : ε 0 <;> cases h1 : ε 1
  · simp only [limitingEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,weightedEndOrder,Nat.cast_zero,mul_zero,Finset.sum_const_zero,sub_self,abs_zero]
    exact hb
  · simpa only [limitingEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte] using
      hmarked (fun k => by simpa only [h0,h1,Bool.false_eq_true,↓reduceIte] using cubicEndOrder_cast hB hS ε k)
  · simpa only [limitingEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte] using
      hmarked (fun k => by simpa only [h0,h1,Bool.false_eq_true,↓reduceIte] using cubicEndOrder_cast hB hS ε k)
  · have hdeg (k : TrapezoidWeight A B) := cubicEndOrder_cast hB hS ε k
    simp only [h0,h1,↓reduceIte] at hdeg
    simp only [hdeg,limitingEndOrder,h0,h1,↓reduceIte]
    rw [probability_affine_degree (by exact hsum) (by exact hmean),sub_self,abs_zero]
    exact hb

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped Topology
open Set Filter
open scoped BigOperators ContDiff
open Function

theorem lowerTrapezoid_interior_sequence {A B : ℝ} {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ q : ℕ → Plane,(∀ n,planeVector (q n).1 (q n).2∈openTrapezoid A B) ∧
      Tendsto q atTop (𝓝 p) := by
  let e : ℝ := min (A-p.1) (B-(p.1+p.2))/4
  have he : 0<e := div_pos (lt_min (sub_pos.mpr hp.2.1) (sub_pos.mpr hp.2.2.2)) (by norm_num)
  have he0 : e≤(A-p.1)/4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he1 : e≤(B-(p.1+p.2))/4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let d : ℕ → ℝ := fun n => e*(1/((n:ℝ)+1))
  have hd (n : ℕ) : 0<d n ∧ d n≤e := by
    have hn : (1:ℝ)≤(n:ℝ)+1 := by have hh : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
    refine ⟨mul_pos he (one_div_pos.mpr (by positivity)),?_⟩
    simpa [d] using mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hn) he.le
  refine ⟨fun n => (p.1+d n,p.2+d n),?_,?_⟩
  · intro n
    change 0<p.1+d n ∧ p.1+d n<A ∧ 0<p.2+d n ∧ (p.1+d n)+(p.2+d n)<B
    have hh := hd n
    exact ⟨by linarith [hp.1],by linarith,by linarith [hp.2.2.1],by linarith⟩
  · have ht : Tendsto d atTop (𝓝 0) := by
      simpa [d] using tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [add_zero,Prod.eta] using
      (tendsto_const_nhds.add ht).prodMk_nhds (tendsto_const_nhds.add ht)

theorem trapezoid_selected_tendsto {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) {q : ℕ → Plane}
    (hq : ∀ n,q n∈lowerTrapezoid A B) (ht : Tendsto q atTop (𝓝 p))
    (i : TrapezoidWeight A B) :
    Tendsto (fun n => selected latticeIndex a (q n) i) atTop (𝓝 (selected latticeIndex a p i)) := by
  have hf := (trapezoid_selected_contDiffWithinAt hA hAB ha hp i).continuousWithinAt
  have hm : Tendsto (fun n => (a,q n)) atTop
      (𝓝[{z : (TrapezoidWeight A B → ℝ) × Plane | (∀ j,0<z.1 j) ∧ z.2∈lowerTrapezoid A B}] (a,p)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds ht,Eventually.of_forall (fun n => ⟨ha,hq n⟩)⟩
  exact hf.tendsto.comp hm

theorem selected_marked_error_lower {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A≤B) (hSB : S≤B) {a : TrapezoidWeight A B → ℝ} {n : TrapezoidWeight A B → ℕ}
    {M t D C : ℝ} (ha : ∀ k,0<a k) (hloga : ∀ k,|Real.log (a k)|≤M)
    (ht : 0<t) (ht1 : t<1)
    (hn : ∀ k,(n k:ℝ)=D-C*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
      markedHeight S (trapezoidWeight A B k)) {p : Plane} (hp : p∈lowerTrapezoid A B) :
    |(∑ k,selected latticeIndex (fun j => a j/t^(n j)) p k*(n k:ℝ))-
      (D-C*(p.1+p.2)-markedHeight S (planeVector p.1 p.2))|≤
      (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log t) := by
  let b : TrapezoidWeight A B → ℝ := fun j => a j/t^(n j)
  have hb (j : TrapezoidWeight A B) : 0<b j := div_pos (ha j) (pow_pos ht _)
  obtain ⟨q,hq,hqlim⟩ := lowerTrapezoid_interior_sequence hp
  have hqlo (j : ℕ) : q j∈lowerTrapezoid A B :=
    ⟨(hq j).1.le,(hq j).2.1,(hq j).2.2.1.le,(hq j).2.2.2⟩
  have hs (j : ℕ) :
      |(∑ k,selected latticeIndex b (q j) k*(n k:ℝ))-
        (D-C*((q j).1+(q j).2)-markedHeight S (planeVector (q j).1 (q j).2))|≤
        (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log t) := by
    have hw : Surrounds (weight latticeIndex) (planeVector (q j).1 (q j).2) :=
      trapezoidWeight_surrounds hAB (hq j)
    simp_rw [selected_eq_exponential hb (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hw]
    exact selected_marked_error hA hS hAB hSB ha hloga ht ht1 hn (hq j)
  have hsum : Tendsto (fun j => ∑ k,selected latticeIndex b (q j) k*(n k:ℝ)) atTop
      (𝓝 (∑ k,selected latticeIndex b p k*(n k:ℝ))) :=
    tendsto_finsetSum _ (fun i _ => (trapezoid_selected_tendsto hA hAB hb hp hqlo hqlim i).mul_const _)
  have hh : Continuous (fun z : Plane => D-C*(z.1+z.2)-markedHeight S (planeVector z.1 z.2)) := by
    simp only [markedHeight,planeVector]
    fun_prop
  exact le_of_tendsto ((hsum.sub (hh.continuousAt.tendsto.comp hqlim)).abs) (Eventually.of_forall hs)

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 theorem radialEndProbability_regularized {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (p : Radial.Plane) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    radialEndProbability (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) p ε y=
      Radial.selected (Radial.latticeIndex (A := A) (B := B)) (fun k =>
        regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y/
          (radiusSq y)^(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε)) p := by
  unfold radialEndProbability radialProbability
  have he : (fun k : TrapezoidWeight A B => coefficientNorm (cubicDegree D k) (cubicMarkedOrder S k)
      (infinityDiffeomorph (parameters 0) ε y))=(fun k => regularCoefficientNorm (cubicDegree D k)
      (cubicMarkedOrder S k) ε y/(radiusSq y)^(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε)) := by
    funext k
    exact coefficientNorm_eq_regular_div (cubicMarked_lt_degree hB hS k).le
      (cubicMarked_twice_complement hB hS k) ε hy hR
  rw [he]

 theorem radialEndResidue_error {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (ht : 0<radiusSq y) (ht1 : radiusSq y<1) {M : ℝ} (hM : 0≤M)
    (hlog : ∀ k : TrapezoidWeight A B,|Real.log (regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y)|≤M)
    (c : ℝ) :
    |radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p ε y-
      c*limitingEndOrder D S (planeVector p.1 p.2) ε|≤
      |c| * ((2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y))) := by
  have hb : 0≤(2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)) :=
    div_nonneg (by positivity) (neg_pos.mpr (Real.log_neg ht ht1)).le
  have he : radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p ε y=
      c*(∑ k,radialEndProbability (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) p ε y k*
        (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)) := by
    simp only [radialEndResidue,weightedEndResidue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have hsum := radialProbability_sum (Radial.lattice_zero A B) (cubicDegree D) (cubicMarkedOrder S) p
    (infinityDiffeomorph (parameters 0) ε y)
  have hmean := radialProbability_mean hAB (cubicDegree D) (cubicMarkedOrder S) hp
    (infinityDiffeomorph (parameters 0) ε y)
  have hmarked (hn : ∀ k,(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)=
      (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-markedHeight S (trapezoidWeight A B k)) :
      |(∑ k,radialEndProbability (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) p ε y k*
        (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ))-
        ((D:ℝ)-3*(p.1+p.2)-markedHeight S (planeVector p.1 p.2))|≤
        (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)) := by
    rw [radialEndProbability_regularized hB hS p ε hy hR]
    exact Radial.selected_marked_error_lower hA hS0 hAB hSB
      (fun k => regularCoefficientNorm_pos _ _ _ _) hlog ht ht1 hn hp
  cases h0 : ε 0 <;> cases h1 : ε 1
  · simp only [limitingEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,weightedEndOrder,Nat.cast_zero,mul_zero,Finset.sum_const_zero,sub_self,abs_zero]
    exact hb
  · simpa [limitingEndOrder,h0,h1,planeVector] using
      hmarked (fun k => by simpa only [h0,h1,Bool.false_eq_true,↓reduceIte] using cubicEndOrder_cast hB hS ε k)
  · simpa [limitingEndOrder,h0,h1,planeVector] using
      hmarked (fun k => by simpa only [h0,h1,Bool.false_eq_true,↓reduceIte] using cubicEndOrder_cast hB hS ε k)
  · have hdeg (k : TrapezoidWeight A B) := cubicEndOrder_cast hB hS ε k
    simp only [h0,h1,↓reduceIte] at hdeg
    simp only [hdeg,limitingEndOrder,h0,h1,↓reduceIte]
    rw [probability_affine_degree (by exact hsum) (by exact hmean),sub_self,abs_zero]
    exact hb

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem reducedEndProbability_contDiffAt {w : ι → MomentPlane} (D m : ι → ℕ) {p : MomentPlane}
    (hp : Surrounds w p) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) (i : ι) :
    ContDiffAt ℝ ∞ (fun z => reducedEndProbability w D m p ε z i) y :=
  ((reducedProbability_smooth D m hp i).contMDiffAt.comp y
    ((infinityDiffeomorph (parameters 0) ε).contMDiffOn.contMDiffAt
      ((infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy))).contDiffAt

 theorem reducedEndRegularPrimitive_contDiffAt {w : ι → MomentPlane} (D m : ι → ℕ)
    (c : ℝ) {p : MomentPlane} (hp : Surrounds w p) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (reducedEndRegularPrimitive w D m c p ε) y :=
  ContDiffAt.sum (fun i _ => (reducedEndProbability_contDiffAt D m hp ε hy i).smul
    (weightedRegularEndPrimitive_contDiffAt (D i) (m i) ε c hR))

 theorem reducedEndResidue_contDiffAt {w : ι → MomentPlane} (D m : ι → ℕ)
    (c : ℝ) {p : MomentPlane} (hp : Surrounds w p) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    ContDiffAt ℝ ∞ (reducedEndResidue w D m c p ε) y :=
  ContDiffAt.sum (fun i _ => (reducedEndProbability_contDiffAt D m hp ε hy i).mul contDiffAt_const)

end PackingSufficiencySupport.CubicModel
end

end OAI
