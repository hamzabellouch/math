import Mathlib
import OAI.Geometry.BallPacking.Normal.CompactDegenerationTransfer

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open MvPolynomial
open FiniteMoment.Radial

 theorem actual_six_cubic_inner_polynomial_packing_avoid_axes_large (Q : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t : ℝ,0<t ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t) (f i)) ∧
        (∀ i,MapsTo (f i) (closedBall 3 (r' i)) cubicAffineDomain) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  classical
  obtain ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,h₁,h₂,_hrh,_hh₁₂,hh₁,hh₂,ℓ,φ,hφ,hm,hd⟩ :=
    actual_six_cubic_inner_normal_packing_large Q r r' hr hr' hrr ha ha1 hrs hvol
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  let K : Set CubicPhysicalSpace := ⋃ i,φ i '' closedBall 3 (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact 3 (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hPS := physicalParameter_maps_six_region hL hh₁ hh₂
    (show (A:ℝ)=(L:ℝ)*((A:ℝ)/L) by field_simp)
    (show (B:ℝ)=(L:ℝ)*((B:ℝ)/L) by field_simp)
  have hKd (p : CubicPhysicalSpace) (hp : p∈K) :
      physicalParameter L (planeMoments p.2)∈Radial.lowerTrapezoid A B := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact hPS (interior_subset (hm i hx)).2
  have hinv (p : CubicPhysicalSpace) (hp : p∈K) :
      (cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact (hφ i).target_invertible (complexSplitPhase 2).toLinearEquiv.finrank_eq hx
      (successorStandardForm_isInvertible 2)
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgT,hgform⟩ :=
    exists_actual_cubic_normal_transfer_into hA hAB D S hLr hK hKd hinv
      cubicAffineDomain_isOpen inclusion_mem_cubicAffineDomain
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r' i))
    (fun _ => successorStandardForm 2) (cubicPhysicalForm (A := A) (B := B) D S L)
    (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t)
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
  exact ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,t,ht,fun i => g ∘ φ i,hf,fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 def quadricParam (u v w : ℂ) : Fin 4 → ℂ := ![v*w,u^2,u*v,u*w]
 def liftAlpha (n J K : ℕ) := J+K-n
 def liftBeta (n J K : ℕ) := n+liftAlpha n J K-(J+K)
 def liftGamma (n J K : ℕ) := J-liftAlpha n J K
 def liftDelta (n J K : ℕ) := K-liftAlpha n J K

 theorem lift_exponents {n J K : ℕ} (hJ : J≤n) (hK : K≤n) :
    liftAlpha n J K+liftGamma n J K=J ∧
    liftAlpha n J K+liftDelta n J K=K ∧
    2*liftBeta n J K+liftGamma n J K+liftDelta n J K=2*n-(J+K) ∧
    liftAlpha n J K+liftBeta n J K+liftGamma n J K+liftDelta n J K=n := by
  dsimp [liftAlpha,liftBeta,liftGamma,liftDelta]
  omega

 theorem lift_order_bounds {n J K r : ℕ} (hJ : J≤n) (hK : K≤n)
    (hr : r≤n) (hJK : J+K+r≤2*n) :
    r≤liftBeta n J K+liftGamma n J K+liftDelta n J K ∧
    liftBeta n J K+liftGamma n J K+liftDelta n J K≤n := by
  dsimp [liftAlpha,liftBeta,liftGamma,liftDelta]
  omega

 def quadricLiftMonomial (n J K : ℕ) (x : Fin 4 → ℂ) :=
  x 0^liftAlpha n J K*x 1^liftBeta n J K*x 2^liftGamma n J K*x 3^liftDelta n J K

 theorem quadricLiftMonomial_smooth (n J K : ℕ) :
    ContDiff ℂ ∞ (quadricLiftMonomial n J K) :=
  ((((contDiff_apply ℂ ℂ 0).pow _).mul ((contDiff_apply ℂ ℂ 1).pow _)).mul
    ((contDiff_apply ℂ ℂ 2).pow _)).mul ((contDiff_apply ℂ ℂ 3).pow _)

 theorem quadricLiftMonomial_param {n J K : ℕ} (hJ : J≤n) (hK : K≤n)
    (u v w : ℂ) :
    quadricLiftMonomial n J K (quadricParam u v w)=u^(2*n-(J+K))*v^J*w^K := by
  obtain ⟨heJ,heK,heI,_⟩ := lift_exponents hJ hK
  change (v*w)^liftAlpha n J K*(u^2)^liftBeta n J K*
    (u*v)^liftGamma n J K*(u*w)^liftDelta n J K=_
  calc
    _=u^(2*liftBeta n J K+liftGamma n J K+liftDelta n J K)*
      v^(liftAlpha n J K+liftGamma n J K)*w^(liftAlpha n J K+liftDelta n J K) := by
        simp only [mul_pow,pow_add,pow_mul]
        ring
    _=_ := by rw [heJ,heK,heI]

 theorem quadricLiftMonomial_homogeneous {n J K : ℕ} (hJ : J≤n) (hK : K≤n)
    (ζ : ℂ) (x : Fin 4 → ℂ) :
    quadricLiftMonomial n J K (ζ • x)=ζ^n*quadricLiftMonomial n J K x := by
  have he := (lift_exponents hJ hK).2.2.2
  unfold quadricLiftMonomial
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow]
  calc
    _=ζ^(liftAlpha n J K+liftBeta n J K+liftGamma n J K+liftDelta n J K)*
      (x 0^liftAlpha n J K*x 1^liftBeta n J K*x 2^liftGamma n J K*x 3^liftDelta n J K) := by
        simp only [pow_add]; ring
    _=_ := by rw [he]

 def quadricLiftPolynomial (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) (x : Fin 4 → ℂ) : ℂ :=
  ∑ d∈q.support,q.coeff d*quadricLiftMonomial n (d 0) (d 1) x

 theorem quadricLiftPolynomial_smooth (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    ContDiff ℂ ∞ (quadricLiftPolynomial n q) := by
  unfold quadricLiftPolynomial
  exact ContDiff.sum (fun _ _ => contDiff_const.mul (quadricLiftMonomial_smooth _ _ _))

 theorem quadricLiftPolynomial_param {n : ℕ} (q : MvPolynomial (Fin 2) ℂ)
    (h0 : q.degreeOf 0≤n) (h1 : q.degreeOf 1≤n) (v w : ℂ) :
    quadricLiftPolynomial n q (quadricParam 1 v w)=MvPolynomial.eval ![v,w] q := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro d hd
  rw [quadricLiftMonomial_param ((MvPolynomial.monomial_le_degreeOf 0 hd).trans h0)
    ((MvPolynomial.monomial_le_degreeOf 1 hd).trans h1)]
  simp [Fin.prod_univ_two]

 theorem quadricLiftPolynomial_homogeneous {n : ℕ} (q : MvPolynomial (Fin 2) ℂ)
    (h0 : q.degreeOf 0≤n) (h1 : q.degreeOf 1≤n) (ζ : ℂ) (x : Fin 4 → ℂ) :
    quadricLiftPolynomial n q (ζ • x)=ζ^n*quadricLiftPolynomial n q x := by
  unfold quadricLiftPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [quadricLiftMonomial_homogeneous ((MvPolynomial.monomial_le_degreeOf 0 hd).trans h0)
    ((MvPolynomial.monomial_le_degreeOf 1 hd).trans h1)]
  ring

 theorem quadricLiftPolynomial_orders {n r : ℕ} (q : MvPolynomial (Fin 2) ℂ)
    (h0 : q.degreeOf 0≤n) (h1 : q.degreeOf 1≤n)
    (hr : r≤n) (hdeg : q.totalDegree+r≤2*n) (d : Fin 2 →₀ ℕ) (hd : d∈q.support) :
    r≤liftBeta n (d 0) (d 1)+liftGamma n (d 0) (d 1)+liftDelta n (d 0) (d 1) ∧
    liftBeta n (d 0) (d 1)+liftGamma n (d 0) (d 1)+liftDelta n (d 0) (d 1)≤n := by
  apply lift_order_bounds ((MvPolynomial.monomial_le_degreeOf 0 hd).trans h0)
    ((MvPolynomial.monomial_le_degreeOf 1 hd).trans h1) hr
  have h := MvPolynomial.le_totalDegree hd
  have he : d.sum (fun _ e => e)=d 0+d 1 := by
    rw [d.sum_fintype (fun _ e => e) (by simp)]
    simp [Fin.sum_univ_two]
  rw [he] at h
  omega

 def planeCubicPolynomial : MvPolynomial (Fin 2) ℂ :=
  X 0^2*X 1+C (-1)*(X 0*X 1^2)+X 1+C (-2)*X 0

 theorem planeCubicPolynomial_eval (v w : ℂ) :
    eval ![v,w] planeCubicPolynomial=polynomial (v,w) := by
  simp only [planeCubicPolynomial,map_add,map_mul,map_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
  change v^2*w+(-1)*(v*w^2)+w+(-2)*v=v*w*(v-w)+w-2*v
  ring

 theorem planeCubicPolynomial_degreeOf (i : Fin 2) : planeCubicPolynomial.degreeOf i≤2 := by
  have h0 : (X 0^2*X 1 : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    have h := degreeOf_mul_le i (X 0^2 : MvPolynomial (Fin 2) ℂ) (X 1)
    fin_cases i <;> simp [degreeOf_X_pow_of_ne,degreeOf_X] at h ⊢ <;> omega
  have h1 : (C (-1)*(X 0*X 1^2) : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    apply (degreeOf_C_mul_le _ _ _).trans
    have h := degreeOf_mul_le i (X 0 : MvPolynomial (Fin 2) ℂ) (X 1^2)
    fin_cases i <;> simp [degreeOf_X_pow_of_ne,degreeOf_X] at h ⊢ <;> omega
  have h2 : (X 1 : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    fin_cases i <;> simp [degreeOf_X]
  have h3 : (C (-2)*X 0 : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    apply (degreeOf_C_mul_le _ _ _).trans
    fin_cases i <;> simp [degreeOf_X]
  exact (degreeOf_add_le _ _ _).trans (max_le ((degreeOf_add_le _ _ _).trans
    (max_le ((degreeOf_add_le _ _ _).trans (max_le h0 h1)) h2)) h3)

 theorem planeCubicPolynomial_totalDegree : planeCubicPolynomial.totalDegree≤3 := by
  have h0 : (X 0^2*X 1 : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by
    have h := totalDegree_mul (X 0^2 : MvPolynomial (Fin 2) ℂ) (X 1)
    rw [totalDegree_X_pow,totalDegree_X] at h
    exact h
  have h1 : (C (-1)*(X 0*X 1^2) : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C,zero_add]
    have h := totalDegree_mul (X 0 : MvPolynomial (Fin 2) ℂ) (X 1^2)
    rw [totalDegree_X,totalDegree_X_pow] at h
    exact h
  have h2 : (X 1 : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by simp
  have h3 : (C (-2)*X 0 : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by
    exact (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
    (max_le ((totalDegree_add _ _).trans (max_le h0 h1)) h2)) h3)

 def coefficientPowers (D m : ℕ) : WeightedHomogeneousIndex → ℕ × ℕ
  | none => (0,0)
  | some none => (D-m,0)
  | some (some j) => ![(0,D-m),(D-m,m),(m,D-m)] j

 theorem coefficientPowers_bounds {D m : ℕ} (hm : 2*m≤D) (i : WeightedHomogeneousIndex) :
    (coefficientPowers D m i).1≤D-m ∧ (coefficientPowers D m i).2≤D-m ∧
      (coefficientPowers D m i).1+(coefficientPowers D m i).2≤D := by
  cases i with
  | none => simp [coefficientPowers]
  | some i =>
    cases i with
    | none => simp [coefficientPowers]
    | some i => fin_cases i <;> dsimp [coefficientPowers] <;> omega

 def coefficientPolynomial (D m : ℕ) (i : WeightedHomogeneousIndex) : MvPolynomial (Fin 2) ℂ :=
  X 0^(coefficientPowers D m i).1*X 1^(coefficientPowers D m i).2

 theorem coefficientPolynomial_eval (D m : ℕ) (i : WeightedHomogeneousIndex) (v w : ℂ) :
    eval ![v,w] (coefficientPolynomial D m i)=ambientWeightedCoefficient D m (v,w) i := by
  unfold ambientWeightedCoefficient
  rw [←complexCartesian_affineComplex,ContinuousLinearEquiv.symm_apply_apply]
  simp only [coefficientPolynomial,map_mul,map_pow,MvPolynomial.eval_X]
  cases i with
  | none => simp [coefficientPowers,complexAffineLift]
  | some i =>
    cases i with
    | none => simp [coefficientPowers,complexAffineLift,weightedProjection,affineComplex]
    | some i => fin_cases i <;>
        simp [coefficientPowers,complexAffineLift,weightedProjection,affineComplex]

 theorem coefficientPolynomial_degreeOf {D m : ℕ} (hm : 2*m≤D)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (coefficientPolynomial D m i).degreeOf j≤D-m := by
  have h := degreeOf_mul_le j (X 0^(coefficientPowers D m i).1 : MvPolynomial (Fin 2) ℂ)
    (X 1^(coefficientPowers D m i).2)
  have hb := coefficientPowers_bounds hm i
  fin_cases j <;> simp [degreeOf_X_pow_of_ne] at h
  · exact h.trans hb.1
  · exact h.trans hb.2.1

 theorem coefficientPolynomial_totalDegree {D m : ℕ} (hm : 2*m≤D) (i : WeightedHomogeneousIndex) :
    (coefficientPolynomial D m i).totalDegree≤D := by
  have h := totalDegree_mul (X 0^(coefficientPowers D m i).1 : MvPolynomial (Fin 2) ℂ)
    (X 1^(coefficientPowers D m i).2)
  simp only [totalDegree_X_pow] at h
  exact h.trans (coefficientPowers_bounds hm i).2.2

 def cubicNormalSection (D m k : ℕ) (i : WeightedHomogeneousIndex) : MvPolynomial (Fin 2) ℂ :=
  planeCubicPolynomial^k*coefficientPolynomial D m i

 theorem cubicNormalSection_eval (D m k : ℕ) (i : WeightedHomogeneousIndex) (v w : ℂ) :
    eval ![v,w] (cubicNormalSection D m k i)=polynomial (v,w)^k*ambientWeightedCoefficient D m (v,w) i := by
  rw [cubicNormalSection,map_mul,map_pow,planeCubicPolynomial_eval,coefficientPolynomial_eval]

 theorem cubicNormalSection_degreeOf {D m : ℕ} (hm : 2*m≤D) (k : ℕ)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (cubicNormalSection D m k i).degreeOf j≤2*k+(D-m) := by
  exact (degreeOf_mul_le _ _ _).trans (add_le_add
    ((degreeOf_pow_le _ _ _).trans ((Nat.mul_le_mul_left k (planeCubicPolynomial_degreeOf j)).trans_eq (Nat.mul_comm k 2)))
    (coefficientPolynomial_degreeOf hm i j))

 theorem cubicNormalSection_totalDegree {D m : ℕ} (hm : 2*m≤D) (k : ℕ)
    (i : WeightedHomogeneousIndex) : (cubicNormalSection D m k i).totalDegree≤3*k+D := by
  exact (totalDegree_mul _ _).trans (add_le_add
    ((totalDegree_pow _ _).trans ((Nat.mul_le_mul_left k planeCubicPolynomial_totalDegree).trans_eq (Nat.mul_comm k 3)))
    (coefficientPolynomial_totalDegree hm i))

 theorem cubic_lift_integer_bounds {L S k₁ k₂ : ℕ} (hS : 2*S<L) (hk₁ : k₁<S)
    (hk : 3*(k₁+k₂)<L+S) :
    2*(S-(k₁+k₂))≤L+S-3*(k₁+k₂) ∧
    2*k₂+(L+S-3*(k₁+k₂)-(S-(k₁+k₂)))≤L-2*k₁ ∧
    L-S-k₁≤L-2*k₁ ∧
    3*k₂+(L+S-3*(k₁+k₂))+(L-S-k₁)≤2*(L-2*k₁) := by omega

 def firstQuadric (x : Fin 4 → ℂ) : ℂ := x 0*x 1-x 2*x 3

 theorem firstQuadric_smooth : ContDiff ℂ ∞ firstQuadric :=
  ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).sub
    ((contDiff_apply ℂ ℂ 2).mul (contDiff_apply ℂ ℂ 3))

 theorem firstQuadric_homogeneous (ζ : ℂ) (x : Fin 4 → ℂ) :
    firstQuadric (ζ • x)=ζ^2*firstQuadric x := by
  simp only [firstQuadric,Pi.smul_apply,smul_eq_mul]
  ring

 theorem inner_lattice_bounds {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (k : TrapezoidWeight A B) :
    2*cubicMarkedOrder S k≤cubicDegree (L+S) k ∧
    2*(latticeIndex k).2+(cubicDegree (L+S) k-cubicMarkedOrder S k)≤L-2*(latticeIndex k).1 ∧
    L-S-(latticeIndex k).1≤L-2*(latticeIndex k).1 ∧
    3*(latticeIndex k).2+cubicDegree (L+S) k+(L-S-(latticeIndex k).1)≤2*(L-2*(latticeIndex k).1) := by
  have hk1 : (latticeIndex k).1<S := by
    have h := k.property.1
    change k.val.1.val<S
    omega
  have hk : 3*((latticeIndex k).1+(latticeIndex k).2)<L+S := by
    have h := totalWeight_le k
    change 3*totalWeight k<L+S
    omega
  exact cubic_lift_integer_bounds hS hk1 hk

 def liftedSection {A B : ℕ} (L S : ℕ) (k : TrapezoidWeight A B)
    (i : WeightedHomogeneousIndex) (x : Fin 4 → ℂ) : ℂ :=
  firstQuadric x^(latticeIndex k).1 *
    quadricLiftPolynomial (L-2*(latticeIndex k).1)
      (cubicNormalSection (cubicDegree (L+S) k) (cubicMarkedOrder S k) (latticeIndex k).2 i) x

 theorem liftedSection_smooth {A B : ℕ} (L S : ℕ) (k : TrapezoidWeight A B)
    (i : WeightedHomogeneousIndex) : ContDiff ℂ ∞ (liftedSection L S k i) :=
  (firstQuadric_smooth.pow _).mul (quadricLiftPolynomial_smooth _ _)

 theorem liftedSection_homogeneous {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (k : TrapezoidWeight A B) (i : WeightedHomogeneousIndex)
    (ζ : ℂ) (x : Fin 4 → ℂ) : liftedSection L S k i (ζ • x)=ζ^L*liftedSection L S k i x := by
  obtain ⟨hm,hdeg,_,_⟩ := inner_lattice_bounds hAS hS hB k
  have hd (j : Fin 2) := (cubicNormalSection_degreeOf hm (latticeIndex k).2 i j).trans hdeg
  have he : 2*(latticeIndex k).1+(L-2*(latticeIndex k).1)=L := by
    have h := k.property.1
    dsimp [Radial.latticeIndex]
    omega
  rw [liftedSection,firstQuadric_homogeneous,quadricLiftPolynomial_homogeneous _ (hd 0) (hd 1)]
  simp only [mul_pow,←pow_mul]
  rw [show ζ^L=ζ^(2*(latticeIndex k).1)*ζ^(L-2*(latticeIndex k).1) by rw [←pow_add,he]]
  unfold liftedSection
  ring

 theorem liftedSection_origin_orders {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (k : TrapezoidWeight A B) (i : WeightedHomogeneousIndex)
    (d : Fin 2 →₀ ℕ)
    (hd : d∈(cubicNormalSection (cubicDegree (L+S) k) (cubicMarkedOrder S k) (latticeIndex k).2 i).support) :
    L-S≤(latticeIndex k).1+liftBeta (L-2*(latticeIndex k).1) (d 0) (d 1)+
      liftGamma (L-2*(latticeIndex k).1) (d 0) (d 1)+liftDelta (L-2*(latticeIndex k).1) (d 0) (d 1) := by
  obtain ⟨hm,hdeg,hr,horder⟩ := inner_lattice_bounds hAS hS hB k
  have hdj (j : Fin 2) := (cubicNormalSection_degreeOf hm (latticeIndex k).2 i j).trans hdeg
  have htotal := cubicNormalSection_totalDegree hm (latticeIndex k).2 i
  have hh := (quadricLiftPolynomial_orders _ (hdj 0) (hdj 1) hr
    (show (cubicNormalSection (cubicDegree (L+S) k) (cubicMarkedOrder S k) (latticeIndex k).2 i).totalDegree+
      (L-S-(latticeIndex k).1)≤2*(L-2*(latticeIndex k).1) by omega) d hd).1
  have hk := k.property.1
  dsimp [Radial.latticeIndex] at *
  omega

 def firstQuadricChart (p : CubicAmbient) : Fin 4 → ℂ := ![p.2,1,p.1.1,p.1.2]

 theorem firstQuadricChart_smooth : ContDiff ℂ ∞ firstQuadricChart := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd
  · exact contDiff_const
  · exact contDiff_fst.fst
  · exact contDiff_fst.snd

 def outerTube (δ : ℝ) (p : CubicAmbient) : CubicAmbient :=
  (p.1,p.1.1*p.1.2+(δ:ℂ)*p.2)

 theorem outerTube_smooth : ContDiff ℝ ∞ (fun p : ℝ × CubicAmbient => outerTube p.1 p.2) :=
  contDiff_snd.fst.prodMk ((contDiff_snd.fst.fst.mul contDiff_snd.fst.snd).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_snd.snd))

 theorem outerTube_firstQuadric (δ : ℝ) (p : CubicAmbient) :
    firstQuadric (firstQuadricChart (outerTube δ p))=(δ:ℂ)*p.2 := by
  simp only [firstQuadric,firstQuadricChart,outerTube,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,mul_one]
  ring

 def outerPolynomial {A B : ℕ} (L S : ℕ) (t δ : ℝ) (x : Fin 4 → ℂ) :
    TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  fun ki => (δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
    liftedSection L S ki.1 ki.2 x

 def outerConePolynomial {A B : ℕ} (L S : ℕ) (t : ℝ) (p : ℝ × CubicAmbient) :
    TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  fun ki => p.2.2^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
    quadricLiftPolynomial (L-2*(latticeIndex ki.1).1)
      (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2)
      (firstQuadricChart (outerTube p.1 p.2))

 theorem outerPolynomial_smooth {A B : ℕ} (L S : ℕ) (t δ : ℝ) :
    ContDiff ℂ ∞ (outerPolynomial (A := A) (B := B) L S t δ) := by
  exact contDiff_pi.mpr (fun ki => contDiff_const.mul (liftedSection_smooth _ _ _ _))

 theorem outerConePolynomial_smooth {A B : ℕ} (L S : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (outerConePolynomial (A := A) (B := B) L S t) := by
  apply contDiff_pi.mpr
  intro ki
  exact ((contDiff_snd.snd.pow _).mul contDiff_const).mul
    (((quadricLiftPolynomial_smooth _ _).restrict_scalars ℝ).comp
      ((firstQuadricChart_smooth.restrict_scalars ℝ).comp outerTube_smooth))

 theorem outerConePolynomial_eq {A B : ℕ} (L S : ℕ) (t : ℝ) {δ : ℝ} (hδ : δ≠0)
    (p : CubicAmbient) : outerConePolynomial (A := A) (B := B) L S t (δ,p)=
      outerPolynomial L S t δ (firstQuadricChart (outerTube δ p)) := by
  ext ki
  simp only [outerConePolynomial,outerPolynomial,liftedSection,outerTube_firstQuadric,mul_pow]
  have hδc : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  rw [show (δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
      ((δ:ℂ)^(latticeIndex ki.1).1*p.2^(latticeIndex ki.1).1 *
      quadricLiftPolynomial (L-2*(latticeIndex ki.1).1)
        (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2)
        (firstQuadricChart (outerTube δ p)))=
      ((δ:ℂ)⁻¹*(δ:ℂ))^(latticeIndex ki.1).1 * outerConePolynomial (A := A) (B := B) L S t (δ,p) ki by
        simp only [mul_pow,outerConePolynomial]; ring]
  rw [inv_mul_cancel₀ hδc,one_pow,one_mul]
  rfl

 theorem outerConePolynomial_zero {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (t : ℝ) (p : CubicAmbient) :
    outerConePolynomial (A := A) (B := B) L S t (0,p)=
      conePolynomial (L+S) S (cubicNormalCoordinates t p) := by
  ext ki
  obtain ⟨hm,hdeg,_,_⟩ := inner_lattice_bounds hAS hS hB ki.1
  have hd (j : Fin 2) := (cubicNormalSection_degreeOf hm (latticeIndex ki.1).2 ki.2 j).trans hdeg
  have hc : firstQuadricChart (outerTube 0 p)=quadricParam 1 p.1.1 p.1.2 := by
    ext j
    fin_cases j <;> simp [firstQuadricChart,outerTube,quadricParam]
  simp only [outerConePolynomial,hc,quadricLiftPolynomial_param _ (hd 0) (hd 1),cubicNormalSection_eval]
  change _=p.2^(latticeIndex ki.1).1*(t⁻¹ • polynomial p.1)^(latticeIndex ki.1).2*
    ambientWeightedCoefficient (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) p.1 ki.2
  rw [Complex.real_smul,mul_pow,Complex.ofReal_inv]
  ring

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
 theorem primitivePullback_comp (α : G → G →L[ℝ] ℝ) {f : F → G} {g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    primitivePullback (primitivePullback α f) g=primitivePullback α (f ∘ g) := by
  funext x
  unfold primitivePullback
  rw [fderiv_comp x (hf.differentiable (by simp) (g x)) (hg.differentiable (by simp) x)]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem quadricLiftPolynomial_one (n : ℕ) (x : Fin 4 → ℂ) :
    quadricLiftPolynomial n 1 x=x 1^n := by
  classical
  simp [quadricLiftPolynomial,quadricLiftMonomial,liftAlpha,liftBeta,liftGamma,liftDelta]

 theorem outerConePolynomial_vertex {A B : ℕ} (L S : ℕ) (t : ℝ)
    (p : ℝ × CubicAmbient) (k : TrapezoidWeight A B) (hk : Radial.latticeIndex k=(0,0)) :
    outerConePolynomial L S t p (k,none)=1 := by
  simp [outerConePolynomial,hk,cubicNormalSection,coefficientPolynomial,coefficientPowers,
    quadricLiftPolynomial_one,firstQuadricChart]

 theorem outerPolynomial_vertex {A B : ℕ} (L S : ℕ) (t δ : ℝ)
    (p : CubicAmbient) (k : TrapezoidWeight A B) (hk : Radial.latticeIndex k=(0,0)) :
    outerPolynomial L S t δ (firstQuadricChart p) (k,none)=1 := by
  simp [outerPolynomial,liftedSection,hk,cubicNormalSection,coefficientPolynomial,
    coefficientPowers,quadricLiftPolynomial_one,firstQuadricChart]

 theorem outerConePolynomial_nonzero {A B : ℕ} (L S : ℕ) (t : ℝ) (p : ℝ × CubicAmbient) :
    complexCartesian (outerConePolynomial (A := A) (B := B) L S t p)≠0 := by
  obtain ⟨k,hk⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (k,none)
  rw [outerConePolynomial_vertex L S t p k hk] at he
  exact one_ne_zero he

 theorem outerPolynomial_nonzero {A B : ℕ} (L S : ℕ) (t δ : ℝ) (p : CubicAmbient) :
    complexCartesian (outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart p))≠0 := by
  obtain ⟨k,hk⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (k,none)
  rw [outerPolynomial_vertex L S t δ p k hk] at he
  exact one_ne_zero he

 def outerAmbientPrimitive {A B : ℕ} (L S : ℕ) (c t δ : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
  primitivePullback (hopfPrimitive c)
    (complexCartesian ∘ outerPolynomial (A := A) (B := B) L S t δ ∘ firstQuadricChart)

 theorem outerAmbientPrimitive_smooth {A B : ℕ} (L S : ℕ) (c t δ : ℝ) :
    ContDiff ℝ ∞ (outerAmbientPrimitive (A := A) (B := B) L S c t δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact primitivePullback_smoothAt (hopfPrimitive_smoothAt c (outerPolynomial_nonzero L S t δ p))
    ((complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).contDiff.comp
      (((outerPolynomial_smooth L S t δ).restrict_scalars ℝ).comp
        (firstQuadricChart_smooth.restrict_scalars ℝ))).contDiffAt

 def outerAmbientForm {A B : ℕ} (L S : ℕ) (c t δ : ℝ) :=
  euclideanExteriorOneForm (outerAmbientPrimitive (A := A) (B := B) L S c t δ)

 def outerConePrimitive {A B : ℕ} (L S : ℕ) (c t δ : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
  primitivePullback (hopfPrimitive c)
    (fun p => complexCartesian (outerConePolynomial (A := A) (B := B) L S t (δ,p)))

 theorem outerConePrimitive_smooth {A B : ℕ} (L S : ℕ) (c t : ℝ) :
    SmoothOneFormFamily (outerConePrimitive (A := A) (B := B) L S c t) := by
  let F : ℝ × CubicAmbient → PlanePhase (TrapezoidWeight A B × WeightedHomogeneousIndex) :=
    complexCartesian ∘ outerConePolynomial L S t
  have hF : ContDiff ℝ ∞ F := complexCartesian.contDiff.comp (outerConePolynomial_smooth L S t)
  have hβ : ContDiff ℝ ∞ (primitivePullback (hopfPrimitive c) F) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact primitivePullback_smoothAt (hopfPrimitive_smoothAt c (outerConePolynomial_nonzero L S t p)) hF.contDiffAt
  have he (p : ℝ × CubicAmbient) : outerConePrimitive (A := A) (B := B) L S c t p.1 p.2=
      (primitivePullback (hopfPrimitive c) F p).comp (ContinuousLinearMap.inr ℝ ℝ CubicAmbient) := by
    have hi : HasFDerivAt (fun x : CubicAmbient => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ CubicAmbient) p.2 := by
      convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
    have hd := (hF.differentiable (by simp) p).hasFDerivAt.comp p.2 hi
    unfold outerConePrimitive primitivePullback
    rw [show fderiv ℝ (fun x => complexCartesian (outerConePolynomial L S t (p.1,x))) p.2=_ from hd.fderiv]
    rfl
  have hΓ : ContDiff ℝ ∞ (fun p : ℝ × CubicAmbient => outerConePrimitive (A := A) (B := B) L S c t p.1 p.2) := by
    simp_rw [he]
    exact hβ.clm_comp contDiff_const
  intro z
  simpa only [vector_chartOneForm] using hΓ.contDiffOn

 theorem outerConePrimitive_zero {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (c t : ℝ) :
    outerConePrimitive (A := A) (B := B) L S c t 0=cubicAmbientPrimitive (A := A) (B := B) (L+S) S c t := by
  have he : (fun p => complexCartesian (outerConePolynomial (A := A) (B := B) L S t (0,p)))=
      (complexCartesian ∘ conePolynomial (L+S) S) ∘ cubicNormalCoordinates t := by
    funext p
    rw [outerConePolynomial_zero hAS hS hB]
    rfl
  unfold outerConePrimitive cubicAmbientPrimitive cubicConePrimitive
  rw [he]
  symm
  exact primitivePullback_comp (hopfPrimitive (ι := TrapezoidWeight A B × WeightedHomogeneousIndex) c)
    (f := complexCartesian ∘ conePolynomial (A := A) (B := B) (L+S) S)
    (g := cubicNormalCoordinates t)
    (complexCartesian.contDiff.comp (conePolynomial_smooth _ _))
    (cubicNormalCoordinates_smooth t)

 theorem outerConePrimitive_positive {A B : ℕ} (L S : ℕ) (c t : ℝ) {δ : ℝ} (hδ : δ≠0) :
    outerConePrimitive (A := A) (B := B) L S c t δ=
      primitivePullback (outerAmbientPrimitive (A := A) (B := B) L S c t δ) (outerTube δ) := by
  have he : (fun p => complexCartesian (outerConePolynomial (A := A) (B := B) L S t (δ,p)))=
      (complexCartesian ∘ outerPolynomial L S t δ ∘ firstQuadricChart) ∘ outerTube δ := by
    funext p
    rw [outerConePolynomial_eq L S t hδ]
    rfl
  unfold outerConePrimitive outerAmbientPrimitive
  rw [he]
  symm
  exact primitivePullback_comp (hopfPrimitive (ι := TrapezoidWeight A B × WeightedHomogeneousIndex) c)
    (f := complexCartesian ∘ outerPolynomial (A := A) (B := B) L S t δ ∘ firstQuadricChart)
    (g := outerTube δ)
    (complexCartesian.contDiff.comp (((outerPolynomial_smooth L S t δ).restrict_scalars ℝ).comp
      (firstQuadricChart_smooth.restrict_scalars ℝ)))
    (outerTube_smooth.comp (contDiff_const.prodMk contDiff_id))

 theorem outerTube_isEmbedding {δ : ℝ} (hδ : δ≠0) : Topology.IsEmbedding (outerTube δ) := by
  let R : CubicAmbient → CubicAmbient := fun p => (p.1,(δ:ℂ)⁻¹*(p.2-p.1.1*p.1.2))
  have hR : Continuous R := continuous_fst.prodMk
    (continuous_const.mul (continuous_snd.sub (continuous_fst.fst.mul continuous_fst.snd)))
  have he : R ∘ outerTube δ=id := by
    funext p
    change (p.1,(δ:ℂ)⁻¹*((p.1.1*p.1.2+(δ:ℂ)*p.2)-p.1.1*p.1.2))=p
    refine Prod.ext ?_ ?_
    · rfl
    change (δ:ℂ)⁻¹*((p.1.1*p.1.2+(δ:ℂ)*p.2)-p.1.1*p.1.2)=p.2
    rw [add_sub_cancel_left,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hδ),one_mul]
  apply Topology.IsEmbedding.of_comp
    ((outerTube_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous) hR
  change Topology.IsEmbedding (R ∘ outerTube δ)
  rw [he]
  exact Topology.IsEmbedding.id

 theorem exists_actual_outer_normal_transfer {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (c t : ℝ) {K : Set CubicAmbient} (hK : IsCompact K)
    (hKd : K⊆cubicAffineDomain)
    (hinv : ∀ p∈K,(cubicAmbientForm (A := A) (B := B) (L+S) S c t p).IsInvertible) :
    ∃ δ : ℝ,0<δ ∧ ∃ g : CubicAmbient → CubicAmbient,∃ W : Set CubicAmbient,
      IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      (∀ x∈W,(g x).2≠0) ∧ ∀ x∈W,∀ v w,
      outerAmbientForm (A := A) (B := B) L S c t δ (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
        cubicAmbientForm (A := A) (B := B) (L+S) S c t x v w := by
  have hΓ := outerConePrimitive_smooth (A := A) (B := B) L S c t
  have hΓ0 : ∀ x,manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t 0) x=
      cubicAmbientForm (A := A) (B := B) (L+S) S c t x := by
    intro x
    rw [outerConePrimitive_zero hAS hS hB,vector_exteriorOneForm]
    rfl
  have hnondeg (x : CubicAmbient) (hx : x∈K) :
      (manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t 0) x).IsInvertible := by
    rw [hΓ0]
    exact hinv x hx
  have hform (δ : ℝ) (hδ : δ∈Ioc (0:ℝ) 1) (x : CubicAmbient) (_hx : x∈(univ : Set CubicAmbient)) :
      manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t δ) x=
      (outerAmbientForm (A := A) (B := B) L S c t δ (outerTube δ x)).bilinearComp
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicAmbient) (outerTube δ) x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicAmbient) (outerTube δ) x) := by
    have hTube : ContDiff ℝ ∞ (outerTube δ) :=
      outerTube_smooth.comp (contDiff_const.prodMk contDiff_id)
    rw [outerConePrimitive_positive L S c t (ne_of_gt hδ.1),vector_exteriorOneForm,
      primitivePullback_exterior (outerAmbientPrimitive_smooth L S c t δ) hTube]
    simp only [outerAmbientForm,manifoldMapDifferential,mfderiv_eq_fderiv]
  have hinto : MapsTo (outerTube 0) K {p : CubicAmbient | p.2≠0} := by
    intro x hx
    have h := hKd hx
    change x.1.1*x.1.2+(0:ℂ)*x.2≠0
    rw [zero_mul,add_zero]
    exact mul_ne_zero h.1 h.2
  have hTubeM : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicAmbient)) 𝓘(ℝ,CubicAmbient) ∞
      (fun p : ℝ×CubicAmbient => outerTube p.1 p.2) := by
    rw [modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact outerTube_smooth.contMDiff
  obtain ⟨δ,hδ,g,W,hW,hKW,hg,hgemb,hgT,hgform⟩ :=
    exists_compact_exact_fibre_embedding_central_into hΓ hK hnondeg isOpen_univ (subset_univ K)
      (by norm_num : 0<(1:ℝ)) hTubeM
      (fun δ hδ => (outerTube_isEmbedding (ne_of_gt hδ.1)).comp Topology.IsEmbedding.subtypeVal)
      (isOpen_ne_fun continuous_snd continuous_const) hinto
      (fun δ => outerAmbientForm (A := A) (B := B) L S c t δ) hform
  refine ⟨δ,hδ.1,g,W,hW,hKW,hg.contDiff,hgemb,hgT,?_⟩
  intro x hx v w
  have hh := hgform x hx v w
  rw [hΓ0] at hh
  simp only [mfderiv_eq_fderiv] at hh
  convert! hh using 1

end PackingSufficiencySupport.CubicModel
end

end OAI
