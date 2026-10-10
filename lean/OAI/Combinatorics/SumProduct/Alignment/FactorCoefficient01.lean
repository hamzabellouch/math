import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AffineCoefficient01
import OAI.Combinatorics.SumProduct.Alignment.SquareHorizontal01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace LagrangeBounds
variable {ι : Type*} [DecidableEq ι]
 
lemma common_denominator (s : Finset ι) (p : ι → ℚ[X]) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ i ∈ s, C (D : ℚ) * p i ∈ lifts (algebraMap ℤ ℚ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨D, hD, hs⟩ := ih
    obtain ⟨b, hb, hp⟩ := IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) (p i)
    have hbi : C (b : ℚ) * p i ∈ lifts (algebraMap ℤ ℚ) := by
      apply (mem_lifts _).mpr
      refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p i), ?_⟩
      rw [hp, ← algebraMap_smul ℚ, smul_eq_C_mul]
      rfl
    refine ⟨b * D, mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp hb) hD, ?_⟩
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · simpa [Int.cast_mul, map_mul, mul_assoc, mul_left_comm, mul_comm] using
        base_mul_mem_lifts D hbi
    · simpa [Int.cast_mul, map_mul, mul_assoc] using base_mul_mem_lifts b (hs j hj)

 
theorem interpolation_common_denominator (s : Finset ι) (v : ι → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ r : ι → ℤ,
      C (D : ℚ) * Lagrange.interpolate s v (fun i => (r i : ℚ)) ∈
        lifts (algebraMap ℤ ℚ) := by
  obtain ⟨D, hD, hbasis⟩ := common_denominator s (Lagrange.basis s v)
  refine ⟨D, hD, fun r => ?_⟩
  rw [Lagrange.interpolate_apply, mul_sum]
  apply (lifts (algebraMap ℤ ℚ)).sum_mem
  intro i hi
  simpa [mul_assoc, mul_left_comm, mul_comm] using base_mul_mem_lifts (r i) (hbasis i hi)

lemma map_interpolate {F K : Type*} [Field F] [Field K] (f : F →+* K)
    (s : Finset ι) (v r : ι → F) :
    (Lagrange.interpolate s v r).map f =
      Lagrange.interpolate s (fun i => f (v i)) (fun i => f (r i)) := by
  simp [Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.map_sum, Polynomial.map_prod]

end LagrangeBounds

namespace PeriodicCoefficients

 

theorem denominator (s T : ℕ) (hT : 0<T) :
    ∃ D : ℤ, D≠0 ∧ ∀ P : ℝ[X], P.natDegree ≤ s →
      (∀ k : ℕ, ∃ z : ℤ, P.eval ((T:ℝ)*k)-P.eval 0=z) →
      ∀ j : ℕ, 0<j → ∃ z : ℤ, (D:ℝ)*P.coeff j=z := by
  classical
  let nodes : Fin (s+1) → ℚ := fun i => (T:ℚ)*i.val
  obtain ⟨D,hD,hd⟩ := LagrangeBounds.interpolation_common_denominator Finset.univ nodes
  refine ⟨D,hD,?_⟩
  intro P hP hv
  let R := P-C (P.eval 0)
  have hR : R.natDegree ≤ s := by
    exact (natDegree_sub_le P (C (P.eval 0))).trans (max_le hP (by simp))
  let m : Fin (s+1) → ℤ := fun i => (hv i.val).choose
  have hm (i : Fin (s+1)) : R.eval ((T:ℝ)*i.val)=(m i:ℝ) := by
    simpa [R,m] using (hv i.val).choose_spec
  have hinj : Function.Injective (fun i : Fin (s+1) => (T:ℝ)*i.val) := by
    intro i k he
    apply Fin.ext
    exact_mod_cast (mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hT : (T:ℝ)≠0) he)
  have hdeg : R.degree < ((Finset.univ : Finset (Fin (s+1))).card:WithBot ℕ) := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact (degree_le_natDegree (p:=R)).trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hR))
  have he : R=Lagrange.interpolate Finset.univ (fun i : Fin (s+1) => (T:ℝ)*i.val) (fun i => (m i:ℝ)) := by
    simpa only [hm] using (Lagrange.eq_interpolate hinj.injOn hdeg)
  obtain ⟨U,hU⟩ := (mem_lifts _).mp (hd m)
  have hh := congrArg (fun q : ℚ[X] => q.map (Rat.castHom ℝ)) hU
  have hhom : (Rat.castHom ℝ).comp (algebraMap ℤ ℚ)=Int.castRingHom ℝ := by ext; simp
  have hh' : U.map (Int.castRingHom ℝ)=C (D:ℝ)*R := by
    simpa only [Polynomial.map_map,hhom,Polynomial.map_mul,Polynomial.map_C,LagrangeBounds.map_interpolate,
      Rat.coe_castHom,Rat.cast_intCast,nodes,Rat.cast_mul,Rat.cast_natCast,← he] using hh
  intro j hj
  refine ⟨U.coeff j,?_⟩
  have hc := congrArg (fun q : ℝ[X] => q.coeff j) hh'
  simpa [R,coeff_sub,coeff_C,show j≠0 by omega] using hc.symm

end PeriodicCoefficients
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
namespace SmoothCharacterCoefficients
open RationalLattice DensePolynomialInterpolation

 

theorem interval_coefficients (s N : ℕ) (hN : 2*(s+1) ≤ N)
    (B : ℝ) (hB : 0 ≤ B) (P : ℝ[X]) (hP : P.natDegree ≤ s)
    (hb : ∀ z : ℤ, |(z:ℝ)| ≤ N → |P.eval (z:ℝ)| ≤ B) :
    ∀ j : ℕ, |P.coeff j| ≤ coefficientConstant s * uniformBound s 1 * B/(N:ℝ)^j := by
  classical
  let E : Finset ℤ := (range N).image (fun k : ℕ => (k:ℤ))
  have hcard : E.card=N := by
    rw [Finset.card_image_of_injective _ (Nat.cast_injective : Function.Injective (fun k : ℕ => (k:ℤ))),Finset.card_range]
  have hNp : 0<N := by omega
  have hEN : ∀ z∈E, (z:ℝ)∈Set.Icc 0 (N:ℝ) := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
    rw [Int.cast_natCast]
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (mem_range.mp hk).le⟩
  intro j
  by_cases hj : j ≤ s
  · apply dense_coefficient_bound s N hNp 1 B (by norm_num) hB E
      (by rwa [hcard]) (by simp [hcard]) hEN P hP
    intro z hz
    apply hb z
    rw [abs_of_nonneg (hEN z hz).1]
    exact (hEN z hz).2
    exact hj
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP (by omega)),abs_zero]
    have hU : 0 ≤ uniformBound s 1 := by dsimp [uniformBound]; positivity
    exact div_nonneg (mul_nonneg (mul_nonneg (coefficientConstant_pos s).le hU) hB) (by positivity)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {m : ℕ}

 

omit [IsTopologicalGroup G] in
theorem coordinate_character_bound (c : RealCoordinates G m)
    (χ : G →* Multiplicative ℝ) (hχ : Continuous χ) (B : ℝ) :
    ∃ A : ℝ, 0<A ∧ ∀ g : G, ‖c.coord g‖ ≤ B → |(χ g).toAdd| ≤ A := by
  let K := c.coord.symm '' Metric.closedBall (0 : Fin m → ℝ) B
  have hK : IsCompact K := (isCompact_closedBall _ _).image c.coord.symm.continuous
  have hc : Continuous (fun g : G => (χ g).toAdd) := hχ
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|A|+1,by positivity,?_⟩
  intro g hg
  have hm : g∈K := ⟨c.coord g,by simpa only [Metric.mem_closedBall,dist_zero_right] using hg,c.coord.symm_apply_apply g⟩
  have hh := hA g hm
  rw [Real.norm_eq_abs] at hh
  exact hh.trans ((le_abs_self A).trans (by linarith))

end SmoothCharacterCoefficients
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
namespace FactorCoefficientTransfer
open DensePolynomialInterpolation

 

theorem factorized_coefficients (s T : ℕ) (hT : 0<T)
    (A B M : ℝ) (hA : 0≤A) (hB : 0≤B) (hM : 1≤M) :
    ∃ q : ℤ, q≠0 ∧ ∃ C : ℝ, 0<C ∧ ∀ N K : ℕ, 2*(s+1) ≤ N → 0<K →
      (N:ℝ) ≤ M*K → ∀ r : ℤ, 0≤r → (r:ℝ) ≤ N →
      ∀ P E Q W : ℝ[X], E.natDegree ≤ s → Q.natDegree ≤ s → W.natDegree ≤ s →
      P=E+Q+W →
      (∀ z : ℤ, |(z:ℝ)| ≤ N → |E.eval (z:ℝ)| ≤ B) →
      (∀ k : ℕ, ∃ z : ℤ, W.eval ((T:ℝ)*k)-W.eval 0=z) →
      (∀ j : ℕ, 0<j → ∃ z : ℤ,
        |(Q.comp (Polynomial.C (T:ℝ)*X+Polynomial.C (r:ℝ))).coeff j-z| ≤ A/(K:ℝ)^j) →
      ∀ j : ℕ, 0<j → ∃ z : ℤ, |(q:ℝ)*P.coeff j-z| ≤ C/(N:ℝ)^j := by
  obtain ⟨D,hD,hden⟩ := PeriodicCoefficients.denominator s T hT
  let R := coefficientConstant s*((s+1:ℝ)*A*M^s)
  let S := coefficientConstant s*uniformBound s 1*B
  let C₀ := |(D:ℝ)| *(T:ℝ)^s*(R+S)
  have hR : 0≤R := mul_nonneg (coefficientConstant_pos s).le (by positivity)
  have hS : 0≤S := by
    have hU : 0≤uniformBound s 1 := by dsimp [uniformBound]; positivity
    exact mul_nonneg (mul_nonneg (coefficientConstant_pos s).le hU) hB
  have hC : 0≤C₀ := by dsimp only [C₀]; positivity
  refine ⟨D*(T:ℤ)^s,mul_ne_zero hD (pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hT)),
    C₀+1,by positivity,?_⟩
  intro N K hN hK hNK r hr hrN P E Q W hE hQ hW hP hEb hWb hQc j hj
  have hNp : 0<N := by omega
  obtain ⟨z,hz⟩ := AffineCoefficientTransfer.progression_coefficients s T N K hT hNp hK r hr hrN
    A M hA hM hNK Q hQ hQc j hj
  obtain ⟨w,hw⟩ := hden W hW hWb j hj
  have he := SmoothCharacterCoefficients.interval_coefficients s N hN B hB E hE hEb j
  refine ⟨D*z+(T:ℤ)^s*w,?_⟩
  have hid : ((D*(T:ℤ)^s:ℤ):ℝ)*P.coeff j-((D*z+(T:ℤ)^s*w:ℤ):ℝ)=
      (D:ℝ)*((T:ℝ)^s*Q.coeff j-z)+(D:ℝ)*(T:ℝ)^s*E.coeff j := by
    rw [hP,coeff_add,coeff_add]
    push_cast
    calc
      _ = (D:ℝ)*((T:ℝ)^s*Q.coeff j-z)+(D:ℝ)*(T:ℝ)^s*E.coeff j+
          (T:ℝ)^s*((D:ℝ)*W.coeff j-w) := by ring
      _ = _ := by rw [hw]; ring
  rw [hid]
  calc
    _ ≤ |(D:ℝ)*((T:ℝ)^s*Q.coeff j-z)|+|(D:ℝ)*(T:ℝ)^s*E.coeff j| := abs_add_le _ _
    _ = |(D:ℝ)| *|(T:ℝ)^s*Q.coeff j-z|+(|(D:ℝ)| *(T:ℝ)^s)*|E.coeff j| := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(T:ℝ)^s)]
    _ ≤ |(D:ℝ)| *((T:ℝ)^s*coefficientConstant s*((s+1:ℝ)*A*M^s)/(N:ℝ)^j)+
          (|(D:ℝ)| *(T:ℝ)^s)*(S/(N:ℝ)^j) :=
      add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg _))
        (mul_le_mul_of_nonneg_left he (by positivity))
    _ = C₀/(N:ℝ)^j := by dsimp only [C₀,R,S]; ring
    _ ≤ (C₀+1)/(N:ℝ)^j := div_le_div_of_nonneg_right (by linarith) (by positivity)

end FactorCoefficientTransfer
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace FactorCoefficientTransfer
open CubeFaces CubePolynomials RationalLattice LeibmanSquare

lemma eq_of_int_evals (P Q : ℝ[X]) (h : ∀ z : ℤ, P.eval (z:ℝ)=Q.eval (z:ℝ)) : P=Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Int.cast_injective : Function.Injective (fun z : ℤ => (z:ℝ)))).mono
  rintro x ⟨z,rfl⟩
  exact h z

variable {G : Type*} [Group G]

lemma periodic_character_values (Γ : Subgroup G) (χ : G →* Multiplicative ℝ)
    (hint : ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z)
    (T : ℕ) (b : ℤ → G)
    (hp : Function.Periodic (fun z => (QuotientGroup.mk (b z) : G⧸Γ)) (T:ℤ))
    (P : ℝ[X]) (he : ∀ z : ℤ, P.eval (z:ℝ)=(χ (b z)).toAdd) :
    ∀ k : ℕ, ∃ z : ℤ, P.eval ((T:ℝ)*k)-P.eval 0=z := by
  intro k
  have hq : (QuotientGroup.mk (b ((T:ℤ)*k)) : G⧸Γ)=QuotientGroup.mk (b 0) := by
    simpa only [zero_add,nsmul_eq_mul,mul_comm] using (hp.nat_mul k) 0
  have hg : (b 0)⁻¹*b ((T:ℤ)*k)∈Γ := QuotientGroup.eq.mp hq.symm
  obtain ⟨z,hz⟩ := hint _ hg
  refine ⟨z,?_⟩
  have he1 := he ((T:ℤ)*k)
  have he0 := he 0
  simp only [Int.cast_mul,Int.cast_natCast] at he1
  simp only [Int.cast_zero] at he0
  rw [he1,he0]
  simpa only [map_mul,map_inv,toAdd_mul,toAdd_inv,sub_eq_add_neg,add_comm] using hz

variable [TopologicalSpace G] [IsTopologicalGroup G]

 

omit [IsTopologicalGroup G] in
theorem uniform_character_transfer (H : Filtration G) (_h0 : H.level 0=⊤)
    (Γ : Subgroup G) {m : ℕ} (c : RealCoordinates (H.level 2) m)
    (s : ℕ) (hs : H.level (s+1)=⊥) (T : ℕ) (hT : 0<T)
    (χ : G →* Multiplicative ℝ) (hχ : Continuous χ)
    (hint : ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z)
    (A B M : ℝ) (hA : 0≤A) (hM : 1≤M) :
    ∃ q : ℤ, q≠0 ∧ ∃ C : ℝ, 0<C ∧ ∀ N K : ℕ, 2*(s+1) ≤ N → 0<K →
      (N:ℝ) ≤ M*K → ∀ r : ℤ, 0≤r → (r:ℝ) ≤ N →
      ∀ f f' : ℤ → G, ∀ e b : ℤ → H.level 2,
      Polynomial H 0 f → Polynomial H 0 (fun z => (e z).val) →
      Polynomial H 0 (fun z => (b z).val) →
      (∀ z, f z=(e z).val*f' z*(b z).val) →
      Function.Periodic (fun z => (QuotientGroup.mk (b z).val : G⧸Γ)) (T:ℤ) →
      (∀ z : ℤ, |(z:ℝ)| ≤ N → ‖c.coord (e z)‖ ≤ B) →
      ∀ v : G, ∀ R : ℝ[X],
      (∀ z : ℤ, R.eval (z:ℝ)=(χ (v⁻¹*f' ((T:ℤ)*z+r)*v)).toAdd) →
      (∀ j : ℕ, 0<j → ∃ z : ℤ, |R.coeff j-z| ≤ A/(K:ℝ)^j) →
      ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
        ∀ j : ℕ, 0<j → ∃ z : ℤ, |(q:ℝ)*P.coeff j-z| ≤ C/(N:ℝ)^j := by
  obtain ⟨Bχ,hBχ,hbound⟩ := SmoothCharacterCoefficients.coordinate_character_bound c
    (χ.comp (H.level 2).subtype) (hχ.comp continuous_subtype_val) B
  obtain ⟨q,hq,C,hC,htransfer⟩ := factorized_coefficients s T hT A Bχ M hA hBχ.le hM
  refine ⟨q,hq,C,hC,?_⟩
  intro N K hN hK hNK r hr hrN f f' e b hf hep hbp hfac hper hB v R hRe hRc
  obtain ⟨P,hP,hPe⟩ := character_polynomial H s hs hf χ
  obtain ⟨E,hE,hEe⟩ := character_polynomial H s hs hep χ
  obtain ⟨W,hW,hWe⟩ := character_polynomial H s hs hbp χ
  let Q := P-E-W
  have hQ : Q.natDegree ≤ s :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le hP hE)) hW)
  have hsum : P=E+Q+W := by dsimp only [Q]; ring
  have hQe (z : ℤ) : Q.eval (z:ℝ)=(χ (f' z)).toAdd := by
    simp only [Q,eval_sub,hPe,hEe,hWe,hfac,map_mul,toAdd_mul]
    ring
  have hQR : Q.comp (Polynomial.C (T:ℝ)*X+Polynomial.C (r:ℝ))=R := by
    apply eq_of_int_evals
    intro z
    rw [eval_comp]
    have ha : (Polynomial.C (T:ℝ)*X+Polynomial.C (r:ℝ)).eval (z:ℝ)=(((T:ℤ)*z+r:ℤ):ℝ) := by simp
    rw [ha,hQe,hRe]
    simp only [map_mul,map_inv,toAdd_mul,toAdd_inv]
    ring
  refine ⟨P,hP,hPe,htransfer N K hN hK hNK r hr hrN P E Q W hE hQ hW hsum ?_ ?_ ?_⟩
  · intro z hz
    rw [hEe]
    exact hbound (e z) (hB z hz)
  · exact periodic_character_values Γ χ hint T (fun z => (b z).val) hper W hWe
  · simpa only [hQR] using hRc

end FactorCoefficientTransfer

end
end
end
end
end

end OAI
