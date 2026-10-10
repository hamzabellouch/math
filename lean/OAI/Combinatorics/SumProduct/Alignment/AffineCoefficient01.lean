import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.DensePolynomial01
import OAI.Combinatorics.SumProduct.Alignment.FiniteCover01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace FiniteCoverObservable
open MeasureTheory
variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MulAction G X] [ContinuousSMul G X]

 

omit [IsTopologicalGroup G] in
theorem finite_unit_cover_tests (q : C(Y,X)) (C : Set G) (hC : IsCompact C)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SMulInvariantMeasure G X μ] (hmap : Measure.map q ν=μ)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ S : Finset C(Y,ℂ), (∀ F∈S, LipschitzWith 1 F ∧ ‖F‖ ≤ 1) ∧
      ∃ η : ℝ, 0<η ∧ ∀ N : ℕ, 0<N → ∀ y : ℕ → Y, ∀ g∈C,
      ∀ F : C(X,ℂ), LipschitzWith 1 F → ‖F‖ ≤ 1 →
        δ ≤ ‖(𝔼 n∈Finset.range N, F (g • q (y n)))-(∫ x, F x ∂μ)‖ →
        ∃ φ∈S, η ≤ ‖FourierObstruction.discrepancy ν N y φ‖ := by
  obtain ⟨K,hK,hunit⟩ := compact_translated_family q C hC
  obtain ⟨S,hS,η,hη,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction K hK δ 2 hδ (by norm_num)
  refine ⟨S,hS,η,hη,?_⟩
  intro N hN y g hg F hFL hFn hdisc
  apply htest (FourierObstruction.discrepancy ν N y)
    (FourierObstruction.discrepancy_bound ν N hN y)
  refine ⟨translated q g F,hunit g hg F hFL hFn,?_⟩
  change δ ≤ ‖(𝔼 n∈Finset.range N, translated q g F (y n)) - _‖
  rw [integral_translated q μ ν hmap]
  exact hdisc

end FiniteCoverObservable
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace FactorProgression
open CubeFaces CubePolynomials RationalLattice ProgressionPartition MeasureTheory

lemma mean_sum_obstruction {N : ℕ} (hN : 0<N) (f : ℕ → ℂ) (μ : ℂ) (δ : ℝ) :
    δ ≤ ‖(𝔼 i∈Finset.range N, f i)-μ‖ ↔
      δ*N ≤ ‖∑ i∈Finset.range N, (f i-μ)‖ := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hNc : (N:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (∑ i∈Finset.range N, (f i-μ))=
      (N:ℂ)*((𝔼 i∈Finset.range N, f i)-μ) := by
    simp only [Finset.expect_eq_sum_div_card,Finset.card_range,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  rw [he,norm_mul,Complex.norm_natCast,mul_comm δ]
  exact (mul_le_mul_iff_right₀ hNr).symm

variable {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (Γ : Subgroup G) {m : ℕ} (c : RealCoordinates (H.level 2) m)
variable [mtr : MetricSpace (G⧸Γ)]
local instance metricCoverOriginalTopology : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace
variable [hcpt : CompactSpace (G⧸Γ)] [hcsm : ContinuousSMul G (G⧸Γ)]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

include hcpt hcsm in
 

theorem factor_cover_obstruction
    (q : C(Y,G⧸Γ)) (lift : G → Y) (hq : ∀ g, q (lift g)=QuotientGroup.mk g)
    (μ : Measure (G⧸Γ)) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SMulInvariantMeasure G (G⧸Γ) μ] (hmap : Measure.map q ν=μ)
    (C : Set G) (hCc : IsCompact C)
    (hC : ∀ g : G, ∃ v∈C, (QuotientGroup.mk g : G⧸Γ)=QuotientGroup.mk v)
    (B δ : ℝ) (hB : 0<B) (hδ : 0<δ) (Tmax : ℕ) (hTmax : 0<Tmax) :
    ∃ J : ℕ, 0<J ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∃ S : Finset C(Y,ℂ), (∀ F∈S, LipschitzWith 1 F ∧ ‖F‖ ≤ 1) ∧
      ∃ η : ℝ, 0<η ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ, 0<T → T ≤ Tmax →
      ∀ (L : Filtration G), L.level 0=⊤ →
      ∀ (f f' : ℤ → G) (e b : ℤ → H.level 2),
      f'∈polynomials L 0 → (∀ z, f z=(e z).val*f' z*(b z).val) →
      Function.Periodic (fun z => (QuotientGroup.mk (b z).val : G⧸Γ)) (T:ℤ) →
      (∀ z : ℤ, |(z:ℝ)| ≤ N → ‖c.coord (e z)‖ ≤ B) →
      (∀ z w : ℤ, |(z:ℝ)| ≤ N → |(w:ℝ)| ≤ N →
        ‖c.coord (e z*(e w)⁻¹)‖ ≤ (B/N)*|(z:ℝ)-(w:ℝ)|) →
      ∀ F : C(G⧸Γ,ℂ), LipschitzWith 1 F → ‖F‖ ≤ 1 →
      δ ≤ ‖FourierObstruction.discrepancy μ N (fun n => QuotientGroup.mk (f n)) F‖ →
      let K : ℕ := N/(J*T)
      0<K ∧ N ≤ 2*J*Tmax*K ∧
      ∃ w : ℕ, w<N ∧ ∃ v∈C,
        (fun z : ℤ => v⁻¹*f' ((T:ℤ)*z+w)*v)∈polynomials L 0 ∧
        ∃ Φ∈S, η ≤ ‖FourierObstruction.discrepancy ν K
          (fun n => lift (v⁻¹*f' ((T:ℤ)*n+w)*v)) Φ‖ := by
  classical
  let D : Set G := (fun p : (H.level 2) × G => p.1.val*p.2) ''
    ((c.coord.symm '' Metric.closedBall (0 : Fin m → ℝ) B) ×ˢ C)
  have hD : IsCompact D := by
    apply IsCompact.image
    exact ((isCompact_closedBall (0 : Fin m → ℝ) B).image c.coord.symm.continuous).prod hCc
    fun_prop
  obtain ⟨S,hS,η,hη,htest⟩ := FiniteCoverObservable.finite_unit_cover_tests q D hD μ ν hmap (δ/4) (by positivity)
  obtain ⟨J,hJ,N₀,hN₀,hprog⟩ := factor_progression_obstruction H Γ c B δ hB hδ Tmax hTmax
  refine ⟨J,hJ,N₀,hN₀,S,hS,η,hη,?_⟩
  intro N hN T hT hTT L hL f f' e b hfp hfac hper hev hed F hFL hFn hdisc
  have hn : 0<N := hN₀.trans_le hN
  have hμ : ‖∫ x, F x ∂μ‖ ≤ 1 := by
    simpa only [probReal_univ,mul_one] using (norm_integral_le_of_norm_le_const
      (μ:=μ) (Filter.Eventually.of_forall (fun x => (F.norm_coe_le_norm x).trans hFn)))
  have hd : δ*N ≤ ‖∑ i∈Finset.range N, (F (QuotientGroup.mk (f i))-(∫ x, F x ∂μ))‖ :=
    (mean_sum_obstruction hn _ _ δ).mp hdisc
  obtain ⟨hK,hKT,hcomp,a,ha,r,hr,v,hv,hev0,hpp,hob⟩ :=
    hprog N hN T hT hTT C hC L hL f f' e b hfp hfac hper hev hed F hFL hFn _ hμ hd
  let K := N/(J*T)
  change 0<K at hK
  change J*K*T ≤ N at hKT
  refine ⟨hK,hcomp,a*K*T+r,?_,v,hv,hpp,?_⟩
  · have hw : a*K*T+r < J*K*T := by
      simpa using cell_lt (a:=a) (n:=0) ha hK hr
    exact hw.trans_le hKT
  · have hDv : (e ((a*K*T+r:ℕ):ℤ)).val*v ∈ D := by
      refine ⟨(e ((a*K*T+r:ℕ):ℤ),v),⟨?_,hv⟩,rfl⟩
      exact ⟨c.coord (e ((a*K*T+r:ℕ):ℤ)),by simpa only [Metric.mem_closedBall,dist_zero_right] using hev0,c.coord.symm_apply_apply _⟩
    apply htest K hK (fun n => lift (v⁻¹*f' ((T:ℤ)*n+(a*K*T+r:ℕ))*v)) _ hDv F hFL hFn
    have hh := (mean_sum_obstruction hK _ _ (δ/4)).mpr hob
    convert hh using 2
    apply congrArg (fun z : ℂ => z-(∫ x, F x ∂μ))
    apply Finset.expect_congr rfl
    intro n hn
    rw [hq]
    simp only [K]
    congr 5; push_cast; ring_nf

end FactorProgression
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace AffineCoefficientTransfer
open DensePolynomialInterpolation

 

theorem integer_pullback (s T : ℕ) (hT : 0<T) (r : ℤ)
    (U : ℤ[X]) (hU : U.natDegree ≤ s) :
    ∃ V : ℤ[X], V.map (Int.castRingHom ℝ) =
      C ((T:ℝ)^s) * (U.map (Int.castRingHom ℝ)).comp
        (C ((T:ℝ)⁻¹)*X-C ((r:ℝ)/(T:ℝ))) := by
  let V : ℤ[X] := C ((T:ℤ)^(s-U.natDegree)) * (U.scaleRoots (T:ℤ)).taylor (-r)
  refine ⟨V, Polynomial.funext fun x => ?_⟩
  have hTn : (T:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hT
  simp only [V,Polynomial.map_mul,Polynomial.map_C,map_taylor,eval_mul,eval_C,
    taylor_eval,Int.cast_pow,Int.cast_natCast,Int.cast_neg,Int.coe_castRingHom,
    eval_comp,eval_sub,eval_X]
  rw [eval_map]
  have hx : x+ -(r:ℝ)=(T:ℝ)*((T:ℝ)⁻¹*x-(r:ℝ)/(T:ℝ)) := by field_simp; ring
  have hscale := scaleRoots_eval₂_mul (p:=U) (Int.castRingHom ℝ) ((T:ℝ)⁻¹*x-(r:ℝ)/(T:ℝ)) (T:ℤ)
  simp only [Int.coe_castRingHom,Int.cast_natCast] at hscale
  rw [hx,hscale]
  rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hU,eval_map]

 

theorem eval_bound (s : ℕ) (R : ℝ[X]) (hR : R.natDegree ≤ s)
    (A K M : ℝ) (hA : 0 ≤ A) (hK : 0<K) (hM : 1 ≤ M)
    (hc : ∀ j : ℕ, |R.coeff j| ≤ A/K^j)
    (x : ℝ) (hx : |x| ≤ M*K) :
    |R.eval x| ≤ (s+1:ℝ)*A*M^s := by
  rw [R.eval_eq_sum_range' (by omega : R.natDegree<s+1)]
  calc
    _ ≤ ∑ j∈range (s+1), |R.coeff j*x^j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈range (s+1), A*M^s := by
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ s := by have := mem_range.mp hj; omega
      rw [abs_mul,abs_pow]
      calc
        _ ≤ (A/K^j)*(M*K)^j := mul_le_mul (hc j) (pow_le_pow_left₀ (abs_nonneg _) hx j)
          (by positivity) (by positivity)
        _ = A*M^j := by rw [mul_pow]; field_simp
        _ ≤ A*M^s := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM hjle) hA
    _ = (s+1:ℝ)*A*M^s := by simp [Nat.cast_add,Nat.cast_one]; ring

end AffineCoefficientTransfer
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace AffineCoefficientTransfer
open DensePolynomialInterpolation PolynomialIntegralResidual

 

theorem progression_coefficients (s T N K : ℕ) (hT : 0<T) (hN : 0<N) (hK : 0<K)
    (r : ℤ) (hr : 0≤r) (hrN : (r:ℝ) ≤ N)
    (A M : ℝ) (hA : 0≤A) (hM : 1≤M) (hNK : (N:ℝ) ≤ M*K)
    (P : ℝ[X]) (hP : P.natDegree ≤ s)
    (hc : ∀ j : ℕ, 0<j → ∃ z : ℤ,
      |(P.comp (C (T:ℝ)*X+C (r:ℝ))).coeff j-z| ≤ A/(K:ℝ)^j) :
    ∀ j : ℕ, 0<j → ∃ z : ℤ,
      |(T:ℝ)^s*P.coeff j-z| ≤
        (T:ℝ)^s*coefficientConstant s*((s+1:ℝ)*A*M^s)/(N:ℝ)^j := by
  classical
  let Q := P.comp (C (T:ℝ)*X+C (r:ℝ))
  let m : ℕ → ℤ := fun j => if h : 0<j then (hc j h).choose else 0
  let U := integerPart s m
  let R := Q-U.map (Int.castRingHom ℝ)-C (Q.coeff 0)
  let invA : ℝ[X] := C ((T:ℝ)⁻¹)*X-C ((r:ℝ)/(T:ℝ))
  let E := R.comp invA
  have hTi : (T:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hT
  have hNi : (0:ℝ)<N := by exact_mod_cast hN
  have hKi : (0:ℝ)<K := by exact_mod_cast hK
  have hU : U.natDegree ≤ s := integerPart_degree s m
  have hxdeg (z : ℝ) : (C z*X : ℝ[X]).natDegree ≤ 1 :=
    natDegree_mul_le.trans (by simp)
  have hQ : Q.natDegree ≤ s := by
    apply natDegree_comp_le.trans
    have he : (C (T:ℝ)*X+C (r:ℝ)).natDegree ≤ 1 := by
      exact (natDegree_add_le _ _).trans (max_le (hxdeg _) (by simp))
    exact (Nat.mul_le_mul_left _ he).trans (by simpa using hP)
  have hR : R.natDegree ≤ s := by
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le hQ (natDegree_map_le.trans hU))) (by simp))
  have hE : E.natDegree ≤ s := by
    apply natDegree_comp_le.trans
    have he : invA.natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (max_le (hxdeg _) (by simp))
    exact (Nat.mul_le_mul_left _ he).trans (by simpa using hR)
  have hRc : ∀ j : ℕ, |R.coeff j| ≤ A/(K:ℝ)^j := by
    intro j
    by_cases hj : j ≤ s
    · by_cases hj0 : j = 0
      · subst j
        have hm0 : m 0=0 := by simp [m]
        simp [R,coeff_sub,coeff_map,integerPart_coeff s m 0 (Nat.zero_le s),U,hm0,hA]
      · have hpj : 0<j := Nat.pos_iff_ne_zero.mpr hj0
        simpa only [R,coeff_sub,coeff_map,U,integerPart_coeff s m j hj,coeff_C,ite_eq_right hj0,sub_zero,m,dite_eq_left hpj,Int.coe_castRingHom,Q]
          using (hc j hpj).choose_spec
    · rw [coeff_eq_zero_of_natDegree_lt (hR.trans_lt (by omega)),abs_zero]
      positivity
  have hEv : ∀ x∈Set.Icc 0 (N:ℝ), |E.eval x| ≤ (s+1:ℝ)*A*M^s := by
    intro x hx
    simp only [E,eval_comp,invA,eval_sub,eval_mul,eval_C,eval_X]
    apply AffineCoefficientTransfer.eval_bound s R hR A K M hA hKi hM hRc
    have hrr : (0:ℝ)≤r := by exact_mod_cast hr
    have ht : (1:ℝ)≤T := by exact_mod_cast hT
    have he : (T:ℝ)⁻¹*x-(r:ℝ)/(T:ℝ)=(x-r)/T := by ring
    rw [he,abs_div,abs_of_pos (show (0:ℝ)<T from Nat.cast_pos.mpr hT)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hT)).mpr
    have hab : |x-r| ≤ N := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    exact hab.trans (hNK.trans (le_mul_of_one_le_right (by positivity) ht))
  obtain ⟨V,hV⟩ := integer_pullback s T hT r U hU
  have hcomp : Q.comp invA=P := by
    apply Polynomial.funext
    intro x
    simp only [Q,invA,eval_comp,eval_add,eval_mul,eval_C,eval_X,eval_sub]
    congr 1
    field_simp
    ring
  have hid : C ((T:ℝ)^s)*P-V.map (Int.castRingHom ℝ)-C ((T:ℝ)^s*Q.coeff 0) =
      C ((T:ℝ)^s)*E := by
    dsimp only [E,R]
    rw [sub_comp,sub_comp,hcomp,C_comp,hV]
    rw [C_mul]
    dsimp only [invA]
    ring
  intro j hj
  refine ⟨V.coeff j,?_⟩
  have hec := congrArg (fun p : ℝ[X] => p.coeff j) hid
  simp only [coeff_sub,coeff_C_mul,coeff_map,coeff_C,ite_eq_right (Nat.ne_of_gt hj),sub_zero,Int.coe_castRingHom] at hec
  rw [hec,abs_mul,abs_of_nonneg (by positivity : 0≤(T:ℝ)^s)]
  by_cases hjs : j ≤ s
  · have hh := coefficient_bound_span s E hE N ((s+1:ℝ)*A*M^s) hNi (by positivity) hEv j hjs
    calc
      _ ≤ (T:ℝ)^s*(coefficientConstant s*((s+1:ℝ)*A*M^s)/(N:ℝ)^j) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  · rw [coeff_eq_zero_of_natDegree_lt (hE.trans_lt (by omega)),abs_zero,mul_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (coefficientConstant_pos s).le) (by positivity)) (by positivity)

end AffineCoefficientTransfer

end
end
end
end
end

end OAI
