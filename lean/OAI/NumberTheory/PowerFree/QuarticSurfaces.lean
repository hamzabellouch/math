import OAI.NumberTheory.PowerFree.TwoPoles

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators Classical
open MvPolynomial

theorem twoPole_hilbert_lower {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (r₀ r₁ θ₀ θ₁ : K) (hr : r₀ ≠ r₁)
    (t q b₀ b₁ u₀ : MvPolynomial σ K ⧸ I)
    (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t)))
    (h₀ : (t-algebraMap K _ r₀)^2*b₀=q-algebraMap K _ θ₀)
    (h₁ : (t-algebraMap K _ r₁)^2*b₁=q-algebraMap K _ θ₁)
    (hu₀ : (t-algebraMap K _ r₀)^2*u₀=1)
    (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ht : t ∈ weightedFunctions I ω U) (hb₀ : b₀ ∈ weightedFunctions I ω V)
    (hb₁ : b₁ ∈ weightedFunctions I ω V) (huw : u₀ ∈ weightedFunctions I ω V) :
    ∀ T : ℝ, 0 ≤ T → ((V+4*U)/(2*U*V^2))*T^2-
      ((V+4*U)*(U+V)/(U*V^2))*T ≤ weightedHilbert I ω T := by
  intro T hT0
  by_cases hT : U ≤ T
  · let M := ⌊(T-U)/V⌋₊
    let N := fun m : Fin (M+1) => ⌊(T-V*m.val)/U⌋₊+1
    let ι := Σ m : Fin (M+1), Fin (N m) ⊕ ((Fin m.val × Fin 2) ⊕ (Fin (M-m.val) × Fin 2))
    let v : ι → MvPolynomial σ K ⧸ I := fun i =>
      twoPoleFunction t (t-algebraMap K _ r₀) (t-algebraMap K _ r₁) b₀ b₁ u₀ M i.1.val (N i.1) i.2
    have hM : V*(M:ℝ) ≤ T-U := by
      have hh := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) hV.le)
      simpa only [mul_comm] using (le_div_iff₀ hV).mp hh
    have ht₀ : t-algebraMap K _ r₀ ∈ weightedFunctions I ω U :=
      (weightedFunctions I ω U).sub_mem ht (weightedFunctions_algebraMap I ω hω hU.le r₀)
    have ht₁ : t-algebraMap K _ r₁ ∈ weightedFunctions I ω U :=
      (weightedFunctions I ω U).sub_mem ht (weightedFunctions_algebraMap I ω hω hU.le r₁)
    have hv (i : ι) : v i ∈ weightedFunctions I ω T := by
      obtain ⟨m,j⟩ := i
      have hm : (m.val:ℝ) ≤ M := by exact_mod_cast (show m.val ≤ M by omega)
      cases j with
      | inl j =>
        apply weightedFunctions_mono I ω hω _ (weightedFunctions_mul I ω hω
          (weightedFunctions_pow I ω hω ht j.val) (weightedFunctions_pow I ω hω hb₀ m.val))
        have hn : 0 ≤ T-V*m.val := by nlinarith
        have hj : (j.val:ℝ) ≤ ⌊(T-V*m.val)/U⌋₊ := by
          exact_mod_cast (show j.val ≤ ⌊(T-V*m.val)/U⌋₊ by have := j.isLt; dsimp [N] at this; omega)
        have hf := hj.trans (Nat.floor_le (div_nonneg hn hU.le))
        have hh := (le_div_iff₀ hU).mp hf
        nlinarith
      | inr j =>
        cases j with
        | inl j =>
          apply weightedFunctions_mono I ω hω _ (weightedFunctions_mul I ω hω
            (weightedFunctions_mul I ω hω (weightedFunctions_pow I ω hω hb₀ (m.val-(j.1.val+1)))
              (weightedFunctions_pow I ω hω hb₁ (j.1.val+1))) (weightedFunctions_pow I ω hω ht₁ j.2.val))
          have hj : j.1.val+1 ≤ m.val := by omega
          rw [Nat.cast_sub hj]
          have he : (j.2.val:ℝ) ≤ 1 := by exact_mod_cast (show j.2.val ≤ 1 by omega)
          nlinarith [mul_le_mul_of_nonneg_left hm hV.le,mul_le_mul_of_nonneg_left he hU.le]
        | inr j =>
          apply weightedFunctions_mono I ω hω _ (weightedFunctions_mul I ω hω
            (weightedFunctions_mul I ω hω (weightedFunctions_pow I ω hω hb₀ m.val)
              (weightedFunctions_pow I ω hω huw (j.1.val+1))) (weightedFunctions_pow I ω hω ht₀ j.2.val))
          have hj : ((j.1.val+1:ℕ):ℝ) ≤ (M:ℝ)-m.val := by
            rw [←Nat.cast_sub (by omega : m.val ≤ M)]
            exact_mod_cast (show j.1.val+1 ≤ M-m.val by omega)
          have he : (j.2.val:ℝ) ≤ 1 := by exact_mod_cast (show j.2.val ≤ 1 by omega)
          nlinarith [mul_le_mul_of_nonneg_left hj hV.le,mul_le_mul_of_nonneg_left he hU.le]
    have hi' : LinearIndependent K v := twoPole_functions_independent r₀ r₁ θ₀ θ₁ hr t q b₀ b₁ u₀ hi h₀ h₁ hu₀ M N
    let u : ι → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
    have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype hi'
    have hcard : (Fintype.card ι:ℝ) ≤ weightedHilbert I ω T := by
      exact_mod_cast hu.fintype_card_le_finrank
    have hce : (Fintype.card ι:ℝ) = (∑ m : Fin (M+1), (N m:ℝ))+2*(M:ℝ)*(M+1) := by
      simp only [ι,Fintype.card_sigma,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,
        Nat.cast_sum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      have he (m : Fin (M+1)) : (N m:ℝ)+((m.val:ℝ)*2+((M-m.val:ℕ):ℝ)*2) = (N m:ℝ)+2*(M:ℝ) := by
        rw [Nat.cast_sub (by omega : m.val ≤ M)]
        ring
      simp_rw [he,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      ring
    rw [hce] at hcard
    exact (pole_family_count_lower U V T hU hV hT).trans hcard
  · have hc : 0 < (V+4*U)/(2*U*V^2) := by positivity
    have he : (V+4*U)*(U+V)/(U*V^2) = ((V+4*U)/(2*U*V^2))*(2*(U+V)) := by ring
    rw [he]
    have hh : ((V+4*U)/(2*U*V^2))*T^2-
        ((V+4*U)/(2*U*V^2))*(2*(U+V))*T ≤ 0 := by
      have hsmall : T ≤ 2*(U+V) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hsmall hT0,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall hT0) hc.le]
    exact hh.trans (Nat.cast_nonneg _)
end

section
open scoped Classical
open MvPolynomial

lemma affine_pole_identity {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (c b : K) (hc : c ≠ 0) (t : A) :
    algebraMap K A c*t+algebraMap K A b = algebraMap K A c*(t-algebraMap K A (-b/c)) := by
  rw [mul_sub,←map_mul]
  have he : c*(-b/c) = -b := by field_simp
  rw [he,map_neg,sub_neg_eq_add]

theorem affine_pole_hilbert {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (r θ : Fin 4 → K) (hθ : Function.Injective θ)
    (t q : MvPolynomial (Fin n) K ⧸ I) (b : Fin 4 → MvPolynomial (Fin n) K ⧸ I)
    (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t)))
    (heq : ∀ i, (t-algebraMap K _ (r i))^2*b i=q-algebraMap K _ (θ i))
    (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ht : t ∈ weightedFunctions I ω U) (hb : ∀ i, b i ∈ weightedFunctions I ω V)
    (hr : ¬ ∀ i, r i = r 0) :
    ∀ T : ℝ, 0 ≤ T → ((V+4*U)/(2*U*V^2))*T^2-
      ((V+4*U)*(U+V)/(U*V^2))*T ≤ weightedHilbert I ω T := by
  classical
  by_cases hinj : Function.Injective r
  · exact threePole_hilbert_lower I ω hω (r 0) (θ 0)
      (fun i : Fin 2 => r (⟨i.val+1,by omega⟩ : Fin 4)) (fun i : Fin 2 => θ (⟨i.val+1,by omega⟩ : Fin 4))
      (by intro i he; have hh := hinj he; have hv := congrArg Fin.val hh; fin_cases i <;> norm_num at hv)
      (by intro i j he; have hh := congrArg Fin.val (hinj he); fin_cases i <;> fin_cases j <;> norm_num at *)
      t q (b 0) (fun i : Fin 2 => b (⟨i.val+1,by omega⟩ : Fin 4)) hi (heq 0) (fun i => heq _) U V hU hV ht (hb 0) (fun i => hb _)
  · obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hinj
    have hex : ∃ l, r l ≠ r i := by
      by_contra hn
      push Not at hn
      exact hr (fun l => (hn l).trans (hn 0).symm)
    obtain ⟨l,hl⟩ := hex
    let u := algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ j-θ i)⁻¹*(b i-b j)
    have hu : (t-algebraMap K _ (r i))^2*u = 1 := by
      have he : (t-algebraMap K _ (r i))^2*(b i-b j) = algebraMap K _ (θ j-θ i) := by
        rw [mul_sub,heq i,hij,heq j,map_sub]
        ring
      dsimp [u]
      rw [mul_left_comm,he,←map_mul,inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm (hθ.ne hne))),map_one]
    have huw : u ∈ weightedFunctions I ω V := by
      dsimp only [u]
      rw [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
      exact (weightedFunctions I ω V).smul_mem _ ((weightedFunctions I ω V).sub_mem (hb i) (hb j))
    exact twoPole_hilbert_lower I ω hω (r i) (r l) (θ i) (θ l) hl.symm t q
      (b i) (b l) u hi (heq i) (heq l) hu U V hU hV ht (hb i) (hb l) huw

end

open MvPolynomial

lemma radial_affine_points {n d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (a : Fin d → MvPolynomial (Fin n) ℂ) (c : Fin d → ℂ) (r : ℂ)
    (t : MvPolynomial (Fin n) ℂ ⧸ I)
    (he : ∀ i, Ideal.Quotient.mk I (a i)=algebraMap ℂ _ (c i)*(t-algebraMap ℂ _ r))
    (s : Fin d) (z₀ : Fin n → ℤ) (hz₀ : PointOn I z₀)
    (ha₀ : MvPolynomial.aeval (fun j => (z₀ j:ℂ)) (a s) ≠ 0)
    (z : Fin n → ℤ) (hz : PointOn I z) :
    ∃ u : ℂ, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (a i) =
      u*MvPolynomial.aeval (fun j => (z₀ j:ℂ)) (a i) := by
  have hh (w : Fin n → ℤ) (hw : PointOn I w) (i) :
      MvPolynomial.aeval (fun j => (w j:ℂ)) (a i)=c i*(pointEvaluation I w hw t-r) := by
    have h := congrArg (pointEvaluation I w hw) (he i)
    simp only [map_mul,map_sub,AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply] at h
    exact h
  have hn : pointEvaluation I z₀ hz₀ t-r ≠ 0 := by
    intro hn
    apply ha₀
    rw [hh z₀ hz₀ s,hn,mul_zero]
  refine ⟨(pointEvaluation I z hz t-r)/(pointEvaluation I z₀ hz₀ t-r),fun i => ?_⟩
  rw [hh z hz i,hh z₀ hz₀ i]
  field_simp

open MvPolynomial
open scoped Classical

theorem quartic_surface_alternatives {n D A B : ℕ} (hD : 0 < D)
    (U V L : ℝ) (hU : 0 < U) (hV : 0 < V) (hL : 0 < L)
    (hA : (A:ℝ)=L*U) (hB : (B:ℝ)=L*V)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0)
    (hscale : ∀ i, (w i:ℝ)=L*ω i) (M : QuarticBoxSystem n D A B U ω w) (E : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (S : Finset (Fin n → ℤ)) (F R : ℕ),
    (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
    (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i,
      MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i)=c*MvPolynomial.aeval (fun j => (z₀ j:ℂ)) (M.a i))).card ≤ R) →
    (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
    ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
    (∀ z ∈ S, PointOn I z) →
    (∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0) →
    Transcendental ℂ (Ideal.Quotient.mk I M.q) → affineDimension I = 2 → affineDegree I ≤ E →
    S.card ≤ F+R ∨ ∀ T : ℝ, 1 ≤ T →
      min (((min (2*A) B:ℕ):ℝ)*((2*A+B:ℕ):ℝ)*L^2/(2*(A:ℝ)^2*(B:ℝ)^2))
        ((V+4*U)/(2*U*V^2))*T^2-H*T ≤ weightedHilbert I ω T := by
  classical
  have hAn : 0 < A := by
    have : (0:ℝ) < A := by rw [hA]; positivity
    exact_mod_cast this
  have hBn : 0 < B := by
    have : (0:ℝ) < B := by rw [hB]; positivity
    exact_mod_cast this
  obtain ⟨C,hC,hbound⟩ := norm_real_hilbert_uniform_affine_pair (n := n) (d := 4) (K := ℂ)
    (k := 2) (by omega) A B hAn hBn E D hD L hL
  let H := C+(V+4*U)*(U+V)/(U*V^2)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H,hH,fun S F R hF hR hn I hI hMI hon ha hq hdim hdeg => ?_⟩
  let : I.IsPrime := hI
  by_cases hp : ∃ z ∈ S, ∃ v ∈ S, (fun i => z (M.x i)) ≠ (fun i => v (M.x i))
  swap
  · left
    by_cases hs : S.Nonempty
    · obtain ⟨z,hz⟩ := hs
      have ht : S.filter (fun v => ∀ i, v (M.x i)=z (M.x i)) = S := by
        apply Finset.filter_true_of_mem
        intro v hv i
        have he : (fun i => v (M.x i))=(fun i => z (M.x i)) := by
          by_contra he; exact hp ⟨v,hv,z,hz,he⟩
        exact congrFun he i
      have hh := hF (fun i => z (M.x i)); rw [ht] at hh; omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.card_empty]; omega
  obtain ⟨z,hz,v,hv,hzv⟩ := hp
  obtain ⟨s,hind⟩ := norm_surface_left_basis I 2 M.a M.b M.q M.θ ha
    (M.quotient_equations I hMI) (quotient_pair_generates M.a M.b M.generates I) hq hdim
  have hts : Transcendental ℂ (Ideal.Quotient.mk I (M.a s)) := by
    exact hind.transcendental (Fin.succ 0)
  rcases affine_left_dichotomy (fun i => Ideal.Quotient.mk I (M.a i)) s hts with ⟨i,hi⟩|⟨c,b,he⟩
  · right
    let j : Fin 2 → Fin 4 := fun l => if l=0 then i else s
    have hj : Function.Injective j := by
      have hh := hi.injective
      intro u v huv
      have he : (some u:Option (Fin 2))=some v := hh (by simpa only [Option.elim,j,apply_ite] using congrArg (fun l => Ideal.Quotient.mk I (M.a l)) huv)
      exact Option.some.inj he
    have hh := hbound I M.a M.b M.q M.θ M.distinct ha (M.quotient_equations I hMI)
      j hj (by simpa [j] using hind) (by simpa only [j,apply_ite] using hi) hdim hdeg M.leftDegree M.qDegree w hw M.leftWeight M.rightWeight ω hω hscale
    intro T hT
    have hb := hh T hT
    norm_num only [Nat.factorial_two,Nat.cast_ofNat,pow_one] at hb
    have hm := mul_le_mul_of_nonneg_right (min_le_left
      (((min (2*A) B:ℕ):ℝ)*((2*A+B:ℕ):ℝ)*L^2/(2*(A:ℝ)^2*(B:ℝ)^2)) ((V+4*U)/(2*U*V^2))) (sq_nonneg T)
    have he : C*T ≤ H*T := mul_le_mul_of_nonneg_right (by dsimp [H]; exact le_add_of_nonneg_right (by positivity)) (by linarith)
    linarith
  · have hc : ∀ i, c i ≠ 0 := fun i => conjugate_affine_slope_ne_zero M.v M.independent (M.σ i)
      M.x I (c i) (b i) (Ideal.Quotient.mk I (M.a s)) (he i) z v (hon z hz) (hon v hv) hzv
    let r := fun i => -b i/c i
    have hr (i) : Ideal.Quotient.mk I (M.a i)=algebraMap ℂ _ (c i)*
        (Ideal.Quotient.mk I (M.a s)-algebraMap ℂ _ (r i)) :=
      (he i).trans (affine_pole_identity (c i) (b i) (hc i) _)
    by_cases hr0 : ∀ i, r i=r 0
    · left
      have ht : S.filter (fun w => ∃ u : ℂ, ∀ i, MvPolynomial.aeval (fun j => (w j:ℂ)) (M.a i)=
          u*MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i))=S := by
        apply Finset.filter_true_of_mem
        intro w hw
        exact radial_affine_points I M.a c (r 0) (Ideal.Quotient.mk I (M.a s))
          (fun i => by rw [←hr0 i]; exact hr i) s z (hon z hz) (hn z hz s) w (hon w hw)
      have hh := hR z hz; rw [ht] at hh; omega
    · right
      let b' := fun i => algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) (c i)^2*Ideal.Quotient.mk I (M.b i)
      have hbw : ∀ i, b' i ∈ weightedFunctions I ω V := by
        intro i
        dsimp [b']
        rw [←map_pow,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
        exact (weightedFunctions I ω V).smul_mem _ (M.right_real_weight hω L V hL hV.le hB hscale I i)
      have ht : Ideal.Quotient.mk I (M.a s) ∈ weightedFunctions I ω U := by
        have hh := weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale U hU.le
        rw [←hA,Nat.floor_natCast] at hh
        exact hh ⟨M.a s,M.leftWeight s,rfl⟩
      have heq : ∀ i, (Ideal.Quotient.mk I (M.a s)-algebraMap ℂ _ (r i))^2*b' i=
          Ideal.Quotient.mk I M.q-algebraMap ℂ _ (M.θ i) := by
        intro i
        rw [←M.quotient_equations I hMI i,hr i]
        dsimp [b']; ring
      have hind' : AlgebraicIndependent ℂ (fun o : Option PUnit => o.elim (Ideal.Quotient.mk I M.q)
          (fun _ => Ideal.Quotient.mk I (M.a s))) := by
        let e : Option PUnit.{1} → Fin 2 := fun o => o.elim 0 (fun _ => 1)
        have hei : Function.Injective e := by decide
        convert hind.comp e hei using 1
        · funext o; cases o <;> rfl
      intro T hT
      have hh := affine_pole_hilbert I ω hω r M.θ M.distinct (Ideal.Quotient.mk I (M.a s))
        (Ideal.Quotient.mk I M.q) b' hind' heq U V hU hV ht hbw hr0 T (by linarith)
      have hm := mul_le_mul_of_nonneg_right (min_le_right
        (((min (2*A) B:ℕ):ℝ)*((2*A+B:ℕ):ℝ)*L^2/(2*(A:ℝ)^2*(B:ℝ)^2)) ((V+4*U)/(2*U*V^2))) (sq_nonneg T)
      have he : ((V+4*U)*(U+V)/(U*V^2))*T ≤ H*T := mul_le_mul_of_nonneg_right
        (by dsimp [H]; linarith) (by linarith)
      linarith

end QuarticPowerFree

end OAI
