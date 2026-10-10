import OAI.NumberTheory.PowerFree.QuarticComponents

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical

theorem quartic_box_prime_count {n D : ℕ} (j : Fin 100) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 1/2)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 400*ω i)
    (M : QuarticBoxSystem n D (quarticA j) (quarticB j) (quarticU j) ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F R e₀ : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i, MvPolynomial.aeval (fun l => (z l:ℂ)) (M.a i)=
        c*MvPolynomial.aeval (fun l => (z₀ l:ℂ)) (M.a i))).card ≤ R) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
        affineDimension I ≤ 5 → affineDegree I ≤ e₀ → (∀ z ∈ S, PointOn I z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  choose K H hK hH halt using fun (e : ℕ) (i : Fin 5) =>
    quartic_component_alternatives (h := 5-i.val) j (by omega) (by omega) hD
      ω hω hωW w hw hscale M Cbox (by linarith) F R e (1/4000) (by norm_num)
  let c := fun e => ∑ i : Fin 5, H e i
  let Ke := fun e => 1+∑ i : Fin 5, K e i
  have hc : ∀ e, 0 ≤ c e := fun e => Finset.sum_nonneg (fun i _ => hH e i)
  have hKe : ∀ e, 1 ≤ Ke e := by
    intro e
    dsimp [Ke]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hK e i)))
  have hci (e) (i : Fin 5) : H e i ≤ c e := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => hH e j) (Finset.mem_univ i)
  have hKi (e) (i : Fin 5) : K e i ≤ Ke e := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hK e j)) (Finset.mem_univ i)
    dsimp [Ke]
    linarith
  let W : ℝ := 1+∑ j, ω j
  have hsum : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => (hω j).le)
  have hW : 0 ≤ W := by dsimp [W]; linarith
  obtain ⟨C,Xcut,hC,hcount⟩ := physical_affine_count n 5 0 e₀ (by omega)
    ω hω Cbox W hCbox hW (quarticIncrement j) (quarticStage j)
    (quartic_increment_nonneg j) (fun i => quarticEnvelope_pos _ _)
    (quartic_prefix j) (1/1000) (by norm_num) c Ke hc hKe
  refine ⟨C,max (max 2 Cbox) Xcut,hC,fun X hX S hbox hnF haF hrad hnonzero I hI hMI hdim hdeg hon => ?_⟩
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hCX : Cbox ≤ X := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX)
  have hXcut : Xcut < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hmax (j : Fin n) : ω j ≤ ∑ l, ω l := Finset.single_le_sum
    (fun l _ => (hω l).le) (Finset.mem_univ j)
  have hbound (z) (hz : z ∈ S) (j) : |(z j:ℝ)| ≤ X^W := by
    calc
      _ ≤ Cbox*X^(ω j) := hbox z hz j
      _ ≤ X*X^(∑ l, ω l) := mul_le_mul hCX
        (Real.rpow_le_rpow_of_exponent_le hX1 (hmax j)) (Real.rpow_nonneg hXp.le _) hXp.le
      _ = X^W := by dsimp [W]; rw [Real.rpow_add hXp,Real.rpow_one]
  let G : KernelGeometry n := ⟨S,X^W,Real.one_le_rpow hX1 hW,hbound⟩
  have hb := hcount X hXcut G le_rfl hbox I hI hdim hdeg hon
  have hcS := hb (by
    intro i e J hJ hIJ _ hJe hJdim hp
    let : J.IsPrime := hJ
    obtain ⟨z,hz,hzJ⟩ := hp
    have ha := M.quotient_left_nonzero J z hzJ (hnonzero z hz)
    have hh := halt e i X hX2.le S hbox hnF haF hrad hnonzero J hJ (hMI.trans hIJ) hJdim hJe ha
    rcases hh with hs | hHilb
    · left
      have hm := mul_le_mul_of_nonneg_right (hKi e i) (Real.rpow_nonneg hXp.le (1/4000))
      norm_num only [show (1/1000:ℝ)/4=1/4000 by norm_num]
      exact hs.trans hm
    · right
      intro T hT
      have hh := hHilb T hT
      have hm := mul_le_mul_of_nonneg_right (hci e i) (pow_nonneg (by linarith : 0 ≤ T) (5-i.val-1))
      change T^(5-i.val)/(((5-i.val).factorial:ℝ)*(quarticEnvelope j (5-i.val))^(5-i.val))-
        c e*T^(5-i.val-1) ≤ _
      linarith only [hh,hm])
  exact hcS.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 (quartic_sum j)) hC.le)

theorem quartic_box_prime_count_unrestricted {n D : ℕ} (j : Fin 100) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 1/2)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 400*ω i)
    (M : QuarticBoxSystem n D (quarticA j) (quarticB j) (quarticU j) ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F R e₀ : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i, MvPolynomial.aeval (fun l => (z l:ℂ)) (M.a i)=
        c*MvPolynomial.aeval (fun l => (z₀ l:ℂ)) (M.a i))).card ≤ R) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
        affineDegree I ≤ e₀ → (∀ z ∈ S, PointOn I z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  obtain ⟨C,X₀,hC,hb⟩ := quartic_box_prime_count j hD ω hω hωW w hw hscale M Cbox hCbox F R e₀
  refine ⟨C+F+1,max 2 X₀,by positivity,fun X hX S hbox hqF haF hrad hn I hI hMI hdeg hon => ?_⟩
  let : I.IsPrime := hI
  have hX1 : 1 ≤ X := by have := (le_max_left 2 X₀).trans_lt hX; linarith
  have hp : 1 ≤ X^(997/1000:ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hfilter : S.filter (PointOn I) = S := Finset.filter_true_of_mem hon
  by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
  · have hcard := algebraic_polynomial_fibre_count S F M.q hqF I hq
    rw [hfilter] at hcard
    calc
      (S.card:ℝ) ≤ F := by exact_mod_cast hcard
      _ ≤ (C+F+1)*X^(997/1000:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) F]
  · by_cases hs : S.Nonempty
    · obtain ⟨z,hz⟩ := hs
      have ha := M.quotient_left_nonzero I z (hon z hz) (hn z hz)
      have hdim := norm_dimension_le I 2 M.a M.b M.q M.θ ha (M.quotient_equations I hMI) M.generates hq
      have hh := hb X (lt_of_le_of_lt (le_max_right _ _) hX) S hbox hqF haF hrad hn I hI hMI hdim hdeg hon
      exact hh.trans (mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) F; linarith : C ≤ C+F+1) (by positivity))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.card_empty,Nat.cast_zero]
      positivity

theorem quartic_box_count {n D : ℕ} (j : Fin 100) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 1/2)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 400*ω i)
    (M : QuarticBoxSystem n D (quarticA j) (quarticB j) (quarticU j) ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F R : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i, MvPolynomial.aeval (fun l => (z l:ℂ)) (M.a i)=
        c*MvPolynomial.aeval (fun l => (z₀ l:ℂ)) (M.a i))).card ≤ R) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      (∀ z ∈ S, PointOn M.ideal z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) M.ideal).toFinset
  let E : ℕ := ∑ I ∈ Q, ⌈affineDegree I⌉₊
  have hQ (I) (hI : I ∈ Q) : I ∈ M.ideal.minimalPrimes := (Set.Finite.mem_toFinset _).mp hI
  have hE (I) (hI : I ∈ Q) : affineDegree I ≤ E := by
    have hsum : ⌈affineDegree I⌉₊ ≤ E := Finset.single_le_sum (f := fun J => ⌈affineDegree J⌉₊) (fun _ _ => Nat.zero_le _) hI
    exact (Nat.le_ceil _).trans (by exact_mod_cast hsum)
  obtain ⟨C,X₀,hC,hb⟩ := quartic_box_prime_count_unrestricted j hD ω hω hωW w hw hscale M Cbox hCbox F R E
  refine ⟨(Q.card+1)*C,max 2 X₀,by positivity,fun X hX S hbox hqF haF hrad hn hon => ?_⟩
  have hXpos : 0 ≤ X := by have := (le_max_left 2 X₀).trans_lt hX; linarith
  have hX₀ : X₀ < X := (le_max_right _ _).trans_lt hX
  have cover : S ⊆ Q.biUnion (fun I => S.filter (PointOn I)) := by
    intro z hz
    obtain ⟨I,hI,hzI⟩ := point_on_minimal_component M.ideal (fun j => (z j:ℂ)) (hon z hz)
    exact Finset.mem_biUnion.mpr ⟨I,(Set.Finite.mem_toFinset _).mpr hI,Finset.mem_filter.mpr ⟨hz,hzI⟩⟩
  have hbound (I) (hI : I ∈ Q) : ((S.filter (PointOn I)).card:ℝ) ≤ C*X^(997/1000:ℝ) := by
    apply hb X hX₀ (S.filter (PointOn I))
    · intro z hz; exact hbox z (Finset.mem_filter.mp hz).1
    · intro t
      apply (Finset.card_le_card ?_).trans (hqF t)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro c
      apply (Finset.card_le_card ?_).trans (haF c)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro z hz
      apply (Finset.card_le_card ?_).trans (hrad z (Finset.mem_filter.mp hz).1)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro z hz; exact hn z (Finset.mem_filter.mp hz).1
    · exact (hQ I hI).isPrime
    · exact (hQ I hI).1.2
    · exact hE I hI
    · intro z hz; exact (Finset.mem_filter.mp hz).2
  calc
    (S.card:ℝ) ≤ (∑ I ∈ Q, (S.filter (PointOn I)).card : ℕ) := by
      exact_mod_cast (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
    _ = ∑ I ∈ Q, ((S.filter (PointOn I)).card:ℝ) := by simp
    _ ≤ ∑ I ∈ Q, C*X^(997/1000:ℝ) := Finset.sum_le_sum hbound
    _ = Q.card*(C*X^(997/1000:ℝ)) := by simp
    _ ≤ ((Q.card+1)*C)*X^(997/1000:ℝ) := by nlinarith [Real.rpow_nonneg (x := X) hXpos (997/1000:ℝ)]

end

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

noncomputable def quarticBoxWeight (j : Fin 100) : Fin (4+4) → ℝ :=
  Fin.addCases (m := 4) (n := 4) (fun _ : Fin 4 => quarticU j) (fun _ : Fin 4 => quarticV j)
def quarticBoxNatWeight (j : Fin 100) : Fin (4+4) → ℕ :=
  Fin.addCases (m := 4) (n := 4) (fun _ : Fin 4 => quarticA j) (fun _ : Fin 4 => quarticB j)
lemma quarticBoxWeight_pos (j : Fin 100) (i : Fin (4+4)) : 0 < quarticBoxWeight j i := by
  induction i using (Fin.addCases (m := 4) (n := 4)) <;> simp only [quarticBoxWeight,Fin.addCases_left,Fin.addCases_right]
  · exact quarticU_pos j
  · exact quarticV_pos j
lemma quarticBoxWeight_le (j : Fin 100) (i : Fin (4+4)) : quarticBoxWeight j i ≤ 1/2 := by
  induction i using (Fin.addCases (m := 4) (n := 4)) <;> simp only [quarticBoxWeight,Fin.addCases_left,Fin.addCases_right]
  · exact quarticU_le j
  · exact quarticV_le j
lemma quarticBoxNatWeight_ne (j : Fin 100) (i : Fin (4+4)) : quarticBoxNatWeight j i ≠ 0 := by
  induction i using (Fin.addCases (m := 4) (n := 4)) <;> simp only [quarticBoxNatWeight,Fin.addCases_left,Fin.addCases_right]
  · exact (quarticA_pos j).ne'
  · exact (quarticB_pos j).ne'
lemma quarticBoxWeight_scale (j : Fin 100) (i : Fin (4+4)) : (quarticBoxNatWeight j i:ℝ)=400*quarticBoxWeight j i := by
  induction i using (Fin.addCases (m := 4) (n := 4)) <;> simp only [quarticBoxNatWeight,quarticBoxWeight,Fin.addCases_left,Fin.addCases_right,quarticU,quarticV] <;> ring

noncomputable def quarticBoxOfChart {K : Type} [Field K] [NumberField K] (j : Fin 100)
    (T : IntegralEmbeddingChart K 4) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) :
    QuarticBoxSystem 8 5 (quarticA j) (quarticB j) (quarticU j) (quarticBoxWeight j) (quarticBoxNatWeight j) := by
  let a : Fin 4 → MvPolynomial (Fin (4+4)) ℂ := fun i => coordinateLinearForm (Fin.castAdd 4) (T.A i)
  let b : Fin 4 → MvPolynomial (Fin (4+4)) ℂ := fun i => C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd 4) (T.A i)
  let i₀ : Fin 4 := 0
  have hb (i) : (b i).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using coordinateLinearForm_totalDegree (Fin.natAdd 4) (T.A i))
  refine ⟨K,T.V,T.V.linearIndependent,T.σ,fun i => T.σ i θ,hθ,Fin.castAdd 4,
    ?_,b,a i₀^2*b i₀+C (T.σ i₀ θ),?_,?_,?_,?_,?_⟩
  · intro i; simp only [quarticBoxWeight,Fin.addCases_left]
  · exact pairedLinearForms_generate T.A T.det_ne_zero (μ:ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast hμ.ne'))
  · intro i; exact (coordinateLinearForm_totalDegree _ _).trans (by omega)
  · apply (totalDegree_add _ _).trans
    rw [max_le_iff]
    refine ⟨(totalDegree_mul _ _).trans ?_,by simp⟩
    have ha : (a i₀).totalDegree ≤ 1 := coordinateLinearForm_totalDegree _ _
    have hp := (totalDegree_pow (a i₀) 2).trans (Nat.mul_le_mul_left 2 ha)
    have hh := hb i₀
    omega
  · intro i
    exact coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [quarticBoxNatWeight,Fin.addCases_left,le_refl])
  · intro i
    change C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd 4) (T.A i) ∈ _
    rw [←smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [quarticBoxNatWeight,Fin.addCases_right,le_refl]))

theorem quarticIntegralPoint_equation {K : Type} [Field K] [NumberField K] (j : Fin 100)
    (T : IntegralEmbeddingChart K 4) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) (α β : 𝓞 K) (n : ℤ)
    (he : (α:K)^2*(β:K) = (μ:K)*((n:K)-θ)) :
    let M := quarticBoxOfChart j T θ hθ μ hμ
    let z := normIntegralPoint T α β
    MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = n ∧ PointOn M.ideal z := by
  let M := quarticBoxOfChart j T θ hθ μ hμ
  let z := normIntegralPoint T α β
  have ha (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) = T.σ i (α:K) := normIntegralPoint_left T α β i
  have hb (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.b i) = T.σ i (β:K)/(μ:ℂ) := normIntegralPoint_right T α β μ i
  have hμc : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hrel (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i)^2*
      MvPolynomial.aeval (fun j => (z j:ℂ)) (M.b i) = (n:ℂ)-T.σ i θ := by
    rw [ha,hb,←mul_div_assoc]
    have hh := congrArg (T.σ i) he
    simp only [map_mul,map_pow,map_natCast,map_sub,map_intCast] at hh
    rw [hh,mul_div_cancel_left₀ _ hμc]
  have hq : MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = (n:ℂ) := by
    change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a 0^2*M.b 0+C (T.σ 0 θ)) = _
    rw [map_add,map_mul,map_pow,MvPolynomial.aeval_C,hrel]
    simp only [Algebra.algebraMap_self,RingHom.id_apply]
    ring
  refine ⟨hq,?_⟩
  change M.ideal ≤ RingHom.ker (MvPolynomial.eval (fun j => (z j:ℂ)))
  apply Ideal.span_le.mpr
  rintro p ⟨i,rfl⟩
  change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.equation i) = 0
  simp only [QuarticBoxSystem.equation,map_add,map_sub,map_mul,map_pow,MvPolynomial.aeval_C,hrel,hq]
  change (n:ℂ)-T.σ i θ-n+T.σ i θ = 0
  ring

end

open NumberField Module
open scoped Classical BigOperators

lemma prime_rational_fourth_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (r : ℚ)
    (he : (p:ℚ) = r^4*q) : p=q ∧ (r=1 ∨ r= -1) := by
  have hs : IsSquare ((p*q:ℕ):ℚ) := by
    refine ⟨r^2*q,?_⟩
    push_cast
    rw [he]
    ring
  obtain ⟨m,hm⟩ := Rat.isSquare_natCast_iff.mp hs
  have hpm : p ∣ m := by
    have hh : p ∣ m*m := by rw [←hm]; exact dvd_mul_right p q
    exact (hp.dvd_mul.mp hh).elim id id
  obtain ⟨k,rfl⟩ := hpm
  have heq : q=p*(k*k) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    nlinarith [hm]
  have hpq : p=q := ((Nat.dvd_prime hq).mp ⟨k*k,heq⟩).resolve_left hp.ne_one
  refine ⟨hpq,?_⟩
  rw [hpq] at he
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr : r^4=1 := by apply mul_right_cancel₀ hq0; nlinarith [he]
  have hs0 : (r^2-1)*(r^2+1)=0 := by nlinarith [hr]
  have hs1 : r^2=1 := by
    rcases mul_eq_zero.mp hs0 with h|h
    · linarith
    · nlinarith [sq_nonneg r]
  exact (sq_eq_one_iff).mp hs1

lemma IntegralEmbeddingChart.proportional_rat {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) (hα : α ≠ 0) (c : ℂ)
    (h : ∀ i, T.σ i (β:K)=c*T.σ i (α:K)) :
    ∃ r : ℚ, c=(r:ℂ) ∧ (β:K)=algebraMap ℚ K r*(α:K) := by
  have he : (fun i => T.σ i (β:K)) = c • (fun i => T.σ i (α:K)) := by
    funext i; exact h i
  have hc : ∀ j, (T.coord β j:ℂ)=c*(T.coord α j:ℂ) := by
    have hh := congrArg (fun v => T.A⁻¹.mulVec v) he
    rw [T.inverse_coordinates β,Matrix.mulVec_smul,T.inverse_coordinates α] at hh
    intro j; exact congrFun hh j
  have hex : ∃ j, T.coord α j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα
    apply T.B.repr.injective
    ext j
    simpa only [IntegralEmbeddingChart.coord,map_zero,Finsupp.zero_apply] using hn j
  obtain ⟨j,hj⟩ := hex
  let r : ℚ := (T.coord β j:ℚ)/(T.coord α j:ℚ)
  have hr : c=(r:ℂ) := by
    have hjc : (T.coord α j:ℂ) ≠ 0 := by exact_mod_cast hj
    dsimp [r]
    push_cast
    exact (eq_div_iff hjc).mpr (hc j).symm
  refine ⟨r,hr,?_⟩
  have hd : 0 < d := by have := j.isLt; omega
  apply (T.σ ⟨0,hd⟩).injective
  rw [map_mul]
  change T.σ ⟨0,hd⟩ (β:K) = T.σ ⟨0,hd⟩ (r:K)*T.σ ⟨0,hd⟩ (α:K)
  rw [map_ratCast,←hr]
  exact h _

lemma prime_norm_proportional_sign {K : Type*} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 4) (α β : 𝓞 K) (p q Q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hQ : 0 < Q)
    (hα : |(Algebra.norm ℚ (α:K):ℝ)| = (p*Q:ℕ))
    (hβ : |(Algebra.norm ℚ (β:K):ℝ)| = (q*Q:ℕ))
    (r : ℚ) (hr : (β:K)=algebraMap ℚ K r*(α:K)) : β=α ∨ β= -α := by
  have he := congrArg (fun z : K => |(Algebra.norm ℚ z:ℝ)|) hr
  rw [map_mul,Algebra.norm_algebraMap,hd] at he
  push_cast at he
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (r:ℝ)^4),hα,hβ] at he
  have hQr : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hratio : (q:ℝ)=(r:ℝ)^4*p := by
    apply mul_right_cancel₀ hQr
    push_cast at he
    nlinarith [he]
  have hratio' : (q:ℚ)=r^4*p := by exact_mod_cast hratio
  obtain ⟨_,hs⟩ := prime_rational_fourth_ratio hq hp r hratio'
  rcases hs with rfl|rfl
  · left
    apply Subtype.val_injective
    change (β:K) = (α:K)
    simpa only [map_one,one_mul] using hr
  · right
    apply Subtype.val_injective
    change (β:K) = -(α:K)
    simpa using hr

end QuarticPowerFree

end OAI
