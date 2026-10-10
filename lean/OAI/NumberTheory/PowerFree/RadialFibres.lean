import OAI.NumberTheory.PowerFree.QuarticBoxes

namespace OAI

namespace QuarticPowerFree

section
open NumberField
open scoped BigOperators Classical

theorem quartic_radial_fibre_count {K : Type*} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K=4) (T : IntegralEmbeddingChart K 4)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (A : ι → 𝓞 K) (P : ι → ℕ)
    (J : ι → Ideal (𝓞 K)) (Q : Finset (Ideal (𝓞 K)))
    (hQ : ∀ I ∈ Q, I ≠ ⊥) (hJ : ∀ i ∈ S, J i ∈ Q)
    (hA : ∀ i ∈ S, A i ≠ 0) (hP : ∀ i ∈ S, (P i).Prime)
    (hnorm : ∀ i ∈ S, |(Algebra.norm ℚ (A i:K):ℝ)| = ((P i*Ideal.absNorm (J i):ℕ):ℝ))
    (F : ℕ) (hF : ∀ α : 𝓞 K, (S.filter (fun i => A i = α)).card ≤ F) (α : 𝓞 K) :
    (S.filter (fun i => ∃ c : ℂ, ∀ l, T.σ l (A i:K)=c*T.σ l (α:K))).card ≤ 2*Q.card*F := by
  classical
  let R := S.filter (fun i => ∃ c : ℂ, ∀ l, T.σ l (A i:K)=c*T.σ l (α:K))
  have hc (I) (hI : I ∈ Q) : (R.filter (fun i => J i=I)).card ≤ 2*F := by
    by_cases hr : (R.filter (fun i => J i=I)).Nonempty
    · obtain ⟨i₀,hi₀⟩ := hr
      obtain ⟨hiR,hiJ⟩ := Finset.mem_filter.mp hi₀
      obtain ⟨hiS,c₀,hc₀⟩ := Finset.mem_filter.mp hiR
      have hc0 : c₀ ≠ 0 := by
        intro he
        have hn := hc₀ 0
        rw [he,zero_mul] at hn
        have : (A i₀:K) = 0 := (map_eq_zero (T.σ 0)).mp hn
        apply hA i₀ hiS
        exact_mod_cast this
      have hN : 0 < I.absNorm := Nat.pos_of_ne_zero (fun h => hQ I hI (Ideal.absNorm_eq_zero_iff.mp h))
      have hcov : R.filter (fun i => J i=I) ⊆
          S.filter (fun i => A i=A i₀) ∪ S.filter (fun i => A i= -A i₀) := by
        intro i hi
        obtain ⟨hiR',hiJ'⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiS',c,hc'⟩ := Finset.mem_filter.mp hiR'
        have hprop : ∀ l, T.σ l (A i:K)=(c/c₀)*T.σ l (A i₀:K) := by
          intro l
          rw [hc' l,hc₀ l]
          field_simp
        obtain ⟨r,_,hr⟩ := T.proportional_rat (A i₀) (A i) (hA i₀ hiS) (c/c₀) hprop
        have h₀ := hnorm i₀ hiS
        have h₁ := hnorm i hiS'
        rw [hiJ] at h₀
        rw [hiJ'] at h₁
        rcases prime_norm_proportional_sign hd (A i₀) (A i) (P i₀) (P i) I.absNorm
          (hP i₀ hiS) (hP i hiS') hN h₀ h₁ r hr with he|he
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiS',he⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiS',he⟩)
      calc
        _ ≤ (S.filter (fun i => A i=A i₀) ∪ S.filter (fun i => A i= -A i₀)).card := Finset.card_le_card hcov
        _ ≤ (S.filter (fun i => A i=A i₀)).card+(S.filter (fun i => A i= -A i₀)).card := Finset.card_union_le ..
        _ ≤ F+F := Nat.add_le_add (hF _) (hF _)
        _ = 2*F := by omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hr,Finset.card_empty]; omega
  have hcover : R ⊆ Q.biUnion (fun I => R.filter (fun i => J i=I)) := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨J i,hJ i (Finset.mem_filter.mp hi).1,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
  calc
    R.card ≤ (Q.biUnion (fun I => R.filter (fun i => J i=I))).card := Finset.card_le_card hcover
    _ ≤ ∑ I ∈ Q, (R.filter (fun i => J i=I)).card := Finset.card_biUnion_le
    _ ≤ ∑ _I ∈ Q, 2*F := Finset.sum_le_sum hc
    _ = 2*Q.card*F := by simp; ring

end

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

theorem quartic_indexed_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (_hd : f.natDegree=4) (b : Fin 100)
    {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K=4) (T : IntegralEmbeddingChart K 4) (θ : K)
    (hθ : Function.Injective (fun i => T.σ i θ)) (μ : ℕ) (hμ : 0 < μ)
    (Q : Finset (Ideal (𝓞 K))) (hQ : ∀ I ∈ Q, I ≠ ⊥)
    (Cbox : ℝ) (hCbox : 1 ≤ Cbox) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ (ι : Type) [Fintype ι]
      (a : ι → ℤ) (P : ι → ℕ) (J : ι → Ideal (𝓞 K)) (A B : ι → 𝓞 K),
      Function.Injective a →
      (∀ i, X < (a i:ℝ) ∧ (a i:ℝ) ≤ 2*X) →
      (∀ i, J i ∈ Q) →
      (∀ i, (P i).Prime ∧ X < P i ∧ (P i:ℤ) ∣ f.eval (a i)) →
      (∀ i, A i ≠ 0) →
      (∀ i, (A i:K)^2*(B i:K) = (μ:K)*((a i:K)-θ)) →
      (∀ i, |(Algebra.norm ℚ (A i:K):ℝ)| = ((P i*Ideal.absNorm (J i):ℕ):ℝ)) →
      (∀ i j, |(T.coord (A i) j:ℝ)| ≤ Cbox*X^(quarticU b) ∧
        |(T.coord (B i) j:ℝ)| ≤ Cbox*X^(quarticV b)) →
      (Fintype.card ι:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  let M := quarticBoxOfChart b T θ hθ μ hμ
  let F := Q.card*f.natDegree+1
  obtain ⟨C,X₀,hC,hcount⟩ := quartic_box_count b (by omega : 0 < 5)
    (quarticBoxWeight b) (quarticBoxWeight_pos b) (quarticBoxWeight_le b)
    (quarticBoxNatWeight b) (quarticBoxNatWeight_ne b) (quarticBoxWeight_scale b)
    M Cbox hCbox F (2*Q.card*F)
  refine ⟨C,X₀,hC,fun X hX ι _ a P J A B hainj hrange hJ hP hA he hnorm hbox => ?_⟩
  let z := fun i => normIntegralPoint T (A i) (B i)
  let S := Finset.univ.image z
  have heval (i) : MvPolynomial.aeval (fun j => (z i j:ℂ)) M.q = (a i:ℂ) ∧ PointOn M.ideal (z i) :=
    quarticIntegralPoint_equation b T θ hθ μ hμ (A i) (B i) (a i) (he i)
  have hzinj : Function.Injective z := by
    intro i j hij
    apply hainj
    apply Int.cast_injective (α := ℂ)
    rw [←(heval i).1,←(heval j).1,hij]
  have hcard : S.card = Fintype.card ι := by simp only [S,Finset.card_image_of_injective _ hzinj,Finset.card_univ]
  have hb := hcount X hX S
  rw [←hcard]
  apply hb
  · intro v hv j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    induction j using (Fin.addCases (m := 4) (n := 4)) with
    | left j => simpa only [z,normIntegralPoint,Fin.addCases_left,quarticBoxWeight] using (hbox i j).1
    | right j => simpa only [z,normIntegralPoint,Fin.addCases_right,quarticBoxWeight] using (hbox i j).2
  · intro t
    apply (Finset.card_le_one.mpr ?_).trans (by dsimp [F]; omega)
    intro v hv w hw
    obtain ⟨hvS,hvt⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwS,hwt⟩ := Finset.mem_filter.mp hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvS
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hwS
    have hij : a i = a j := Int.cast_injective (α := ℂ) ((heval i).1.symm.trans
      ((hvt.trans hwt.symm).trans (heval j).1))
    rw [hainj hij]
  · intro c
    let R := Finset.univ.filter (fun i => ∀ j, z i (Fin.castAdd 4 j) = c j)
    have hsubset : S.filter (fun v => ∀ j, v (M.x j) = c j) ⊆ R.image z := by
      intro v hv
      obtain ⟨hvS,hvc⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvS
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hvc⟩,rfl⟩
    apply ((Finset.card_le_card hsubset).trans (Finset.card_image_le)).trans
    by_cases hR : R.Nonempty
    · obtain ⟨i₀,hi₀⟩ := hR
      have hRsub : R ⊆ Finset.univ.filter (fun i => A i=A i₀) := by
        intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,T.B.repr.injective ?_⟩
        ext j
        have h₁ := (Finset.mem_filter.mp hi).2 j
        have h₂ := (Finset.mem_filter.mp hi₀).2 j
        simpa only [z,normIntegralPoint,Fin.addCases_left,IntegralEmbeddingChart.coord] using h₁.trans h₂.symm
      have hc := norm_left_fibre_count f hf Finset.univ a hainj.injOn X
        (fun i _ => hrange i) P J A Q hQ (fun i _ => hJ i) (fun i _ => hP i)
        (fun i _ => hnorm i) (A i₀)
      exact ((Finset.card_le_card hRsub).trans hc).trans (by dsimp [F]; omega)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty]
      exact Nat.zero_le _
  · intro v₀ hv₀
    obtain ⟨i₀,_,rfl⟩ := Finset.mem_image.mp hv₀
    let R := Finset.univ.filter (fun i => ∃ c : ℂ, ∀ l, T.σ l (A i:K)=c*T.σ l (A i₀:K))
    have hsub : S.filter (fun v => ∃ c : ℂ, ∀ l, MvPolynomial.aeval (fun t => (v t:ℂ)) (M.a l)=
        c*MvPolynomial.aeval (fun t => (z i₀ t:ℂ)) (M.a l)) ⊆ R.image z := by
      intro v hv
      obtain ⟨hvS,c,hc⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvS
      refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,c,?_⟩,rfl⟩
      intro l
      have he₁ : MvPolynomial.aeval (fun t => (z i t:ℂ)) (M.a l)=T.σ l (A i:K) := normIntegralPoint_left T (A i) (B i) l
      have he₂ : MvPolynomial.aeval (fun t => (z i₀ t:ℂ)) (M.a l)=T.σ l (A i₀:K) := normIntegralPoint_left T (A i₀) (B i₀) l
      simpa only [he₁,he₂] using hc l
    apply ((Finset.card_le_card hsub).trans Finset.card_image_le).trans
    apply quartic_radial_fibre_count hK T Finset.univ A P J Q hQ
      (fun i _ => hJ i) (fun i _ => hA i) (fun i _ => (hP i).1) (fun i _ => hnorm i) F _ (A i₀)
    intro α
    have hc := norm_left_fibre_count f hf Finset.univ a hainj.injOn X
      (fun i _ => hrange i) P J A Q hQ (fun i _ => hJ i) (fun i _ => hP i)
      (fun i _ => hnorm i) α
    exact hc.trans (by dsimp [F]; omega)
  · intro v hv j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    change MvPolynomial.aeval (fun l => (z i l:ℂ)) (coordinateLinearForm (Fin.castAdd 4) (T.A j)) ≠ 0
    rw [normIntegralPoint_left]
    apply (map_ne_zero (T.σ j)).mpr
    exact_mod_cast hA i
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact (heval i).2

end

section
open scoped Classical

noncomputable def quarticLowerEta (j : Fin 100) : ℝ := 1+(j.val:ℝ)/100
noncomputable def quarticUpperEta (j : Fin 100) : ℝ := 1+((j.val:ℝ)+1)/100
lemma quartic_eta_U (j : Fin 100) : quarticUpperEta j/4 = quarticU j := by
  simp only [quarticUpperEta,quarticU,quarticA,Nat.cast_add,Nat.cast_ofNat]
  ring
lemma quartic_eta_V (j : Fin 100) : 1-quarticLowerEta j/2 = quarticV j := by
  have hj : 2*j.val ≤ 200 := by have := j.isLt; omega
  simp only [quarticLowerEta,quarticV,quarticB,Nat.cast_sub hj,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem quartic_prime_bin (X F p : ℝ) (hX : 1 ≤ X) (hF : 1 ≤ F)
    (hp : X < p) (hp' : p ≤ F*X^2) :
    ∃ j : Fin 100, X^(quarticLowerEta j) < p ∧ p ≤ F*X^(quarticUpperEta j) := by
  let P (m : ℕ) : Prop := m ≤ 99 ∧ p ≤ F*X^(1+((m:ℝ)+1)/100:ℝ)
  have hex : ∃ m, P m := by
    refine ⟨99,by omega,?_⟩
    norm_num only [Nat.cast_ofNat,show (1+((99:ℝ)+1)/100:ℝ)=2 by norm_num,Real.rpow_two]
    exact hp'
  let m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  refine ⟨⟨m,by have := hm.1; omega⟩,?_,hm.2⟩
  by_cases hm0 : m=0
  · simpa only [quarticLowerEta,hm0,Nat.cast_zero,zero_div,add_zero,Real.rpow_one] using hp
  · have hprev : ¬P (m-1) := Nat.find_min hex (by dsimp [m] at hm0 ⊢; omega)
    have hpv : F*X^(1+(((m-1:ℕ):ℝ)+1)/100:ℝ) < p := by
      apply lt_of_not_ge
      intro he
      exact hprev ⟨by have := hm.1; omega,he⟩
    have hcast : ((m-1:ℕ):ℝ)+1=(m:ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one]; ring
    rw [hcast] at hpv
    have hx : 0 ≤ X^(1+(m:ℝ)/100:ℝ) := Real.rpow_nonneg (by linarith) _
    exact (le_mul_of_one_le_left hx hF).trans_lt hpv

theorem quartic_bin_exponents (j : Fin 100) (X F p : ℝ) (hX : 1 ≤ X) (hF : 1 ≤ F)
    (hp : X^(quarticLowerEta j) < p) (hp' : p ≤ F*X^(quarticUpperEta j)) :
    p^(1/4:ℝ) ≤ F*X^(quarticU j) ∧ X/p^(1/2:ℝ) ≤ X^(quarticV j) := by
  have hXp : 0 < X := by linarith
  have hFp : 0 < F := by linarith
  have hpp : 0 < p := (Real.rpow_pos_of_pos hXp _).trans hp
  constructor
  · have hb := Real.rpow_le_rpow (by linarith : 0 ≤ p) hp' (by norm_num : (0:ℝ) ≤ 1/4)
    rw [Real.mul_rpow hFp.le (Real.rpow_nonneg hXp.le _),←Real.rpow_mul hXp.le] at hb
    have hFr : F^(1/4:ℝ) ≤ F := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hF (by norm_num : (1/4:ℝ) ≤ 1)
    rw [show quarticUpperEta j*(1/4:ℝ)=quarticU j by rw [mul_one_div,quartic_eta_U]] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hFr (Real.rpow_nonneg hXp.le _))
  · have hb := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hp.le (by norm_num : (0:ℝ) ≤ 1/2)
    rw [←Real.rpow_mul hXp.le] at hb
    have hdiv := div_le_div_of_nonneg_left hXp.le (Real.rpow_pos_of_pos hXp _) hb
    have he : X/X^(quarticLowerEta j*(1/2:ℝ)) = X^(quarticV j) := by
      calc
        X/X^(quarticLowerEta j*(1/2:ℝ)) = X^(1:ℝ)/X^(quarticLowerEta j*(1/2:ℝ)) := by rw [Real.rpow_one]
        _ = X^(1-quarticLowerEta j*(1/2:ℝ)) := (Real.rpow_sub hXp _ _).symm
        _ = X^(quarticV j) := by rw [mul_one_div,quartic_eta_V]
    exact hdiv.trans_eq he

end

open NumberField Module
open scoped Classical BigOperators

theorem balanced_coordinates_quarticbox {K : Type} [Field K] [NumberField K] (b : Fin 100) (T : IntegralEmbeddingChart K 4) (μ : ℕ) (hμ : 0 < μ)
    (C F : ℝ) (hC : 1 ≤ C) (hF : 1 ≤ F) :
    ∃ Cbox : ℝ, 1 ≤ Cbox ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (p : ℕ), X^(quarticLowerEta b) < p →
      (p:ℝ) ≤ F*X^(quarticUpperEta b) → ∀ α β : 𝓞 K,
      (∀ w : InfinitePlace K, w (α:K) ≤ C*(p:ℝ)^((4:ℝ)⁻¹) ∧
        w ((β:K)/(μ:K)) ≤ (3*C^2)*(X/(p:ℝ)^((4:ℝ)⁻¹*(2:ℕ)))) →
      ∀ j, |(T.coord α j:ℝ)| ≤ Cbox*X^(quarticU b) ∧
        |(T.coord β j:ℝ)| ≤ Cbox*X^(quarticV b) := by
  obtain ⟨E,hE,hbound⟩ := T.coordinates_bound
  let Ca := E*(C*F)
  let Cb := E*((μ:ℝ)*(3*C^2))
  let Cbox := 1+Ca+Cb
  have hCp : 0 ≤ C := by linarith
  have hFp : 0 ≤ F := by linarith
  have hEp : 0 ≤ E := by linarith
  have hCa : 0 ≤ Ca := mul_nonneg hEp (mul_nonneg hCp hFp)
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have haC : Ca ≤ Cbox := by dsimp [Cbox]; linarith
  have hbC : Cb ≤ Cbox := by dsimp [Cbox]; linarith
  refine ⟨Cbox,by dsimp [Cbox]; linarith,fun X hX p hp hv α β harch j => ?_⟩
  have hXp : 0 < X := by linarith
  have hab := quartic_bin_exponents b X F p hX hF hp hv
  have hα (i) : ‖T.σ i (α:K)‖ ≤ (C*F)*X^(quarticU b) := by
    have hh := (harch (InfinitePlace.mk (T.σ i))).1
    rw [InfinitePlace.apply] at hh
    norm_num only [show (4:ℝ)⁻¹=1/4 by norm_num] at hh
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hab.1 hCp)
  have hβ (i) : ‖T.σ i (β:K)‖ ≤ ((μ:ℝ)*(3*C^2))*X^(quarticV b) := by
    have hh := (harch (InfinitePlace.mk (T.σ i))).2
    simp only [InfinitePlace.apply,map_div₀,map_natCast,Complex.norm_natCast] at hh
    norm_num only [Nat.cast_ofNat,show ((4:ℝ)⁻¹*2)=1/2 by norm_num] at hh
    have hμR : (0:ℝ) < μ := by exact_mod_cast hμ
    have ht : ‖T.σ i (β:K)‖/(μ:ℝ) ≤ (3*C^2)*X^(quarticV b) :=
      hh.trans (mul_le_mul_of_nonneg_left hab.2 (by positivity))
    have hh' := (div_le_iff₀ hμR).mp ht
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh'
  constructor
  · have hh := hbound α ((C*F)*X^(quarticU b)) (by positivity) hα j
    exact hh.trans (by simpa only [Ca,mul_assoc] using mul_le_mul_of_nonneg_right haC (Real.rpow_nonneg hXp.le _))
  · have hh := hbound β (((μ:ℝ)*(3*C^2))*X^(quarticV b)) (by positivity) hβ j
    exact hh.trans (by simpa only [Cb,mul_assoc] using mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hXp.le _))

end QuarticPowerFree

end OAI
