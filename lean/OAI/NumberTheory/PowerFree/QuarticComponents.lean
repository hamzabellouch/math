import OAI.NumberTheory.PowerFree.QuarticSurfaces

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

def quarticA (j : Fin 100) : ℕ := 101+j.val
def quarticB (j : Fin 100) : ℕ := 200-2*j.val
def quarticNumerator (j : Fin 100) (h : ℕ) : ℕ :=
  if j.val < 60 then if h ≤ 2 then 206 else if h=3 then 200 else 191
  else if h=1 then 252 else if h=2 then 206 else 175
noncomputable def quarticEnvelope (j : Fin 100) (h : ℕ) : ℝ := quarticNumerator j h/1000
noncomputable def quarticU (j : Fin 100) : ℝ := quarticA j/400
noncomputable def quarticV (j : Fin 100) : ℝ := quarticB j/400
noncomputable def quarticStage (j : Fin 100) (i : Fin 5) : ℝ := quarticEnvelope j (5-i.val)
noncomputable def quarticIncrement (j : Fin 100) (i : Fin 5) : ℝ :=
  if i.val=0 then quarticStage j i else quarticStage j i-quarticEnvelope j (6-i.val)

lemma quarticA_pos (j : Fin 100) : 0 < quarticA j := by dsimp [quarticA]; omega
lemma quarticB_pos (j : Fin 100) : 0 < quarticB j := by have := j.isLt; dsimp [quarticB]; omega
lemma quarticU_pos (j : Fin 100) : 0 < quarticU j := by dsimp [quarticU]; exact div_pos (Nat.cast_pos.mpr (quarticA_pos j)) (by norm_num)
lemma quarticV_pos (j : Fin 100) : 0 < quarticV j := by dsimp [quarticV]; exact div_pos (Nat.cast_pos.mpr (quarticB_pos j)) (by norm_num)
lemma quarticEnvelope_pos (j : Fin 100) (h : ℕ) : 0 < quarticEnvelope j h := by
  unfold quarticEnvelope quarticNumerator; split_ifs <;> norm_num
lemma quarticU_le (j : Fin 100) : quarticU j ≤ 1/2 := by
  have : quarticA j ≤ 200 := by have := j.isLt; dsimp [quarticA]; omega
  dsimp [quarticU]; have : (quarticA j:ℝ) ≤ 200 := by exact_mod_cast this
  linarith
lemma quarticV_le (j : Fin 100) : quarticV j ≤ 1/2 := by
  have : quarticB j ≤ 200 := by dsimp [quarticB]; omega
  dsimp [quarticV]; have : (quarticB j:ℝ) ≤ 200 := by exact_mod_cast this
  linarith

lemma quartic_full_nat : ∀ j : Fin 100,
    (quarticA j)^4*(quarticB j)^4*1000^5 ≤
      (2*quarticA j+quarticB j)^3*400^5*(quarticNumerator j 5)^5 := by decide
lemma quartic_generic_nat : ∀ (j : Fin 100) (h : Fin 2),
    (quarticA j)^(h.val+3)*(quarticB j)^(h.val+3)*1000^(h.val+3) ≤
      min (quarticA j) (quarticB j)*(2*quarticA j+quarticB j)^(h.val+2)*400^(h.val+3)*(quarticNumerator j (h.val+3))^(h.val+3) := by decide
lemma quartic_affine_nat : ∀ j : Fin 100,
    (quarticA j)^2*(quarticB j)^2*1000^2 ≤
      min (2*quarticA j) (quarticB j)*(2*quarticA j+quarticB j)*400^2*(quarticNumerator j 2)^2 := by decide
lemma quartic_pole_nat : ∀ j : Fin 100,
    quarticA j*(quarticB j)^2*1000^2 ≤
      (quarticB j+4*quarticA j)*400^2*(quarticNumerator j 2)^2 := by decide

lemma quartic_increment_nonneg (j : Fin 100) (i : Fin 5) : 0 ≤ quarticIncrement j i := by
  by_cases hj : j.val < 60 <;> fin_cases i <;>
    norm_num [quarticIncrement,quarticStage,quarticEnvelope,quarticNumerator,hj]
lemma quartic_prefix (j : Fin 100) (i : Fin 5) :
    quarticStage j i ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin 5 => l.val ≤ i.val), quarticIncrement j l := by
  by_cases hj : j.val < 60 <;> fin_cases i <;>
    norm_num [quarticIncrement,quarticStage,quarticEnvelope,quarticNumerator,hj,Fin.sum_univ_succ,Finset.sum_filter]
lemma quartic_sum (j : Fin 100) :
    (∑ i : Fin 5, ((5-i.val:ℕ):ℝ)*quarticIncrement j i)+1/1000 ≤ 997/1000 := by
  by_cases hj : j.val < 60 <;>
    norm_num [quarticIncrement,quarticStage,quarticEnvelope,quarticNumerator,hj,Fin.sum_univ_succ]

lemma quartic_generic_rat : ∀ (j : Fin 100) (h : Fin 2),
    (1:ℚ)/((h.val+3).factorial*((quarticNumerator j (h.val+3):ℚ)/1000)^(h.val+3)) ≤
      min (quarticA j) (quarticB j)*(2*quarticA j+quarticB j:ℕ)^(h.val+2)*400^(h.val+3)/
        ((h.val+3).factorial*(quarticA j:ℚ)^(h.val+3)*(quarticB j:ℚ)^(h.val+3)) := by decide +kernel
lemma quartic_full_rat : ∀ j : Fin 100,
    (1:ℚ)/(120*((quarticNumerator j 5:ℚ)/1000)^5) ≤
      (2*quarticA j+quarticB j:ℕ)^3*400^5/(120*(quarticA j:ℚ)^4*(quarticB j:ℚ)^4) := by decide +kernel
lemma quartic_affine_rat : ∀ j : Fin 100,
    (1:ℚ)/(2*((quarticNumerator j 2:ℚ)/1000)^2) ≤
      min (2*quarticA j) (quarticB j)*(2*quarticA j+quarticB j:ℕ)*400^2/(2*(quarticA j:ℚ)^2*(quarticB j:ℚ)^2) := by decide +kernel
lemma quartic_pole_rat : ∀ j : Fin 100,
    (1:ℚ)/(2*((quarticNumerator j 2:ℚ)/1000)^2) ≤
      ((quarticB j:ℚ)/400+4*((quarticA j:ℚ)/400))/(2*((quarticA j:ℚ)/400)*((quarticB j:ℚ)/400)^2) := by decide +kernel
lemma quartic_curve_rat : ∀ j : Fin 100,
    (1:ℚ)/((quarticNumerator j 1:ℚ)/1000) ≤
      min (2/((quarticA j:ℚ)/400)) (max (1/((quarticA j:ℚ)/400)) (3/((quarticB j:ℚ)/400))) := by decide +kernel

lemma quartic_generic_threshold (j : Fin 100) (h : ℕ) (hh : 3 ≤ h) (hh' : h ≤ 4) :
    1/((h.factorial:ℝ)*(quarticEnvelope j h)^h) ≤
      ((min (quarticA j) (quarticB j):ℕ):ℝ)*(2*quarticA j+quarticB j:ℕ)^(h-1)*400^h/
        ((h.factorial:ℝ)*(quarticA j:ℝ)^h*(quarticB j:ℝ)^h) := by
  have hb := quartic_generic_rat j ⟨h-3,by omega⟩
  have he : h-3+3=h := by omega
  have he' : h-3+2=h-1 := by omega
  dsimp only at hb
  rw [he,he'] at hb
  dsimp only [quarticEnvelope]
  have hb' := (Rat.cast_le (K := ℝ)).mpr hb
  push_cast at hb'
  simpa only [Nat.cast_min, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hb'
lemma quartic_full_threshold (j : Fin 100) :
    1/(((5:ℕ).factorial:ℝ)*(quarticEnvelope j 5)^5) ≤
      (2*quarticA j+quarticB j:ℕ)^3*(400:ℝ)^5/(((5:ℕ).factorial:ℝ)*(quarticA j:ℝ)^4*(quarticB j:ℝ)^4) := by
  norm_num only [Nat.factorial]
  dsimp only [quarticEnvelope]
  have hb := (Rat.cast_le (K := ℝ)).mpr (quartic_full_rat j)
  push_cast at hb
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hb ⊢
  exact hb
lemma quartic_affine_threshold (j : Fin 100) :
    1/(2*(quarticEnvelope j 2)^2) ≤
      ((min (2*quarticA j) (quarticB j):ℕ):ℝ)*(2*quarticA j+quarticB j:ℕ)*(400:ℝ)^2/
        (2*(quarticA j:ℝ)^2*(quarticB j:ℝ)^2) := by
  dsimp only [quarticEnvelope]
  have hb := (Rat.cast_le (K := ℝ)).mpr (quartic_affine_rat j)
  push_cast at hb
  simpa only [Nat.cast_min, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hb
lemma quartic_pole_threshold (j : Fin 100) :
    1/(2*(quarticEnvelope j 2)^2) ≤
      (quarticV j+4*quarticU j)/(2*quarticU j*(quarticV j)^2) := by
  dsimp only [quarticEnvelope,quarticU,quarticV]
  have hb := (Rat.cast_le (K := ℝ)).mpr (quartic_pole_rat j)
  push_cast at hb
  exact hb
lemma quartic_curve_threshold (j : Fin 100) :
    1/quarticEnvelope j 1 ≤ min (2/quarticU j) (max (1/quarticU j) (3/quarticV j)) := by
  dsimp only [quarticEnvelope,quarticU,quarticV]
  have hb := (Rat.cast_le (K := ℝ)).mpr (quartic_curve_rat j)
  push_cast at hb
  exact hb

end

open MvPolynomial

theorem quartic_generic_threshold_uniform {n h : ℕ} (j : Fin 100)
    (hh : 3 ≤ h) (hh' : h ≤ 4) (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin 4 → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin 4 → ℂ), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^2*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = h → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → q.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w (quarticA j)) → (∀ i, b i ∈ weightedSpace w (quarticB j)) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 400*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h)-C*T^(h-1) ≤ weightedHilbert I ω T := by
  have hsucc : h-1+1 = h := by omega
  obtain ⟨C,hC,hbound⟩ := norm_real_hilbert_uniform (n := n) (d := 4) (h := h-1) (K := ℂ)
    (k := 2) (by omega) (quarticA j) (quarticB j) (quarticA_pos j) (quarticB_pos j) E D hD 400 (by norm_num)
  refine ⟨C,hC,fun I _ a b q θ hθ ha heq hg hq hdim hdeg hadeg hqdeg w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hbound I a b q θ hθ ha heq (quotient_pair_generates a b hg I) hq
    (hsucc ▸ hdim) (hsucc ▸ hh') hdeg hadeg hqdeg w hw haw hbw ω hω hscale T hT
  rw [hsucc] at hb
  have hc := mul_le_mul_of_nonneg_right (quartic_generic_threshold j h hh hh')
    (pow_nonneg (by linarith : 0 ≤ T) h)
  have hc' : T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h) ≤
      ((min (quarticA j) (quarticB j):ℕ):ℝ)*(2*quarticA j+quarticB j:ℕ)^(h-1)*400^h/
        ((h.factorial:ℝ)*(quarticA j:ℝ)^h*(quarticB j:ℝ)^h)*T^h := by
    simpa only [one_div_mul_eq_div] using hc
  linarith only [hb,hc']

theorem quartic_full_threshold_uniform {n : ℕ} (j : Fin 100) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin 4 → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin 4 → ℂ),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^2*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = 5 →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w (quarticA j)) → (∀ i, b i ∈ weightedSpace w (quarticB j)) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 400*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^5/(((5:ℕ).factorial:ℝ)*(quarticEnvelope j 5)^5)-C*T^4 ≤ weightedHilbert I ω T := by
  obtain ⟨C,hC,hbound⟩ := norm_full_real_hilbert_uniform (N := n) (n := 3) (K := ℂ)
    2 (quarticA j) (quarticB j) (quarticA_pos j) (quarticB_pos j) 400 (by norm_num)
  refine ⟨C,hC,fun I _ a b q θ ha heq hg hq hdim w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hbound I a b q θ ha heq (quotient_pair_generates a b hg I) hq
    hdim w hw haw hbw ω hω hscale T hT
  have hc := mul_le_mul_of_nonneg_right (quartic_full_threshold j) (pow_nonneg (by linarith : 0 ≤ T) 5)
  have hc' : T^5/(((5:ℕ).factorial:ℝ)*(quarticEnvelope j 5)^5) ≤
      (2*quarticA j+quarticB j:ℕ)^3*(400:ℝ)^5/(((5:ℕ).factorial:ℝ)*(quarticA j:ℝ)^4*(quarticB j:ℝ)^4)*T^5 := by
    simpa only [one_div_mul_eq_div] using hc
  linarith only [hb,hc']

open MvPolynomial
open scoped Classical BigOperators

theorem quartic_component_alternatives {n h D : ℕ} (j : Fin 100)
    (hh : 1 ≤ h) (hh' : h ≤ 5) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 1/2)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 400*ω i)
    (M : QuarticBoxSystem n D (quarticA j) (quarticB j) (quarticU j) ω w)
    (Cbox : ℝ) (hCbox : 0 < Cbox) (F R E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K H : ℝ, 1 ≤ K ∧ 0 ≤ H ∧ ∀ X : ℝ, 2 ≤ X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ i, |(z i:ℝ)| ≤ Cbox*X^(ω i)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun i => (z i:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i, MvPolynomial.aeval (fun l => (z l:ℂ)) (M.a i)=
        c*MvPolynomial.aeval (fun l => (z₀ l:ℂ)) (M.a i))).card ≤ R) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun l => (z l:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
      affineDimension I = h → affineDegree I ≤ E →
      (∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0) →
      ((S.filter (PointOn I)).card:ℝ) ≤ K*X^ε ∨
      ∀ T : ℝ, 1 ≤ T → T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h)-H*T^(h-1) ≤ weightedHilbert I ω T := by
  classical
  have hsmall (X : ℝ) (hX : 2 ≤ X) (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) ℂ))
      (K : ℝ) (hKF : ((F+R:ℕ):ℝ) ≤ K) (hK : 0 ≤ K) (hcard : (S.filter (PointOn I)).card ≤ F+R) :
      ((S.filter (PointOn I)).card:ℝ) ≤ K*X^ε := by
    have hx : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
    calc
      _ ≤ ((F+R:ℕ):ℝ) := by exact_mod_cast hcard
      _ ≤ K := hKF
      _ ≤ K*X^ε := by nlinarith
  have hB : (quarticB j:ℝ)=400*quarticV j := by dsimp [quarticV]; ring
  by_cases h1 : h = 1
  · subst h
    obtain ⟨B,H,hB',hH,hcurve⟩ := norm_curve_alternatives (n := n) (d := 4) (by omega)
      2 (by omega) ω hω M.x (quarticU j) (quarticV j) (1/2) Cbox (quarticU_pos j) (quarticV_pos j)
      (by norm_num) hCbox M.xweight hωW E ε hε
    let K : ℝ := max 1 (max B (F+R:ℕ))
    have hK : 1 ≤ K := le_max_left _ _
    have hKF : ((F+R:ℕ):ℝ) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    have hKB : B ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    refine ⟨K,H,hK,hH,fun X hX S hbox hnF haF _hr _hn I hI hMI hdim hdeg ha => ?_⟩
    let : I.IsPrime := hI
    by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
    · exact Or.inl (hsmall X hX S I K hKF (by linarith) ((algebraic_polynomial_fibre_count S F M.q hnF I hq).trans (by omega)))
    by_cases hxa : ∀ i, IsAlgebraic ℂ (Ideal.Quotient.mk I (MvPolynomial.X (M.x i)))
    · exact Or.inl (hsmall X hX S I K hKF (by linarith) ((algebraic_left_fibre_count S F M.x haF I hxa).trans (by omega)))
    push Not at hxa
    obtain ⟨s,hs⟩ := hxa
    have hsS (z) (hz : z ∈ S.filter (PointOn I)) := (Finset.mem_filter.mp hz).1
    have hh := hcurve M.Carrier M.v M.independent M.σ M.θ M.distinct X hX
      (S.filter (PointOn I)) (fun z hz i => hbox z (hsS z hz) i) I hI hdim.le hdeg
      (fun z hz => (Finset.mem_filter.mp hz).2) M.b M.q
      (M.right_real_weight hω 400 (quarticV j) (by norm_num) (quarticV_pos j).le hB hscale I) hq (M.quotient_equations I hMI) s hs
    rcases hh with hc | hHilb
    · left
      exact hc.trans (mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg (by linarith) _))
    · right
      intro T hT
      have hb := hHilb T (by linarith)
      have hc := mul_le_mul_of_nonneg_right (quartic_curve_threshold j) (by linarith : 0 ≤ T)
      norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one]
      have hc' : T/quarticEnvelope j 1 ≤ min (2/quarticU j) (max (1/quarticU j) (3/quarticV j))*T := by
        simpa only [one_div_mul_eq_div] using hc
      norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.cast_ofNat] at hb
      linarith only [hb,hc']
  · by_cases h2 : h=2
    · subst h
      obtain ⟨H,hH,hSurf⟩ := quartic_surface_alternatives hD (quarticU j) (quarticV j) 400
        (quarticU_pos j) (quarticV_pos j) (by norm_num) (by dsimp [quarticU]; ring) hB ω hω w hw hscale M E
      let K : ℝ := max 1 (F+R:ℕ)
      have hK : 1 ≤ K := le_max_left _ _
      have hKF : ((F+R:ℕ):ℝ) ≤ K := le_max_right _ _
      refine ⟨K,H,hK,hH,fun X hX S _ hnF haF hr hn I hI hMI hdim hdeg ha => ?_⟩
      let : I.IsPrime := hI
      by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
      · exact Or.inl (hsmall X hX S I K hKF (by linarith) ((algebraic_polynomial_fibre_count S F M.q hnF I hq).trans (by omega)))
      have hsub (z) (hz : z ∈ S.filter (PointOn I)) := (Finset.mem_filter.mp hz).1
      have hfilt (p : (Fin n → ℤ) → Prop) [DecidablePred p] :
          ((S.filter (PointOn I)).filter p).card ≤ (S.filter p).card :=
        Finset.card_le_card (by intro z hz; exact Finset.mem_filter.mpr ⟨hsub z (Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩)
      have hb := hSurf (S.filter (PointOn I)) F R (fun c => (hfilt _).trans (haF c))
        (fun z hz => (hfilt _).trans (hr z (hsub z hz))) (fun z hz => hn z (hsub z hz)) I hI hMI
        (fun z hz => (Finset.mem_filter.mp hz).2) ha hq hdim hdeg
      rcases hb with hc|hb
      · exact Or.inl (hsmall X hX S I K hKF (by linarith) hc)
      · right
        intro T hT
        have hc := mul_le_mul_of_nonneg_right (le_min (quartic_affine_threshold j) (quartic_pole_threshold j)) (sq_nonneg T)
        have hb := hb T hT
        norm_num only [Nat.factorial_two,Nat.cast_ofNat,Nat.reduceSub,pow_one]
        rw [one_div_mul_eq_div] at hc
        linarith only [hc,hb]
    · by_cases hhd : h ≤ 4
      · obtain ⟨H,hH,hHilb⟩ := quartic_generic_threshold_uniform (n := n) j (by omega) hhd E D hD
        let K : ℝ := max 1 (F+R:ℕ)
        have hK : 1 ≤ K := le_max_left _ _
        have hKF : ((F+R:ℕ):ℝ) ≤ K := le_max_right _ _
        refine ⟨K,H,hK,hH,fun X hX S _ hnF _ _ _ I hI hMI hdim hdeg ha => ?_⟩
        let : I.IsPrime := hI
        by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
        · exact Or.inl (hsmall X hX S I K hKF (by linarith) ((algebraic_polynomial_fibre_count S F M.q hnF I hq).trans (by omega)))
        · exact Or.inr (hHilb I M.a M.b M.q M.θ M.distinct ha (M.quotient_equations I hMI)
            M.generates hq hdim hdeg M.leftDegree M.qDegree w hw M.leftWeight M.rightWeight ω hω hscale)
      · have he : h=5 := by omega
        subst h
        obtain ⟨H,hH,hHilb⟩ := quartic_full_threshold_uniform (n := n) j
        let K : ℝ := max 1 (F+R:ℕ)
        have hK : 1 ≤ K := le_max_left _ _
        have hKF : ((F+R:ℕ):ℝ) ≤ K := le_max_right _ _
        refine ⟨K,H,hK,hH,fun X hX S _ hnF _ _ _ I hI hMI hdim _ ha => ?_⟩
        let : I.IsPrime := hI
        by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
        · exact Or.inl (hsmall X hX S I K hKF (by linarith) ((algebraic_polynomial_fibre_count S F M.q hnF I hq).trans (by omega)))
        · exact Or.inr (hHilb I M.a M.b M.q M.θ ha (M.quotient_equations I hMI)
            M.generates hq hdim w hw M.leftWeight M.rightWeight ω hω hscale)

end QuarticPowerFree

end OAI
