import OAI.NumberTheory.PowerFree.CurveThresholds

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical

theorem quotient_pair_generates {n d : ℕ} (a b : Fin d → MvPolynomial (Fin n) ℂ)
    (hg : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    Algebra.adjoin ℂ (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
      Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ := by
  let e := Ideal.Quotient.mkₐ ℂ I
  have hr : Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪ Set.range (fun i => Ideal.Quotient.mk I (b i)) =
      e '' (Set.range a ∪ Set.range b) := by
    simp only [Set.image_union,← Set.range_comp]
    rfl
  rw [hr,Algebra.adjoin_image,hg]
  apply top_unique
  intro z _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I z
  exact ⟨p,by trivial,_root_.rfl⟩

theorem norm_dimension_le {n d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (k : ℕ) (a b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) (θ : Fin d → ℂ)
    (ha : ∀ i, Ideal.Quotient.mk I (a i) ≠ 0)
    (heq : ∀ i, Ideal.Quotient.mk I (a i)^k*Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i))
    (hg : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤)
    (hq : Transcendental ℂ (Ideal.Quotient.mk I q)) : affineDimension I ≤ d+1 := by
  let := pair_projection_isAlgebraic k (fun i => Ideal.Quotient.mk I (a i))
    (fun i => Ideal.Quotient.mk I (b i)) (Ideal.Quotient.mk I q) θ ha heq (quotient_pair_generates a b hg I)
  obtain ⟨m,j,_,hj,ht⟩ := left_coordinates_transcendence_selection
    (fun i => Ideal.Quotient.mk I (a i)) (Ideal.Quotient.mk I q) hq
  have hm : m ≤ d := by simpa using Fintype.card_le_of_injective j hj
  have hdim := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
  rw [ht] at hdim
  have hh : affineDimension I = m+1 := by exact_mod_cast hdim
  omega

theorem polynomial_constant_at_point {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) (t : ℂ)
    (ht : algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) t = Ideal.Quotient.mk I q)
    (z : Fin n → ℤ) (hz : PointOn I z) : MvPolynomial.aeval (fun j => (z j:ℂ)) q = t := by
  have hh := congrArg (pointEvaluation I z hz) ht
  rw [AlgHom.commutes] at hh
  change t = MvPolynomial.aeval (fun j => (z j:ℂ)) q at hh
  exact hh.symm

theorem algebraic_polynomial_fibre_count {n : ℕ} (S : Finset (Fin n → ℤ)) (F : ℕ)
    (q : MvPolynomial (Fin n) ℂ)
    (hf : ∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) q = t)).card ≤ F)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hq : IsAlgebraic ℂ (Ideal.Quotient.mk I q)) : (S.filter (PointOn I)).card ≤ F := by
  obtain ⟨t,ht⟩ := algebraic_coordinate_constant (Ideal.Quotient.mk I q) hq
  apply (Finset.card_le_card ?_).trans (hf t)
  intro z hz
  have h := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨h.1,polynomial_constant_at_point I q t ht z h.2⟩

theorem algebraic_left_fibre_count {n d : ℕ} (S : Finset (Fin n → ℤ)) (F : ℕ)
    (x : Fin d → Fin n)
    (hf : ∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (x i) = c i)).card ≤ F)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hx : ∀ i, IsAlgebraic ℂ (Ideal.Quotient.mk I (MvPolynomial.X (x i)))) :
    (S.filter (PointOn I)).card ≤ F := by
  by_cases he : (S.filter (PointOn I)).Nonempty
  · obtain ⟨z,hz⟩ := he
    have hzI := (Finset.mem_filter.mp hz).2
    apply (Finset.card_le_card ?_).trans (hf (fun i => z (x i)))
    intro w hw
    obtain ⟨hwS,hwI⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨hwS,fun i => ?_⟩
    obtain ⟨t,ht⟩ := algebraic_coordinate_constant (Ideal.Quotient.mk I (MvPolynomial.X (x i))) (hx i)
    exact Int.cast_injective (α := ℂ) ((coordinate_constant_at_point I w hwI (x i) t ht).trans
      (coordinate_constant_at_point I z hzI (x i) t ht).symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    exact Nat.zero_le _

end
section
open MvPolynomial

theorem norm_generic_threshold_uniform {n d h : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8)
    (hh : 2 ≤ h) (hh' : h ≤ d) (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin d → ℂ), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^(d-2)*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = h → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → q.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w 5) → (∀ i, b i ∈ weightedSpace w 6) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 15*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^h/((h.factorial:ℝ)*(normBoxEnvelope d h)^h)-C*T^(h-1) ≤ weightedHilbert I ω T := by
  have hsucc : h-1+1 = h := by omega
  obtain ⟨C,hC,hbound⟩ := norm_real_hilbert_uniform (n := n) (d := d) (h := h-1) (K := ℂ)
    (k := d-2) (by omega) 5 6 (by norm_num) (by norm_num) E D hD 15 (by norm_num)
  refine ⟨C,hC,fun I _ a b q θ hθ ha heq hg hq hdim hdeg hadeg hqdeg w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hbound I a b q θ hθ ha heq (quotient_pair_generates a b hg I) hq
    (hsucc ▸ hdim) (hsucc ▸ hh') hdeg hadeg hqdeg w hw haw hbw ω hω hscale T hT
  rw [hsucc] at hb
  norm_num only [Nat.min_def,show (5:ℕ) ≤ 6 by omega,ite_true,Nat.cast_ofNat] at hb
  have hc := mul_le_mul_of_nonneg_right (normBox_generic_threshold d h hd hd' hh hh')
    (pow_nonneg (by linarith : 0 ≤ T) h)
  have hc' : T^h/((h.factorial:ℝ)*(normBoxEnvelope d h)^h) ≤
      5*(((d-2)*5+6:ℕ):ℝ)^(h-1)*15^h/((h.factorial:ℝ)*5^h*6^h)*T^h := by
    simpa only [one_div_mul_eq_div] using hc
  linarith only [hb,hc']

theorem norm_full_threshold_uniform {n d : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin d → ℂ),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^(d-2)*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = d+1 →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w 5) → (∀ i, b i ∈ weightedSpace w 6) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 15*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^(d+1)/(((d+1).factorial:ℝ)*(normBoxEnvelope d (d+1))^(d+1))-C*T^d ≤ weightedHilbert I ω T := by
  have hsucc : d-1+1 = d := by omega
  have hsucc' : d-1+2 = d+1 := by omega
  have hb := norm_full_real_hilbert_uniform (N := n) (n := d-1) (K := ℂ)
    (d-2) 5 6 (by norm_num) (by norm_num) 15 (by norm_num)
  rw [hsucc,hsucc'] at hb
  obtain ⟨C,hC,hbound⟩ := hb
  refine ⟨C,hC,fun I _ a b q θ ha heq hg hq hdim w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hbound I a b q θ ha heq (quotient_pair_generates a b hg I) hq
    hdim w hw haw hbw ω hω hscale T hT
  have hc := mul_le_mul_of_nonneg_right (normBox_full_threshold d hd hd')
    (pow_nonneg (by linarith : 0 ≤ T) (d+1))
  have hc' : T^(d+1)/(((d+1).factorial:ℝ)*(normBoxEnvelope d (d+1))^(d+1)) ≤
      (((d-2)*5+6:ℕ):ℝ)^(d-1)*15^(d+1)/(((d+1).factorial:ℝ)*5^d*6^d)*T^(d+1) := by
    simpa only [one_div_mul_eq_div] using hc
  norm_num only [Nat.cast_ofNat] at hb
  linarith only [hb,hc']

open MvPolynomial
open scoped BigOperators Classical

structure NormBoxSystem (n d D : ℕ) (ω : Fin n → ℝ) (w : Fin n → ℕ) where
  Carrier : Type
  [field : Field Carrier]
  [charZero : CharZero Carrier]
  v : Fin d → Carrier
  independent : LinearIndependent ℚ v
  σ : Fin d → Carrier →+* ℂ
  θ : Fin d → ℂ
  distinct : Function.Injective θ
  x : Fin d → Fin n
  xweight : ∀ i, ω (x i) = 1/3
  b : Fin d → MvPolynomial (Fin n) ℂ
  q : MvPolynomial (Fin n) ℂ
  generates : Algebra.adjoin ℂ
    (Set.range (fun i => coordinateLinearForm x (σ i ∘ v)) ∪ Set.range b) = ⊤
  leftDegree : ∀ i, (coordinateLinearForm x (σ i ∘ v)).totalDegree ≤ D
  qDegree : q.totalDegree ≤ D
  leftWeight : ∀ i, coordinateLinearForm x (σ i ∘ v) ∈ weightedSpace w 5
  rightWeight : ∀ i, b i ∈ weightedSpace w 6

attribute [instance] NormBoxSystem.field NormBoxSystem.charZero

noncomputable def NormBoxSystem.a {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  coordinateLinearForm M.x (M.σ i ∘ M.v)

noncomputable def NormBoxSystem.equation {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  M.a i^(d-2)*M.b i-M.q+C (M.θ i)

noncomputable def NormBoxSystem.ideal {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range M.equation)

theorem NormBoxSystem.quotient_equations {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (I : Ideal (MvPolynomial (Fin n) ℂ)) (hI : M.ideal ≤ I) :
    ∀ i, Ideal.Quotient.mk I (M.a i)^(d-2)*Ideal.Quotient.mk I (M.b i) =
      Ideal.Quotient.mk I M.q-algebraMap ℂ _ (M.θ i) := by
  intro i
  have hm : M.equation i ∈ I := hI (Ideal.subset_span ⟨i,rfl⟩)
  have he := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  simp only [NormBoxSystem.equation,map_add,map_sub,map_mul,map_pow] at he
  change Ideal.Quotient.mk I (M.a i)^(d-2)*Ideal.Quotient.mk I (M.b i)-
    Ideal.Quotient.mk I M.q+algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) (M.θ i) = 0 at he
  linear_combination he

theorem NormBoxSystem.quotient_left_nonzero {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℤ) (hz : PointOn I z)
    (ha : ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) :
    ∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0 := by
  intro i hi
  have hh := congrArg (pointEvaluation I z hz) hi
  rw [map_zero] at hh
  change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) = 0 at hh
  exact ha i hh

theorem NormBoxSystem.right_real_weight {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (hω : ∀ i, 0 < ω i) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (i : Fin d) :
    Ideal.Quotient.mk I (M.b i) ∈ weightedFunctions I ω (2/5) := by
  have hh := weightedSpace_map_le_weightedFunctions I w ω hω 15 (by norm_num) hscale (2/5) (by norm_num)
  norm_num only [show (15:ℝ)*(2/5) = 6 by norm_num,Nat.floor_natCast] at hh
  exact hh ⟨M.b i,M.rightWeight i,rfl⟩

end
open MvPolynomial
open scoped BigOperators Classical

theorem norm_component_alternatives {n d h D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8)
    (hh : 1 ≤ h) (hh' : h ≤ d+1) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 0 < Cbox)
    (F E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K H : ℝ, 1 ≤ K ∧ 0 ≤ H ∧ ∀ X : ℝ, 2 ≤ X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
      affineDimension I = h → affineDegree I ≤ E →
      (∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0) →
      ((S.filter (PointOn I)).card:ℝ) ≤ K*X^ε ∨
      ∀ T : ℝ, 1 ≤ T → T^h/((h.factorial:ℝ)*(normBoxEnvelope d h)^h)-H*T^(h-1) ≤ weightedHilbert I ω T := by
  classical
  have hsmall (X : ℝ) (hX : 2 ≤ X) (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) ℂ))
      (K : ℝ) (hKF : (F:ℝ) ≤ K) (hK : 0 ≤ K) (hcard : (S.filter (PointOn I)).card ≤ F) :
      ((S.filter (PointOn I)).card:ℝ) ≤ K*X^ε := by
    have hx : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
    calc
      _ ≤ (F:ℝ) := by exact_mod_cast hcard
      _ ≤ K := hKF
      _ ≤ K*X^ε := by nlinarith
  by_cases h1 : h = 1
  · subst h
    obtain ⟨B,H,hB,hH,hcurve⟩ := norm_curve_alternatives (n := n) (d := d) (by omega)
      (d-2) (by omega) ω hω M.x (1/3) (2/5) (2/5) Cbox (by norm_num) (by norm_num)
      (by norm_num) hCbox M.xweight hωW E ε hε
    let K : ℝ := max 1 (max B F)
    have hK : 1 ≤ K := le_max_left _ _
    have hKF : (F:ℝ) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    have hKB : B ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    refine ⟨K,H,hK,hH,fun X hX S hbox hnF haF I hI hMI hdim hdeg ha => ?_⟩
    let : I.IsPrime := hI
    by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
    · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_polynomial_fibre_count S F M.q hnF I hq))
    by_cases hxa : ∀ i, IsAlgebraic ℂ (Ideal.Quotient.mk I (MvPolynomial.X (M.x i)))
    · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_left_fibre_count S F M.x haF I hxa))
    push Not at hxa
    obtain ⟨s,hs⟩ := hxa
    have hsS (z) (hz : z ∈ S.filter (PointOn I)) := (Finset.mem_filter.mp hz).1
    have hh := hcurve M.Carrier M.v M.independent M.σ M.θ M.distinct X hX
      (S.filter (PointOn I)) (fun z hz j => hbox z (hsS z hz) j) I hI hdim.le hdeg
      (fun z hz => (Finset.mem_filter.mp hz).2) M.b M.q
      (M.right_real_weight hω hscale I) hq (M.quotient_equations I hMI) s hs
    rcases hh with hc | hHilb
    · left
      exact hc.trans (mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg (by linarith) _))
    · right
      intro T hT
      have hb := hHilb T (by linarith)
      have hc := mul_le_mul_of_nonneg_right (normBox_curve_threshold d hd hd') (by linarith : 0 ≤ T)
      norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one]
      have hc' : T/normBoxEnvelope d 1 ≤ min (2/(1/3:ℝ)) (max (1/(1/3:ℝ)) (((d-1)*(d-2-1):ℕ)/(2/5:ℝ)))*T := by
        simpa only [one_div_mul_eq_div] using hc
      linarith only [hb,hc']
  · have hh2 : 2 ≤ h := by omega
    by_cases hhd : h ≤ d
    · obtain ⟨H,hH,hHilb⟩ := norm_generic_threshold_uniform (n := n) hd hd' hh2 hhd E D hD
      let K : ℝ := max 1 F
      have hK : 1 ≤ K := le_max_left _ _
      have hKF : (F:ℝ) ≤ K := le_max_right _ _
      refine ⟨K,H,hK,hH,fun X hX S _ hnF _ I hI hMI hdim hdeg ha => ?_⟩
      let : I.IsPrime := hI
      by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
      · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_polynomial_fibre_count S F M.q hnF I hq))
      · exact Or.inr (hHilb I M.a M.b M.q M.θ M.distinct ha (M.quotient_equations I hMI)
          M.generates hq hdim hdeg M.leftDegree M.qDegree w hw M.leftWeight M.rightWeight ω hω hscale)
    · have he : h = d+1 := by omega
      subst h
      obtain ⟨H,hH,hHilb⟩ := norm_full_threshold_uniform (n := n) hd hd'
      let K : ℝ := max 1 F
      have hK : 1 ≤ K := le_max_left _ _
      have hKF : (F:ℝ) ≤ K := le_max_right _ _
      refine ⟨K,H,hK,hH,fun X hX S _ hnF _ I hI hMI hdim _ ha => ?_⟩
      let : I.IsPrime := hI
      by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
      · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_polynomial_fibre_count S F M.q hnF I hq))
      · right
        simpa only [Nat.add_sub_cancel] using hHilb I M.a M.b M.q M.θ ha (M.quotient_equations I hMI)
          M.generates hq hdim w hw M.leftWeight M.rightWeight ω hω hscale

end QuarticPowerFree

end OAI
