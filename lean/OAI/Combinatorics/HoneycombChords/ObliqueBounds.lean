import OAI.Combinatorics.HoneycombChords.OrderedAssociation

namespace OAI

/-!
# Oblique residual and denominator bounds

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Matrix MeasureTheory

lemma obliqueProjection_sub {N : ℕ} {H K : ℝ → ℂ}
    (hH : InPairingDomain N H) (hK : InPairingDomain N K) :
    obliqueProjection N (H-K)=obliqueProjection N H-obliqueProjection N K := by
  symm
  apply projection_unique
  · exact Submodule.sub_mem _ (projection_mem N H) (projection_mem N K)
  · intro j
    rw [pairing_sub (projection_integrable N H j) (projection_integrable N K j),
      projection_pairing,projection_pairing,pairing_sub (hH j) (hK j)]

lemma obliqueResidual_sub {N : ℕ} {H K : ℝ → ℂ}
    (hH : InPairingDomain N H) (hK : InPairingDomain N K) :
    obliqueResidual N (H-K)=obliqueResidual N H-obliqueResidual N K := by
  simp only [obliqueResidual,obliqueProjection_sub hH hK]
  abel

lemma familyGram_neg_left {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) :
    familyGram w (fun i x=> -F i x) G= -(familyGram w F G) := by
  ext i j
  simp only [familyGram,neg_mul,integral_neg,Matrix.neg_apply]

lemma cThree_neg_residual_positiveEvaluation (N : ℕ) :
    PositiveEvaluation (fun i x=>
      -residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) 0 i x) := by
  intro x hx hx0
  have he : evaluationMatrix (fun i x=>
      -residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) 0 i x) x=
      -(evaluationMatrix (residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) 0) x) := rfl
  rw [he,Matrix.det_neg]
  simp only [Fintype.card_fin,pow_add,pow_mul,neg_one_sq,one_pow,one_mul,pow_one,neg_mul,one_mul]
  exact neg_pos.mpr (cThree_residual_evaluation_neg N x hx hx0)

lemma cThree_residual_gram_neg (N : ℕ) :
    (familyGram stripDensity (residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) 0)
      (mixedFamily N)).det<0 := by
  have hi := residualFamily_pair_integrable stripDensity (fixedFamily N) (mixedFamily N)
    (fun x=>(C (3*angle/2) x).re) 0 (fixed_mixed_pair_integrable N)
      (pairingDomain_real_integrable (N:=N) (H:=C (3*angle/2))
        (C_ofReal_re (3*angle/2)) (cThree_in_pairingDomain N))
  have hn : ∀ i j,IntegrableOn (fun p=>
      (-residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) 0 i (p^2))*
        mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) := by
    intro i j
    apply (hi i j).neg.congr
    filter_upwards with p
    simp only [Pi.neg_apply,neg_mul]
  have hp:=familyGram_det_pos stripDensity _ (mixedFamily N) (cThree_neg_residual_positiveEvaluation N)
    (mixedFamily_positiveEvaluation N) (fun _ h=>stripDensity_pos h) hn
  rw [familyGram_neg_left,Matrix.det_neg] at hp
  simp only [Fintype.card_fin,pow_add,pow_mul,neg_one_sq,one_pow,one_mul,pow_one,neg_mul,one_mul] at hp
  exact neg_pos.mp hp

lemma cThree_residual_zero_neg (N : ℕ) :
    (obliqueResidual N (C (3*angle/2)) 0).re<0 := by
  have h0 : (C (3*angle/2) 0).re ≠ 0 := by rw [cThree_zero];norm_num
  rw [source_residual_mean (N:=N) (H:=C (3*angle/2)) (C_ofReal_re (3*angle/2)) (cThree_in_pairingDomain N) h0]
  simp only [Complex.ofReal_re,cThree_zero,one_mul,meanResidualRatio]
  exact div_neg_of_neg_of_pos (cThree_residual_gram_neg N) (fixed_mixed_Gram_det_pos N)

lemma hOne_residual_positiveEvaluation {N : ℕ} (hN : 1 ≤ N) :
    PositiveEvaluation (residualFamily (fixedFamily N) (fun x=>(hOne x).re) 0) := by
  intro x hx hx0
  let z:=nodeExtension x
  have hz i : 0<z i := nodeExtension_pos hx0 i
  have hzo : StrictMono (fun i : Fin (2*N+1)=>z i) := by simpa only [z,nodeExtension_fin] using hx
  have h:= (source_hOne_kernel_bounds hN (u:=0) le_rfl (by norm_num)
    (half_pos strip_angle_pos) (by linarith [strip_angle_pos]) z hz hzo).1
  have pp : 0<poleProduct (fun j=>z j+0) (shiftedPole 0 0) (2*N+1) := by
    apply poleProduct_pos _ (by simpa only [add_zero] using hz)
    norm_num [shiftedPole,physicalPole]
  rw [kernelOriginFunctional_eq_residual_det (interiorKnotLabels N (angle/2)) z 0
    (fun x=>(hOne x).re)] at h
  simp only [neg_zero,z,nodeExtension_fin] at h
  have hd:=(fixedFamily_positiveEvaluation N) x hx hx0
  have hh : 0<(evaluationMatrix (residualFamily (fixedFamily N) (fun x=>(hOne x).re) 0) x).det /
      (evaluationMatrix (fixedFamily N) x).det := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) pp) h
  exact (div_pos_iff.mp hh).elim (fun h=>h.1) (fun h=>False.elim (not_lt_of_ge hd.le h.2))

lemma hOne_residual_zero_pos {N : ℕ} (hN : 1 ≤ N) :
    0<(obliqueResidual N hOne 0).re := by
  have hi:=residualFamily_pair_integrable stripDensity (fixedFamily N) (mixedFamily N)
    (fun x=>(hOne x).re) 0 (fixed_mixed_pair_integrable N)
      (pairingDomain_real_integrable hOne_ofReal_re (hOne_in_pairingDomain N))
  have hp:=familyGram_det_pos stripDensity _ (mixedFamily N) (hOne_residual_positiveEvaluation hN)
    (mixedFamily_positiveEvaluation N) (fun _ h=>stripDensity_pos h) hi
  have h0:=hOne_re_pos (x:=0) (by norm_num)
  rw [source_residual_mean hOne_ofReal_re (hOne_in_pairingDomain N) h0.ne',Complex.ofReal_re]
  exact mul_pos h0 (div_pos hp (fixed_mixed_Gram_det_pos N))

/-- The residual denominator is strictly negative. -/
theorem source_residual_denominator_neg {N : ℕ} (hN : 1 ≤ N) :
    (obliqueResidual N cThreeCorrection 0).re<0 := by
  rw [cThreeCorrection,obliqueResidual_sub (cThree_in_pairingDomain N) (hOne_in_pairingDomain N),
    Pi.sub_apply,Complex.sub_re]
  linarith [cThree_residual_zero_neg N,hOne_residual_zero_pos hN]

theorem source_residual_denominator_ne_zero {N : ℕ} (hN : 1 ≤ N) :
    obliqueResidual N cThreeCorrection 0≠0 := by
  intro he
  have h:=source_residual_denominator_neg hN
  rw [he,Complex.zero_re] at h
  exact (lt_irrefl 0 h)

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Matrix MeasureTheory Filter

lemma cThree_minus_four_pos : 0<(C (3*angle/2) (-4)).re := by
  rw [C,ite_eq_right (show ¬(0:ℝ)≤ -4 by norm_num),Complex.ofReal_re]
  have hs : Real.sqrt (-(-4:ℝ))=2 := by norm_num
  rw [hs,show 3*angle/2*2=3*angle by ring]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> unfold angle <;> linarith [Real.pi_pos]

lemma extended_negative_phase : Real.sqrt ((3*angle/2)^2)*Real.sqrt 4<Real.pi/2 := by
  rw [Real.sqrt_sq (by linarith [strip_angle_pos] : 0≤3*angle/2)]
  norm_num
  unfold angle
  linarith [Real.pi_pos]

lemma cThree_residual_evaluation_minus_four_nonpos (N : ℕ) (x : Fin (2*N+1) → ℝ)
    (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    (evaluationMatrix (residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) (-4)) x).det≤0 := by
  have he:=residual_det_augment_at (fixedFamily N) (fun x=>(C (3*angle/2) x).re) (-4)
    cThree_minus_four_pos.ne' x
  have hh : 0≤(evaluationMatrix (Fin.lastCases (fun x=>(C (3*angle/2) x).re) (fixedFamily N))
      (Fin.cons (-4) x)).det := by
    rw [←extended_family]
    let v : Fin (2*N+2) → ℝ := Fin.cons 0 (fun i=>x i+4)
    have hv : StrictMono v := by
      intro i j
      refine Fin.cases ?_ (fun i=>?_) i
      · refine Fin.cases (fun h=>False.elim (lt_irrefl _ h)) (fun j _=>?_) j
        change 0<x j+4
        linarith [hx0 j]
      · refine Fin.cases (fun h=>False.elim (Fin.not_lt_zero _ h)) (fun j h=>?_) j
        change x i+4<x j+4
        have ht:=hx (Fin.succ_lt_succ_iff.mp h)
        linarith
    have hv0 : ∀ i,0≤v i := Fin.cases le_rfl (fun i=>by change 0≤x i+4;linarith [hx0 i])
    have ht:=translated_kernel_det_nonneg (a:=4) (R:=(3*angle/2)^2) (by norm_num)
      (sq_pos_of_pos (by linarith [strip_angle_pos] : 0<3*angle/2)) extended_negative_phase (extendedKnotLabels N)
      ((extendedKnot_monotone N).comp (fun _ _ h=>h))
      (fun i=>⟨extendedKnot_nonneg N i,extendedKnot_bound N i⟩) v hv hv0
    have hvx : (fun j=> -4+v j)=Fin.cons (-4) x := by
      funext j
      refine Fin.cases ?_ (fun j=>?_) j
      · simp [v]
      · simp [v]
    change 0≤(evaluationMatrix (fun i : Fin (2*N+2)=>cosineKernelJet
      (nodalOrder (extendedKnotLabels N) i) 0 (extendedKnotLabels N i)) (fun j : Fin (2*N+2)=> -4+v j)).det at ht
    rw [hvx] at ht
    exact ht
  have hn : (-1:ℝ)^(2*N+1)= -1 := by simp [pow_add,pow_mul]
  rw [hn] at he
  nlinarith [cThree_minus_four_pos]

lemma familyGram_det_nonneg_of_sorted {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (hD : ∀ p : Fin n → ℝ,StrictMono p → (∀ i,0<p i) → 0≤familyPointDensity w F G p)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    0≤(familyGram w F G).det := by
  let μ:=Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))
  have hae : ∀ᵐ p ∂μ,∀ i,0<p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  have hp:=pointDensity_lower_of_sorted w w F G F 0 (by simpa only [zero_mul] using hD)
  have hI : 0≤∫ p,familyPointDensity w F G p ∂μ := integral_nonneg_of_ae (hae.mono (by simpa only [zero_mul,Pi.zero_apply] using hp))
  rw [(family_gram_andreief w F G hi).2] at hI
  have hc : (0:ℝ)<Fintype.card (Equiv.Perm (Fin n)) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith only [hI,hc]

lemma cThree_residual_minus_four_nonpos (N : ℕ) :
    (obliqueResidual N (C (3*angle/2)) (-4)).re≤0 := by
  let R:=residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) (-4)
  have hi:=residualFamily_pair_integrable stripDensity (fixedFamily N) (mixedFamily N)
    (fun x=>(C (3*angle/2) x).re) (-4) (fixed_mixed_pair_integrable N)
      (pairingDomain_real_integrable (N:=N) (H:=C (3*angle/2))
        (C_ofReal_re (3*angle/2)) (cThree_in_pairingDomain N))
  have hn : ∀ i j,IntegrableOn (fun p=>(-R i (p^2))*mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) := by
    intro i j
    apply (hi i j).neg.congr
    filter_upwards with p
    simp only [Pi.neg_apply,neg_mul,R]
  have hg : 0≤(familyGram stripDensity (fun i x=> -R i x) (mixedFamily N)).det := by
    apply familyGram_det_nonneg_of_sorted _ _ _ _ hn
    intro p hp hp0
    have hp2 : StrictMono (fun i=>(p i)^2) := by
      intro i j hij
      exact (sq_lt_sq₀ (hp0 i).le (hp0 j).le).mpr (hp hij)
    have hs:=cThree_residual_evaluation_minus_four_nonpos N (fun i=>(p i)^2) hp2 (fun i=>sq_pos_of_pos (hp0 i))
    have he : evaluationMatrix (fun i x=> -R i x) (fun i=>(p i)^2)=
        -(evaluationMatrix R (fun i=>(p i)^2)) := rfl
    rw [familyPointDensity,he,Matrix.det_neg]
    simp only [Fintype.card_fin,pow_add,pow_mul,neg_one_sq,one_pow,one_mul,pow_one,neg_mul]
    exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(stripDensity_pos (hp0 i)).le))
      (neg_nonneg.mpr hs)) ((mixedFamily_positiveEvaluation N) _ hp2 (fun i=>sq_pos_of_pos (hp0 i))).le
  rw [familyGram_neg_left,Matrix.det_neg] at hg
  simp only [Fintype.card_fin,pow_add,pow_mul,neg_one_sq,one_pow,one_mul,pow_one,neg_mul] at hg
  rw [source_residual_mean (N:=N) (H:=C (3*angle/2)) (C_ofReal_re (3*angle/2))
    (cThree_in_pairingDomain N) cThree_minus_four_pos.ne',Complex.ofReal_re]
  apply mul_nonpos_of_nonneg_of_nonpos cThree_minus_four_pos.le
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonneg.mp hg) (fixed_mixed_Gram_det_pos N).le

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter Topology

lemma familyGram_det_le_of_sorted {n : ℕ} (w v : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (hD : ∀ p : Fin n → ℝ,StrictMono p → (∀ i,0<p i) →
      familyPointDensity w F G p≤familyPointDensity v F G p)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hv : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*v p) (Set.Ioi 0)) :
    (familyGram w F G).det≤(familyGram v F G).det := by
  let μ:=Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))
  have hae : ∀ᵐ p ∂μ,∀ i,0<p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  have hp:=pointDensity_lower_of_sorted v w F G F 1 (by simpa only [one_mul] using hD)
  have hI:=integral_mono_ae (family_gram_andreief w F G hi).1
    (family_gram_andreief v F G hv).1 (hae.mono (by simpa only [one_mul] using hp))
  rw [(family_gram_andreief w F G hi).2,(family_gram_andreief v F G hv).2] at hI
  have hc : (0:ℝ)<Fintype.card (Equiv.Perm (Fin n)) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith only [hI,hc]

lemma jetFixedMean_zero_bounds (N : ℕ) {s t : ℝ} (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) :
    0≤jetFixedMean N s t 0 ∧ jetFixedMean N s t 0≤jetFixedMean N s t 1 := by
  have hi (u : ℝ) (hu : 0≤u) : ∀ i j,IntegrableOn (fun p=>
      stripJetFamily N s i (p^2)*stripJetFamily N t j (p^2)*(physicalFixedWeight u p*stripDensity p)) (Set.Ioi 0) := by
    rw [physicalFixedWeight_characteristic hu]
    exact stripJet_characteristic_pair_integrable N hs hsL ht htL (by norm_num) _
  have hn : 0<(familyGram (fun p=>physicalFixedWeight 0 p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t)).det := by
    apply familyGram_det_pos _ _ _ (stripJet_positiveEvaluation N hs hsL) (stripJet_positiveEvaluation N ht htL)
      _ (hi 0 le_rfl)
    intro p hp
    apply mul_pos _ (stripDensity_pos hp)
    unfold physicalFixedWeight physicalPole
    positivity
  have hm := familyGram_det_le_of_sorted
    (fun p=>physicalFixedWeight 0 p*stripDensity p) (fun p=>physicalFixedWeight 1 p*stripDensity p)
    (stripJetFamily N s) (stripJetFamily N t) ?_ (hi 0 le_rfl) (hi 1 (by norm_num))
  · exact ⟨(div_pos hn (stripJet_gram_det_pos N hs hsL ht htL)).le,
      div_le_div_of_nonneg_right hm (stripJet_gram_det_pos N hs hsL ht htL).le⟩
  · intro p hpo hp0
    rw [familyPointDensity_tilt,familyPointDensity_tilt]
    apply mul_le_mul_of_nonneg_right _ (familyPointDensity_pos _ _ _ _
      (stripJet_positiveEvaluation N hs hsL) (stripJet_positiveEvaluation N ht htL)
        hp0 (fun _ h=>stripDensity_pos h) hpo.injective).le
    apply Finset.prod_le_prod₀
    · intro i _
      unfold physicalFixedWeight physicalPole
      positivity
    · intro i _
      unfold physicalFixedWeight
      apply div_le_div_of_nonneg_right (by linarith) (by unfold physicalPole;positivity)

/-- A decaying upper bound for residual means at the origin. -/
lemma physical_means_at_zero_upper :
    ∃ A : ℝ,0<A ∧ ∀ᶠ N : ℕ in atTop,∀ s t : ℝ,0<s → s<angle → 0<t → t<angle →
      let P:=((N:ℝ)+1)^(-5/8:ℝ)
      (0 ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) 0 ∧
      meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) 0 ≤ A*P) ∧
      (0 ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) 0 ∧
      meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) 0 ≤ A*P) := by
  obtain ⟨a,A,ha,hA,hbound⟩:=jetFixedMean_bounds (u:=1) (by norm_num) (by norm_num)
  simp only [Real.sqrt_one, show (3 * (1 - 8 / 3) / 8 : ℝ) = -5 / 8 by norm_num] at hbound
  let E : ℝ:=Real.exp (3*physicalPole 0)
  let ε : ℝ:=Real.log (3/2)/2
  have he : 0<ε := by dsimp [ε];exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨2*E*A+2,by dsimp [E];positivity,?_⟩
  filter_upwards [hbound,jetMovingMean_bound he,exponential_tail_below_power (-5/8),eventually_ge_atTop (1:ℕ)] with N hB hM htail hN
  intro s t hs hsL ht htL
  dsimp only
  let P : ℝ:=((N:ℝ)+1)^(-5/8:ℝ)
  have hP : 0<P := by dsimp [P];positivity
  obtain ⟨hB0,hB01⟩:=jetFixedMean_zero_bounds N hs hsL ht htL
  have hBu := hB01.trans (hB s t hs hsL ht htL).2
  have hT : 0<(movingPole N)^2 := lt_of_lt_of_le (by exact_mod_cast (by omega : 0<N)) (movingPole_sq_ge hN)
  have hpen := prefix_penalty_uniform hN (physicalPole_pos 0).le
  have hup : (2*(1+physicalPole 0/(movingPole N)^2)^(2*N+1))*jetFixedMean N s t 0+
      (2*(2/3:ℝ)^N)*jetMovingMean N s t ((movingPole N)^2) ≤ (2*E*A+2)*P := by
    have hfirst:=mul_le_mul_of_nonneg_right hpen hB0
    have hsecond:=mul_le_mul_of_nonneg_left (hM s t hs hsL ht htL) (show 0≤(2/3:ℝ)^N by positivity)
    have hfixed:=mul_le_mul_of_nonneg_left hBu (show 0≤E from (Real.exp_pos _).le)
    change (2/3:ℝ)^N*Real.exp (ε*N)≤P at htail
    change _≤E at hpen
    change _ ≤ E * jetFixedMean N s t 0 at hfirst
    change E * jetFixedMean N s t 0 ≤ E*(A*P) at hfixed
    linarith
  have hl₀:=hZero_mean_lower hN (u:=0) le_rfl (by norm_num) hs hsL ht htL
  have hl₁:=hOne_mean_lower hN (u:=0) le_rfl (by norm_num) hs hsL ht htL
  have hu₀:=hZero_mean_upper hN (u:=0) le_rfl (by norm_num) hT hs hsL ht htL
  have hu₁:=hOne_mean_upper hN (u:=0) le_rfl (by norm_num) hT hs hsL ht htL
  simp only [neg_zero] at hl₀ hl₁ hu₀ hu₁
  exact ⟨⟨hB0.trans hl₀,hu₀.trans hup⟩,⟨(mul_nonneg (by norm_num) hB0).trans hl₁,hu₁.trans hup⟩⟩

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

lemma pinned_residual_det {n : ℕ} (F : Fin (n+1) → ℝ → ℝ)
    (hF : ∀ x,F 0 x=1) (H : ℝ → ℝ) (a : ℝ) (x : Fin n → ℝ)
    (ha : H a≠0) (hHa : H a-H 0≠0) :
    (evaluationMatrix (residualFamily F H a) (Fin.cons 0 x)).det =
      ((H a-H 0)/H a)*
        (evaluationMatrix (residualFamily (fun i y=>F i.succ y-F i.succ 0)
          (fun y=>H y-H 0) a) x).det := by
  let B:=evaluationMatrix (residualFamily F H a) (Fin.cons 0 x)
  let R:=evaluationMatrix (residualFamily (fun i y=>F i.succ y-F i.succ 0)
    (fun y=>H y-H 0) a) x
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j=>
    Fin.cases (B 0 j) (fun i=>Fin.cases 0 (fun j=>R i j) j) i
  let c : Fin (n+1) → ℝ:=Fin.cons 0 (fun i=> -B i.succ 0 / B 0 0)
  have he : A.det=B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c])
    intro i j
    refine Fin.cases ?_ (fun i=>?_) i
    · simp [A,c]
    · refine Fin.cases ?_ (fun j=>?_) j
      · have hh : B 0 0≠0 := by
          dsimp [B,evaluationMatrix,residualFamily]
          simp only [hF,Fin.cons_zero]
          field_simp
          simpa only [mul_zero] using hHa
        simp [A,c,hh]
      · simp only [A,c,Fin.cases_succ,Fin.cons_succ]
        dsimp [B,R,evaluationMatrix,residualFamily]
        simp only [Fin.cons_succ,Fin.cons_zero,hF]
        field_simp
        ring
  rw [Matrix.det_succ_column_zero,Fin.sum_univ_succ] at he
  have hs : (∑ i : Fin n,(-1:ℝ)^i.succ.val*A i.succ 0*
      (A.submatrix i.succ.succAbove Fin.succ).det)=0 := by
    apply sum_eq_zero
    intro i _
    simp [A]
  rw [hs,add_zero] at he
  have hm : A.submatrix (0:Fin (n+1)).succAbove Fin.succ=R := by
    ext i j
    simp [A,Matrix.submatrix]
  rw [hm] at he
  have hb : A 0 0=(H a-H 0)/H a := by
    simp only [A,Fin.cases_zero,B,evaluationMatrix,residualFamily,Fin.cons_zero,hF]
    field_simp
  simpa only [Fin.val_zero,pow_zero,one_mul,hb,A,B,R] using he.symm

lemma zeroJet_as_tail {n : ℕ} (b : ℕ → ℝ) :
    (fun i : Fin (n+1) =>fun x=>cosineKernelJet (nodalOrder b i) 0 (b i) x) =
      Fin.cons (cosineKernelJet (nodalOrder b 0) 0 (b 0))
        (fun i : Fin n=>fun x=>cosineKernelJet (nodalOrder b (i+1)) 0 (b (i+1)) x) := by
  funext i
  refine Fin.cases rfl (fun i=>rfl) i

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Matrix MeasureTheory Filter Topology

lemma hZero_residual_zero_pos {N : ℕ} (hN : 1≤N) :
    0<(obliqueResidual N hZero 0).re := by
  have hF : PositiveEvaluation (residualFamily (fixedFamily N) (fun x=>(hZero x).re) 0) := by
    intro x hx hx0
    let z:=nodeExtension x
    have hz i : 0<z i := nodeExtension_pos hx0 i
    have hzo : StrictMono (fun i : Fin (2*N+1)=>z i) := by simpa only [z,nodeExtension_fin] using hx
    have h:= (source_hZero_kernel_bounds hN (u:=0) le_rfl (by norm_num)
      (half_pos strip_angle_pos) (by linarith [strip_angle_pos]) z hz hzo).1
    have pp : 0<poleProduct (fun j=>z j+0) (shiftedPole 0 0) (2*N+1) := by
      apply poleProduct_pos _ (by simpa only [add_zero] using hz)
      norm_num [shiftedPole,physicalPole]
    rw [kernelOriginFunctional_eq_residual_det (interiorKnotLabels N (angle/2)) z 0
      (fun x=>(hZero x).re)] at h
    simp only [neg_zero,z,nodeExtension_fin] at h
    have hd:=(fixedFamily_positiveEvaluation N) x hx hx0
    have hh : 0<(evaluationMatrix (residualFamily (fixedFamily N) (fun x=>(hZero x).re) 0) x).det /
        (evaluationMatrix (fixedFamily N) x).det := lt_of_lt_of_le pp h
    exact (div_pos_iff.mp hh).elim (fun h=>h.1) (fun h=>False.elim (not_lt_of_ge hd.le h.2))
  have hi:=residualFamily_pair_integrable stripDensity (fixedFamily N) (mixedFamily N)
    (fun x=>(hZero x).re) 0 (fixed_mixed_pair_integrable N)
      (pairingDomain_real_integrable hZero_ofReal_re (hZero_in_pairingDomain N))
  have hp:=familyGram_det_pos stripDensity _ (mixedFamily N) hF
    (mixedFamily_positiveEvaluation N) (fun _ h=>stripDensity_pos h) hi
  have h0:=hZero_re_pos (x:=0) (by norm_num)
  rw [source_residual_mean hZero_ofReal_re (hZero_in_pairingDomain N) h0.ne',Complex.ofReal_re]
  exact mul_pos h0 (div_pos hp (fixed_mixed_Gram_det_pos N))

lemma residual_ofReal_re (N : ℕ) {H : ℝ → ℂ} (hr : ∀ x,((H x).re:ℂ)=H x) (a : ℝ) :
    (((obliqueResidual N H a).re):ℂ)=obliqueResidual N H a := by
  have he : H=fun x=>((H x).re:ℂ) := by funext x;exact (hr x).symm
  rw [he,obliqueResidual,Pi.sub_apply,projection_ofReal,←Complex.ofReal_sub,Complex.ofReal_re]

lemma correction_ofReal_re (x : ℝ) : ((cThreeCorrection x).re:ℂ)=cThreeCorrection x := by
  change (((C (3*angle/2) x-hOne x).re):ℂ)=_
  rw [Complex.sub_re,Complex.ofReal_sub,C_ofReal_re,hOne_ofReal_re]
  rfl

lemma aStar_eq_ofReal : aStar=((2*Real.cos (2*angle)-1:ℝ):ℂ) := by
  simp only [aStar,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_ofNat]
lemma aStar_ofReal_re : ((aStar.re):ℂ)=aStar := by
  rw [aStar_eq_ofReal,Complex.ofReal_re]
lemma aStar_re_pos : 0<aStar.re := by
  rw [aStar_eq_ofReal,Complex.ofReal_re]
  unfold angle
  rw [show 2*(Real.pi/8)=Real.pi/4 by ring,Real.cos_pi_div_four]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

noncomputable def pinnedFamily (N : ℕ) : Fin (2*N+1) → ℝ → ℝ :=
  fun i=>zeroJet (extendedKnotLabels N) i
noncomputable def pinnedHZero (x : ℝ) : ℝ := (hZero x).re-1

lemma hZero_zero : (hZero 0).re=1 := by simp [hZero,D_zero]

lemma hZero_minus_four_gt_one : 1<(hZero (-4)).re := by
  have he : (hZero (-4)).re=1/(2*Real.cos (2*angle)-1) := by
    rw [hZero,D_neg_four,aStar_eq_ofReal,←Complex.ofReal_inv,Complex.ofReal_re,one_div]
  rw [he]
  have hd : 0<2*Real.cos (2*angle)-1 := by
    unfold angle
    rw [show 2*(Real.pi/8)=Real.pi/4 by ring,Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  apply (one_lt_div hd).mpr
  unfold angle
  rw [show 2*(Real.pi/8)=Real.pi/4 by ring,Real.cos_pi_div_four]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]

lemma pinnedHZero_minus_four_pos : 0<pinnedHZero (-4) := by
  dsimp [pinnedHZero]
  linarith [hZero_minus_four_gt_one]

lemma pinnedFamily_positiveEvaluation {N : ℕ} (hN : 1≤N) :
    PositiveEvaluation (pinnedFamily N) := by
  intro x hx hx0
  exact zeroJetEvaluation_det_pos (extendedKnotLabels N) x
    (fun _ _ h=>extendedKnot_monotone N h) (fun i=>extendedKnot_nonneg N i)
    (extendedKnot_first N (by omega)) hx hx0

lemma pinned_kernel_ratio {N : ℕ} (hN : 1≤N) (x : Fin (2*N+1) → ℝ) :
    (evaluationMatrix (residualFamily
      (fun i : Fin (2*N+2)=>cosineKernelJet (nodalOrder (extendedKnotLabels N) i) 0 (extendedKnotLabels N i))
      (fun x=>(hZero x).re) (-4)) (Fin.cons 0 x)).det /
      (jetEvaluation (extendedKnotLabels N) (Fin.cons 0 x)).det =
    (pinnedHZero (-4)/(hZero (-4)).re)*
      ((evaluationMatrix (residualFamily (pinnedFamily N) pinnedHZero (-4)) x).det /
       (evaluationMatrix (pinnedFamily N) x).det) := by
  have hf : extendedKnotLabels N 0=0 := extendedKnot_first N (by omega)
  have he:=pinned_residual_det
    (fun i : Fin (2*N+2)=>cosineKernelJet (nodalOrder (extendedKnotLabels N) i) 0 (extendedKnotLabels N i))
    (fun y=>jet_first_constant (extendedKnotLabels N) hf y) (fun x=>(hZero x).re) (-4) x
    (by linarith [hZero_minus_four_gt_one]) (by rw [hZero_zero];exact pinnedHZero_minus_four_pos.ne')
  rw [hZero_zero] at he
  rw [he,←zeroJetEvaluation_det (extendedKnotLabels N) x hf]
  exact mul_div_assoc _ _ _

lemma pinned_kernel_lower {N : ℕ} (hN : 1≤N) (x : Fin (2*N+1) → ℝ)
    (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    ((9/16:ℝ)*(hZero (-4)).re/pinnedHZero (-4)) *
      (∏ i,(x i+4)/(x i+physicalPole 0)) ≤
      (evaluationMatrix (residualFamily (pinnedFamily N) pinnedHZero (-4)) x).det /
       (evaluationMatrix (pinnedFamily N) x).det := by
  let z : ℕ → ℝ:=nodeExtension (Fin.cons 0 x)
  have hz (i) : 0≤z i := by
    unfold z nodeExtension
    split_ifs with h
    · exact Fin.cases le_rfl (fun i=>(hx0 i).le) ⟨i,h⟩
    · norm_num
  have hzo : StrictMono (fun i : Fin (2*N+2)=>z i) := by
    simp only [z,nodeExtension_fin]
    intro i j
    refine Fin.cases ?_ (fun i=>?_) i
    · refine Fin.cases (fun h=>False.elim (lt_irrefl _ h)) (fun j _=>hx0 j) j
    · refine Fin.cases (fun h=>False.elim (Fin.not_lt_zero _ h)) (fun j h=>?_) j
      exact hx (Fin.succ_lt_succ_iff.mp h)
  have hb:=kernel_hZero_bounds (n:=2*N+1) (q:=0) (u:=4) (R:=(3*angle/2)^2)
    (by norm_num) le_rfl (sq_pos_of_pos (by linarith [strip_angle_pos]))
    CriticalHoneycomb.FiniteFunctional.extended_negative_phase
    (extendedKnotLabels N) (fun i=>z i+4)
    (fun _ _ h=>extendedKnot_monotone N h)
    (fun i=>⟨extendedKnot_nonneg N i,extendedKnot_bound N i⟩) (by omega)
    (fun i hi=>by
      have he : i=0 := by omega
      subst i
      exact extendedKnot_first N (by omega))
    (fun i=>by linarith [hz i]) (fun i=>by linarith [hz i])
    (fun _ _ h=>by have ht:=hzo h;linarith)
  rw [kernelOriginFunctional_eq_residual_det (extendedKnotLabels N) z 4
    (fun x=>(hZero x).re)] at hb
  have he : (fun i : Fin (2*N+2)=>z i)=Fin.cons 0 x := by
    funext i;simp [z,nodeExtension_fin]
  rw [he,pinned_kernel_ratio hN x] at hb
  have hp : poleProduct (fun i=>z i+4) (shiftedPole 4 0) (2*N+2)=
      (9/16:ℝ)*(∏ i,(x i+4)/(x i+physicalPole 0)) := by
    rw [physical_pole_product]
    unfold fixedPoleProduct
    dsimp only [z]
    rw [nodeExtension_prod (Fin.cons 0 x) (fun y=>(y+4)/(y+physicalPole 0)),Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,zero_add]
    norm_num [physicalPole]
  rw [hp] at hb
  have hc : 0<pinnedHZero (-4)/(hZero (-4)).re :=
    div_pos pinnedHZero_minus_four_pos (by linarith [hZero_minus_four_gt_one])
  calc
    _ = ((9/16:ℝ)*(∏ i,(x i+4)/(x i+physicalPole 0)))/
        (pinnedHZero (-4)/(hZero (-4)).re) := by field_simp
    _ ≤ _ := (div_le_iff₀' hc).mpr hb.1

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology

lemma strip_jet_constant_pair_integrable {c : ℝ} (hc0 : 0≤c) (hc : c≤angle^2) (s : ℕ) :
    IntegrableOn (fun p=>cosineKernelJet s 0 c (p^2)*stripDensity p) (Set.Ioi 0) := by
  simpa only [cosineKernelJet_at_zero,pow_zero,mul_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]
    using strip_jet_pair_integrable (b:=0) (by rfl) hc0 (by positivity) hc 0 s

lemma pinnedFamily_pair_integrable (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>pinnedFamily N i (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
  have hi:=strip_jet_pair_integrable (extendedKnot_nonneg N (i+1)) (interiorKnot_nonneg N j t)
    (extendedKnot_bound N (i+1)) (interiorKnot_le N j ht htL)
    (nodalOrder (extendedKnotLabels N) (i+1)) (nodalOrder (interiorKnotLabels N t) j)
  have h0:=strip_jet_constant_pair_integrable (interiorKnot_nonneg N j t)
    (interiorKnot_le N j ht htL) (nodalOrder (interiorKnotLabels N t) j)
  convert hi.sub (h0.const_mul (cosineKernelJet (nodalOrder (extendedKnotLabels N) (i+1)) 0 (extendedKnotLabels N (i+1)) 0)) using 1
  funext p
  simp only [pinnedFamily,zeroJet,stripJetFamily,Pi.sub_apply]
  ring

lemma pinnedFamily_characteristic_pair_integrable (N : ℕ) {t z : ℝ} (ht : 0<t) (htL : t<angle)
    (hz : 0<z) (y : ℝ) (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>pinnedFamily N i (p^2)*stripJetFamily N t j (p^2)*
      (characteristicRatio y z p*stripDensity p)) (Set.Ioi 0) := by
  have hi:=pole_jet_pair_pencil_integrable (extendedKnot_nonneg N (i+1)) (interiorKnot_nonneg N j t)
    (extendedKnot_bound N (i+1)) (interiorKnot_le N j ht htL) hz
    (nodalOrder (extendedKnotLabels N) (i+1)) (nodalOrder (interiorKnotLabels N t) j) (-(y^2))
  have h0:=pole_jet_pair_pencil_integrable (b:=0) (by rfl) (interiorKnot_nonneg N j t)
    (by positivity) (interiorKnot_le N j ht htL) hz 0 (nodalOrder (interiorKnotLabels N t) j) (-(y^2))
  simp only [cosineKernelJet_at_zero,pow_zero,mul_zero,Nat.factorial_zero,Nat.cast_one,div_one] at h0
  apply (hi.sub (h0.const_mul (cosineKernelJet (nodalOrder (extendedKnotLabels N) (i+1)) 0 (extendedKnotLabels N (i+1)) 0))).congr
  filter_upwards with p
  simp only [Pi.sub_apply]
  rw [congrFun (pole_pencil_tilt_weight y z) p]
  simp only [pinnedFamily,zeroJet,stripJetFamily]
  ring

lemma pinnedFamily_jet_Gram_pos {N : ℕ} (hN : 1≤N) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    0<(familyGram stripDensity (pinnedFamily N) (stripJetFamily N t)).det :=
  familyGram_det_pos _ _ _ (pinnedFamily_positiveEvaluation hN) (stripJet_positiveEvaluation N ht htL)
    (fun _ h=>stripDensity_pos h) (pinnedFamily_pair_integrable N ht htL)

lemma pinnedHZero_jet_integrable (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (j : Fin (2*N+1)) :
    IntegrableOn (fun p=>pinnedHZero (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
  convert (hZero_stripJet_integrable N ht htL j).sub
    (strip_jet_constant_pair_integrable (interiorKnot_nonneg N j t) (interiorKnot_le N j ht htL)
      (nodalOrder (interiorKnotLabels N t) j)) using 1
  funext p
  simp only [pinnedHZero,stripJetFamily,Pi.sub_apply]
  ring

lemma pinnedFamily_measurable (N : ℕ) (i : Fin (2*N+1)) :
    Measurable (fun p=>pinnedFamily N i (p^2)*stripDensity p) := by
  have hc : Continuous (fun p : ℝ=>pinnedFamily N i (p^2)) :=
    ((cosineKernelJet_contDiff_right _ 0 _ 0).continuous.comp (by fun_prop)).sub continuous_const
  exact hc.measurable.mul (by unfold stripDensity;fun_prop)

lemma pinnedFamily_cosh_integrable (N : ℕ) (i : Fin (2*N+1)) :
    IntegrableOn (fun p=>|pinnedFamily N i (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  apply weighted_cosh_norm_integrable
  have hi:=strip_jet_pair_integrable (extendedKnot_nonneg N (i+1)) (sq_nonneg angle)
    (extendedKnot_bound N (i+1)) le_rfl (nodalOrder (extendedKnotLabels N) (i+1)) 0
  have h0:=strip_jet_constant_pair_integrable (sq_nonneg angle) le_rfl 0
  apply (hi.sub (h0.const_mul (cosineKernelJet (nodalOrder (extendedKnotLabels N) (i+1)) 0 (extendedKnotLabels N (i+1)) 0))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have he : cosineKernelJet 0 0 (angle^2) (p^2)=Real.cosh (angle*p) := by
    apply Complex.ofReal_injective
    rw [←C_eq_beta_square,C_sq _ hp.le]
  simp only [Pi.sub_apply,he,pinnedFamily,zeroJet]
  ring

lemma pinnedHZero_measurable : Measurable (fun p=>pinnedHZero (p^2)*stripDensity p) :=
  (hZero_sq_measurable.sub measurable_const).mul (by unfold stripDensity;fun_prop)

lemma pinnedHZero_cosh_integrable :
    IntegrableOn (fun p=>|pinnedHZero (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  have hi:=bounded_target_cosh_integrable (fun x=>(hZero x).re) hZero_sq_measurable
    (fun p hp=>hZero_sq_unit hp.le)
  have h0:=bounded_target_cosh_integrable (fun _=>1) measurable_const (by intros;norm_num)
  apply weighted_cosh_norm_integrable
  convert (weighted_cosh_signed_integrable (hZero_sq_measurable.mul (by unfold stripDensity;fun_prop)) hi).sub
    (weighted_cosh_signed_integrable (by simpa only [one_mul] using
      (show Measurable stripDensity by unfold stripDensity;fun_prop)) h0) using 1
  funext p
  simp only [Pi.sub_apply,Pi.mul_apply,pinnedHZero]
  ring

lemma pinnedFamily_mixed_pair_integrable (N : ℕ) (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>pinnedFamily N i (p^2)*mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) := by
  by_cases hj : j=centralIndex N
  · subst j
    simp only [mixedFamily,Function.update_self]
    have hi:=jet_realG_pair_integrable (extendedKnot_nonneg N (i+1)) (extendedKnot_bound N (i+1))
      (nodalOrder (extendedKnotLabels N) (i+1))
    have h0:=jet_realG_pair_integrable (b:=0) (by rfl) (by positivity) 0
    simp only [cosineKernelJet_at_zero,pow_zero,mul_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul] at h0
    convert hi.sub (h0.const_mul (cosineKernelJet (nodalOrder (extendedKnotLabels N) (i+1)) 0 (extendedKnotLabels N (i+1)) 0)) using 1
    funext p
    simp only [Pi.sub_apply,pinnedFamily,zeroJet]
    ring
  · simp only [mixedFamily,Function.update_of_ne hj]
    exact pinnedFamily_pair_integrable N (half_pos strip_angle_pos) (by linarith [strip_angle_pos]) i j

lemma pinnedFamily_mixed_Gram_pos {N : ℕ} (hN : 1≤N) :
    0<(familyGram stripDensity (pinnedFamily N) (mixedFamily N)).det :=
  familyGram_det_pos _ _ _ (pinnedFamily_positiveEvaluation hN) (mixedFamily_positiveEvaluation N)
    (fun _ h=>stripDensity_pos h) (pinnedFamily_mixed_pair_integrable N)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter Topology

lemma pinned_density_lower {N : ℕ} (hN : 1≤N) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    ∀ p : Fin (2*N+1) → ℝ,(∀ i,0<p i) →
      ((9/16:ℝ)*(hZero (-4)).re/pinnedHZero (-4))*
        familyPointDensity (fun p=>physicalFixedWeight 4 p*stripDensity p) (pinnedFamily N) (stripJetFamily N t) p ≤
      familyPointDensity stripDensity (residualFamily (pinnedFamily N) pinnedHZero (-4)) (stripJetFamily N t) p := by
  apply pointDensity_lower_of_sorted
  intro p hp hp0
  have hp2 : StrictMono (fun i=>(p i)^2) := by
    intro i j hij
    exact (sq_lt_sq₀ (hp0 i).le (hp0 j).le).mpr (hp hij)
  have hx0 i : 0<(p i)^2 := sq_pos_of_pos (hp0 i)
  have hd:=(pinnedFamily_positiveEvaluation hN) _ hp2 hx0
  have hbase : 0≤familyPointDensity stripDensity (pinnedFamily N) (stripJetFamily N t) p :=
    (familyPointDensity_pos _ _ _ _ (pinnedFamily_positiveEvaluation hN)
      (stripJet_positiveEvaluation N ht htL) hp0 (fun _ h=>stripDensity_pos h) hp.injective).le
  have h:=mul_le_mul_of_nonneg_right (pinned_kernel_lower hN (fun i=>(p i)^2) hp2 hx0) hbase
  rw [normalized_residual_density _ _ _ _ _ _ hd.ne',familyPointDensity_tilt]
  change _ ≤ _ at h
  simpa only [physicalFixedWeight,mul_assoc] using h

lemma pinned_mean_lower {N : ℕ} (hN : 1≤N) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    ((9/16:ℝ)*(hZero (-4)).re/pinnedHZero (-4))*
      ((familyGram (fun p=>characteristicRatio 2 (8/3) p*stripDensity p) (pinnedFamily N) (stripJetFamily N t)).det/
        (familyGram stripDensity (pinnedFamily N) (stripJetFamily N t)).det) ≤
      meanResidualRatio stripDensity (pinnedFamily N) (stripJetFamily N t) pinnedHZero (-4) := by
  have he : physicalFixedWeight 4=characteristicRatio 2 (8/3) := by
    rw [physicalFixedWeight_characteristic (by norm_num : (0:ℝ)≤4)]
    norm_num
  rw [←he]
  apply meanResidualRatio_lower
  · exact pinnedFamily_pair_integrable N ht htL
  · rw [he]
    exact pinnedFamily_characteristic_pair_integrable N ht htL (by norm_num) 2
  · exact pinnedHZero_jet_integrable N ht htL
  · exact pinnedFamily_jet_Gram_pos hN ht htL
  · exact pinned_density_lower hN ht htL

lemma mixedGram_ratio_lower (N : ℕ) (w : ℝ → ℝ) (F R : Fin (2*N+1) → ℝ → ℝ) (a : ℝ)
    (hfm : ∀ i,Measurable (fun p=>F i (p^2)*w p))
    (hfi : ∀ i,IntegrableOn (fun p=>|F i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hrm : ∀ i,Measurable (fun p=>R i (p^2)*w p))
    (hri : ∀ i,IntegrableOn (fun p=>|R i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hd : 0<(familyGram w F (mixedFamily N)).det)
    (hdt : ∀ t,0<t → t<angle → 0<(familyGram w F (stripJetFamily N t)).det)
    (hb : ∀ t,0<t → t<angle →
      a ≤ (familyGram w R (stripJetFamily N t)).det/(familyGram w F (stripJetFamily N t)).det) :
    a ≤ (familyGram w R (mixedFamily N)).det/(familyGram w F (mixedFamily N)).det := by
  have hcontF : ContinuousOn (fun t=>(familyGram w F (parameterFamily N t)).det) (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact (continuous_id.matrix_det).comp_continuousOn (parameterGram_continuousOn N w F hfm hfi)
  have hcontR : ContinuousOn (fun t=>(familyGram w R (parameterFamily N t)).det) (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact (continuous_id.matrix_det).comp_continuousOn (parameterGram_continuousOn N w R hrm hri)
  have hlo:=intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) strip_angle_pos.le
    (hcontF.intervalIntegrable.const_mul a) hcontR.intervalIntegrable
    (fun t ht=>by
      rw [parameterFamily_interior N ht.1 ht.2]
      exact (le_div_iff₀ (hdt t ht.1 ht.2)).mp (hb t ht.1 ht.2))
  rw [intervalIntegral.integral_const_mul,←mixedGram_det_integral N w F hfm hfi,
    ←mixedGram_det_integral N w R hrm hri] at hlo
  exact (le_div_iff₀ hd).mpr hlo

/-- A lower bound for the zero-pinned interpolation functional. -/
theorem pinned_mixed_mean_lower :
    ∃ a : ℝ,0<a ∧ ∀ᶠ N : ℕ in atTop,
      a*((N:ℝ)+1)^(-1/4:ℝ) ≤
        meanResidualRatio stripDensity (pinnedFamily N) (mixedFamily N) pinnedHZero (-4) := by
  obtain ⟨a,A,ha,hA,hB⟩:=second_oblique_characteristic_product_bounds (y:=2) (z:=8/3) (by norm_num) (by norm_num)
  let c : ℝ := (9/16:ℝ)*(hZero (-4)).re/pinnedHZero (-4)
  have hc : 0<c := div_pos (mul_pos (by norm_num) (by linarith [hZero_minus_four_gt_one])) pinnedHZero_minus_four_pos
  refine ⟨c*a,mul_pos hc ha,?_⟩
  filter_upwards [hB,eventually_ge_atTop (1:ℕ)] with N hB hN
  have hr:=residual_cosh_integrable (pinnedFamily N) pinnedHZero (-4)
    (pinnedFamily_measurable N) pinnedHZero_measurable (pinnedFamily_cosh_integrable N) pinnedHZero_cosh_integrable
  apply mixedGram_ratio_lower N stripDensity (pinnedFamily N) (residualFamily (pinnedFamily N) pinnedHZero (-4)) _
    (pinnedFamily_measurable N) (pinnedFamily_cosh_integrable N) (fun i=>(hr i).1) (fun i=>(hr i).2)
    (pinnedFamily_mixed_Gram_pos hN) (fun t ht htL=>pinnedFamily_jet_Gram_pos hN ht htL)
  intro t ht htL
  have hl:=(hB t ht htL).1
  norm_num only [show (3*((2:ℝ)-8/3)/8)= -1/4 by norm_num] at hl
  have hm:=mul_le_mul_of_nonneg_left hl hc.le
  rw [←mul_assoc] at hm
  simpa only [meanResidualRatio,neg_div] using hm.trans (pinned_mean_lower hN ht htL)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory

lemma meanResidualRatio_realization {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H P : ℝ → ℝ) (a : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hd : (familyGram w F G).det≠0) (ha : H a≠0)
    (hP : P ∈ Submodule.span ℝ (Set.range F))
    (hp : ∀ j,(∫ p in Set.Ioi 0,P (p^2)*G j (p^2)*w p)=
      ∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p) :
    H a*meanResidualRatio w F G H a=H a-P a := by
  obtain ⟨c,rfl⟩:=(Submodule.mem_span_range_iff_exists_fun ℝ).mp hP
  let A:=familyGram w F G
  let v:=fun j=>∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p
  have hc : A.transpose *ᵥ c=v := by
    ext j
    have hej : (fun p=>(∑ i,c i • F i) (p^2)*G j (p^2)*w p)=
        fun p=>∑ i,c i*(F i (p^2)*G j (p^2)*w p) := by
      funext p
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,sum_mul]
      apply sum_congr rfl
      intro i _
      ring
    have hpj := hp j
    rw [hej,integral_finsetSum _ (fun i _=>(hi i j).const_mul (c i))] at hpj
    simp_rw [integral_const_mul] at hpj
    simpa only [A,v,mulVec,dotProduct,familyGram,transpose_apply,mul_comm] using hpj
  have hsolve : c=A.transpose⁻¹ *ᵥ v := by
    rw [←hc,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A.transpose
      (isUnit_iff_ne_zero.mpr (by simpa only [det_transpose] using hd)),Matrix.one_mulVec]
  have heval : (∑ i,c i • F i) a=v ⬝ᵥ (A⁻¹ *ᵥ (fun i=>F i a)) := by
    rw [hsolve,Matrix.dotProduct_mulVec,←Matrix.transpose_nonsing_inv]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,dotProduct,Matrix.mulVec,Matrix.vecMul,Matrix.transpose_apply,mul_comm]
  rw [meanResidualRatio_formula w F G H a hi hH hd,heval]
  have he : (fun i=>F i a/H a)=(H a)⁻¹ • (fun i=>F i a) := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mulVec_smul,dotProduct_smul]
  simp only [smul_eq_mul]
  dsimp only [A,v]
  field_simp

lemma zeroJet_span_of_eq_zero {n : ℕ} (b : ℕ → ℝ) (hb : b 0=0) (P : ℝ → ℝ)
    (hP : P ∈ Submodule.span ℝ (Set.range (fun i : Fin (n+1)=>cosineKernelJet (nodalOrder b i) 0 (b i))))
    (h0 : P 0=0) :
    P ∈ Submodule.span ℝ (Set.range (fun i : Fin n=>zeroJet b i)) := by
  obtain ⟨c,rfl⟩:=(Submodule.mem_span_range_iff_exists_fun ℝ).mp hP
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨fun i=>c i.succ,?_⟩
  funext x
  symm
  have hc : jetCombination b c 0=0 := by
    simpa only [jetCombination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using h0
  simpa only [jetCombination,zeroJetCombination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
    jetCombination_eq_zeroCombination b c hb hc x

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Matrix Finset MeasureTheory Filter

lemma real_projection_mem (N : ℕ) (H : ℝ → ℂ) :
    (fun x=>(obliqueProjection N H x).re) ∈ Submodule.span ℝ (Set.range (fixedFamily N)) := by
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨fun i=>(projectionCoefficients N H i).re,?_⟩
  funext x
  simp only [obliqueProjection,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,fBasis,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

lemma real_projection_cast (N : ℕ) {H : ℝ → ℂ} (hr : ∀ x,((H x).re:ℂ)=H x) (x : ℝ) :
    (((obliqueProjection N H x).re):ℂ)=obliqueProjection N H x := by
  have he : H=fun x=>((H x).re:ℂ) := by funext x;exact (hr x).symm
  rw [he,projection_ofReal,Complex.ofReal_re]

lemma extended_span_contains_fixed (N : ℕ) :
    Submodule.span ℝ (Set.range (fixedFamily N)) ≤
    Submodule.span ℝ (Set.range (fun i : Fin (2*N+2)=>
      cosineKernelJet (nodalOrder (extendedKnotLabels N) i) 0 (extendedKnotLabels N i))) := by
  rw [extended_family]
  apply Submodule.span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨i.castSucc,by simp⟩

lemma extended_span_contains_cThree (N : ℕ) :
    (fun x=>(C (3*angle/2) x).re) ∈
    Submodule.span ℝ (Set.range (fun i : Fin (2*N+2)=>
      cosineKernelJet (nodalOrder (extendedKnotLabels N) i) 0 (extendedKnotLabels N i))) := by
  rw [extended_family]
  apply Submodule.subset_span
  exact ⟨Fin.last _,by simp⟩

lemma extended_span_contains_one {N : ℕ} (hN : 1≤N) :
    (fun _ : ℝ=>(1:ℝ)) ∈
    Submodule.span ℝ (Set.range (fun i : Fin (2*N+2)=>
      cosineKernelJet (nodalOrder (extendedKnotLabels N) i) 0 (extendedKnotLabels N i))) := by
  apply Submodule.subset_span
  refine ⟨0,?_⟩
  funext x
  exact jet_first_constant (extendedKnotLabels N) (extendedKnot_first N (by omega)) x

/-- The zero-pinned mean is realized by the mixed Gram system. -/
theorem pinned_realization {N : ℕ} (hN : 1≤N) :
    pinnedHZero (-4)*meanResidualRatio stripDensity (pinnedFamily N) (mixedFamily N) pinnedHZero (-4)=
      (obliqueResidual N hZero (-4)).re-
        (obliqueResidual N (C (3*angle/2)) (-4)).re *
          (obliqueResidual N hZero 0).re/(obliqueResidual N (C (3*angle/2)) 0).re := by
  let H : ℝ → ℝ := fun x=>(hZero x).re
  let J : ℝ → ℝ := fun x=>(C (3*angle/2) x).re
  let PH : ℝ → ℝ := fun x=>(obliqueProjection N hZero x).re
  let PJ : ℝ → ℝ := fun x=>(obliqueProjection N (C (3*angle/2)) x).re
  let d : ℝ := (obliqueResidual N hZero 0).re/(obliqueResidual N (C (3*angle/2)) 0).re
  let P : ℝ → ℝ := PH-d • PJ+d • J-(fun _=>1)
  have hd : (obliqueResidual N (C (3*angle/2)) 0).re≠0 := (cThree_residual_zero_neg N).ne
  have hP0 : P 0=0 := by
    dsimp [P,PH,PJ,J,d]
    simp only [cThree_zero]
    simp only [obliqueResidual,Pi.sub_apply,Complex.sub_re,hZero_zero,cThree_zero]
    simp only [obliqueResidual,Pi.sub_apply,Complex.sub_re,cThree_zero] at hd
    field_simp
    ring
  have hPs : P∈Submodule.span ℝ (Set.range (pinnedFamily N)) := by
    apply zeroJet_span_of_eq_zero (extendedKnotLabels N) (extendedKnot_first N (by omega)) P _ hP0
    apply Submodule.sub_mem
    · apply Submodule.add_mem
      · exact Submodule.sub_mem _ (extended_span_contains_fixed N (real_projection_mem N hZero))
          (Submodule.smul_mem _ d (extended_span_contains_fixed N (real_projection_mem N (C (3*angle/2)))))
      · exact Submodule.smul_mem _ d (extended_span_contains_cThree N)
    · exact extended_span_contains_one hN
  have hcP : (fun x=>(P x:ℂ))=obliqueProjection N hZero-(d:ℂ) • obliqueProjection N (C (3*angle/2))+
      (d:ℂ) • C (3*angle/2)-(fun _=>1) := by
    funext x
    simp only [P,PH,PJ,J,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_one,
      real_projection_cast N hZero_ofReal_re,real_projection_cast N (C_ofReal_re (3*angle/2)),C_ofReal_re]
  have hone : InPairingDomain N (fun _=>1) := by
    intro j
    have hz:=C_in_pairingDomain N 0 (by rw [abs_zero,add_zero];unfold angle;linarith [Real.pi_pos]) j
    have he : C 0=(fun _=>1) := funext C_parameter_zero
    rwa [he] at hz
  have hHp : InPairingDomain N (fun x=>(pinnedHZero x:ℂ)) := by
    have he : (fun x=>(pinnedHZero x:ℂ))=hZero-(fun _=>1) := by
      funext x
      simp only [pinnedHZero,Complex.ofReal_sub,Complex.ofReal_one,hZero_ofReal_re,Pi.sub_apply]
    rw [he]
    exact fun j=>(hZero_in_pairingDomain N j).sub (hone j)
  have hHi : ∀ j,IntegrableOn (fun p=>pinnedHZero (p^2)*mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) :=
    pairingDomain_real_integrable (by intro x;rfl) hHp
  have hp : ∀ j,(∫ p in Set.Ioi 0,P (p^2)*mixedFamily N j (p^2)*stripDensity p)=
      ∫ p in Set.Ioi 0,pinnedHZero (p^2)*mixedFamily N j (p^2)*stripDensity p := by
    intro j
    apply Complex.ofReal_injective
    rw [←pairing_ofReal,←pairing_ofReal,hcP]
    change pairing _ (gBasis N j)=pairing (fun x=>(pinnedHZero x:ℂ)) (gBasis N j)
    have he : (fun x=>(pinnedHZero x:ℂ))=hZero-(fun _=>1) := by
      funext x
      simp only [pinnedHZero,Complex.ofReal_sub,Complex.ofReal_one,hZero_ofReal_re,Pi.sub_apply]
    rw [he,pairing_sub ((projection_integrable N hZero j).sub
      ((projection_integrable N (C (3*angle/2)) j).smul (d:ℂ)) |>.add
        ((cThree_in_pairingDomain N j).smul (d:ℂ))) (hone j),
      pairing_add ((projection_integrable N hZero j).sub
        ((projection_integrable N (C (3*angle/2)) j).smul (d:ℂ)))
        ((cThree_in_pairingDomain N j).smul (d:ℂ)),
      pairing_sub (projection_integrable N hZero j) ((projection_integrable N (C (3*angle/2)) j).smul (d:ℂ)),
      pairing_smul,pairing_smul,projection_pairing,projection_pairing,
      pairing_sub (hZero_in_pairingDomain N j) (hone j)]
    ring
  rw [meanResidualRatio_realization stripDensity (pinnedFamily N) (mixedFamily N) pinnedHZero P (-4)
    (pinnedFamily_mixed_pair_integrable N) hHi (pinnedFamily_mixed_Gram_pos hN).ne'
    pinnedHZero_minus_four_pos.ne' hPs hp]
  dsimp [P,PH,PJ,J,d,pinnedHZero]
  simp only [Pi.sub_apply,obliqueResidual,Complex.sub_re]
  field_simp
  ring

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Filter Topology

/-- A lower bound for the zero-pinned residual in the physical bridge formula. -/
theorem pinned_source_residual_lower :
    ∃ a : ℝ,0<a ∧ ∀ᶠ N : ℕ in atTop,
      a*((N:ℝ)+1)^(-1/4:ℝ) ≤
        (obliqueResidual N hZero (-4)).re-
          (obliqueResidual N (C (3*angle/2)) (-4)).re *
            (obliqueResidual N hZero 0).re/(obliqueResidual N (C (3*angle/2)) 0).re := by
  obtain ⟨a,ha,hB⟩:=pinned_mixed_mean_lower
  refine ⟨pinnedHZero (-4)*a,mul_pos pinnedHZero_minus_four_pos ha,?_⟩
  filter_upwards [hB,eventually_ge_atTop (1:ℕ)] with N hB hN
  rw [←pinned_realization hN,mul_assoc]
  exact mul_le_mul_of_nonneg_left hB pinnedHZero_minus_four_pos.le

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Filter Topology

/-- A decaying upper bound at the origin for the two mixed residuals. -/
theorem source_h_residuals_at_zero_upper :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      let P := ((N:ℝ)+1)^(-5/8:ℝ)
      (0 ≤ (obliqueResidual N hZero 0).re ∧ (obliqueResidual N hZero 0).re ≤ A*P) ∧
      (0 ≤ (obliqueResidual N hOne 0).re ∧ (obliqueResidual N hOne 0).re ≤ A*P) := by
  obtain ⟨A,hA,hB⟩ := physical_means_at_zero_upper
  refine ⟨A,hA,?_⟩
  filter_upwards [hB] with N hN
  have hs : 0<angle/2 := half_pos strip_angle_pos
  have hsL : angle/2<angle := by linarith [strip_angle_pos]
  have h₀ := mixedMean_bounds N (fun x=>(hZero x).re) 0 0 _ hZero_sq_measurable
    (fun _ hp=>hZero_sq_unit hp.le)
    (fun t ht htL => (hN (angle/2) t hs hsL ht htL).1)
  have h₁ := mixedMean_bounds N (fun x=>(hOne x).re) 0 0 _ hOne_sq_measurable
    (fun _ hp=>hOne_sq_unit hp.le)
    (fun t ht htL => (hN (angle/2) t hs hsL ht htL).2)
  have hOne_zero : (hOne 0).re=1 := by simp [hOne,D_zero,C]
  rw [source_residual_mean hZero_ofReal_re (hZero_in_pairingDomain N)
    (by rw [hZero_zero];norm_num),
    source_residual_mean hOne_ofReal_re (hOne_in_pairingDomain N)
    (by rw [hOne_zero];norm_num)]
  simp only [Complex.ofReal_re,hZero_zero,hOne_zero,one_mul]
  exact ⟨h₀,h₁⟩

end CriticalHoneycomb.FiniteFunctional

end



end OAI
