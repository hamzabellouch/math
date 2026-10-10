import OAI.Analysis.TraceCone.StrongDensity

namespace OAI

/-!
# Strong convergence of positive operators

Norm estimates for positive contractions and strong limits of bounded monotone
nets on a Hilbert space.
-/

noncomputable section
open Filter Topology

namespace TraceConeClassification
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open scoped InnerProductSpace

lemma positive_op_square_le (P : H →L[ℂ] H) (hP : 0 ≤ P) : star P*P ≤ ‖P‖ • P := by
  let R := CFC.sqrt P
  have hR : star R = R := (CFC.sqrt_nonneg P).isSelfAdjoint.star_eq
  have hRR : R*R = P := CFC.sqrt_mul_sqrt_self P hP
  have hsa : star P = P := hP.isSelfAdjoint.star_eq
  calc
    star P*P = star R*P*R := by rw [hsa,hR,← hRR]; simp only [mul_assoc]
    _ ≤ ‖P‖ • (star R*R) := CStarAlgebra.star_left_conjugate_le_norm_smul R P hP.isSelfAdjoint
    _ = ‖P‖ • P := by rw [hR,hRR]

lemma positive_op_normsq_le (P : H →L[ℂ] H) (hP : 0 ≤ P) (ξ : H) :
    ‖P ξ‖ ^ 2 ≤ ‖P‖ * (inner ℂ ξ (P ξ)).re := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr (positive_op_square_le P hP))
  have hh := hp.re_inner_nonneg_right ξ
  change 0 ≤ (inner ℂ ξ ((‖P‖ • P-star P*P) ξ)).re at hh
  simp only [sub_apply,inner_sub_right,Complex.sub_re] at hh
  have he : (inner ℂ ξ ((star P*P) ξ)).re = ‖P ξ‖ ^ 2 :=
    (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right P ξ).symm
  rw [he] at hh
  simpa only [smul_apply,inner_smul_right_eq_smul,Complex.real_smul,Complex.smul_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,sub_nonneg] using hh

lemma positive_contraction_error (P : H →L[ℂ] H) (hP : 0 ≤ P) (hn : ‖P‖ ≤ 1) (ξ : H) :
    ‖ξ-P ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2-‖P ξ‖ ^ 2 := by
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive.mp hP).re_inner_nonneg_right ξ
  have hh := (positive_op_normsq_le P hP ξ).trans (mul_le_of_le_one_left hpos hn)
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖ξ‖ ^ 2-2*(inner ℂ ξ (P ξ)).re+‖P ξ‖ ^ 2 ≤ _
  linarith

end TraceConeClassification

namespace TraceConeClassification
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
open scoped InnerProductSpace

omit [CompleteSpace H] in
lemma operator_inner_mono {S T : H →L[ℂ] H} (h : S ≤ T) (ξ : H) :
    (inner ℂ ξ (S ξ)).re ≤ (inner ℂ ξ (T ξ)).re := by
  have hh := (ContinuousLinearMap.le_def.mp h).re_inner_nonneg_right ξ
  change 0 ≤ (inner ℂ ξ ((T-S) ξ)).re at hh
  simpa only [sub_apply,inner_sub_right,Complex.sub_re,sub_nonneg] using hh

/-- Bounded monotone nets of positive operators are strongly Cauchy. This allows
arbitrary directed index sets, not only sequences or countable weights. -/
lemma monotone_operator_cauchy (T : ι → H →L[ℂ] H) (hT : Monotone T)
    (hpos : ∀ i, 0 ≤ T i) (a : H →L[ℂ] H) (ha : ∀ i, T i ≤ a) (ξ : H) :
    CauchySeq (fun i => T i ξ) := by
  let q : ι → ℝ := fun i => (inner ℂ ξ (T i ξ)).re
  have hq : Monotone q := fun i j hij => operator_inner_mono (hT hij) ξ
  have hb : BddAbove (Set.range q) := by
    refine ⟨(inner ℂ ξ (a ξ)).re,?_⟩
    rintro _ ⟨i,rfl⟩
    exact operator_inner_mono (ha i) ξ
  let c : ℝ := ⨆ i, q i
  have hqc : ∀ i, q i ≤ c := fun i => le_ciSup hb i
  have hlim : Tendsto q atTop (𝓝 c) := tendsto_atTop_ciSup hq hb
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance,?_⟩
  intro ε hε
  let δ := (ε/2)^2/(‖a‖+1)
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (half_pos hε)) (by positivity)
  obtain ⟨N,hN⟩ := (hlim.eventually (lt_mem_nhds (sub_lt_self c hδ))).exists
  have hdiff (i : ι) (hi : N ≤ i) : dist (T i ξ) (T N ξ) < ε/2 := by
    have hpi : 0 ≤ T i-T N := sub_nonneg.mpr (hT hi)
    have hia : T i-T N ≤ a := (sub_le_self _ (hpos N)).trans (ha i)
    have hnorm : ‖T i-T N‖ ≤ ‖a‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hia hpi
    have hsq := positive_op_normsq_le (T i-T N) hpi ξ
    have hform : (inner ℂ ξ ((T i-T N) ξ)).re = q i-q N := by
      simp only [sub_apply,inner_sub_right,Complex.sub_re,q]
    rw [hform] at hsq
    have hnon : 0 ≤ q i-q N := sub_nonneg.mpr (hq hi)
    have hsmall : q i-q N < δ := by linarith [hqc i]
    have hval : (‖a‖+1)*δ = (ε/2)^2 := by dsimp [δ]; field_simp
    have hsq' : ‖(T i-T N) ξ‖ ^ 2 < (ε/2)^2 := by
      calc
        ‖(T i-T N) ξ‖ ^ 2 ≤ ‖T i-T N‖*(q i-q N) := hsq
        _ ≤ (‖a‖+1)*(q i-q N) := mul_le_mul_of_nonneg_right (by linarith) hnon
        _ < (‖a‖+1)*δ := mul_lt_mul_of_pos_left hsmall (by positivity)
        _ = (ε/2)^2 := hval
    rw [dist_eq_norm]
    change ‖(T i-T N) ξ‖ < ε/2
    nlinarith [norm_nonneg ((T i-T N) ξ)]
  refine ⟨(fun i => T i ξ) '' Set.Ici N,?_,?_⟩
  · change {i | T i ξ ∈ (fun i => T i ξ) '' Set.Ici N} ∈ atTop
    exact (eventually_ge_atTop N).mono (fun i hi => ⟨i,hi,rfl⟩)
  · rintro _ ⟨i,hi,rfl⟩ _ ⟨j,hj,rfl⟩
    calc
      dist (T i ξ) (T j ξ) ≤ dist (T i ξ) (T N ξ)+dist (T N ξ) (T j ξ) := dist_triangle _ _ _
      _ < ε/2+ε/2 := add_lt_add (hdiff i hi) (by rw [dist_comm]; exact hdiff j hj)
      _ = ε := add_halves ε

lemma monotone_operator_strong_limit (T : ι → H →L[ℂ] H) (hT : Monotone T)
    (hpos : ∀ i, 0 ≤ T i) (a : H →L[ℂ] H) (ha : ∀ i, T i ≤ a) :
    ∃ S : H →L[ℂ] H, ∀ ξ, Tendsto (fun i => T i ξ) atTop (𝓝 (S ξ)) := by
  have he (ξ : H) := cauchySeq_tendsto_of_complete (monotone_operator_cauchy T hT hpos a ha ξ)
  choose L hL using he
  let f : H →ₗ[ℂ] H :=
    { toFun := L
      map_add' := fun ξ η => tendsto_nhds_unique (hL (ξ+η)) (by
        simpa only [map_add] using (hL ξ).add (hL η))
      map_smul' := fun c ξ => tendsto_nhds_unique (hL (c • ξ)) (by
        simpa only [map_smul, RingHom.id_apply] using (hL ξ).const_smul c) }
  have hf : ∀ ξ, ‖f ξ‖ ≤ ‖a‖*‖ξ‖ := by
    intro ξ
    apply le_of_tendsto (hL ξ).norm
    exact Eventually.of_forall (fun i => ((T i).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (CStarAlgebra.norm_le_norm_of_le_of_nonneg (ha i) (hpos i)) (norm_nonneg ξ)))
  exact ⟨f.mkContinuous ‖a‖ hf,hL⟩

omit [CompleteSpace H] in
/-- Positivity is closed along actual strong-operator limits. -/
lemma strong_limit_nonneg {κ : Type*} {l : Filter κ} [l.NeBot]
    (T : κ → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hlim : ∀ ξ, Tendsto (fun i => T i ξ) l (𝓝 (S ξ))) (hpos : ∀ᶠ i in l, 0 ≤ T i) : 0 ≤ S := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  constructor
  · intro ξ η
    have h₁ := (hlim ξ).inner (𝕜 := ℂ) (tendsto_const_nhds (x := η))
    have h₂ := (tendsto_const_nhds (x := ξ)).inner (𝕜 := ℂ) (hlim η)
    apply tendsto_nhds_unique h₁
    apply h₂.congr'
    exact hpos.mono (fun i hi => (ContinuousLinearMap.nonneg_iff_isPositive.mp hi).inner_left_eq_inner_right ξ η |>.symm)
  · intro ξ
    change 0 ≤ (inner ℂ (S ξ) ξ).re
    apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp
      ((hlim ξ).inner (𝕜 := ℂ) (tendsto_const_nhds (x := ξ))))
    exact hpos.mono (fun i hi => (ContinuousLinearMap.nonneg_iff_isPositive.mp hi).re_inner_nonneg_left ξ)

end TraceConeClassification

namespace TraceConeClassification
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An actual strong-operator approximating net, with the finite-set index
written explicitly. No first-countability of the operator topology is used. -/
lemma bicommutant_strong_net (C : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (C : Set (H →L[ℂ] H)))) :
    ∃ a : Finset H × ℕ → H →L[ℂ] H, (∀ p, a p ∈ C) ∧
      ∀ ξ, Tendsto (fun p => a p ξ) atTop (𝓝 (T ξ)) := by
  classical
  have he (p : Finset H × ℕ) : ∃ a ∈ C, ∀ ξ ∈ p.1,
      ‖a ξ-T ξ‖ < 1/(p.2+1:ℝ) := by
    let e := (Fintype.equivFin p.1).symm
    obtain ⟨a,ha,hap⟩ := bicommutant_strong_density C T hT (Fintype.card p.1)
      (fun i => (e i).1) (1/(p.2+1:ℝ)) (by positivity)
    refine ⟨a,ha,fun ξ hξ => ?_⟩
    simpa [e] using hap ((Fintype.equivFin p.1) ⟨ξ,hξ⟩)
  choose a ha hap using he
  refine ⟨a,ha,fun ξ => Metric.tendsto_nhds.mpr (fun ε hε => ?_)⟩
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({ξ},n) : Finset H × ℕ)] with p hp
  have hξ : ξ ∈ p.1 := hp.1 (Finset.mem_singleton_self ξ)
  have hle : (1:ℝ)/(p.2+1) ≤ 1/(n+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hp.2 1
  simpa only [dist_eq_norm] using (hap p ξ hξ).trans_le hle |>.trans hn

end TraceConeClassification

end

end OAI
