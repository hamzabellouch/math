import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicGlobalization
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFastEvaluation
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Finite periodic ansatz bounds with fixed coefficients and a varying fast scale. -/
noncomputable section
open Set
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion.Family
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Compact spatial control and periodicity give uniform bounds for all
mixed derivatives up to any prescribed finite order. -/
lemma compact_lift_derivative_bound (U : Family A E) {Q : Set A}
    (hQ : IsCompact Q) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ p ∈ Q, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun y : A × ℝ => U.val y.1 (y.2 : Period)) (p,t)‖ ≤ C := by
  let H : A × ℝ → E := fun y => U.val y.1 (y.2 : Period)
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound uniqueDiffOn_univ
    (hQ.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))) (subset_univ _)
    U.smooth.contDiffOn m
  refine ⟨C,zero_le_one.trans hC,?_⟩
  intro j hj p hp t
  let a : ℝ := AddCircle.equivIco 1 0 (t : Period)
  have ha : a ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco 1 0 (t : Period)).property
  have hca : (a : Period) = (t : Period) := AddCircle.coe_equivIco
  let c : ℝ := t-a
  have hcz : (c : Period) = 0 := by
    rw [show c = t-a from rfl,AddCircle.coe_sub,hca,sub_self]
  have he : (fun y : A × ℝ => H (y+(0,c))) = H := by
    funext y
    simp only [H,Prod.fst_add,Prod.snd_add,add_zero,AddCircle.coe_add,hcz]
  have hd := congrArg (fun f : A × ℝ → E => iteratedFDeriv ℝ j f (p,a)) he
  rw [iteratedFDeriv_comp_add_right] at hd
  have hpoint : (p,a)+(0,c) = (p,t) := by
    ext
    · simp
    · dsimp [c]
      ring
  rw [hpoint] at hd
  change ‖iteratedFDeriv ℝ j H (p,t)‖ ≤ C
  rw [hd]
  simpa only [iteratedFDerivWithin_univ] using hb j hj (p,a) ⟨hp,ha.1,ha.2.le⟩

/-- Fast evaluation has precisely the expected derivative-scale loss. -/
lemma compact_fast_derivative_bound (U : Family A E) {Q : Set A}
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ j ≤ m, ∀ p ∈ Q,
      z^j*‖iteratedFDeriv ℝ j (U.fastValue ℓ z) p‖ ≤ C := by
  obtain ⟨D,hD,hb⟩ := U.compact_lift_derivative_bound hQ m
  refine ⟨D*(1+‖ℓ‖)^m,by positivity,?_⟩
  intro z hz hz1 j hj p hp
  let T : A →L[ℝ] A × ℝ := (ContinuousLinearMap.id ℝ A).prod (z⁻¹ • ℓ)
  have hT : T p = (p,ℓ p/z) := by simp [T,div_eq_mul_inv,mul_comm]
  have hTnorm : ‖T‖ ≤ (1+‖ℓ‖)/z := by
    calc
      ‖T‖ = max ‖ContinuousLinearMap.id ℝ A‖ ‖z⁻¹ • ℓ‖ := by
        simp only [T,ContinuousLinearMap.opNorm_prod,Prod.norm_def]
      _ ≤ 1+‖z⁻¹ • ℓ‖ := max_le
        (ContinuousLinearMap.norm_id_le.trans (by linarith [norm_nonneg (z⁻¹ • ℓ)]))
        (by linarith)
      _ = 1+‖ℓ‖/z := by
        rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hz]
        ring
      _ ≤ (1+‖ℓ‖)/z := by
        apply (le_div_iff₀ hz).mpr
        field_simp
        linarith
  have he : U.fastValue ℓ z = (fun y : A × ℝ => U.val y.1 (y.2 : Period)) ∘ T := by
    funext x
    simp [fastValue,T,div_eq_mul_inv,mul_comm]
  rw [he,T.iteratedFDeriv_comp_right U.smooth p (by simp)]
  have hn := (iteratedFDeriv ℝ j
    (fun y : A × ℝ => U.val y.1 (y.2 : Period)) (T p)).norm_compContinuousLinearMap_le
      (fun _ : Fin j => T)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  calc
    z^j*‖(iteratedFDeriv ℝ j (fun y : A × ℝ => U.val y.1 (y.2 : Period)) (T p)).compContinuousLinearMap
        (fun _ => T)‖ ≤ z^j*(D*‖T‖^j) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.le _)
      exact hn.trans (mul_le_mul_of_nonneg_right (by simpa only [hT] using hb j hj p hp (ℓ p/z))
        (pow_nonneg (norm_nonneg T) _))
    _ ≤ z^j*(D*((1+‖ℓ‖)/z)^j) := by
      gcongr
    _ = D*(1+‖ℓ‖)^j := by
      rw [div_pow]
      calc
        z^j*(D*((1+‖ℓ‖)^j/z^j)) = D*(1+‖ℓ‖)^j*(z^j/z^j) := by ring
        _ = D*(1+‖ℓ‖)^j := by rw [div_self (pow_ne_zero j (ne_of_gt hz)),mul_one]
    _ ≤ D*(1+‖ℓ‖)^m := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [norm_nonneg ℓ]) hj) hD

end ClosedSurfaceR4.PeriodicExpansion.Family

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

/-- The actual globally smooth finite ansatz has uniform compact-domain
jets after multiplication by the corresponding power of the fast scale. -/
theorem compact_finiteAnsatz_bounds {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E) {K Q : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzU : ∀ i p, p ∈ O → p ∉ K → (U i).val p = 0)
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (L : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ z : ℝ, 0 < z → z ≤ 1 →
        ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) ∧
        ∀ m p, p ∈ Q → z^m*‖iteratedFDeriv ℝ m (finiteAnsatz F U ℓ L z) p‖ ≤ C m := by
  let hcoeff (i : ℕ) := (U i).global hK hKO (hzU i)
  choose D hD hb using fun m i : ℕ =>
    (hcoeff i).compact_fast_derivative_bound hQ ℓ m
  choose B hB hFbound using fun m => compact_coefficient_bound uniqueDiffOn_univ
    hQ (subset_univ _) hF.contDiffOn m
  refine ⟨fun m => B m+∑ i ∈ Finset.range L, D m i,
    (fun m => add_nonneg (zero_le_one.trans (hB m)) (Finset.sum_nonneg (fun i _ => hD m i))),?_⟩
  intro z hz hz1
  have hs := finiteAnsatz_smooth_global hF U hK hKO hzU ℓ L z
  refine ⟨hs,?_⟩
  intro m p hp
  have hfast (i : ℕ) : (hcoeff i).fastValue ℓ z = (U i).fastValue ℓ z := by
    funext x
    rfl
  have hsU (i : ℕ) : ContDiff ℝ ∞ ((U i).fastValue ℓ z) := by
    rw [← hfast i]
    exact (hcoeff i).fastValue_smooth ℓ z
  have hsTerm (i : ℕ) :
      ContDiff ℝ ∞ (fun x : A => z^(i+1) • (U i).fastValue ℓ z x) :=
    contDiff_const.smul (hsU i)
  have hsSum : ContDiff ℝ ∞
      (fun x : A => ∑ i ∈ Finset.range L, z^(i+1) • (U i).fastValue ℓ z x) :=
    ContDiff.sum (fun i _ => hsTerm i)
  have hterm (i : ℕ) : z^m*‖iteratedFDeriv ℝ m
      (fun x => z^(i+1) • (U i).fastValue ℓ z x) p‖ ≤ D m i := by
    rw [iteratedFDeriv_const_smul_apply'
      ((hsU i).of_le (by simp : (m : ℕ∞ω) ≤ ∞)).contDiffAt,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz.le _)]
    have hbi := hb m i z hz hz1 m le_rfl p hp
    rw [hfast i] at hbi
    calc
      z^m*(z^(i+1)*‖iteratedFDeriv ℝ m ((U i).fastValue ℓ z) p‖) =
          z^(i+1)*(z^m*‖iteratedFDeriv ℝ m ((U i).fastValue ℓ z) p‖) := by ring
      _ ≤ 1*D m i := mul_le_mul
        (pow_le_one₀ hz.le hz1) hbi
        (mul_nonneg (pow_nonneg hz.le _) (norm_nonneg _)) zero_le_one
      _ = D m i := one_mul _
  change z^m*‖iteratedFDeriv ℝ m
    (F+(fun x => ∑ i ∈ Finset.range L, z^(i+1) • (U i).fastValue ℓ z x)) p‖ ≤ _
  rw [iteratedFDeriv_add_apply
    (f := F) (g := fun x : A => ∑ i ∈ Finset.range L, z^(i+1) • (U i).fastValue ℓ z x)
    (hF.of_le (by simp : (m : ℕ∞ω) ≤ ∞)).contDiffAt
    (hsSum.of_le (by simp : (m : ℕ∞ω) ≤ ∞)).contDiffAt,
    iteratedFDeriv_fun_sum_apply
      (f := fun i (x : A) => z^(i+1) • (U i).fastValue ℓ z x)
      (u := Finset.range L) (fun i _ =>
        ((hsTerm i).of_le (by simp : (m : ℕ∞ω) ≤ ∞)).contDiffAt)]
  calc
    z^m*‖iteratedFDeriv ℝ m F p+∑ i ∈ Finset.range L,
        iteratedFDeriv ℝ m (fun x => z^(i+1) • (U i).fastValue ℓ z x) p‖
        ≤ z^m*(‖iteratedFDeriv ℝ m F p‖+∑ i ∈ Finset.range L,
          ‖iteratedFDeriv ℝ m (fun x => z^(i+1) • (U i).fastValue ℓ z x) p‖) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.le _)
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = z^m*‖iteratedFDeriv ℝ m F p‖+∑ i ∈ Finset.range L,
        z^m*‖iteratedFDeriv ℝ m (fun x => z^(i+1) • (U i).fastValue ℓ z x) p‖ := by
      rw [mul_add,Finset.mul_sum]
    _ ≤ B m+∑ i ∈ Finset.range L, D m i := by
      apply add_le_add _ (Finset.sum_le_sum (fun i _ => hterm i))
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hz.le hz1) (norm_nonneg _)).trans
        (by simpa only [one_mul,iteratedFDerivWithin_univ] using hFbound m m le_rfl p hp)

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
