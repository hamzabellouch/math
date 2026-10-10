import OAI.MathematicalPhysics.RapidForcing.VelocitySyntax
import OAI.MathematicalPhysics.RapidForcing.JetBounds

namespace OAI

section
open scoped BigOperators Topology ENNReal ContDiff
open Set Filter
namespace RapidForcing.EffectiveProfile.Formula

def spIndex (i : Fin 3) : Fin 10 := ⟨i.val+1, by omega⟩
def etaIndex (i : Fin 3) : Fin 10 := ⟨i.val+4, by omega⟩
def xiIndex (i : Fin 3) : Fin 10 := ⟨i.val+7, by omega⟩

noncomputable def profileLinear : (ℝ × Space) →L[ℝ] (Fin 10 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ Space,
    (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ ℝ Space),
    (EuclideanSpace.proj 1).comp (ContinuousLinearMap.snd ℝ ℝ Space),
    (EuclideanSpace.proj 2).comp (ContinuousLinearMap.snd ℝ ℝ Space), 0,0,0,0,0,0]
noncomputable def profileParams (η ξ : Space) : Fin 10 → ℝ :=
  ![0,0,0,0,η 0,η 1,η 2,ξ 0,ξ 1,ξ 2]
noncomputable def profilePack (η ξ : Space) (t : ℝ) (x : Space) : Fin 10 → ℝ :=
  profileLinear (t,x) + profileParams η ξ

lemma profilePack_eq (η ξ : Space) (t : ℝ) (x : Space) :
    profilePack η ξ t x = ![t,x 0,x 1,x 2,η 0,η 1,η 2,ξ 0,ξ 1,ξ 2] := by
  ext i
  fin_cases i <;> dsimp [profilePack, profileLinear, profileParams] <;> simp

lemma profileLinear_norm : ‖profileLinear‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
  intro i
  fin_cases i
  · exact norm_fst_le p
  · exact (PiLp.norm_apply_le p.2 0).trans (norm_snd_le p)
  · exact (PiLp.norm_apply_le p.2 1).trans (norm_snd_le p)
  · exact (PiLp.norm_apply_le p.2 2).trans (norm_snd_le p)
  all_goals simp [profileLinear]

lemma profilePack_line (η ξ : Space) (t : ℝ) (x : Space) (i : Fin 3) (s : ℝ) :
    profilePack η ξ t (x + s • basis i) = profilePack η ξ t x + s • Pi.single (spIndex i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [profilePack_eq, spIndex, basis]

noncomputable def profileField (a : Fin 3 → Formula 10) (η ξ : Space) : Field Space :=
  fun t x => WithLp.toLp 2 (fun i => (a i).value (profilePack η ξ t x))
lemma profileField_smooth (a : Fin 3 → Formula 10) (η ξ : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (profileField a η ξ)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact (a i).contDiff.comp (profileLinear.contDiff.add contDiff_const)

lemma profile_partial (a : Formula 10) (η ξ : Space) (t : ℝ) (x : Space) (i : Fin 3) :
    fderiv ℝ (fun y => a.value (profilePack η ξ t y)) x (basis i) =
      (a.diff (spIndex i)).value (profilePack η ξ t x) := by
  have hline : HasDerivAt (fun s : ℝ => x + s • basis i) (basis i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basis i)).const_add x
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => a.value (profilePack η ξ t y)) :=
    a.contDiff.comp ((profileLinear.contDiff.comp (contDiff_const.prodMk contDiff_id)).add contDiff_const)
  have hp := a.hasDerivAt_line (spIndex i) (profilePack η ξ t x) 0
  have he : (fun s : ℝ => a.value (profilePack η ξ t x + s • Pi.single (spIndex i) 1)) =
      fun s => a.value (profilePack η ξ t (x+s • basis i)) := by
    funext s
    rw [← profilePack_line]
  rw [he] at hp
  have hf : HasFDerivAt (fun y => a.value (profilePack η ξ t y))
      (fderiv ℝ (fun y => a.value (profilePack η ξ t y)) x) (x+(0:ℝ) • basis i) := by
    simpa using (hsm.differentiable (by simp) x).hasFDerivAt
  have hc := hf.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero] using hc.unique hp

def profileCurl (a : Fin 3 → Formula 10) : Fin 3 → Formula 10 :=
  ![((a 2).diff (spIndex 1)).sub ((a 1).diff (spIndex 2)),
    ((a 0).diff (spIndex 2)).sub ((a 2).diff (spIndex 0)),
    ((a 1).diff (spIndex 0)).sub ((a 0).diff (spIndex 1))]
lemma profileCurl_value (a : Fin 3 → Formula 10) (η ξ : Space) (t : ℝ) (x : Space) :
    profileField (profileCurl a) η ξ t x = curl (profileField a η ξ t) x := by
  have hs (i j : Fin 3) : (fderiv ℝ (profileField a η ξ t) x (basis i)) j =
      ((a j).diff (spIndex i)).value (profilePack η ξ t x) := by
    have hd : DifferentiableAt ℝ (profileField a η ξ t) x :=
      ((profileField_smooth a η ξ).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x
    rw [← fderiv_coordinate hd]
    exact profile_partial (a j) η ξ t x i
  ext i
  fin_cases i <;> simp [profileField, profileCurl, curl, vec, hs, value_sub]

def scaledFormula : Fin 3 → Formula 10 :=
  let y := fun i => (Formula.var (spIndex i) : Formula 10).sub
    (Formula.mul (Formula.var 0).theta (Formula.var (etaIndex i)))
  let speed := fun i => Formula.mul (Formula.var 0).thetaDot (Formula.var (xiIndex i))
  profileCurl (fun i => Formula.mul (zeta y) (Formula.mul (Formula.const (1/2)) (crossF speed y i)))

lemma scaledFormula_value (η ξ : Space) (t : ℝ) (x : Space) :
    profileField scaledFormula η ξ t x = scaledCurl η ξ t x := by
  unfold scaledFormula
  rw [profileCurl_value]
  unfold scaledCurl
  congr 1
  funext y
  have hy : WithLp.toLp 2 (fun i => ((Formula.var (spIndex i) : Formula 10).sub
      (Formula.mul (Formula.var 0).theta (Formula.var (etaIndex i)))).value (profilePack η ξ t y)) =
      y - θ t • η := by
    ext i
    fin_cases i <;> simp [value_sub, value, value_theta, profilePack_eq, spIndex, etaIndex]
  have hv : WithLp.toLp 2 (fun i => (Formula.mul (Formula.var 0).thetaDot
      (Formula.var (xiIndex i)) : Formula 10).value (profilePack η ξ t y)) = deriv θ t • ξ := by
    ext i
    fin_cases i <;> simp [value, value_thetaDot, profilePack_eq, xiIndex]
  have hcross := value_crossF (fun i => (Formula.mul (Formula.var 0).thetaDot (Formula.var (xiIndex i)) : Formula 10))
    (fun i => (Formula.var (spIndex i) : Formula 10).sub (Formula.mul (Formula.var 0).theta (Formula.var (etaIndex i))))
    (profilePack η ξ t y)
  rw [hy, hv] at hcross
  ext i
  change (zeta _).value _ * ((1/2:ℚ) * (crossF _ _ i).value _) = _
  rw [value_zeta, hy]
  have hc := congrArg (fun v : Space => v i) hcross
  dsimp at hc
  rw [hc]
  norm_num [smul_apply, smul_eq_mul]

def curlJetBound (k : ℕ) : ℚ := ∑ i : Fin 3, (scaledFormula i).jetBound 3 k

lemma curlJetBound_nonneg (k : ℕ) : 0 ≤ curlJetBound k :=
  Finset.sum_nonneg (fun _ _ => jetBound_nonneg _ _ _)

lemma norm_jet_affine_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Formula 10) (L : E →L[ℝ] (Fin 10 → ℝ)) (hL : ‖L‖ ≤ 1)
    (b : Fin 10 → ℝ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => a.value (L y+b)) x‖ ≤
      ‖iteratedFDeriv ℝ k a.value (L x+b)‖ := by
  change ‖iteratedFDeriv ℝ k ((fun z => a.value (z+b)) ∘ L) x‖ ≤ _
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun z => a.value (z+b)) :=
    a.contDiff.comp (contDiff_id.add contDiff_const)
  rw [L.iteratedFDeriv_comp_right hsm _ (finite_order k),
    iteratedFDeriv_comp_add_right]
  have hb := (iteratedFDeriv ℝ k a.value (L x+b)).norm_compContinuousLinearMap_le (fun _ : Fin k => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  exact hb.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg L) hL : ‖L‖ ^ k ≤ 1) (norm_nonneg (iteratedFDeriv ℝ k a.value (L x+b))))

lemma curlJetBound_spec (k : ℕ) (η ξ : Space) (hη : ‖η‖ ≤ 2) (hξ : ‖ξ‖ ≤ 2) (p : ℝ × Space) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (scaledCurl η ξ)) p‖ ≤ (curlJetBound k : ℝ) := by
  by_cases hp : p ∈ Icc (0:ℝ) 1 ×ˢ Metric.closedBall (0:Space) 3
  · have hx : ∀ i, |profilePack η ξ p.1 p.2 i| ≤ |((3:ℚ):ℝ)| := by
      have ht : |p.1| ≤ 3 := by rw [abs_of_nonneg hp.1.1]; linarith [hp.1.2]
      have hy : ‖p.2‖ ≤ 3 := by simpa using hp.2
      have hi (v : Space) (hv : ‖v‖ ≤ 3) (i : Fin 3) : |v i| ≤ 3 := (PiLp.norm_apply_le v i).trans hv
      intro i
      fin_cases i <;> norm_num [profilePack_eq]
      · exact ht
      · exact hi _ hy 0
      · exact hi _ hy 1
      · exact hi _ hy 2
      · exact hi _ (hη.trans (by norm_num)) 0
      · exact hi _ (hη.trans (by norm_num)) 1
      · exact hi _ (hη.trans (by norm_num)) 2
      · exact hi _ (hξ.trans (by norm_num)) 0
      · exact hi _ (hξ.trans (by norm_num)) 1
      · exact hi _ (hξ.trans (by norm_num)) 2
    have he : Function.uncurry (scaledCurl η ξ) = fun q : ℝ × Space => ∑ i : Fin 3,
        (scaledFormula i).value (profilePack η ξ q.1 q.2) • basis i := by
      funext q
      change scaledCurl η ξ q.1 q.2 = _
      rw [← scaledFormula_value]
      ext j
      fin_cases j <;> simp [profileField, basis, Fin.sum_univ_three]
    rw [he]
    apply (jet_sum_le _ _ (fun i _ => ((scaledFormula i).contDiff.comp
      (profileLinear.contDiff.add contDiff_const)).smul contDiff_const) k p).trans
    rw [curlJetBound, Rat.cast_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb : ‖basis i‖ = 1 := by simp [basis]
    apply (jet_smul_const_le ((scaledFormula i).contDiff.comp
      (profileLinear.contDiff.add contDiff_const)) (basis i) k p).trans
    rw [hb, one_mul]
    exact (norm_jet_affine_le (scaledFormula i) profileLinear profileLinear_norm _ _ _).trans
      (norm_jet_le 3 k (scaledFormula i) _ hx)
  · have hz : iteratedFDeriv ℝ k (Function.uncurry (scaledCurl η ξ)) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (scaledCurl_tsupport_subset η ξ hη
        (tsupport_iteratedFDeriv_subset k h)))
    rw [hz, norm_zero]
    exact_mod_cast curlJetBound_nonneg k
end RapidForcing.EffectiveProfile.Formula

end

end OAI
