import OAI.Analysis.Mahler.ClosedWedgePowers
import OAI.Analysis.Mahler.PairExteriorBridge
import OAI.Analysis.Mahler.HomogeneousVariationCoefficient

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma wedge_triple_power_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℝ E] (basis : Module.Basis J ℝ E) (k : ℕ)
    (c : E [⋀^Fin 1]→ₗ[ℝ] ℂ) (D A : E [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    ((wedge ((wedge c D).domDomCongr (prependFinEquiv 2))
      ((wedgePower A k).domDomCongr (powerFinEquiv k))).domDomCongr
        (derivativeLeftEquiv (2*k))).domDomCongr (finCongr (by omega)) =
    (wedge c (wedge D (wedgePower A k))).domDomCongr (boundaryFinEquiv (k+1)) := by
  rw [← wedge_derivative_assoc basis]
  have h1 := wedge_reindex basis (Equiv.refl (Fin 2)) (powerFinEquiv k) D (wedgePower A k)
  simp only [AlternatingMap.domDomCongr_refl] at h1
  rw [← h1]
  simp only [← AlternatingMap.domDomCongr_trans]
  have h2 := wedge_reindex basis (Equiv.refl (Fin 1))
    (((Equiv.refl (Fin 2)).sumCongr (powerFinEquiv k)).trans finSumFinEquiv)
    c (wedge D (wedgePower A k))
  simp only [AlternatingMap.domDomCongr_refl] at h2
  rw [← h2, ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with i | (i | i)
  · fin_cases i; rfl
  · fin_cases i <;> rfl
  · change 2 + (powerFinEquiv k i).val + 1 = 1 + (2 + (powerFinEquiv k i).val)
    omega

/-- The ordered primitive alpha wedge beta wedge (d alpha)^k. -/
noncomputable def powerTransgressionPrimitive (basis : Module.Basis J ℝ E)
    (a b : E → E →L[ℝ] ℂ) (k : ℕ) (x : E) : E [⋀^Fin (2*(k+1))]→L[ℝ] ℂ :=
  continuousReindex (finCongr (by omega))
    (continuousWedgeFin basis (pairExterior (a x) (b x))
      (basisContinuousWedgePower basis (extDeriv (oneForm a) x) k))

def primitiveFinEquiv (k : ℕ) :
    (Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k)) ≃ Fin (2*(k+1)) :=
  (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k)).symm.trans
    (((prependFinEquiv 1).sumCongr (powerFinEquiv k)).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

/-- The continuous primitive is the ordered shuffle product. -/
lemma powerTransgressionPrimitive_is_wedge (basis : Module.Basis J ℝ E)
    (a b : E → E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    (powerTransgressionPrimitive basis a b k x).toAlternatingMap =
      (wedge (oneForm a x).toAlternatingMap
        (wedge (oneForm b x).toAlternatingMap
          (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k))).domDomCongr
        (primitiveFinEquiv k) := by
  unfold powerTransgressionPrimitive
  rw [continuousReindex_toAlternatingMap, continuousWedgeFin_toAlternatingMap,
    pairExterior_is_wedge, basisContinuousWedgePower_toAlternatingMap,
    ← wedge_reindex basis, ← AlternatingMap.domDomCongr_trans,
    ← AlternatingMap.domDomCongr_trans, ← wedge_assoc basis,
    ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with (i | i) | i <;> rfl

/-- Full ambient transgression identity in every degree. The hypotheses are
actual differentiability and d squared alpha = 0, not a formal product law. -/
theorem extDeriv_powerTransgressionPrimitive (basis : Module.Basis J ℝ E)
    {a b : E → E →L[ℝ] ℂ} {x : E} (k : ℕ)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hda : DifferentiableAt ℝ (extDeriv (oneForm a)) x)
    (hclosed : extDeriv (extDeriv (oneForm a)) x = 0) :
    (extDeriv (powerTransgressionPrimitive basis a b k) x).toAlternatingMap =
      (wedge (oneForm b x).toAlternatingMap
        (wedgePower (extDeriv (oneForm a) x).toAlternatingMap (k+1))).domDomCongr
        (boundaryFinEquiv (k+1)) -
      (wedge (oneForm a x).toAlternatingMap
        (wedge (extDeriv (oneForm b) x).toAlternatingMap
          (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k))).domDomCongr
        (boundaryFinEquiv (k+1)) := by
  unfold powerTransgressionPrimitive
  rw [continuousReindex_finCongr_extDeriv, continuousReindex_toAlternatingMap,
    extDeriv_continuousWedge_two basis (differentiableAt_pairExterior ha hb)
      (differentiableAt_basisContinuousWedgePower basis hda k),
    extDeriv_basisContinuousWedgePower basis hda hclosed k]
  simp only [ContinuousAlternatingMap.toAlternatingMap_zero, wedge_power_zero_right,
    AlternatingMap.domDomCongr_zero, add_zero]
  rw [extDeriv_pairExterior basis ha hb, basisContinuousWedgePower_toAlternatingMap]
  have hsub (A B : E [⋀^Fin 3]→ₗ[ℝ] ℂ) (C : E [⋀^Fin (2*k)]→ₗ[ℝ] ℂ) :
      wedge (A-B) C = wedge A C - wedge B C := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ B, wedge_add_left, wedge_smul_left]
    simp only [neg_one_smul, sub_eq_add_neg]
  have hr {ι κ : Type} (e : ι ≃ κ) (C D : E [⋀^ι]→ₗ[ℝ] ℂ) :
      (C-D).domDomCongr e = C.domDomCongr e - D.domDomCongr e :=
    map_sub (AlternatingMap.domDomCongrₗ ℂ e) C D
  rw [hsub, hr, hr,
    wedge_triple_power_order basis, wedge_triple_power_order basis]
  have hdec : wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  have hfin : wedgePowerSlotsFintype (k+1) =
      (inferInstance : Fintype (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  simp only [wedgePower]
  rw [hdec, hfin]
  congr 3

lemma contDiffAt_powerTransgressionPrimitive (basis : Module.Basis J ℝ E)
    {a b : E → E →L[ℝ] ℂ} {x : E} (k q : ℕ)
    (ha : ContDiffAt ℝ (q+1) a x) (hb : ContDiffAt ℝ q b x) :
    ContDiffAt ℝ q (powerTransgressionPrimitive basis a b k) x := by
  unfold powerTransgressionPrimitive
  apply (continuousReindex (E := E) (finCongr (show 2+2*k=2*(k+1) by omega))).contDiff.contDiffAt.comp x
  apply contDiffAt_continuousWedgeFin basis
  · exact contDiffAt_pairExterior q (ha.of_le (by norm_cast; omega)) hb
  · exact contDiffAt_basisContinuousWedgePower basis
      (contDiffAt_extDeriv_power_order q (contDiffAt_oneForm_order (q+1) ha)) k

end Mahler

end OAI
