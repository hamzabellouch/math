import OAI.Analysis.Mahler.ReferenceSphere
import OAI.Analysis.Mahler.WedgeCalculus

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma oneForm_add [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a b : E → E →L[ℝ] ℂ) : oneForm (a+b) = oneForm a + oneForm b := by
  funext x
  ext v
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma oneForm_smul [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (c : ℝ) (a : E → E →L[ℝ] ℂ) : oneForm (c • a) = c • oneForm a := by
  funext x
  ext v
  rfl

lemma extDeriv_oneForm_affine {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (t : ℝ) :
    extDeriv (oneForm (a+t • b)) x =
      extDeriv (oneForm a) x + t • extDeriv (oneForm b) x := by
  rw [oneForm_add, oneForm_smul, extDeriv_add (differentiableAt_oneForm ha)
    ((differentiableAt_oneForm hb).const_smul t), extDeriv_smul]

/-- Actual parameter derivative of the boundary form, at each vector tuple.
The spatial derivatives are exterior derivatives. -/
theorem hasDerivAt_boundaryForm {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (S : Submodule ℝ E) (t : ℝ) (k : ℕ) (v : Fin 1 ⊕ WedgePowerSlots k → S) :
    HasDerivAt
      (fun s => wedge
        ((oneForm (a+s • b) x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (a+s • b)) x).toAlternatingMap.compLinearMap S.subtype) k) v)
      ((wedge ((oneForm b x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (a+t • b)) x).toAlternatingMap.compLinearMap S.subtype) k) +
        wedge ((oneForm (a+t • b) x).toAlternatingMap.compLinearMap S.subtype)
          (wedgePowerVariation
            ((extDeriv (oneForm (a+t • b)) x).toAlternatingMap.compLinearMap S.subtype)
            ((extDeriv (oneForm b) x).toAlternatingMap.compLinearMap S.subtype) k)) v) t := by
  apply hasDerivAt_wedge_eval
  · intro w
    change HasDerivAt (fun s : ℝ => a x (w 0) + s • b x (w 0)) (b x (w 0)) t
    have hh := (hasDerivAt_const t (a x (w 0))).add ((hasDerivAt_id t).smul_const (b x (w 0)))
    change HasDerivAt (fun s : ℝ => a x (w 0) + s • b x (w 0)) (0 + (1 : ℝ) • b x (w 0)) t at hh
    simpa only [zero_add, one_smul] using hh
  · apply hasDerivAt_wedgePower_eval
    intro w
    simp only [extDeriv_oneForm_affine ha hb]
    change HasDerivAt
      (fun s : ℝ => extDeriv (oneForm a) x (fun i => (w i : E)) +
        s • extDeriv (oneForm b) x (fun i => (w i : E)))
      (extDeriv (oneForm b) x (fun i => (w i : E))) t
    have hh := (hasDerivAt_const t (extDeriv (oneForm a) x (fun i => (w i : E)))).add
      ((hasDerivAt_id t).smul_const (extDeriv (oneForm b) x (fun i => (w i : E))))
    change HasDerivAt (fun s : ℝ => extDeriv (oneForm a) x (fun i => (w i : E)) + s • extDeriv (oneForm b) x (fun i => (w i : E))) (0 + (1 : ℝ) • extDeriv (oneForm b) x (fun i => (w i : E))) t at hh
    simpa only [zero_add, one_smul] using hh

/-- The first variation term vanishes for the homogeneous path.
The remaining term is displayed explicitly; this is not flux constancy. -/
theorem MassHypotheses.sphere_boundaryForm_derivative {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ)
    (v : Fin 1 ⊕ WedgePowerSlots (n-1) → sphereTangent z) :
    HasDerivAt
      (fun s => wedge
        (tangentForm z (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m s) z).toAlternatingMap)
        (wedgePower (tangentForm z
          (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m s)) z).toAlternatingMap) (n-1)) v)
      (wedge
        (tangentForm z (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t) z).toAlternatingMap)
        (wedgePowerVariation
          (tangentForm z (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t)) z).toAlternatingMap)
          (tangentForm z (extDeriv (oneForm (betaLinear (polynomialMap G) (coordinateMap n) m)) z).toAlternatingMap)
          (n-1)) v) t := by
  have hfG := polynomialMap_differentiable G
  have htG := tau_pos_of_component_ne_zero (f := polynomialMap G) (x := z) (h.leading_nonzero z hz)
  have hdG := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ z)
    (fun j => (hfG j).differentiableOn) htG)
  have hd0 := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn) (coordinateMap_tau_pos hz))
  have hdA : DifferentiableAt ℝ ((m : ℝ) • dcLinear (logTau (coordinateMap n))) z := hd0.const_smul _
  have hdB : DifferentiableAt ℝ (betaLinear (polynomialMap G) (coordinateMap n) m) z :=
    hdG.sub hdA
  have hh := hasDerivAt_boundaryForm hdA hdB (sphereTangent z) t (n-1) v
  change HasDerivAt _
    ((wedge (tangentForm z (oneForm (betaLinear (polynomialMap G) (coordinateMap n) m) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t)) z).toAlternatingMap) (n-1))) v + _) t at hh
  rw [h.sphere_beta_wedge_power_zero hz t] at hh
  convert hh using 1 <;> simp only [tangentForm, AlternatingMap.zero_apply, zero_add]
  all_goals rfl

end Mahler

end OAI
