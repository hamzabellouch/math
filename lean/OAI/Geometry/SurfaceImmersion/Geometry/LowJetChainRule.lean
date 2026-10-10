import OAI.Geometry.SurfaceImmersion.Geometry.DirectionalJetBounds

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

abbrev Base := Fin 2 → ℝ
abbrev Space := Fin 4 → ℝ
abbrev LowIndex := Fin 2 ⊕ (Fin 7 × Fin 4)
abbrev LowJet := LowIndex → ℝ

def coordinateVector (v : Fin 2) : Base := Pi.single v 1

def lowWord : Fin 7 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]

/-- Actual ordered coordinate derivatives; no symmetry convention is needed. -/
def jet (G : Base → Space) (w : List (Fin 2)) (a : Fin 4) (p : Base) : ℝ :=
  iteratedDirectional (w.map coordinateVector) (fun q => G q a) p

def lowJet (G : Base → Space) (p : Base) : LowJet
  | Sum.inl i => p i
  | Sum.inr (w, a) => jet G (lowWord w) a p

def lowBasis (i : LowIndex) : LowJet := Pi.single i 1

def lowDerivative (G : Base → Space) (v : Fin 2) (p : Base) : LowJet
  | Sum.inl i => coordinateVector v i
  | Sum.inr (w, a) => jet G (v :: lowWord w) a p

lemma jet_smooth {G : Base → Space} (hG : ContDiff ℝ ∞ G) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (jet G w a) := by
  have h := contDiffOn_iteratedDirectional isOpen_univ (contDiff_pi.mp hG a).contDiffOn
    (w.map coordinateVector)
  exact contDiffOn_univ.mp h

lemma lowJet_smooth {G : Base → Space} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (lowJet G) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff
  | inr i => exact jet_smooth hG (lowWord i.1) i.2

lemma jet_cons (G : Base → Space) (v : Fin 2) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet G (v :: w) a p = fderiv ℝ (jet G w a) p (coordinateVector v) := rfl

lemma lowJet_coordinate_derivative (G : Base → Space) (v : Fin 2) (i : LowIndex) (p : Base) :
    fderiv ℝ (fun q => lowJet G q i) p (coordinateVector v) = lowDerivative G v p i := by
  cases i with
  | inl i =>
    change fderiv ℝ (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ) p (coordinateVector v) = _
    rw [(ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).fderiv]
    rfl
  | inr i => rfl

lemma lowJet_derivative {G : Base → Space} (hG : ContDiff ℝ ∞ G) (v : Fin 2) (p : Base) :
    fderiv ℝ (lowJet G) p (coordinateVector v) = lowDerivative G v p := by
  ext i
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply ((lowJet_smooth hG).differentiable (by simp) p) i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    lowJet_coordinate_derivative] using h.symm

lemma lowBasis_expansion (J : LowJet) : J = ∑ i : LowIndex, J i • lowBasis i := by
  ext i
  simp [lowBasis, Pi.single_apply]

/-- Differentiating a low-jet coefficient introduces only the next coordinate
jet, linearly, with new smooth low-jet coefficients. -/
theorem coefficient_chain_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet → E}
    (v : Fin 2) (p : Base) (hc : DifferentiableAt ℝ c (lowJet G p)) :
    fderiv ℝ (fun q => c (lowJet G q)) p (coordinateVector v) =
      ∑ i : LowIndex, (lowDerivative G v p i) • fderiv ℝ c (lowJet G p) (lowBasis i) := by
  have hQ := (lowJet_smooth hG).differentiable (by simp) p
  change fderiv ℝ (c ∘ lowJet G) p (coordinateVector v) = _
  rw [fderiv_comp p hc hQ, ContinuousLinearMap.comp_apply, lowJet_derivative hG]
  conv_lhs => rw [lowBasis_expansion (lowDerivative G v p), map_sum]
  simp only [map_smul]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
