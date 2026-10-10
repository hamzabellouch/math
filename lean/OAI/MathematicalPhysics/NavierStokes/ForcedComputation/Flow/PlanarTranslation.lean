import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProgramBounds

namespace OAI

/-! Rational translation of the finite pulse data. The cutoff support and its
positive separation are translated together. Local field covariance is all
that is needed by the tracked paths. -/

noncomputable section

namespace ForcedComputation.PlanarRouting

open ShearFlows

def translatedPoint (δ : Fin 2 → ℚ) (x : Plane) : Plane := fun j => x j + (δ j : ℝ)

def translatedBox (δ : Fin 2 → ℚ) (R : RationalBox 2) : RationalBox 2 :=
  ⟨fun j => R.lower j + δ j, fun j => R.upper j + δ j⟩

theorem translatedBox_positive (δ : Fin 2 → ℚ) {R : RationalBox 2}
    (hR : R.positive) : (translatedBox δ R).positive := by
  intro j
  change R.lower j + δ j < R.upper j + δ j
  linarith [hR j]

theorem mem_translatedBox (δ : Fin 2 → ℚ) (R : RationalBox 2) (x : Plane) :
    translatedPoint δ x ∈ (translatedBox δ R).carrier ↔ x ∈ R.carrier := by
  simp only [RationalBox.carrier, Set.mem_ofPred_eq, translatedPoint, translatedBox, Rat.cast_add,
    add_le_add_iff_right]

theorem translatedBox_gap (δ : Fin 2 → ℚ) {R S : RationalBox 2} {g : ℚ}
    (h : EndpointGap g R S) : EndpointGap g (translatedBox δ R) (translatedBox δ S) := by
  obtain ⟨j, h | h⟩ := h
  · refine ⟨j, Or.inl ?_⟩
    change R.upper j + δ j + g ≤ S.lower j + δ j
    linarith
  · refine ⟨j, Or.inr ?_⟩
    change S.upper j + δ j + g ≤ R.lower j + δ j
    linarith

end ForcedComputation.PlanarRouting

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows PlanarRouting

def Primitive.translated (δ : Fin 2 → ℚ) (p : Primitive) : Primitive :=
  Primitive.casesOn p Primitive.translation
    (fun c a => .horizontal (c + δ) a) (fun c a => .vertical (c + δ) a)

theorem Primitive.translated_field (δ : Fin 2 → ℚ) (p : Primitive) (x : Plane) :
    field (p.translated δ).potential (translatedPoint δ x) = field p.potential x := by
  cases p with
  | translation v =>
      change field (translationPotential (fun j => (v j : ℝ))) (translatedPoint δ x) =
        field (translationPotential (fun j => (v j : ℝ))) x
      rw [field_translation, field_translation]
  | horizontal c a =>
      simp only [Primitive.translated, Primitive.potential, field_horizontal]
      funext j
      fin_cases j <;> simp [translatedPoint, Pi.add_apply, Rat.cast_add]
  | vertical c a =>
      simp only [Primitive.translated, Primitive.potential, field_vertical]
      funext j
      fin_cases j <;> simp [translatedPoint, Pi.add_apply, Rat.cast_add]

def Pulse.translated (δ : Fin 2 → ℚ) (p : Pulse) : Pulse where
  primitive := p.primitive.translated δ
  rectangle := translatedBox δ p.rectangle
  collar := p.collar
  start := p.start
  finish := p.finish

theorem Pulse.translated_valid (δ : Fin 2 → ℚ) {p : Pulse} (hp : p.Valid) :
    (p.translated δ).Valid := hp

theorem Pulse.spatial_on_rectangle {p : Pulse} (hp : p.Valid) {x : Plane}
    (hx : x ∈ p.rectangle.carrier) : p.spatial x = field p.primitive.potential x :=
  field_cutoff_plateau _ _ (rectangleCutoff_one_near hp.1 hx)

theorem Pulse.translated_spatial (δ : Fin 2 → ℚ) {p : Pulse} (hp : p.Valid)
    {x : Plane} (hx : x ∈ p.rectangle.carrier) :
    (p.translated δ).spatial (translatedPoint δ x) = p.spatial x := by
  rw [(p.translated δ).spatial_on_rectangle (p.translated_valid δ hp)
    ((mem_translatedBox δ p.rectangle x).mpr hx), p.spatial_on_rectangle hp hx]
  exact p.primitive.translated_field δ x

theorem Pulse.translated_velocity (δ : Fin 2 → ℚ) {p : Pulse} (hp : p.Valid)
    {x : Plane} (hx : x ∈ p.rectangle.carrier) (t : ℝ) :
    (p.translated δ).velocity t (translatedPoint δ x) = p.velocity t x := by
  change smoothPulse p.start p.finish t • (p.translated δ).spatial (translatedPoint δ x) = _
  rw [p.translated_spatial δ hp hx]
  rfl

theorem Pulse.translated_inUnit (δ : Fin 2 → ℚ) {p : Pulse} (hp : p.InUnit)
    (hR : Between p.rectangle (1 / 64) (7 / 8))
    (hc : p.collar ≤ 1 / 65536)
    (hδ : ∀ j, -(1 / 128 : ℚ) ≤ δ j ∧ δ j ≤ 1 / 128) :
    (p.translated δ).InUnit := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro j
  have h := hR j
  have h' := hδ j
  change 0 < p.rectangle.lower j + δ j - 2 * p.collar ∧
    p.rectangle.upper j + δ j + 2 * p.collar < 1
  constructor <;> linarith

theorem Pulse.translated_hasDerivAt (δ : Fin 2 → ℚ) {p : Pulse} (hp : p.Valid)
    {γ : ℝ → Plane} {t : ℝ} (hx : γ t ∈ p.rectangle.carrier)
    (hγ : HasDerivAt γ (p.velocity t (γ t)) t) :
    HasDerivAt (fun s => translatedPoint δ (γ s))
      ((p.translated δ).velocity t (translatedPoint δ (γ t))) t := by
  rw [p.translated_velocity δ hp hx]
  exact hγ.add_const (fun j => (δ j : ℝ))

end ForcedComputation.PlanarHamiltonian

end

end OAI
