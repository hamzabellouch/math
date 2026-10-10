import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarCutoff
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarParking

namespace OAI

/-! A finite rational syntax for the planar Hamiltonian processor. Each pulse
has one polynomial potential, one rational rectangle cutoff, and one rational
time interval. Its analytic interpretation is the actual compact Hamiltonian
field, including the cutoff collar. -/

noncomputable section

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

theorem field_const_mul {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) (a : ℝ) (x : Plane) :
    field (fun y => a * H y) x = a • field H x := by
  unfold field spatialD
  rw [fderiv_const_mul (hH.differentiable (by simp) x) a]
  funext j
  fin_cases j <;> simp [basis]

theorem field_sum {ι : Type*} (s : Finset ι) (H : ι → Plane → ℝ)
    (hH : ∀ i ∈ s, ContDiff ℝ ∞ (H i)) (x : Plane) :
    field (fun y => ∑ i ∈ s, H i y) x = ∑ i ∈ s, field (H i) x := by
  unfold field spatialD
  rw [fderiv_fun_sum (fun i hi => (hH i hi).differentiable (by simp) x)]
  simp only [sum_apply, Finset.sum_smul, Finset.sum_sub_distrib]

inductive Primitive
  | translation (v : Fin 2 → ℚ)
  | horizontal (center : Fin 2 → ℚ) (coefficient : ℚ)
  | vertical (center : Fin 2 → ℚ) (coefficient : ℚ)

def Primitive.encoding : Primitive ≃
    ((Fin 2 → ℚ) ⊕ ((Fin 2 → ℚ) × ℚ) ⊕ ((Fin 2 → ℚ) × ℚ)) where
  toFun
    | .translation v => .inl v
    | .horizontal c a => .inr (.inl (c, a))
    | .vertical c a => .inr (.inr (c, a))
  invFun
    | .inl v => .translation v
    | .inr (.inl (c, a)) => .horizontal c a
    | .inr (.inr (c, a)) => .vertical c a
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with v | (c | c) <;> rfl

instance : Primcodable Primitive := Primcodable.ofEquiv _ Primitive.encoding

def Primitive.potential : Primitive → Plane → ℝ
  | .translation v => translationPotential (fun j => (v j : ℝ))
  | .horizontal c a => horizontalPotential (fun j => (c j : ℝ)) a
  | .vertical c a => verticalPotential (fun j => (c j : ℝ)) a

theorem Primitive.potential_smooth (p : Primitive) : ContDiff ℝ ∞ p.potential := by
  cases p with
  | translation v =>
      change ContDiff ℝ ∞ (translationPotential (fun j => (v j : ℝ)))
      exact translationPotential_smooth _
  | horizontal c a =>
      change ContDiff ℝ ∞ (horizontalPotential (fun j => (c j : ℝ)) a)
      exact horizontalPotential_smooth _ _
  | vertical c a =>
      change ContDiff ℝ ∞ (verticalPotential (fun j => (c j : ℝ)) a)
      exact verticalPotential_smooth _ _

structure Pulse where
  primitive : Primitive
  rectangle : RationalBox 2
  collar : ℚ
  start : ℚ
  finish : ℚ

def Pulse.encoding : Pulse ≃ (Primitive × RationalBox 2 × ℚ × ℚ × ℚ) where
  toFun p := (p.primitive, p.rectangle, p.collar, p.start, p.finish)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Pulse := Primcodable.ofEquiv _ Pulse.encoding

def Pulse.Valid (p : Pulse) : Prop := 0 < p.collar ∧ p.start < p.finish

def Pulse.hamiltonian (p : Pulse) (x : Plane) : ℝ :=
  rectangleCutoff p.rectangle p.collar x * p.primitive.potential x

def Pulse.spatial (p : Pulse) : Plane → Plane := field p.hamiltonian

def Pulse.velocity (p : Pulse) (t : ℝ) (x : Plane) : Plane :=
  smoothPulse p.start p.finish t • p.spatial x

theorem Pulse.hamiltonian_smooth (p : Pulse) : ContDiff ℝ ∞ p.hamiltonian :=
  (rectangleCutoff_smooth p.rectangle p.collar).mul p.primitive.potential_smooth

theorem Pulse.hamiltonian_compactSupport {p : Pulse} (hp : p.Valid) :
    HasCompactSupport p.hamiltonian :=
  (rectangleCutoff_compactSupport hp.1).mul_right

theorem Pulse.spatial_smooth (p : Pulse) : ContDiff ℝ ∞ p.spatial :=
  field_smooth p.hamiltonian_smooth

theorem Pulse.spatial_compactSupport {p : Pulse} (hp : p.Valid) :
    HasCompactSupport p.spatial := field_compactSupport (p.hamiltonian_compactSupport hp)

theorem Pulse.spatial_tsupport {p : Pulse} (hp : p.Valid) :
    tsupport p.spatial ⊆ (rectangleCollar p.rectangle p.collar).carrier := by
  apply (field_tsupport p.hamiltonian).trans
  apply tsupport_mul_subset_left.trans
  exact closure_minimal (rectangleCutoff_support hp.1)
    (rectangleCollar_compact p.rectangle p.collar).isClosed

theorem Pulse.velocity_zero_of_notMem {p : Pulse} (hp : p.Valid) {x : Plane}
    (hx : x ∉ (rectangleCollar p.rectangle p.collar).carrier) (t : ℝ) :
    p.velocity t x = 0 := by
  have hs : x ∉ tsupport p.spatial := fun h => hx (p.spatial_tsupport hp h)
  simp only [Pulse.velocity, image_eq_zero_of_notMem_tsupport hs, smul_zero]

theorem Pulse.velocity_zero_on_disjoint {p : Pulse} (hp : p.Valid) {S : Set Plane}
    (hS : Disjoint (rectangleCollar p.rectangle p.collar).carrier S)
    {x : Plane} (hx : x ∈ S) (t : ℝ) : p.velocity t x = 0 := by
  apply p.velocity_zero_of_notMem hp (t := t)
  intro hc
  exact Set.disjoint_left.mp hS hc hx

theorem collar_disjoint_of_gap {R S : RationalBox 2} {gap δ : ℚ}
    (hgap : PlanarRouting.EndpointGap gap R S) (hδ : 2 * δ < gap) :
    Disjoint (rectangleCollar R δ).carrier S.carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, hj⟩ := hgap
  have hr := hx j
  have hs := hy j
  have hd : (2 : ℝ) * δ < gap := by exact_mod_cast hδ
  dsimp [rectangleCollar] at hr
  push_cast at hr
  rcases hj with hj | hj
  · have hg : (R.upper j : ℝ) + gap ≤ S.lower j := by exact_mod_cast hj
    linarith [hr.2, hs.1]
  · have hg : (S.upper j : ℝ) + gap ≤ R.lower j := by exact_mod_cast hj
    linarith [hs.2, hr.1]

theorem Pulse.velocity_zero_of_gap {p : Pulse} (hp : p.Valid) {S : RationalBox 2}
    {gap : ℚ} (hgap : PlanarRouting.EndpointGap gap p.rectangle S)
    (hδ : 2 * p.collar < gap) {x : Plane} (hx : x ∈ S.carrier) (t : ℝ) :
    p.velocity t x = 0 :=
  p.velocity_zero_on_disjoint hp (collar_disjoint_of_gap hgap hδ) hx t

theorem Pulse.velocity_smooth (p : Pulse) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => p.velocity y.1 y.2) :=
  ((smoothPulse_smooth p.start p.finish).comp contDiff_fst).smul
    (p.spatial_smooth.comp contDiff_snd)

theorem Pulse.velocity_hamiltonian (p : Pulse) (t : ℝ) (x : Plane) :
    p.velocity t x = field (fun y => smoothPulse p.start p.finish t * p.hamiltonian y) x :=
  (field_const_mul p.hamiltonian_smooth _ _).symm

theorem Pulse.velocity_divergence (p : Pulse) (t : ℝ) (x : Plane) :
    divergence (p.velocity t) x = 0 := by
  have he : p.velocity t = field (fun y => smoothPulse p.start p.finish t * p.hamiltonian y) := by
    funext y
    exact p.velocity_hamiltonian t y
  rw [he]
  exact field_divergence (contDiff_const.mul p.hamiltonian_smooth) x

theorem Pulse.velocity_integral {p : Pulse} (hp : p.Valid) (t : ℝ) :
    (∫ x, p.velocity t x) = 0 := by
  simp_rw [p.velocity_hamiltonian]
  exact field_integral_eq_zero (contDiff_const.mul p.hamiltonian_smooth)
    ((p.hamiltonian_compactSupport hp).mul_left)

def processorHamiltonian {n : ℕ} (p : Fin n → Pulse) (t : ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin n, smoothPulse (p i).start (p i).finish t * (p i).hamiltonian x

def processorVelocity {n : ℕ} (p : Fin n → Pulse) (t : ℝ) : Plane → Plane :=
  field (processorHamiltonian p t)

theorem processorHamiltonian_smooth {n : ℕ} (p : Fin n → Pulse) (t : ℝ) :
    ContDiff ℝ ∞ (processorHamiltonian p t) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (p i).hamiltonian_smooth

theorem processorHamiltonian_compactSupport {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (t : ℝ) : HasCompactSupport (processorHamiltonian p t) := by
  have hK : IsCompact (⋃ i : Fin n, tsupport (p i).hamiltonian) :=
    isCompact_iUnion (fun i => ((p i).hamiltonian_compactSupport (hp i)).isCompact)
  apply HasCompactSupport.intro hK
  intro x hx
  apply Finset.sum_eq_zero
  intro i _
  have hi : x ∉ tsupport (p i).hamiltonian := fun h => hx (Set.mem_iUnion.mpr ⟨i, h⟩)
  rw [image_eq_zero_of_notMem_tsupport hi, mul_zero]

theorem processorVelocity_eq_sum {n : ℕ} (p : Fin n → Pulse) (t : ℝ) (x : Plane) :
    processorVelocity p t x = ∑ i : Fin n, (p i).velocity t x := by
  change field (fun y => ∑ i : Fin n,
    smoothPulse (p i).start (p i).finish t * (p i).hamiltonian y) x = _
  rw [field_sum _ _ (fun i _ => contDiff_const.mul (p i).hamiltonian_smooth)]
  apply Finset.sum_congr rfl
  intro i _
  exact ((p i).velocity_hamiltonian t x).symm

theorem processorVelocity_smooth {n : ℕ} (p : Fin n → Pulse) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => processorVelocity p y.1 y.2) := by
  have he : (fun y : ℝ × Plane => processorVelocity p y.1 y.2) =
      fun y => ∑ i : Fin n, (p i).velocity y.1 y.2 := by
    funext y
    exact processorVelocity_eq_sum p y.1 y.2
  rw [he]
  exact ContDiff.sum (fun i _ => (p i).velocity_smooth)

theorem processorVelocity_properties {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (t : ℝ) :
    HasCompactSupport (processorVelocity p t) ∧
      (∀ x, divergence (processorVelocity p t) x = 0) ∧
      (∫ x, processorVelocity p t x) = 0 := by
  have hs := processorHamiltonian_smooth p t
  have hc := processorHamiltonian_compactSupport hp t
  exact ⟨field_compactSupport hc, field_divergence hs, field_integral_eq_zero hs hc⟩

/-- The translation pulse used for both extraction and insertion. -/
def translationPulse (R : RationalBox 2) (p : Fin 2 → ℚ) (δ a b : ℚ) : Pulse where
  primitive := .translation (fun j => p j - PlanarRouting.centerQ R j)
  rectangle := PlanarRouting.translationTube R p
  collar := δ
  start := a
  finish := b

theorem translationPulse_realizes {R : RationalBox 2} {p : Fin 2 → ℚ} {δ a b : ℚ}
    (hδ : 0 < δ) {x : Plane} (hx : x ∈ R.carrier) (t : ℝ) :
    HasDerivAt
      (translationPath (smoothRamp a b) ((fun j => (p j : ℝ)) - R.center) x)
      ((translationPulse R p δ a b).velocity t
        (translationPath (smoothRamp a b) ((fun j => (p j : ℝ)) - R.center) x t)) t := by
  have hcurve := PlanarRouting.translationPath_mem_tube hx p (smoothRamp_range a b t)
  have hcut := rectangleCutoff_one_near hδ hcurve
  have hθ : HasDerivAt (smoothRamp a b) (smoothPulse a b t) t :=
    ((smoothRamp_smooth a b).differentiable (by simp) t).hasDerivAt
  have hp : (fun j => ((p j - PlanarRouting.centerQ R j : ℚ) : ℝ)) =
      (fun j => (p j : ℝ)) - R.center := by
    funext j
    simp
  change HasDerivAt _ (smoothPulse a b t •
    field (fun y => rectangleCutoff (PlanarRouting.translationTube R p) δ y *
      translationPotential (fun j => ((p j - PlanarRouting.centerQ R j : ℚ) : ℝ)) y) _) t
  rw [hp]
  exact translationPath_cutoff_ode hθ _ x _ hcut

end ForcedComputation.PlanarHamiltonian

end

end OAI
