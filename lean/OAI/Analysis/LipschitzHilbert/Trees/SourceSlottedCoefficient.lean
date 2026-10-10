import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourcePolarizedInterval

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

abbrev PacketIndex := Σ j, Σ l : P.labels j, Item j l

def physicalSelectedWave (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (q : P.PacketIndex) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d q.1 then P.physicalPacket t q.1 q.2.1 q.2.2 k z else 0

def physicalCoefficient (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : P.labels j) (u : Item j l) :
    EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume)
    (fun q : P.PacketIndex => P.length q.1 * P.width)
    (P.physicalSelectedWave t d v) g ⟨j, l, u⟩

/-- Replace only the profiles in the original labeled collection. -/
abbrev withProfile (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j l u k,
      planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound) :
    SourceLabeledLattice N κ Label Item :=
  { P with profile := alt, profile_bound := hAlt }

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

theorem slotted_physicalSelectedWave (b : Fin B) (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) (z : ℝ × ℝ) :
    (P.slotted hcard b).physicalSelectedWave t d v ⟨j, p⟩ k z =
      P.physicalSelectedWave t d v ⟨j, p.1.1, p.1.2⟩ k z := by
  unfold SourceLatticePacket.physicalSelectedWave physicalSelectedWave
  rw [P.slotted_physicalPacket hcard]

theorem slotted_physicalCoefficient (b : Fin B) (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).physicalCoefficient t d v g j p =
      P.physicalCoefficient t d v g j p.1.1 p.1.2 := by
  ext k
  simp only [SourceLatticePacket.physicalCoefficient, physicalCoefficient,
    analyzingCoefficient, WithLp.ofLp_toLp, P.slotted_length hcard,
    P.slotted_physicalSelectedWave hcard]
  rfl

/-- The reference-line coefficient in each slot is precisely the
original physical selected integral, with the same area normalization. -/
theorem slotted_mainCoefficient_physical (b : Fin B) (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).family.mainCoefficient d
        (fun z => v (sourceReferenceToPhysical t z))
        (fun z => g (sourceReferenceToPhysical t z)) j p =
      P.physicalCoefficient t d v g j p.1.1 p.1.2 := by
  rw [(P.slotted hcard b).family_mainCoefficient_physical]
  exact P.slotted_physicalCoefficient hcard b t d v g j p

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

def slottedAlt (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) :
    SchwartzMap (ℝ × ℝ) ℂ := alt j p.1.1 p.1.2 k

include hAlt in
theorem slottedAlt_bound (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) :
    planarProfileConstant (P.slottedAlt hcard alt b j p k)
        (2 * (P.slotted hcard b).order) ≤ (P.slotted hcard b).profileBound :=
  hAlt j p.1.1 p.1.2 k

/-- Profile replacement commutes with the actual slot constructor. -/
theorem withProfile_slotted (b : Fin B) :
    (P.withProfile alt hAlt).slotted hcard b =
      (P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b) := by
  rfl

theorem slotted_alt_raw (b : Fin B) (i : Fin 3) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) (y : ℝ) :
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b)).raw i j p k y =
      (P.withProfile alt hAlt).raw i j p.1.1 p.1.2 k y := by
  rw [← P.withProfile_slotted hcard alt hAlt b]
  exact (P.withProfile alt hAlt).slotted_raw hcard b i j p k y

theorem slotted_alt_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b)).physicalPacket t j p k =
      (P.withProfile alt hAlt).physicalPacket t j p.1.1 p.1.2 k := by
  rw [← P.withProfile_slotted hcard alt hAlt b]
  exact (P.withProfile alt hAlt).slotted_physicalPacket hcard b t j p k

/-- The source interval before splitting labels into lattice slots. -/
def rawInterval (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  planarPacketInterval (ι := fun j => Σ l : P.labels j, Item j l) (fun j p => coeff j p.1 p.2)
    (fun j p k t s => P.raw i j p.1 p.2 k t s) lower upper x y

omit alt hAlt hcard in
theorem rawInterval_scaled_covariant
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    P.scale • covariantSignal P.frequency
      (fun k t => P.rawInterval coeff 0 lower upper x t k) y =
        P.rawInterval coeff 1 lower upper x y := by
  unfold rawInterval
  apply planarPacketInterval_scaled_covariant_eq
  · intro j p k t
    exact modulatedPlanarJet_differentiable (P.profile j p.1 p.2 k) (P.actualX j p.1 p.2)
      (P.actualZ j p.1 p.2) (P.length j) P.width (-P.rowSlope j p.1) (P.frequency k)
      P.scale t (P.length_pos j).ne' 0 x
  · intro j p k
    exact modulatedPlanarJet_covariant_zero (P.profile j p.1 p.2 k) (P.actualX j p.1 p.2)
      (P.actualZ j p.1 p.2) (P.length j) P.width (-P.rowSlope j p.1) (P.frequency k)
      P.scale y (P.length_pos j).ne' x

omit alt hAlt in
theorem sum_slotted_rawInterval
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (∑ b : Fin B, (P.slotted hcard b).rawInterval
      (fun j p => coeff j p.1.1 p.1.2) i lower upper x y) =
      P.rawInterval coeff i lower upper x y := by
  have hband (j : Fin N) (k : κ) (y : ℝ) :
      (∑ b : Fin B, ∑ p : P.SlotItem hcard b j,
        coeff j p.1.1 p.1.2 k * (P.slotted hcard b).raw i j p k y x) =
      ∑ p : Σ l : P.labels j, Item j l, coeff j p.1 p.2 k * P.raw i j p.1 p.2 k y x := by
    simp_rw [P.slotted_raw hcard]
    simpa only [Fintype.sum_sigma] using
      P.sum_slotted hcard j (fun l u => coeff j l u k * P.raw i j l u k y x)
  have hpartial (n : ℕ) (k : κ) :
      (∑ b : Fin B, scalarBandPartial (fun j =>
        planarPacketBand (ι := P.SlotItem hcard b) (fun j p => coeff j p.1.1 p.1.2)
          (fun j p k t s => (P.slotted hcard b).raw i j p k t s) j k x) n y) =
      scalarBandPartial (fun j => planarPacketBand (ι := fun j => Σ l : P.labels j, Item j l)
        (fun j p => coeff j p.1 p.2)
        (fun j p k t s => P.raw i j p.1 p.2 k t s) j k x) n y := by
    unfold scalarBandPartial
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < n
    · simp only [hj, ite_true, planarPacketBand]
      exact hband j k y
    · simp only [hj, ite_false, Finset.sum_const_zero]
  ext k
  simp only [SourceLatticePacket.rawInterval, rawInterval, planarPacketInterval,
    bandIntervalSignal, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp]
  rw [Finset.sum_sub_distrib, hpartial, hpartial]

omit alt hAlt in
theorem sum_slotted_covariant (hscale : P.scale ≠ 0)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    (∑ b : Fin B, covariantSignal P.frequency (fun k t =>
      (P.slotted hcard b).rawInterval (fun j p => coeff j p.1.1 p.1.2)
        0 lower upper x t k) y) =
      covariantSignal P.frequency (fun k t => P.rawInterval coeff 0 lower upper x t k) y := by
  apply smul_right_injective (M := EuclideanSpace ℂ κ) hscale
  calc
    P.scale • (∑ b : Fin B, covariantSignal P.frequency (fun k t =>
        (P.slotted hcard b).rawInterval (fun j p => coeff j p.1.1 p.1.2)
          0 lower upper x t k) y) =
        ∑ b : Fin B, (P.slotted hcard b).rawInterval
          (fun j p => coeff j p.1.1 p.1.2) 1 lower upper x y := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact (P.slotted hcard b).rawInterval_scaled_covariant
        (fun j p => coeff j p.1.1 p.1.2) lower upper x y
    _ = P.rawInterval coeff 1 lower upper x y :=
      P.sum_slotted_rawInterval hcard coeff 1 lower upper x y
    _ = P.scale • covariantSignal P.frequency
        (fun k t => P.rawInterval coeff 0 lower upper x t k) y :=
      (P.rawInterval_scaled_covariant coeff lower upper x y).symm

theorem sum_slotted_cross_rawInterval (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (∑ b : Fin B, ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b)).rawInterval
      ((P.slotted hcard b).family.mainCoefficient d
        (fun z => v (sourceReferenceToPhysical t z))
        (fun z => g (sourceReferenceToPhysical t z))) i lower upper x y) =
      (P.withProfile alt hAlt).rawInterval (P.physicalCoefficient t d v g)
        i lower upper x y := by
  have hc (b : Fin B) : (P.slotted hcard b).family.mainCoefficient d
      (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) =
      (fun j p => P.physicalCoefficient t d v g j p.1.1 p.1.2) := by
    funext j p
    exact P.slotted_mainCoefficient_physical hcard b t d v g j p
  simp_rw [hc]
  simp_rw [← P.withProfile_slotted hcard alt hAlt]
  exact (P.withProfile alt hAlt).sum_slotted_rawInterval hcard
    (P.physicalCoefficient t d v g) i lower upper x y

/-- The finite physical adjoint sum over the original labeled packets. -/
def physicalSynthesis (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (t : ℝ) (z : ℝ × ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    coeff j l u k * P.physicalPacket t j l u k z)

omit alt hAlt in
theorem sum_slotted_physicalSynthesis
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (t : ℝ) (z : ℝ × ℝ) :
    (∑ b : Fin B, diagonalSynthesis
      (fun (q : Σ j, P.SlotItem hcard b j) k w =>
        (P.slotted hcard b).physicalPacket t q.1 q.2 k w)
      (fun q => coeff q.1 q.2.1.1 q.2.1.2) z) = P.physicalSynthesis coeff t z := by
  ext k
  simp only [diagonalSynthesis, physicalSynthesis, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_toLp, Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [P.slotted_physicalPacket hcard]
  exact P.sum_slotted hcard j (fun l u => coeff j l u k * P.physicalPacket t j l u k z)

theorem sum_slotted_cross_physicalSynthesis (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ) (z : ℝ × ℝ) :
    (∑ b : Fin B, diagonalSynthesis
      (fun (q : Σ j, P.SlotItem hcard b j) k w =>
        ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
          (P.slottedAlt_bound hcard alt hAlt b)).physicalPacket t q.1 q.2 k w)
      (fun q => (P.slotted hcard b).physicalCoefficient t d v g q.1 q.2) z) =
      (P.withProfile alt hAlt).physicalSynthesis (P.physicalCoefficient t d v g) t z := by
  simp_rw [P.slotted_physicalCoefficient hcard]
  simp_rw [← P.withProfile_slotted hcard alt hAlt]
  exact (P.withProfile alt hAlt).sum_slotted_physicalSynthesis hcard
    (P.physicalCoefficient t d v g) t z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
