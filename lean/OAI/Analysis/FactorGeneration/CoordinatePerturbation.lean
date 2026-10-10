import OAI.Analysis.FactorGeneration.FreeGroupMoments
import OAI.Analysis.FactorGeneration.LongWords

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def boundedToSequence (b : Bounded M) : Sequences M :=
  Classical.choose (boundedMap_surjective b)

theorem boundedToSequence_map (b : Bounded M) : boundedMap (boundedToSequence b)=b :=
  Classical.choose_spec (boundedMap_surjective b)

theorem boundedToSequence_apply (b : Bounded M) (k : ℕ) : boundedToSequence b k=b.val k :=
  congrArg (fun a : Bounded M => a.val k) (boundedToSequence_map b)

def boundedUnitarySequence (b : Bounded M) (hb : ∀ k,b.val k ∈ unitary M.toStarSubalgebra) :
    unitary (Sequences M) :=
  ⟨boundedToSequence b,by
    apply Unitary.mem_iff.mpr
    constructor <;> apply BoundedContinuousFunction.ext <;> intro k
    · change star (boundedToSequence b k)*boundedToSequence b k=1
      rw [boundedToSequence_apply]
      exact Unitary.star_mul_self_of_mem (hb k)
    · change boundedToSequence b k*star (boundedToSequence b k)=1
      rw [boundedToSequence_apply]
      exact Unitary.mul_star_self_of_mem (hb k)⟩

def sequenceUnitaryQuotient : unitary (Sequences M) →* unitary (Q τ ω) where
  toFun u := ⟨sequenceQuotient τ ω (u : Sequences M),Unitary.map_mem (sequenceQuotient τ ω) u.property⟩
  map_one' := Subtype.ext (map_one (sequenceQuotient τ ω))
  map_mul' a b := Subtype.ext (map_mul (sequenceQuotient τ ω) (a : Sequences M) (b : Sequences M))

theorem sequenceUnitaryQuotient_bounded (b : Bounded M)
    (hb : ∀ k,b.val k ∈ unitary M.toStarSubalgebra) :
    (sequenceUnitaryQuotient τ ω (boundedUnitarySequence b hb) : Q τ ω)=
      quotientMap τ (ω : Filter ℕ) b := by
  change quotientMap τ (ω : Filter ℕ) (boundedMap (boundedToSequence b))=_
  rw [boundedToSequence_map]

def coordinateGroupRing {A : Type*} (v : A → unitary (Sequences M)) :
    MonoidAlgebra ℂ (FreeGroup A) →ₐ[ℂ] Sequences M :=
  MonoidAlgebra.lift ℂ (Sequences M) (FreeGroup A)
    ((unitary (Sequences M)).subtype.comp (FreeGroup.lift v))

theorem coordinateGroupRing_single {A : Type*} (v : A → unitary (Sequences M))
    (g : FreeGroup A) : coordinateGroupRing v (MonoidAlgebra.single g 1)=(FreeGroup.lift v g : Sequences M) := by
  simp [coordinateGroupRing]

theorem freeGroup_quotient {A : Type*} (v : A → unitary (Sequences M))
    (q : A → unitary (Q τ ω)) (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (g : FreeGroup A) : sequenceUnitaryQuotient τ ω (FreeGroup.lift v g)=
      unitaryRepresentation τ ω q g := by
  exact FreeGroup.lift_unique ((sequenceUnitaryQuotient τ ω).comp (FreeGroup.lift v))
    (fun a => by simpa only [MonoidHom.comp_apply,FreeGroup.lift_apply_of] using hv a)

theorem coordinateGroupRing_quotient_single {A : Type*} (v : A → unitary (Sequences M))
    (q : A → unitary (Q τ ω)) (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (g : FreeGroup A) : sequenceQuotient τ ω (coordinateGroupRing v (MonoidAlgebra.single g 1))=
      (unitaryRepresentation τ ω q g : Q τ ω) := by
  rw [coordinateGroupRing_single]
  exact congrArg Subtype.val (freeGroup_quotient τ ω v q hv g)

theorem coordinateGroupRing_gram_limits {A : Type*} [DecidableEq A]
    (v : A → unitary (Sequences M)) (q : A → unitary (Q τ ω))
    (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω q g : Q τ ω)=0)
    (g h : FreeGroup A) :
    Tendsto (fun k => τ.trace (star (coordinateGroupRing v (MonoidAlgebra.single g 1) k)*
      coordinateGroupRing v (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g=h then 1 else 0)) := by
  have ht := sequence_inner_tendsto τ ω (coordinateGroupRing v (MonoidAlgebra.single g 1))
    (coordinateGroupRing v (MonoidAlgebra.single h 1))
  simpa only [sequenceInclusion_apply,inclusion_inner,
    coordinateGroupRing_quotient_single τ ω v q hv,unitaryRepresentation_gram τ ω q hzero] using ht

theorem coordinateGroupRing_orthonormal {A : Type*} [DecidableEq A]
    (v : A → unitary (Sequences M)) (q : A → unitary (Q τ ω))
    (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω q g : Q τ ω)=0) :
    Orthonormal ℂ (fun g => sequenceInclusion τ ω (coordinateGroupRing v (MonoidAlgebra.single g 1))) := by
  rw [orthonormal_iff_ite]
  intro g h
  simp only [sequenceInclusion_apply,inclusion_inner,
    coordinateGroupRing_quotient_single τ ω v q hv,unitaryRepresentation_gram τ ω q hzero]

theorem coordinateGroupRing_isometry {A : Type*} [DecidableEq A]
    (v : A → unitary (Sequences M)) (q : A → unitary (Q τ ω))
    (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω q g : Q τ ω)=0)
    (f : MonoidAlgebra ℂ (FreeGroup A)) :
    ‖sequenceQuotient τ ω (coordinateGroupRing v f)‖^2=
      ∑ g ∈ f.coeff.support,‖f.coeff g‖^2 := by
  have h := groupRing_coefficient_isometry
    ((sequenceInclusion τ ω).toLinearMap.comp (coordinateGroupRing v).toLinearMap)
    (coordinateGroupRing_orthonormal τ ω v q hv hzero) f
  simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,AlgHom.toLinearMap_apply,
    sequenceInclusion_apply,LinearIsometry.norm_map] using h

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem unitaryRepresentation_prefix (u : unitary (Q τ ω))
    (t : ℕ → unitary (Q τ ω)) (k : ℕ) :
    unitaryRepresentation τ ω (prefixVariable τ ω u t) (freePrefix k)=
      prefixProduct τ ω u t k := by
  induction k with
  | zero => exact map_one _
  | succ k ih =>
    rw [freePrefix,(unitaryRepresentation τ ω (prefixVariable τ ω u t)).map_mul,ih]
    change prefixProduct τ ω u t k*FreeGroup.lift (prefixVariable τ ω u t) (FreeGroup.of k)=_
    rw [FreeGroup.lift_apply_of]
    rfl

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.labelUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (ell : ℕ) (p : PrefixLabel ell) : unitary (Q τ ω) :=
  unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) p.val

def SuccessiveCoordinateHaar.targetUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (ell : ℕ) : unitary (Q τ ω) :=
  z*(prefixProduct τ ω u (fun k => (F.step k).t) (ell+1))⁻¹

def SuccessiveCoordinateHaar.conjugateUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (ell : ℕ) : PrefixLabel ell → unitary (Q τ ω) :=
  conjugateVariables τ ω (F.labelUnitary τ ω u ell) (F.targetUnitary τ ω u z ell)

theorem SuccessiveCoordinateHaar.label_mem (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) (p : PrefixLabel ell) :
    (F.labelUnitary τ ω u ell p : Q τ ω) ∈ F.algebra ell := by
  classical
  have hp := p.property
  change p.val ∈ ratioLabels ell at hp
  simp only [ratioLabels,Finset.mem_insert,Finset.mem_image] at hp
  rcases hp with he | ⟨ij,_,he⟩
  · change (unitaryRepresentation τ ω _ p.val : Q τ ω) ∈ _
    rw [he,map_one]
    exact (F.algebra ell).one_mem
  · change (unitaryRepresentation τ ω _ p.val : Q τ ω) ∈ _
    let f := unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t))
    have hright := (f.map_inv (freePrefix (ij.2.val+1))).trans
      (congrArg Inv.inv (unitaryRepresentation_prefix τ ω u (fun k => (F.step k).t) (ij.2.val+1)))
    have hratio := (congrArg f he.symm).trans
      ((f.map_mul (freePrefix (ij.1.val+1)) ((freePrefix (ij.2.val+1))⁻¹)).trans
        (congrArg₂ (fun a b => a*b)
          (unitaryRepresentation_prefix τ ω u (fun k => (F.step k).t) (ij.1.val+1)) hright))
    have hj : star (prefixProduct τ ω u (fun k => (F.step k).t) (ij.2.val+1) : Q τ ω) ∈ F.algebra ell :=
      star_mem (F.prefix_mem τ ω u hu (by omega))
    exact (congrArg (fun a : unitary (Q τ ω) => (a : Q τ ω) ∈ F.algebra ell) hratio).mpr
      ((F.algebra ell).mul_mem (F.prefix_mem τ ω u hu (by omega)) hj)

theorem SuccessiveCoordinateHaar.label_ratio_zero (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (ell : ℕ)
    (p q : PrefixLabel ell) (hpq : p ≠ q) :
    quotientTrace τ ω (↑((F.labelUnitary τ ω u ell p)⁻¹*F.labelUnitary τ ω u ell q) : Q τ ω)=0 := by
  change quotientTrace τ ω (↑((unitaryRepresentation τ ω _ p.val)⁻¹*
    unitaryRepresentation τ ω _ q.val) : Q τ ω)=0
  let f := unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t))
  rw [← f.map_inv,← f.map_mul]
  apply F.freeGroup_trace τ ω u hu
  exact fun h => hpq (Subtype.ext (_root_.inv_mul_eq_one.mp h))

theorem SuccessiveCoordinateHaar.conjugate_trace (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed)
    (ell : ℕ) (g : FreeGroup (PrefixLabel ell)) (hg : g ≠ 1) :
    quotientTrace τ ω (unitaryRepresentation τ ω (F.conjugateUnitary τ ω u z ell) g : Q τ ω)=0 := by
  classical
  exact conjugate_freeGroup_trace τ ω _ (F.algebra ell) (F.label_mem τ ω u hu ell)
    (F.label_ratio_zero τ ω u hu ell) _ (F.target_endpoints τ ω u z hu hz ell) g hg

theorem SuccessiveCoordinateHaar.conjugate_injective (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (ell : ℕ) :
    Function.Injective (unitaryRepresentation τ ω (F.conjugateUnitary τ ω u z ell)) :=
  unitaryRepresentation_injective τ ω _ (F.conjugate_trace τ ω u z hu hz ell)

theorem SuccessiveCoordinateHaar.conjugate_gram (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed)
    (ell : ℕ) (g h : FreeGroup (PrefixLabel ell)) :
    quotientTrace τ ω
      (star (unitaryRepresentation τ ω (F.conjugateUnitary τ ω u z ell) g : Q τ ω)*
        (unitaryRepresentation τ ω (F.conjugateUnitary τ ω u z ell) h : Q τ ω))=
      if g=h then 1 else 0 := by
  classical
  exact unitaryRepresentation_gram τ ω _ (F.conjugate_trace τ ω u z hu hz ell) g h

theorem SuccessiveCoordinateHaar.conjugate_orthonormal
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (ell : ℕ) :
    Orthonormal ℂ (fun g : FreeGroup (PrefixLabel ell) => inclusion τ ω
      (unitaryRepresentation τ ω (F.conjugateUnitary τ ω u z ell) g : Q τ ω)) := by
  classical
  rw [orthonormal_iff_ite]
  intro g h
  rw [inclusion_inner]
  exact F.conjugate_gram τ ω u z hu hz ell g h

end

section

/-! The finite-prefix analytic bound in the actual bounded-sequence/tracial
quotient realization. Word moments remain explicit premises: no free-Haar
existence or perturbation construction is asserted by this transport theorem. -/
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem orthonormal_of_coordinate_moments {G : Type*} [Monoid G]
    (Φ : MonoidAlgebra ℂ G →ₐ[ℂ] Sequences M)
    (hmom : ∀ g h : G,
      Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
        Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g = h then 1 else 0))) :
    Orthonormal ℂ (fun g => sequenceInclusion τ ω (Φ (MonoidAlgebra.single g 1))) := by
  classical
  rw [orthonormal_iff_ite]
  intro g h
  exact tendsto_nhds_unique (sequence_inner_tendsto τ ω
    (Φ (MonoidAlgebra.single g 1)) (Φ (MonoidAlgebra.single h 1))) (hmom g h)

def remainderSequence (n : ℕ) (α : ℝ)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M) : Sequences M :=
  ((finitePerturbationRows n α).map (fun r => NormedSpace.exp (Φ r))).prod -
    1 - ((finitePerturbationRows n α).map Φ).sum

/-- The actual quotient two-norm estimate from coordinate word moments. -/
theorem tracial_remainder_of_coordinate_moments (n : ℕ) (hn : 0 < n)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M)
    (hmom : ∀ g h : FreeGroup (PrefixLabel n),
      Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
        Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g = h then 1 else 0)))
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖sequenceQuotient τ ω (remainderSequence n α Φ)‖ ≤ 4*α^2/(1-2*α) := by
  have h := finite_prefix_remainder_transfer (B := Sequences M) (E := L2 τ ω) n hn Φ (sequenceInclusion τ ω)
    (orthonormal_of_coordinate_moments τ ω Φ (by
      intro g h
      by_cases hgh : g = h
      · simpa only [ite_eq_left hgh] using hmom g h
      · simpa only [ite_eq_right hgh] using hmom g h)) α hα hhalf
  simpa only [remainderSequence, sequenceInclusion_apply, LinearIsometry.norm_map] using h

/-- The remainder bound holds with any positive slack on an ultrafilter-large
set of actual coordinates, once the displayed word moments are constructed. -/
theorem coordinate_remainder_eventually (n : ℕ) (hn : 0 < n)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M)
    (hmom : ∀ g h : FreeGroup (PrefixLabel n),
      Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
        Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g = h then 1 else 0)))
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in (ω : Filter ℕ), τ.norm₂ (remainderSequence n α Φ k) < 4*α^2/(1-2*α)+ε := by
  have hb := tracial_remainder_of_coordinate_moments τ ω n hn Φ hmom α hα hhalf
  exact (sequence_norm_tendsto τ ω (remainderSequence n α Φ))
    (Iio_mem_nhds (lt_of_le_of_lt hb (lt_add_of_pos_right _ hε)))

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantSequenceUnitary (u : unitary M.toStarSubalgebra) : unitary (Sequences M) :=
  ⟨constantSequence (u : M.toStarSubalgebra),Unitary.map_mem constantSequence u.property⟩

def constantQuotientUnitary (u : unitary M.toStarSubalgebra) : unitary (Q τ ω) :=
  sequenceUnitaryQuotient τ ω (constantSequenceUnitary u)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.haarSequence (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j : ℕ) : unitary (Sequences M) :=
  boundedUnitarySequence (boundedInclusion hNM (F.step j).coordinates)
    (fun k => Unitary.map_mem (coordinateInclusion hNM) ((F.step j).unitary_coordinates k))

theorem SuccessiveCoordinateHaar.haarSequence_apply (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j k : ℕ) : (F.haarSequence τ ω j : Sequences M) k=
      coordinateInclusion hNM ((F.step j).coordinates.val k) :=
  boundedToSequence_apply _ k

theorem SuccessiveCoordinateHaar.haarSequence_quotient (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j : ℕ) : sequenceUnitaryQuotient τ ω (F.haarSequence τ ω j)=(F.step j).t := by
  apply Subtype.ext
  exact (sequenceUnitaryQuotient_bounded τ ω
    (boundedInclusion hNM (F.step j).coordinates)
    (fun k => Unitary.map_mem (coordinateInclusion hNM) ((F.step j).unitary_coordinates k))).trans
      (F.step j).represents

def SuccessiveCoordinateHaar.coordinateVariables (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) : ℕ → unitary (Sequences M)
  | 0 => F.haarSequence τ ω 0
  | j+1 => constantSequenceUnitary u*F.haarSequence τ ω (j+1)

theorem SuccessiveCoordinateHaar.coordinateVariables_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra) (j : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinateVariables τ ω u j)=
      prefixVariable τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) j := by
  cases j with
  | zero => exact F.haarSequence_quotient τ ω 0
  | succ j =>
    change sequenceUnitaryQuotient τ ω (constantSequenceUnitary u*F.haarSequence τ ω (j+1))=_
    rw [(sequenceUnitaryQuotient τ ω).map_mul,F.haarSequence_quotient]
    rfl

def SuccessiveCoordinateHaar.coordinateLabels (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (ell : ℕ) (p : PrefixLabel ell) : unitary (Sequences M) :=
  FreeGroup.lift (F.coordinateVariables τ ω u) p.val

def SuccessiveCoordinateHaar.coordinateTarget (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) : unitary (Sequences M) :=
  constantSequenceUnitary z*(FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix (ell+1)))⁻¹

def SuccessiveCoordinateHaar.coordinateConjugates (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (p : PrefixLabel ell) : unitary (Sequences M) :=
  F.coordinateLabels τ ω u ell p*F.coordinateTarget τ ω u z ell*(F.coordinateLabels τ ω u ell p)⁻¹

theorem SuccessiveCoordinateHaar.coordinateLabels_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra)
    (ell : ℕ) (p : PrefixLabel ell) :
    sequenceUnitaryQuotient τ ω (F.coordinateLabels τ ω u ell p)=
      F.labelUnitary τ ω (constantQuotientUnitary τ ω u) ell p :=
  freeGroup_quotient τ ω _ _ (F.coordinateVariables_quotient τ ω u) p.val

theorem SuccessiveCoordinateHaar.coordinateTarget_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra) (ell : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinateTarget τ ω u z ell)=
      F.targetUnitary τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z) ell := by
  let q := sequenceUnitaryQuotient τ ω
  let a := FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix (ell+1))
  have hp := (freeGroup_quotient τ ω _ _ (F.coordinateVariables_quotient τ ω u)
    (freePrefix (ell+1))).trans
      (unitaryRepresentation_prefix τ ω (constantQuotientUnitary τ ω u)
        (fun k => (F.step k).t) (ell+1))
  exact (q.map_mul (constantSequenceUnitary z) a⁻¹).trans
    (congrArg (fun b => constantQuotientUnitary τ ω z*b)
      ((q.map_inv a).trans (congrArg Inv.inv hp)))

theorem SuccessiveCoordinateHaar.coordinateConjugates_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (p : PrefixLabel ell) :
    sequenceUnitaryQuotient τ ω (F.coordinateConjugates τ ω u z ell p)=
      F.conjugateUnitary τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z) ell p := by
  let q := sequenceUnitaryQuotient τ ω
  let a := F.coordinateLabels τ ω u ell p
  let b := F.coordinateTarget τ ω u z ell
  have ha := F.coordinateLabels_quotient τ ω u ell p
  have hb := F.coordinateTarget_quotient τ ω u z ell
  exact (q.map_mul (a*b) a⁻¹).trans
    (congrArg₂ (fun x y => x*y)
      ((q.map_mul a b).trans (congrArg₂ (fun x y => x*y) ha hb))
      ((q.map_inv a).trans (congrArg Inv.inv ha)))

def SuccessiveCoordinateHaar.perturbationMap (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell)) →ₐ[ℂ] Sequences M :=
  coordinateGroupRing (F.coordinateConjugates τ ω u z ell)

theorem SuccessiveCoordinateHaar.perturbationMap_gram
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (g h : FreeGroup (PrefixLabel ell)) :
    Tendsto (fun k => τ.trace (star (F.perturbationMap τ ω u z ell (MonoidAlgebra.single g 1) k)*
      F.perturbationMap τ ω u z ell (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g=h then 1 else 0)) := by
  classical
  exact coordinateGroupRing_gram_limits τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell)
    (F.conjugate_trace τ ω _ _ hu hz ell) g h

theorem SuccessiveCoordinateHaar.perturbationMap_isometry
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (f : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) :
    ‖sequenceQuotient τ ω (F.perturbationMap τ ω u z ell f)‖^2=
      ∑ g ∈ f.coeff.support,‖f.coeff g‖^2 := by
  classical
  exact coordinateGroupRing_isometry τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell)
    (F.conjugate_trace τ ω _ _ hu hz ell) f

theorem SuccessiveCoordinateHaar.perturbation_remainder
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖sequenceQuotient τ ω (remainderSequence ell α (F.perturbationMap τ ω u z ell))‖ ≤
      4*α^2/(1-2*α) :=
  tracial_remainder_of_coordinate_moments τ ω ell hell _
    (F.perturbationMap_gram τ ω u z hu hz ell) α hα hhalf

theorem SuccessiveCoordinateHaar.coordinate_remainder
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in (ω : Filter ℕ),τ.norm₂ (remainderSequence ell α (F.perturbationMap τ ω u z ell) k)<
      4*α^2/(1-2*α)+ε :=
  coordinate_remainder_eventually τ ω ell hell _
    (F.perturbationMap_gram τ ω u z hu hz ell) α hα hhalf ε hε

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.coordinatePrefix (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (k : ℕ) : unitary (Sequences M) :=
  FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix k)

def SuccessiveCoordinateHaar.commonPerturbation (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : Sequences M :=
  (α/(2*ell)) • ∑ j : Fin ell,
    let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
      F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1))
    a-star a

theorem SuccessiveCoordinateHaar.commonPerturbation_skew
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    star (F.commonPerturbation τ ω u z ell α) = -F.commonPerturbation τ ω u z ell α := by
  let A : Sequences M := ∑ j : Fin ell,
    let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
      F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1))
    a-star a
  have hA : star A = -A := by
    unfold A
    rw [star_sum]
    calc
      _ = ∑ j : Fin ell, -(let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
          F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1)); a-star a) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only
        rw [star_sub,star_star,neg_sub]
      _ = _ := Finset.sum_neg_distrib _
  change star ((α/(2*ell) : ℝ) • A) = -((α/(2*ell) : ℝ) • A)
  calc
    _ = (α/(2*ell) : ℝ) • star A := by rw [star_smul,star_trivial]
    _ = (α/(2*ell) : ℝ) • (-A) := congrArg ((α/(2*ell) : ℝ) • ·) hA
    _ = _ := smul_neg _ _

theorem SuccessiveCoordinateHaar.coordinateLabels_pair
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) {ell : ℕ} (k j : Fin ell) :
    F.coordinateLabels τ ω u ell (pairLabel k j)=
      F.coordinatePrefix τ ω u (k.val+1)*(F.coordinatePrefix τ ω u (j.val+1))⁻¹ := by
  change FreeGroup.lift _ (freePrefix _*(freePrefix _)⁻¹)=_
  rw [(FreeGroup.lift (F.coordinateVariables τ ω u)).map_mul,
    (FreeGroup.lift (F.coordinateVariables τ ω u)).map_inv]
  rfl

theorem SuccessiveCoordinateHaar.perturbationMap_row
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) {ell : ℕ} (α : ℝ) (k : Fin ell) :
    F.perturbationMap τ ω u z ell (finitePerturbationRow α k)=
      (F.coordinatePrefix τ ω u (k.val+1) : Sequences M)*
        F.commonPerturbation τ ω u z ell α*
        star (F.coordinatePrefix τ ω u (k.val+1) : Sequences M) := by
  let Φ := F.perturbationMap τ ω u z ell
  have hs (r : ℝ) (a : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) : Φ (r • a)=r • Φ a :=
    map_smul (Φ.restrictScalars ℝ).toLinearMap r a
  have hgen (p : PrefixLabel ell) : Φ (MonoidAlgebra.single (FreeGroup.of p) 1)=
      (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,FreeGroup.lift_apply_of]
  have hinv (p : PrefixLabel ell) : Φ (MonoidAlgebra.single ((FreeGroup.of p)⁻¹) 1)=
      star (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,map_inv,FreeGroup.lift_apply_of]
    rfl
  change Φ (finitePerturbationRow α k)=_
  rw [finitePerturbationRow,hs,commonPerturbation]
  simp only [map_sum,map_sub,hgen,hinv,mul_smul_comm,smul_mul_assoc,
    Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateConjugates,coordinateLabels_pair]
  simp only [← Unitary.star_eq_inv,Submonoid.coe_mul,Unitary.coe_star]
  simp only [star_mul,star_star,mul_sub,sub_mul,mul_assoc]

def SuccessiveCoordinateHaar.perturbingUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  ⟨NormedSpace.exp (F.commonPerturbation τ ω u z ell α),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (show F.commonPerturbation τ ω u z ell α ∈ skewAdjoint (Sequences M) from
        skewAdjoint.mem_iff.mpr (F.commonPerturbation_skew τ ω u z ell α))⟩

def SuccessiveCoordinateHaar.perturbedUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  F.perturbingUnitary τ ω u z ell α*constantSequenceUnitary u

theorem sequence_exp_conjugate (g : unitary (Sequences M)) (a : Sequences M) :
    NormedSpace.exp ((g : Sequences M)*a*star (g : Sequences M))=
      (g : Sequences M)*NormedSpace.exp a*star (g : Sequences M) := by
  have h : SemiconjBy (g : Sequences M) a ((g : Sequences M)*a*star (g : Sequences M)) := by
    unfold SemiconjBy
    simp only [mul_assoc,Unitary.coe_star_mul_self,mul_one]
  have he := congrArg (fun b : Sequences M => b*star (g : Sequences M)) h.exp_right
  have hg : (g : Sequences M)*star (g : Sequences M)=1 := g.property.2
  simpa only [mul_assoc,hg,mul_one] using he.symm

theorem SuccessiveCoordinateHaar.exponential_row
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) {ell : ℕ} (α : ℝ) (k : Fin ell) :
    NormedSpace.exp (F.perturbationMap τ ω u z ell (finitePerturbationRow α k))=
      (↑(F.coordinatePrefix τ ω u (k.val+1)*F.perturbingUnitary τ ω u z ell α*
        (F.coordinatePrefix τ ω u (k.val+1))⁻¹) : Sequences M) := by
  rw [F.perturbationMap_row,sequence_exp_conjugate]
  rfl

end Generator.Tracial

end

end OAI
