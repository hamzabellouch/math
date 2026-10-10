import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMeshStep
import OAI.MathematicalPhysics.Boltzmann.Branching.EntrySites
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.OutgoingPairIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.ThreeSelectedIntegral
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformAverageCompactness
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricPositiveCompact

namespace OAI

section

/-! # Actual cold partners and densities at the three entry collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryPartner₀ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) : V :=
  beamVelocity θ η α γ σ (entrySite₀ t x v s)

def entryDensity₀ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) : ℝ :=
  beamDensity θ η α γ 1 σ (entrySite₀ t x v s)

def entryPartner₁ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V) : V :=
  beamVelocity θ η α γ (-σ) (entrySite₁ t x v s u)

def entryDensity₁ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V) : ℝ :=
  beamDensity θ η α γ 1 (-σ) (entrySite₁ t x v s u)

def entryPartner₂ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V)
    (a : Sphere × Sphere) : V :=
  beamVelocity θ η α γ 1 (entrySite₂ t x v s u
    (child u (entryPartner₁ θ η α γ σ t x v s u) a.1.1))

def entryDensity₂ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V)
    (a : Sphere × Sphere) : ℝ :=
  beamDensity θ η α γ 1 1 (entrySite₂ t x v s u
    (child u (entryPartner₁ θ η α γ σ t x v s u) a.1.1))

def entryAngularMass (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (κ ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
    ‖v-entryPartner₀ θ η α γ σ t x v s‖)*
    ∫⁻ u, (∫⁻ a, accessWeight u (fun _ => entryPartner₁ θ η α γ σ t x v s u)
      (entryPartner₂ θ η α γ σ t x v s u)
      (fun _ => entryDensity₁ θ η α γ σ t x v s u)
      (entryDensity₂ θ η α γ σ t x v s u) κ ρ a
      ∂sphereProbability.prod sphereProbability)
      ∂outgoing (v,entryPartner₀ θ η α γ σ t x v s)

theorem entryPartner₀_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ t : ℝ)
    (x v : V) (s : ThreeWaits) :
    ‖entryPartner₀ θ η α γ σ t x v s-σ • beamAxis‖ ≤ α :=
  beamVelocity_error hα θ η γ σ _

theorem entryPartner₁_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ t : ℝ)
    (x v : V) (s : ThreeWaits) (u : V) :
    ‖entryPartner₁ θ η α γ σ t x v s u-(-(σ • beamAxis))‖ ≤ α := by
  simpa only [entryPartner₁,neg_smul] using beamVelocity_error hα θ η γ (-σ) (entrySite₁ t x v s u)

theorem entryPartner₂_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ t : ℝ)
    (x v : V) (s : ThreeWaits) (u : V) (a : Sphere × Sphere) :
    ‖entryPartner₂ θ η α γ σ t x v s u a-beamAxis‖ ≤ α := by
  simpa only [entryPartner₂,one_smul] using beamVelocity_error hα θ η γ 1
    (entrySite₂ t x v s u (child u (entryPartner₁ θ η α γ σ t x v s u) a.1.1))

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The entry signs are the two physical beam marks -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryMark (σ : ℝ) : HistoryMark := if σ = 1 then 1 else 2

theorem entryMark_ne_zero (σ : ℝ) : entryMark σ ≠ 0 := by
  unfold entryMark
  split <;> norm_num

theorem entryMark_child {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η : ℝ) (p : ℝ × V) (v : V) (n : Sphere) :
    markedChild (entryMark σ) v ((beamCoefficients hθ hα hγ η 1).plusPartner p)
      ((beamCoefficients hθ hα hγ η 1).minusPartner p) n.1 =
      child v (beamVelocity θ η α γ σ p) n.1 := by
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hσ with h | h
  · subst σ
    norm_num [entryMark,markedChild,beamCoefficients]
  · subst σ
    norm_num [entryMark,markedChild,beamCoefficients]

theorem entryMark_rate {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η : ℝ) (p : ℝ × V) (v : V) :
    mediumMarkedRate (beamCoefficients hθ hα hγ η 1) (entryMark σ) (p,v) =
      ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ 1 σ p*
        ‖v-beamVelocity θ η α γ σ p‖) := by
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hσ with h | h
  · subst σ
    norm_num [entryMark,mediumMarkedRate,markedRate,beamCoefficients]
  · subst σ
    norm_num [entryMark,mediumMarkedRate,markedRate,beamCoefficients]

theorem mediumPoint_entry₀ (t h : ℝ) (x v : V) (s : ThreeWaits) :
    mediumPoint (t+h) (h,(x,v)) s.1 = entrySite₀ t x v s := by
  simp [mediumPoint,entrySite₀]

theorem mediumPoint_entry₁ (t h : ℝ) (x v u : V) (s : ThreeWaits) :
    mediumPoint (t+h) (h-s.1,((entrySite₀ t x v s).2,u)) s.2.1 =
      entrySite₁ t x v s u := by
  apply Prod.ext
  · simp only [mediumPoint,entrySite₁]
    ring
  · rfl

theorem mediumPoint_entry₂ (t h : ℝ) (x v u z : V) (s : ThreeWaits) :
    mediumPoint (t+h) (h-s.1-s.2.1,((entrySite₁ t x v s u).2,z)) s.2.2 =
      entrySite₂ t x v s u z := by
  apply Prod.ext
  · simp only [mediumPoint,entrySite₂]
    ring
  · rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A uniform three-collision entry lower bound for the actual cold field -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_entry_lower {θ η α γ κ ρ ε L X R h t T σ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hL : 0 < L) (hX : 0 ≤ X) (hR : 0 ≤ R) (hT0 : 0 ≤ T)
    (ht : 0 ≤ t) (hT : t+3*h ≤ T) (hsmall : (R+6)*h ≤ 1)
    (hσ : |σ| = 1) (x v : V) (hx : ‖x‖ ≤ X) (hxr : L+1 < ‖VelocityWeight.transverse x‖)
    (hv : ‖v‖ ≤ R) (hvfar : 1 ≤ ‖v-σ • beamAxis‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ThreeWaits,
      s.1 ∈ Icc 0 h → s.2.1 ∈ Icc 0 h → s.2.2 ∈ Icc 0 h →
      firstEntryMass R ε c *
        ((ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
          (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) ≤
        entryAngularMass θ η α γ σ t x v s κ ρ := by
  obtain ⟨c,hc,hcold⟩ := nearby_beamDensity_lower hθ hη hα hγ hL hX hT0
  have he : ‖σ • beamAxis‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,hσ,axis_norms.2.2,mul_one]
  have hαsmall : α ≤ 1/4 := by linarith
  have hαε' : α ≤ ε := by linarith
  refine ⟨c,hc,?_⟩
  intro s hs₀ hs₁ hs₂
  have hzero : ‖(0:V)‖ ≤ 3 := by norm_num
  have hsites₀ := entrySites_bounded (x := x) hR hsmall ht hT hs₀ hs₁ hs₂ hv hzero hzero
  have hbc₀ : c ≤ entryDensity₀ θ η α γ σ t x v s :=
    hcold x hx hxr _ hsites₀.1.2 _ hsites₀.1.1 σ hσ
  have hw₀ := entryPartner₀_error hα θ η γ σ t x v s
  have hw₀norm : ‖entryPartner₀ θ η α γ σ t x v s‖ ≤ 2 := by
    have hn := norm_sub_norm_le (entryPartner₀ θ η α γ σ t x v s) (σ • beamAxis)
    rw [he] at hn
    linarith
  have hfar : 3/4 ≤ ‖v-entryPartner₀ θ η α γ σ t x v s‖ := by
    have hh := nearby_partner_distance hvfar hw₀
    linarith
  have hnear : dist (entryPartner₀ θ η α γ σ t x v s) (σ • beamAxis) ≤ ε/2 := by
    rw [dist_eq_norm]
    exact hw₀.trans hαε
  have hpartners (u : V) (_hu : u ∈ ball (σ • beamAxis) ε)
      (a : Sphere × Sphere) (_ha : a ∈ accessAngles κ (ρ/2)) :
      ‖entryPartner₁ θ η α γ σ t x v s u-(-(σ • beamAxis))‖ ≤ ε ∧
        ‖entryPartner₂ θ η α γ σ t x v s u a-beamAxis‖ ≤ ε :=
    ⟨(entryPartner₁_error hα θ η γ σ t x v s u).trans hαε',
      (entryPartner₂_error hα θ η γ σ t x v s u a).trans hαε'⟩
  have hdensities (u : V) (hu : u ∈ ball (σ • beamAxis) ε)
      (a : Sphere × Sphere) (ha : a ∈ accessAngles κ (ρ/2)) :
      c ≤ entryDensity₁ θ η α γ σ t x v s u ∧
        c ≤ entryDensity₂ θ η α γ σ t x v s u a := by
    have hule : ‖u-σ • beamAxis‖ ≤ ε := le_of_lt hu
    have hu3 : ‖u‖ ≤ 3 := by
      have hh := norm_sub_norm_le u (σ • beamAxis)
      rw [he] at hh
      linarith
    obtain ⟨hw₁,hw₂⟩ := hpartners u hu a ha
    have hg := access_pair_stability hκ0 hκ hρ hε hερ he hule hw₁ hw₂ ha
    dsimp only at hg
    have hsites := entrySites_bounded (x := x) hR hsmall ht hT hs₀ hs₁ hs₂ hv hu3 hg.2.2.1
    exact ⟨hcold x hx hxr _ hsites.2.1.2 _ hsites.2.1.1 (-σ) (by simpa using hσ),
      hcold x hx hxr _ hsites.2.2.2 _ hsites.2.2.1 1 (by norm_num)⟩
  exact three_collision_access_lower hκ0 hκ hρ hε0 hε hερ hc hbc₀ hR he hv hw₀norm hfar hnear
    (fun u _ => entryPartner₁ θ η α γ σ t x v s u)
    (entryPartner₂ θ η α γ σ t x v s)
    (fun u _ => entryDensity₁ θ η α γ σ t x v s u)
    (entryDensity₂ θ η α γ σ t x v s) hpartners hdensities

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Measurability of the actual three-collision entry integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryAccess_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η σ t κ ρ : ℝ) (x v : V) :
    Measurable (fun q : (ThreeWaits × V) × (Sphere × Sphere) => accessWeight q.1.2
      (fun _ => entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2)
      (fun _ => entryDensity₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2) κ ρ q.2) := by
  have h₁v : Measurable (fun q : ThreeWaits × V => entryPartner₁ θ η α γ σ t x v q.1 q.2) :=
    (beamVelocity_measurable hθ hα hγ η (-σ)).comp (by unfold entrySite₁; fun_prop)
  have h₁b : Measurable (fun q : ThreeWaits × V => entryDensity₁ θ η α γ σ t x v q.1 q.2) :=
    (beamDensity_measurable hθ hα hγ η 1 (-σ)).comp (by unfold entrySite₁; fun_prop)
  let P := (ThreeWaits × V) × (Sphere × Sphere)
  have h₁v' : Measurable (fun q : P => entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) :=
    h₁v.comp measurable_fst
  have hu : Measurable (fun q : P => child q.1.2
      (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1) := by
    unfold child
    fun_prop
  have hsite : Measurable (fun q : P => entrySite₂ t x v q.1.1 q.1.2
      (child q.1.2 (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1)) := by
    unfold entrySite₂
    fun_prop
  have h₂v : Measurable (fun q : P => entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2 q.2) :=
    (beamVelocity_measurable hθ hα hγ η 1).comp hsite
  have h₂b : Measurable (fun q : P => entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2 q.2) :=
    (beamDensity_measurable hθ hα hγ η 1 1).comp hsite
  have hz : Measurable (fun q : P => child (child q.1.2
      (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1)
      (entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2 q.2) q.2.2.1) := by
    unfold child
    fun_prop
  have h₁b' := h₁b.comp (measurable_fst : Measurable (Prod.fst : P → ThreeWaits × V))
  have hm : Measurable (fun q : P => accessWeight q.1.2
      (fun _ => entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2)
      (fun _ => entryDensity₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2) κ ρ q.2) := by
    have hr₁ : Measurable (fun q : P => ENNReal.ofReal (4*Real.pi*
        entryDensity₁ θ η α γ σ t x v q.1.1 q.1.2*
          ‖q.1.2-entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2‖)) := by fun_prop
    have hr₂ : Measurable (fun q : P => ENNReal.ofReal (4*Real.pi*
        entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2 q.2*
          ‖child q.1.2 (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1-
            entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2 q.2‖)) := by fun_prop
    exact (hr₁.mul hr₂).mul ((measurable_const.indicator measurableSet_ball).comp hz)
  exact hm

theorem entryAngularMass_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η σ t κ ρ : ℝ) (x v : V) :
    Measurable (fun s : ThreeWaits => entryAngularMass θ η α γ σ t x v s κ ρ) := by
  have h₀v : Measurable (entryPartner₀ θ η α γ σ t x v) :=
    (beamVelocity_measurable hθ hα hγ η σ).comp (by unfold entrySite₀; fun_prop)
  have h₀b : Measurable (entryDensity₀ θ η α γ σ t x v) :=
    (beamDensity_measurable hθ hα hγ η 1 σ).comp (by unfold entrySite₀; fun_prop)
  have hm := entryAccess_measurable hθ hα hγ η σ t κ ρ x v
  have hi := hm.lintegral_prod_right' (ν := sphereProbability.prod sphereProbability)
  let J : Kernel ThreeWaits V := outgoing.comap
    (fun s => (v,entryPartner₀ θ η α γ σ t x v s)) (measurable_const.prodMk h₀v)
  have hj := hi.lintegral_kernel_prod_right' (κ := J)
  exact ((measurable_const.mul h₀b).mul (measurable_const.sub h₀v).norm).ennreal_ofReal.mul hj

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three physical state transitions follow the geometric entry path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryVelocity₀ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) : V :=
  child v (entryPartner₀ θ η α γ σ t x v s) a.1.1

def entryVelocity₁ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) : V :=
  child (entryVelocity₀ θ η α γ σ t x v s a)
    (entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)) a.2.1.1

def entryVelocity₂ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) : V :=
  child (entryVelocity₁ θ η α γ σ t x v s a)
    (entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a) a.2) a.2.2.1

def entryState₁ (θ η α γ σ t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    PhysicalFlightState :=
  (h-s.1,((entrySite₀ t x v s).2,entryVelocity₀ θ η α γ σ t x v s a))

def entryState₂ (θ η α γ σ t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    PhysicalFlightState :=
  (h-s.1-s.2.1,((entrySite₁ t x v s (entryVelocity₀ θ η α γ σ t x v s a)).2,
    entryVelocity₁ θ η α γ σ t x v s a))

def entryState₃ (θ η α γ σ t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    PhysicalFlightState :=
  (h-s.1-s.2.1-s.2.2,((entrySite₂ t x v s (entryVelocity₀ θ η α γ σ t x v s a)
    (entryVelocity₁ θ η α γ σ t x v s a)).2,entryVelocity₂ θ η α γ σ t x v s a))

theorem entryState_first {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    mediumParameterState (beamCoefficients hθ hα hγ η 1) (t+h)
      (h,(x,v)) (entryMark σ,(s.1,a.1)) = entryState₁ θ η α γ σ t h x v s a := by
  dsimp only [mediumParameterState]
  rw [mediumPoint_entry₀,entryMark_child hθ hα hγ hσ]
  rfl

theorem entryState_second {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    mediumParameterState (beamCoefficients hθ hα hγ η 1) (t+h)
      (entryState₁ θ η α γ σ t h x v s a) (entryMark (-σ),(s.2.1,a.2.1)) =
        entryState₂ θ η α γ σ t h x v s a := by
  dsimp only [mediumParameterState,entryState₁]
  rw [mediumPoint_entry₁,entryMark_child hθ hα hγ (by simpa only [abs_neg] using hσ)]
  rfl

theorem entryState_third {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    mediumParameterState (beamCoefficients hθ hα hγ η 1) (t+h)
      (entryState₂ θ η α γ σ t h x v s a) (entryMark 1,(s.2.2,a.2.2)) =
        entryState₃ θ η α γ σ t h x v s a := by
  dsimp only [mediumParameterState,entryState₂]
  rw [mediumPoint_entry₂,entryMark_child hθ hα hγ (by norm_num : |(1:ℝ)| = 1)]
  rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Physical collision weights along the three entry transitions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalParameterWeight_wait_eq (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (p : PhysicalFlightState) (a : EventParameter)
    (hs : a.1 ∈ Ioc 0 p.1) :
    physicalParameterWeight b endTime C m p a =
      clockSurvival C a.1 * mediumMarkedRate b m (mediumPoint endTime p a.1,p.2.2) := by
  unfold physicalParameterWeight
  rw [show physicalWaitingWeight C (p,a.1) = clockSurvival C a.1 by
    simp [physicalWaitingWeight,hs.1,hs.2]]

end BoltzmannNonuniqueness.ReferenceGeometry

open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryRate_first {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) (C : ℝ≥0)
    (hs : s.1 ∈ Ioc 0 h) :
    physicalParameterWeight (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark σ) (h,(x,v)) (s.1,a.1) =
      clockSurvival C s.1 * ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
        ‖v-entryPartner₀ θ η α γ σ t x v s‖) := by
  rw [physicalParameterWeight_wait_eq _ _ _ _ _ _ hs,mediumPoint_entry₀,
    entryMark_rate hθ hα hγ hσ]
  rfl

theorem entryRate_second {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) (C : ℝ≥0)
    (hs : s.2.1 ∈ Ioc 0 (h-s.1)) :
    physicalParameterWeight (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark (-σ)) (entryState₁ θ η α γ σ t h x v s a) (s.2.1,a.2.1) =
      clockSurvival C s.2.1 * ENNReal.ofReal (4*Real.pi*
        entryDensity₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)*
        ‖entryVelocity₀ θ η α γ σ t x v s a-
          entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)‖) := by
  rw [physicalParameterWeight_wait_eq _ _ _ _ _ _ hs]
  simp only [entryState₁]
  rw [mediumPoint_entry₁,entryMark_rate hθ hα hγ (by simpa only [abs_neg] using hσ)]
  rfl

theorem entryRate_third {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) (C : ℝ≥0)
    (hs : s.2.2 ∈ Ioc 0 (h-s.1-s.2.1)) :
    physicalParameterWeight (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark 1) (entryState₂ θ η α γ σ t h x v s a) (s.2.2,a.2.2) =
      clockSurvival C s.2.2 * ENNReal.ofReal (4*Real.pi*
        entryDensity₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a) a.2*
        ‖entryVelocity₁ θ η α γ σ t x v s a-
          entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a) a.2‖) := by
  rw [physicalParameterWeight_wait_eq _ _ _ _ _ _ hs]
  simp only [entryState₂]
  rw [mediumPoint_entry₂,entryMark_rate hθ hα hγ (by norm_num : |(1:ℝ)| = 1)]
  rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Exact retained weight of the three physical entry collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryTerminal (C : ℝ≥0) (κ ρ : ℝ) (p : PhysicalFlightState) : ℝ≥0∞ :=
  clockSurvival C p.1 * (ball (κ • firstAxis) ρ).indicator 1 p.2.2

theorem entryTerminal_measurable (C : ℝ≥0) (κ ρ : ℝ) : Measurable (entryTerminal C κ ρ) := by
  exact (show Measurable (fun p : PhysicalFlightState => clockSurvival C p.1) by
    unfold clockSurvival; fun_prop).mul
      ((measurable_const.indicator measurableSet_ball).comp (by fun_prop))

theorem entry_integrand_eq {θ α γ σ h : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (hh : 0 < h) (η t κ ρ : ℝ) (x v : V)
    (s : ThreeWaits) (hs : s ∈ threeWaitBox h) (a : ThreeAngles) (C : ℝ≥0) :
    threeSelectedIntegrand (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark σ) (entryMark (-σ)) (entryMark 1) (h,(x,v)) (entryTerminal C κ ρ)
        (joinThreeEvents s a) =
      clockSurvival C h * (ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
        ‖v-entryPartner₀ θ η α γ σ t x v s‖) *
        accessWeight (entryVelocity₀ θ η α γ σ t x v s a)
          (fun _ => entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (fun _ => entryDensity₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryDensity₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)) κ ρ a.2) := by
  obtain ⟨hs₀,hs₁,hs₂,hsum⟩ := threeWaitBox_sum hh hs
  have hw₀ : s.1 ∈ Ioc 0 h := ⟨hs₀,by linarith⟩
  have hw₁ : s.2.1 ∈ Ioc 0 (h-s.1) := ⟨hs₁,by linarith⟩
  have hw₂ : s.2.2 ∈ Ioc 0 (h-s.1-s.2.1) := ⟨hs₂,by linarith⟩
  simp only [threeSelectedIntegrand,selectedWordDensity,selectedWordState,joinThreeEvents]
  simp only [entryState_first hθ hα hγ hσ,entryState_second hθ hα hγ hσ,
    entryState_third hθ hα hγ]
  rw [entryRate_first hθ hα hγ hσ _ _ _ _ _ _ _ _ hw₀,
    entryRate_second hθ hα hγ hσ _ _ _ _ _ _ _ _ hw₁,
    entryRate_third hθ hα hγ _ _ _ _ _ _ _ _ hw₂]
  have hc : clockSurvival C s.1*clockSurvival C s.2.1*clockSurvival C s.2.2*
      clockSurvival C (h-s.1-s.2.1-s.2.2) = clockSurvival C h := by
    rw [show h-s.1-s.2.1-s.2.2 = h-(s.1+s.2.1+s.2.2) by ring]
    exact three_wait_survival C h s
  rw [← hc]
  simp only [entryTerminal,entryState₃,accessWeight,entryVelocity₁,entryVelocity₂]
  ac_rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive collision-time mass for entry in the actual cold field -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryTimeMass (θ η α γ σ t : ℝ) (x v : V) (κ ρ h : ℝ) (C : ℝ≥0) : ℝ≥0∞ :=
  clockSurvival C h * ∫⁻ s in threeWaitBox h, entryAngularMass θ η α γ σ t x v s κ ρ

theorem entryTimeMass_pos {θ η α γ κ ρ ε L X R h t T σ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hX : 0 ≤ X) (hR : 0 ≤ R) (hT0 : 0 ≤ T)
    (ht : 0 ≤ t) (hT : t+3*h ≤ T) (hsmall : (R+6)*h ≤ 1)
    (hσ : |σ| = 1) (x v : V) (hx : ‖x‖ ≤ X) (hxr : L+1 < ‖VelocityWeight.transverse x‖)
    (hv : ‖v‖ ≤ R) (hvfar : 1 ≤ ‖v-σ • beamAxis‖)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < entryTimeMass θ η α γ σ t x v κ ρ h C := by
  obtain ⟨c,hc,hbound⟩ := geometric_entry_lower hθ hη hα hγ hαε hε0 hε
    hκ0 hκ hρ hερ hL hX hR hT0 ht hT hsmall hσ x v hx hxr hv hvfar
  have hfirst : 0 < firstEntryMass R ε c := firstEntryMass_pos hR hε0 hc
  have hpair : 0 < (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
      (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)) := by
    apply pos_iff_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))) (ne_of_gt hA)
  have hpositive : ∀ s ∈ threeWaitBox h, 0 < entryAngularMass θ η α γ σ t x v s κ ρ := by
    intro s hs
    have hwait : h/4 ≤ h := by linarith
    have h₀ : s.1 ∈ Icc 0 h := ⟨hs.1.1.le,hs.1.2.le.trans hwait⟩
    have h₁ : s.2.1 ∈ Icc 0 h := ⟨hs.2.1.1.le,hs.2.1.2.le.trans hwait⟩
    have h₂ : s.2.2 ∈ Icc 0 h := ⟨hs.2.2.1.le,hs.2.2.2.le.trans hwait⟩
    exact (pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hfirst) (ne_of_gt hpair))).trans_le
      (hbound s h₀ h₁ h₂)
  have hi := threeWaitBox_integral_pos hh
    (entryAngularMass_measurable hθ hα hγ η σ t κ ρ x v) hpositive
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hi))

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three outgoing sphere integral is the actual entry mass -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryAngularMass_sphere {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (η σ t κ ρ : ℝ) (x v : V) (s : ThreeWaits) :
    entryAngularMass θ η α γ σ t x v s κ ρ =
      ∫⁻ a : ThreeAngles, ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
        ‖v-entryPartner₀ θ η α γ σ t x v s‖) *
        accessWeight (entryVelocity₀ θ η α γ σ t x v s a)
          (fun _ => entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (fun _ => entryDensity₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryDensity₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)) κ ρ a.2
        ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  have hjmap : Measurable (fun q : V × (Sphere × Sphere) => ((s,q.1),q.2)) := by
    fun_prop
  have hm := (entryAccess_measurable hθ hα hγ η σ t κ ρ x v).comp hjmap
  exact outgoing_pair_lintegral _ ENNReal.ofReal_ne_top v
    (entryPartner₀ θ η α γ σ t x v s) hm

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive entry mass is carried by the actual physical gain histories -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryTimeMass_le_history {θ α γ σ h : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hσ : |σ| = 1) (hh : 0 < h) (η t κ ρ : ℝ)
    (x v : V) (C : ℝ≥0) :
    entryTimeMass θ η α γ σ t x v κ ρ h C ≤
      ∫⁻ q, entryTerminal C κ ρ q ∂physicalMarkedWord (beamCoefficients hθ hα hγ η 1)
        (t+h) C [entryMark σ,entryMark (-σ),entryMark 1] (h,(x,v)) := by
  rw [threeSelected_time_angles _ _ _ _ _ _ _ (entryTerminal_measurable C κ ρ)]
  unfold entryTimeMass
  have hc : clockSurvival C h ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_const_mul' _ _ hc]
  refine le_trans (le_of_eq ?_) (setLIntegral_le_lintegral (threeWaitBox h) _)
  apply setLIntegral_congr_fun (threeWaitBox_measurable h)
  intro s hs
  dsimp only
  rw [entryAngularMass_sphere hθ hα hγ,← lintegral_const_mul' _ _ hc]
  apply lintegral_congr
  intro a
  exact (entry_integrand_eq hθ hα hγ hσ hh η t κ ρ x v s hs a C).symm

theorem geometric_entry_history_positive {θ η α γ κ ρ ε L X R h t T σ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hX : 0 ≤ X) (hR : 0 ≤ R) (hT0 : 0 ≤ T)
    (ht : 0 ≤ t) (hT : t+3*h ≤ T) (hsmall : (R+6)*h ≤ 1)
    (hσ : |σ| = 1) (x v : V) (hx : ‖x‖ ≤ X) (hxr : L+1 < ‖VelocityWeight.transverse x‖)
    (hv : ‖v‖ ≤ R) (hvfar : 1 ≤ ‖v-σ • beamAxis‖)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < ∫⁻ q, entryTerminal C κ ρ q ∂physicalMarkedWord (beamCoefficients hθ hα hγ η 1)
      (t+h) C [entryMark σ,entryMark (-σ),entryMark 1] (h,(x,v)) :=
  (entryTimeMass_pos hθ hη hα hγ hαε hε0 hε hκ0 hκ hρ hερ hh hL hX hR hT0
    ht hT hsmall hσ x v hx hxr hv hvfar hA C).trans_le
      (entryTimeMass_le_history hθ hα hγ hσ hh η t κ ρ x v C)

theorem entryTimeMass_le_beam_history {θ α γ σ h : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hσ : |σ| = 1) (hh : 0 < h) (η t κ ρ : ℝ)
    (x v : V) (C : ℝ≥0) :
    entryTimeMass θ η α γ σ t x v κ ρ h C ≤
      ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1)
        (t+h) C)^3) (h,(x,v)) := by
  apply (entryTimeMass_le_history hθ hα hγ hσ hh η t κ ρ x v C).trans
  apply lintegral_mono' _ le_rfl
  have hm : ∀ m ∈ [entryMark σ,entryMark (-σ),entryMark 1], m ≠ 0 := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl | rfl <;> exact entryMark_ne_zero _
  exact physicalMarkedWord_le_beam _ _ _ _ hm _

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Every bounded incoming velocity has positive entry through the two beams -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_beam_entry_positive {θ η α γ κ ρ ε L R h t : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t) (hsmall : (R+6)*h ≤ 1)
    (x v : V) (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1)
      (t+h) C)^3) (h,(x,v)) := by
  have H (σ : ℝ) (hσ : |σ| = 1) (hfar : 1 ≤ ‖v-σ • beamAxis‖) :
      0 < ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1)
        (t+h) C)^3) (h,(x,v)) :=
    (entryTimeMass_pos hθ hη hα hγ hαε hε0 hε hκ0 hκ hρ hερ hh hL
      (norm_nonneg x) hR (by linarith : 0 ≤ t+3*h) ht le_rfl hsmall hσ x v le_rfl hxr hv hfar hA C).trans_le
        (entryTimeMass_le_beam_history hθ hα hγ hσ hh η t κ ρ x v C)
  rcases exists_separated_beam v with hplus | hminus
  · exact H 1 (by norm_num) (by simpa only [one_smul] using hplus)
  · exact H (-1) (by norm_num) (by simpa only [neg_one_smul,sub_neg_eq_add] using hminus)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A positive incoming measure produces positive physical entry mass -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryRegion (L R : ℝ) : Set (V × V) :=
  {p | L+1 < ‖VelocityWeight.transverse p.1‖ ∧ ‖p.2‖ ≤ R}

theorem entryRegion_measurable (L R : ℝ) : MeasurableSet (entryRegion L R) := by
  unfold entryRegion
  measurability

theorem geometric_entry_measure_positive {θ η α γ κ ρ ε L R h t : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t) (hsmall : (R+6)*h ≤ 1)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) (μ : Measure (V × V)) (hμ : 0 < μ (entryRegion L R)) :
    0 < ∫⁻ p, (∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent
      (beamCoefficients hθ hα hγ η 1) (t+h) C)^3) (h,p)) ∂μ := by
  have hm : Measurable (fun p : V × V => ∫⁻ q, entryTerminal C κ ρ q
      ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1) (t+h) C)^3) (h,p)) :=
    (entryTerminal_measurable C κ ρ).lintegral_kernel.comp
      (measurable_const.prodMk measurable_id)
  apply (lintegral_pos_iff_support hm).mpr
  apply hμ.trans_le (measure_mono ?_)
  intro p hp
  exact ne_of_gt (geometric_beam_entry_positive hθ hη hα hγ hαε hε0 hε hκ0 hκ hρ hερ
    hh hL hR ht hsmall p.1 p.2 hp.1 hp.2 hA C)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Changing the cold density scales each physical gain intensity -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamDensity_mul_unit (θ η α γ r σ : ℝ) (p : ℝ × V) :
    beamDensity θ η α γ r σ p = r*beamDensity θ η α γ 1 σ p := by
  unfold beamDensity
  ring

theorem beam_gain_rate_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η : ℝ) (m : HistoryMark) (hm : m ≠ 0)
    (p : ℝ × V) (v : V) :
    mediumMarkedRate (beamCoefficients hθ hα hγ η r) m (p,v) =
      ENNReal.ofReal r * mediumMarkedRate (beamCoefficients hθ hα hγ η 1) m (p,v) := by
  fin_cases m
  · exact False.elim (hm rfl)
  · change ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ r 1 p*
        ‖v-beamVelocity θ η α γ 1 p‖) =
      ENNReal.ofReal r * ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ 1 1 p*
        ‖v-beamVelocity θ η α γ 1 p‖)
    rw [beamDensity_mul_unit,show 4*Real.pi*(r*beamDensity θ η α γ 1 1 p)*
      ‖v-beamVelocity θ η α γ 1 p‖ = r*(4*Real.pi*beamDensity θ η α γ 1 1 p*
        ‖v-beamVelocity θ η α γ 1 p‖) by ring,ENNReal.ofReal_mul hr]
  · change ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ r (-1) p*
        ‖v-beamVelocity θ η α γ (-1) p‖) =
      ENNReal.ofReal r * ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ 1 (-1) p*
        ‖v-beamVelocity θ η α γ (-1) p‖)
    rw [beamDensity_mul_unit,show 4*Real.pi*(r*beamDensity θ η α γ 1 (-1) p)*
      ‖v-beamVelocity θ η α γ (-1) p‖ = r*(4*Real.pi*beamDensity θ η α γ 1 (-1) p*
        ‖v-beamVelocity θ η α γ (-1) p‖) by ring,ENNReal.ofReal_mul hr]

theorem beam_marked_collision_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (m : HistoryMark) (hm : m ≠ 0)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedCollision (beamCoefficients hθ hα hγ η r) endTime m p) =
      ENNReal.ofReal r * ∫⁻ q, F q ∂physicalMarkedCollision
        (beamCoefficients hθ hα hγ η 1) endTime m p := by
  rw [physicalMarkedCollision_lintegral _ _ _ _ hF,
    physicalMarkedCollision_lintegral _ _ _ _ hF,beam_gain_rate_scaling hθ hα hγ hr η m hm]
  exact mul_assoc _ _ _

theorem beam_collision_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalBeamCollision (beamCoefficients hθ hα hγ η r) endTime p) =
      ENNReal.ofReal r * ∫⁻ q, F q ∂physicalBeamCollision
        (beamCoefficients hθ hα hγ η 1) endTime p := by
  rw [physicalBeamCollision_lintegral,physicalBeamCollision_lintegral,
    beam_marked_collision_scaling hθ hα hγ hr η endTime 1 (by decide) p hF,
    beam_marked_collision_scaling hθ hα hγ hr η endTime 2 (by decide) p hF,mul_add]

theorem beam_event_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (C : ℝ≥0) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C p) =
      ENNReal.ofReal r * ∫⁻ q, F q ∂physicalBeamEvent
        (beamCoefficients hθ hα hγ η 1) endTime C p := by
  rw [physicalBeamEvent,physicalBeamEvent,Kernel.lintegral_comp _ _ _ hF,
    Kernel.lintegral_comp _ _ _ hF]
  simp_rw [beam_collision_scaling hθ hα hγ hr η endTime _ hF]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The actual beam representation holds almost everywhere along characteristics -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem active_ae_velocity {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ x : Velocity ∂volume, 0 < ‖transverse x‖ →
      Real.exp η*l < ‖transverse x‖ → active θ η l (transverse x) := by
  have h := (MeasureTheory.QuasiMeasurePreserving.snd
    split_measurePreserving.quasiMeasurePreserving).ae (active_ae_above_cutoff hθ hη l)
  simpa only [split_apply] using h

theorem active_ae_characteristic {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ z : CharacteristicPhase ∂volume,
      0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      Real.exp η*l < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      active θ η l (transverse (z.2.1+z.1 • z.2.2)) := by
  have ht : ∀ᵐ p : ℝ × Velocity ∂volume,
      0 < ‖transverse p.2‖ → Real.exp η*l < ‖transverse p.2‖ →
      active θ η l (transverse p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae
      (active_ae_velocity hθ hη l)
  have hk : ∀ᵐ p : Published.KineticPhase ∂volume,
      0 < ‖transverse p.1.2‖ → Real.exp η*l < ‖transverse p.1.2‖ →
      active θ η l (transverse p.1.2) :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae ht
  exact (characteristic_measurePreserving volume).quasiMeasurePreserving.ae hk

theorem background_eq_beamMeasure_ae_characteristic {θ K α γ r η : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ z : CharacteristicPhase ∂volume, 0 ≤ z.1 →
      0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      Real.exp η*l < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      background θ η l K α γ z.1
        (transverse (z.2.1+z.1 • z.2.2),axial (z.2.1+z.1 • z.2.2)) =
      ENNReal.ofReal (K/(4*r)) • ReferenceGeometry.beamMeasure
        (beamCoefficients hθ hα hγ η r) (z.1,z.2.1+z.1 • z.2.2) := by
  filter_upwards [active_ae_characteristic hθ hη l] with z hz ht hp hc
  exact background_eq_beamMeasure hθ hK hα hγ hr ht η l _ (hz hp hc)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A finite physical gain history has one density factor per collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beam_history_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (C : ℝ≥0) (n : ℕ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C)^n) p) =
      (ENNReal.ofReal r)^n * ∫⁻ q, F q
        ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1) endTime C)^n) p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    change (∫⁻ q, F q ∂(((physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C)^n) ∘ₖ
      physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C) p) =
      (ENNReal.ofReal r)^(n+1) * ∫⁻ q, F q
        ∂(((physicalBeamEvent (beamCoefficients hθ hα hγ η 1) endTime C)^n) ∘ₖ
          physicalBeamEvent (beamCoefficients hθ hα hγ η 1) endTime C) p
    rw [Kernel.lintegral_comp _ _ _ hF,Kernel.lintegral_comp _ _ _ hF]
    simp_rw [ih]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      beam_event_scaling hθ hα hγ hr η endTime C p hF.lintegral_kernel,pow_succ]
    exact (mul_assoc _ _ _).symm

theorem geometric_density_entry_positive {θ η α γ κ ρ ε L R h t r : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t) (hsmall : (R+6)*h ≤ 1)
    (x v : V) (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η r)
      (t+h) C)^3) (h,(x,v)) := by
  rw [beam_history_scaling hθ hα hγ hr.le η (t+h) C 3 _ (entryTerminal_measurable C κ ρ)]
  apply pos_iff_ne_zero.mpr
  exact mul_ne_zero (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr)))
    (ne_of_gt (geometric_beam_entry_positive hθ hη hα hγ hαε hε0 hε hκ0 hκ hρ hερ
      hh hL hR ht hsmall x v hxr hv hA C))

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
