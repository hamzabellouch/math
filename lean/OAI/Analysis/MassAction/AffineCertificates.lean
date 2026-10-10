import OAI.Analysis.MassAction.FixedMinimum

namespace OAI

/-! Certificates for the dimension induction and interval gluing.

In particular a local certificate retains a strictly stronger offset decay
exponent. Merely retaining `o(h^t)` would not suffice for interval gluing.
-/

noncomputable section
open Filter Topology

namespace Problem326.Affine

/-- Sequential approximation on the whole exponent cube, allowing the
approximating sequence to lie outside the cube. -/
def SequentialApproximation {d : ℕ} (Λ : Finset (Label d))
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- The conclusion of the affine approximation lemma in one dimension `d`.
The label set and its slopes are fixed before a small parameter is chosen. -/
structure FullCertificate (d : ℕ) (a b : ℝ) (E : (Fin d → ℝ) → ℝ) where
  labels : Finset (Label d)
  nonempty : labels.Nonempty
  slopes : ∀ L ∈ labels, Cube a b L.slope
  offsets : ∀ L ∈ labels,
    L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a)
  approximation : SequentialApproximation labels a b E

/-- The output required at a fixed minimum before neighborhood extension.
`decay_gt` and `offsets` are essential data for the subsequent gluing step. -/
structure LocalCertificate (d : ℕ) (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) where
  labels : Finset (Label d)
  baseline : (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ labels
  slopes : ∀ L ∈ labels, Cube t b L.slope
  minima : ∀ L ∈ labels, HasMinimum L.slope t
  decayExponent : ℝ
  decay_gt : t < decayExponent
  offsets : ∀ L ∈ labels,
    L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ decayExponent)
  approximation : ApproximatesAtMinimum labels a b t E

lemma LocalCertificate.nonempty {d : ℕ} {a b t : ℝ}
    {E : (Fin d → ℝ) → ℝ} (C : LocalCertificate d a b t E) : C.labels.Nonempty :=
  ⟨_, C.baseline⟩

/-- The fixed-minimum singleton construction in species dimension one. -/
def localCertificate_one (a b t : ℝ) (htb : t ≤ b)
    (E : (Fin 1 → ℝ) → ℝ) (hE : 0 < E (fun _ => t)) :
    LocalCertificate 1 a b t E := by
  classical
  refine {
    labels := {⟨fun _ => t, fun _ => 0⟩}
    baseline := by simp
    slopes := ?_
    minima := ?_
    decayExponent := t + 1
    decay_gt := by linarith
    offsets := ?_
    approximation := singleton_approximates_one a b t E hE
  }
  · intro L hL
    have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
    subst L
    exact fun _ => ⟨le_rfl, htb⟩
  · intro L hL
    have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
    subst L
    exact ⟨fun _ => le_rfl, ⟨0, rfl⟩⟩
  · intro L hL
    have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
    subst L
    exact Asymptotics.isLittleO_zero _ _

/-- The fixed-minimum singleton construction at the upper corner. -/
def localCertificate_upper {d : ℕ} (hd : 0 < d) (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ) (hE : 0 < E (fun _ => b)) :
    LocalCertificate d a b b E := by
  classical
  refine {
    labels := {⟨fun _ => b, fun _ => 0⟩}
    baseline := by simp
    slopes := ?_
    minima := ?_
    decayExponent := b + 1
    decay_gt := by linarith
    offsets := ?_
    approximation := singleton_approximates_upper a b E hE
  }
  · intro L hL
    have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
    subst L
    exact fun _ => ⟨le_rfl, le_rfl⟩
  · intro L hL
    have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
    subst L
    exact ⟨fun _ => le_rfl, ⟨⟨0, hd⟩, rfl⟩⟩
  · intro L hL
    have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
    subst L
    exact Asymptotics.isLittleO_zero _ _

/-- Harmless dimension-zero base for strong induction. It is not used as a
positive-dimensional fixed-minimum family. -/
def fullCertificate_zero (a b : ℝ) (E : (Fin 0 → ℝ) → ℝ)
    (hE : ∀ r, Cube a b r → 0 < E r) : FullCertificate 0 a b E := by
  classical
  let L : Label 0 := ⟨fun _ => a, fun _ => 0⟩
  refine {
    labels := {L}
    nonempty := Finset.singleton_nonempty L
    slopes := ?_
    offsets := ?_
    approximation := ?_
  }
  · intro J hJ i
    exact Fin.elim0 i
  · intro J hJ
    have hJL : J = L := by simpa using hJ
    subst J
    exact Asymptotics.isLittleO_zero _ _
  · intro J hJ h p p₀ hh hhlim hp hp₀ ha
    have hJL : J = L := by simpa using hJ
    subst J
    have heq : p₀ = L.slope := by funext i; exact Fin.elim0 i
    rw [heq, sub_self, norm_zero]
    exact hE L.slope (fun i => Fin.elim0 i)

/-- Strong induction assembles full certificates from fixed-minimum
certificates and finite interval gluing. -/
theorem fullCertificate_of_local_and_glue
    (construct : ∀ d : ℕ, 0 < d →
      (∀ k : ℕ, k < d → ∀ a b : ℝ, ∀ E : (Fin k → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate k a b E)) →
      ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) →
        ∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E))
    (glue : ∀ d : ℕ, 0 < d → ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      (∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E)) →
      Nonempty (FullCertificate d a b E)) :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate d a b E) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro a b E hab hE
      by_cases hd : d = 0
      · subst d
        exact ⟨fullCertificate_zero a b E hE⟩
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        exact glue d hdpos a b E hab hE (construct d hdpos ih a b E hab hE)

end Problem326.Affine

end

end OAI
