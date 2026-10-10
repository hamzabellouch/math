import OAI.Geometry.SurfaceImmersion.Geometry.ConjugatedMultilinearBounds

namespace OAI

/-! Finite polynomial perturbations have one fixed short-scale exponent. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

variable {n : ℕ}

def order (P : Fin n → Expression) : ℕ := Finset.univ.sup (fun l => (P l).order)
def loss (P : Fin n → Expression) : ℕ := Finset.univ.sup (fun l => (P l).loss + 6)

def conjugated (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Fin 3 → Base → ℝ) (H : DirectionFields) (τ : ℝ) (i : Fin 3) (z : Base × ℝ) : ℂ :=
  ∑ l, ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i z

lemma conjugatedVariation_smooth {U : Set Base} {O : Set LowJet} {e : Expression}
    (he : e.SmoothCoeffs O) {G : Base → Space} {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (hO : IsOpen O)
    (hQ : Set.MapsTo (lowJet G) U O) (τ : ℝ) (i : Fin 3) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => conjugatedVariation e G φ H τ i (p, t)) U := by
  have h := evalComplex_parameter_smooth hG hQ
    (fun j w a => (amplitudeData_smooth hG hφ hH τ j w a).contDiffOn)
    (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
  convert h using 1
  funext p
  exact conjugatedVariation_eq e G hφ hH τ i (p, t)

/-- The perturbation parameter enters linearly in the bound, and the single
short-scale loss works at every requested output order. -/
theorem compact_conjugated_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B Q : ℝ) (hB : 1 ≤ B) (hQ : 0 ≤ Q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ ε : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ j, WeightedBound U s (m + order P) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + order P) Q
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * ε * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ loss P) (fun p => conjugated P ε G φ H τ i (p, t)) := by
  classical
  have hex := fun l => compact_conjugated_multilinear_bound hU hO hK hKO (P l) (hP l) m B Q hB hQ
  choose D hD hb using hex
  refine ⟨∑ l, D l, Finset.sum_nonneg (fun l _ => hD l), ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let W := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 ≤ W := by
    have h₀ := (hC 0).le
    have h₁ := (hC 1).le
    have h₂ := (hC 2).le
    dsimp only [W]
    split_ifs <;> positivity
  have hval (l : Fin n) : WeightedBound U s m (D l * ε * W / τ ^ loss P)
      (fun p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t)) := by
    have hl : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hh := hb l G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK
      (hGb.mono_order (Nat.add_le_add_left hl m))
      (fun j => (hHb j).mono_order (Nat.add_le_add_left hl m))
      (fun j v => (hφb j v).mono_order (Nat.add_le_add_left hl m)) t ht i
    have hsmooth := conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t
    have hh' : WeightedBound U s m (D l * W / τ ^ loss P)
        (fun p => conjugatedVariation (P l) G φ H τ i (p, t)) :=
      hh.mono_const (div_le_div_of_nonneg_left (mul_nonneg (hD l) hW) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
          (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))))
    have hscaled := hh'.const_smul hU.uniqueDiffOn hsmooth (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have heps : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l * W / τ ^ loss P) :=
        mul_le_mul_of_nonneg_right heps
          (div_nonneg (mul_nonneg (hD l) hW) (pow_nonneg hτ.le _))
      _ = _ := by ring
  have hsum := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l * ε * W / τ ^ loss P)
    (fun l p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t))
    (fun l _ => (conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t).const_smul _) (fun l _ => hval l)
  simpa only [conjugated, ← Finset.sum_div, ← Finset.sum_mul, W] using hsum

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
