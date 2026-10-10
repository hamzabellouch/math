import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProperCocompactMetric

namespace OAI

/-!
# Composing the metric comparisons in a Lie-model reduction

The proper cocompact homomorphism reduction has arrows in both directions.
We keep actual coarse inverse maps and their affine bounds, so that the
three-arrow zigzag can be composed without assuming a recognition result.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Actual coarse inverse maps with affine metric bounds in both directions. -/
structure MetricQuasiEquivalence (X Y : Type*) [PseudoMetricSpace X] [PseudoMetricSpace Y] where
  toFun : X → Y
  invFun : Y → X
  toFun_control : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ x y, dist (toFun x) (toFun y) ≤ K * dist x y + C
  invFun_control : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ x y, dist (invFun x) (invFun y) ≤ K * dist x y + C
  left_close : ∃ E : ℝ, 0 ≤ E ∧ ∀ x, dist x (invFun (toFun x)) ≤ E
  right_close : ∃ E : ℝ, 0 ≤ E ∧ ∀ y, dist y (toFun (invFun y)) ≤ E

namespace MetricQuasiEquivalence

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- Reverse a comparison using its specified coarse inverse. -/
def symm (e : MetricQuasiEquivalence X Y) : MetricQuasiEquivalence Y X where
  toFun := e.invFun
  invFun := e.toFun
  toFun_control := e.invFun_control
  invFun_control := e.toFun_control
  left_close := e.right_close
  right_close := e.left_close

/-- Compose actual comparisons, including explicit bounds for the errors
of their composite inverse maps. -/
def trans (e : MetricQuasiEquivalence X Y) (e' : MetricQuasiEquivalence Y Z) :
    MetricQuasiEquivalence X Z where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  toFun_control := by
    obtain ⟨K, C, hK, hC, hf⟩ := e.toFun_control
    obtain ⟨K', C', hK', hC', hf'⟩ := e'.toFun_control
    refine ⟨K' * K, K' * C + C', mul_nonneg hK' hK,
      add_nonneg (mul_nonneg hK' hC) hC', fun x y => ?_⟩
    calc
      dist (e'.toFun (e.toFun x)) (e'.toFun (e.toFun y))
          ≤ K' * dist (e.toFun x) (e.toFun y) + C' := hf' _ _
      _ ≤ K' * (K * dist x y + C) + C' := by gcongr; exact hf x y
      _ = (K' * K) * dist x y + (K' * C + C') := by ring
  invFun_control := by
    obtain ⟨K, C, hK, hC, hf⟩ := e.invFun_control
    obtain ⟨K', C', hK', hC', hf'⟩ := e'.invFun_control
    refine ⟨K * K', K * C' + C, mul_nonneg hK hK',
      add_nonneg (mul_nonneg hK hC') hC, fun x y => ?_⟩
    calc
      dist (e.invFun (e'.invFun x)) (e.invFun (e'.invFun y))
          ≤ K * dist (e'.invFun x) (e'.invFun y) + C := hf _ _
      _ ≤ K * (K' * dist x y + C') + C := by gcongr; exact hf' x y
      _ = (K * K') * dist x y + (K * C' + C) := by ring
  left_close := by
    obtain ⟨E, hE, he⟩ := e.left_close
    obtain ⟨E', hE', he'⟩ := e'.left_close
    obtain ⟨K, C, hK, hC, hf⟩ := e.invFun_control
    refine ⟨E + (K * E' + C), add_nonneg hE (add_nonneg (mul_nonneg hK hE') hC),
      fun x => ?_⟩
    calc
      dist x (e.invFun (e'.invFun (e'.toFun (e.toFun x))))
          ≤ dist x (e.invFun (e.toFun x)) +
              dist (e.invFun (e.toFun x))
                (e.invFun (e'.invFun (e'.toFun (e.toFun x)))) := dist_triangle _ _ _
      _ ≤ E + (K * E' + C) := by
        exact add_le_add (he x) ((hf _ _).trans
          (add_le_add (mul_le_mul_of_nonneg_left (he' (e.toFun x)) hK) le_rfl))
  right_close := by
    obtain ⟨E, hE, he⟩ := e.right_close
    obtain ⟨E', hE', he'⟩ := e'.right_close
    obtain ⟨K, C, hK, hC, hf⟩ := e'.toFun_control
    refine ⟨E' + (K * E + C), add_nonneg hE' (add_nonneg (mul_nonneg hK hE) hC),
      fun y => ?_⟩
    calc
      dist y (e'.toFun (e.toFun (e.invFun (e'.invFun y))))
          ≤ dist y (e'.toFun (e'.invFun y)) +
              dist (e'.toFun (e'.invFun y))
                (e'.toFun (e.toFun (e.invFun (e'.invFun y)))) := dist_triangle _ _ _
      _ ≤ E' + (K * E + C) := by
        exact add_le_add (he' y) ((hf _ _).trans
          (add_le_add (mul_le_mul_of_nonneg_left (he (e'.invFun y)) hK) le_rfl))

/-- Choose a coarse inverse from the coarse-surjectivity part of a
quasi-isometry, and prove its affine bound using the lower inequality. -/
def ofQuasiIsometry (f : X → Y) {K C K' C' E : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hC' : 0 ≤ C') (hE : 0 ≤ E)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hsurj : ∀ y, ∃ x, dist y (f x) ≤ E) : MetricQuasiEquivalence X Y := by
  choose r hr using hsurj
  refine ⟨f, r, ⟨K, C, hK, hC, hupper⟩, ?_, ?_, ⟨E, hE, hr⟩⟩
  · refine ⟨K', K' * (E + E) + C', hK',
      add_nonneg (mul_nonneg hK' (add_nonneg hE hE)) hC', fun x y => ?_⟩
    have hd : dist (f (r x)) (f (r y)) ≤ dist x y + (E + E) := by
      calc
        dist (f (r x)) (f (r y)) ≤
            dist (f (r x)) x + dist x y + dist y (f (r y)) := dist_triangle4 _ _ _ _
        _ ≤ E + dist x y + E := by
          exact add_le_add (add_le_add ((dist_comm _ _).trans_le (hr x)) le_rfl) (hr y)
        _ = dist x y + (E + E) := by ring
    calc
      dist (r x) (r y) ≤ K' * dist (f (r x)) (f (r y)) + C' := hlower _ _
      _ ≤ K' * (dist x y + (E + E)) + C' := by gcongr
      _ = K' * dist x y + (K' * (E + E) + C') := by ring
  · refine ⟨K' * E + C', add_nonneg (mul_nonneg hK' hE) hC', fun x => ?_⟩
    exact (hlower x (r (f x))).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hr (f x)) hK') le_rfl)

/-- Recover the usual inequalities from actual coarse inverse maps. -/
theorem quasiIsometry_toFun (e : MetricQuasiEquivalence X Y) :
    ∃ K C K' C' E : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ K' ∧ 0 ≤ C' ∧ 0 ≤ E ∧
      (∀ x y, dist (e.toFun x) (e.toFun y) ≤ K * dist x y + C) ∧
      (∀ x y, dist x y ≤ K' * dist (e.toFun x) (e.toFun y) + C') ∧
      (∀ y, ∃ x, dist y (e.toFun x) ≤ E) := by
  obtain ⟨K, C, hK, hC, hf⟩ := e.toFun_control
  obtain ⟨K', C', hK', hC', hr⟩ := e.invFun_control
  obtain ⟨L, hL, hl⟩ := e.left_close
  obtain ⟨E, hE, he⟩ := e.right_close
  refine ⟨K, C, K', C' + (L + L), E, hK, hC, hK',
    add_nonneg hC' (add_nonneg hL hL), hE, hf, ?_, fun y => ⟨e.invFun y, he y⟩⟩
  intro x y
  calc
    dist x y ≤ dist x (e.invFun (e.toFun x)) +
        dist (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) +
          dist (e.invFun (e.toFun y)) y := dist_triangle4 _ _ _ _
    _ ≤ L + (K' * dist (e.toFun x) (e.toFun y) + C') + L := by
      exact add_le_add (add_le_add (hl x) (hr _ _)) ((dist_comm _ _).trans_le (hl y))
    _ = K' * dist (e.toFun x) (e.toFun y) + (C' + (L + L)) := by ring

end MetricQuasiEquivalence

/-- Coarse inverse maps for a proper cocompact homomorphism, suitable for
composition along the model zigzag. -/
theorem nonempty_metricQuasiEquivalence_of_proper_cocompact_hom
    {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
    [IsIsometricSMul G G] [IsIsometricSMul H H] [ProperSpace G] [ProperSpace H]
    (CG : LinearMetricChains G) (CH : LinearMetricChains H)
    (f : G →* H) (hf : Continuous f) (hproper : IsProperMap f)
    (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    Nonempty (MetricQuasiEquivalence G H) := by
  obtain ⟨A, B, A', B', E, hA, hB, hA', hB', hE, hup, hlo, hsurj⟩ :=
    proper_cocompact_hom_quasiIsometry CG CH f hf hproper K hK hcover
  exact ⟨MetricQuasiEquivalence.ofQuasiIsometry f hA hB hA' hB' hE hup hlo hsurj⟩

end PolycyclicRecognition

end

end OAI
