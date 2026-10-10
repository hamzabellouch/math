import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanPrefixes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanBoxAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectPrefixTuples
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceFiniteSubexponential

namespace OAI

/-! # Controlled transition lifts give compatible lifts of target tuples

The previous Cartan prefixes act on the nilpotent transitions. Their
logarithmic size remains subexponential, and their height tends to zero on
the scale, so these actions preserve each specified template box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

/-- Single-transition decompositions determine compatible tuple lifts. No
compatibility of independently chosen decompositions is assumed. -/
theorem exists_sequence_accumulated_tuple_lifts
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (h : ℕ) (E : Fin h → Set W) (β : Fin h → M.Bases)
    (hEc : ∀ i, IsCompact (E i)) (hEn : ∀ i, (E i).Nonempty)
    (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (E i)) (β i).val)
    (scale RN RD η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRN0 : ∀ n, 0 ≤ RN n) (hRD0 : ∀ n, 0 ≤ RD n)
    (hη0 : ∀ n, 0 ≤ η n) (hRN : HasSubexponentialUpperBoundSeq scale RN)
    (hRD : HasSubexponentialUpperBoundSeq scale RD) (hη : Tendsto η atTop (𝓝 0))
    (s : ℕ → Set (Fin h → G))
    (u : ℕ → (Fin h → G) → ℕ → F.N.carrier)
    (d : ℕ → (Fin h → G) → ℕ → F.D.carrier)
    (hprod : ∀ n x, x ∈ s n → ∀ j < h,
      F.inclusionN (u n x j) * F.inclusionD (d n x j) =
        (basedTuplePosition x j)⁻¹ * basedTuplePosition x (j + 1))
    (hu : ∀ n x, x ∈ s n → ∀ i : Fin h,
      u n x i.val ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (E i) (β i) (scale n) (RN n))
    (hd : ∀ n x, x ∈ s n → ∀ j < h,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d n x j))‖ ≤ RD n)
    (hhgt : ∀ n x, x ∈ s n → ∀ j < h,
      ‖(π (F.inclusionD (d n x j))).toAdd‖ ≤ η n * scale n) :
    ∃ (RH R : ℕ → ℝ)
      (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier)),
      (∀ n, 0 ≤ RH n) ∧ (∀ n, 0 ≤ R n) ∧
      HasSubexponentialUpperBoundSeq scale RH ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n x, x ∈ s n →
        (∀ i, F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i) ∧
        (∀ i, ‖(finBasis ℝ H).equivFun
          (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n) ∧
        (∀ i, ‖eW (heightProjection T.character
          (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) :
            GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ((h : ℝ) * η n) * scale n) ∧
        (∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n)) := by
  obtain ⟨RH, hRH0, hRH, hprefix⟩ := exists_sequence_cartan_prefix_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD h scale RD hs hRD0 hRD
  have hη' : Tendsto (fun n => (h : ℝ) * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hη
  have hη'0 : ∀ n, 0 ≤ (h : ℝ) * η n := fun n => mul_nonneg (Nat.cast_nonneg _) (hη0 n)
  have haction := fun i => M.exists_sequence_small_height_box_action T hunimod eW
    F.N.equiv F.ExpN F.isExpN hbijN dynkinN b₀ (hEc i) (hEn i) (β i) (hβ i)
    scale RH RN (fun n => (h : ℝ) * η n) hs hscale hRH0 hRN0 hη'0 hRH hRN hη'
  choose R₀ hR₀0 hR₀ hR₀bound using haction
  obtain ⟨R, hR0, hR, hRle⟩ := finite_subexponential_envelope hs R₀ hR₀0 hR₀
  let p := fun n x =>
    (prefixCoordinateEquiv h (fun i => F.action (wordPrefix (d n x) i.val) (u n x i.val)),
      fun i : Fin h => wordPrefix (d n x) (i.val + 1))
  have hlog (n : ℕ) (x : Fin h → G) (hx : x ∈ s n) (j : ℕ) (hj : j ≤ h) :
      ‖(finBasis ℝ H).equivFun
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix (d n x) j))‖ ≤ RH n :=
    hprefix n (d n x) (hd n x hx) j hj
  have hheight (n : ℕ) (x : Fin h → G) (hx : x ∈ s n) (j : ℕ) (hj : j ≤ h) :
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix (d n x) j) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ((h : ℝ) * η n) * scale n := by
    rw [← F.inclusionD_height T eW π hπExp hbijD]
    have hb := wordPrefix_height_bound (π.comp F.inclusionD) (d n x) (η n * scale n) j
      (fun k hk => hhgt n x hx k (hk.trans_le hj))
    apply hb.trans
    have hj' : (j : ℝ) ≤ h := by exact_mod_cast hj
    calc
      (j : ℝ) * (η n * scale n) ≤ (h : ℝ) * (η n * scale n) :=
        mul_le_mul_of_nonneg_right hj' (mul_nonneg (hη0 n) (hscale n).le)
      _ = ((h : ℝ) * η n) * scale n := (mul_assoc _ _ _).symm
  refine ⟨RH, R, p, hRH0, hR0, hRH, hR, ?_⟩
  intro n x hx
  refine ⟨tuple_accumulated_lifts_eq F.inclusionN F.inclusionD F.action F.conjugation
    x (u n x) (d n x) (hprod n x hx), ?_, ?_, ?_⟩
  · exact fun i => hlog n x hx (i.val + 1) i.isLt
  · exact fun i => hheight n x hx (i.val + 1) i.isLt
  intro i
  change (prefixCoordinateEquiv h).symm
    (prefixCoordinateEquiv h (fun j => F.action (wordPrefix (d n x) j.val) (u n x j.val))) i ∈ _
  rw [MeasurableEquiv.symm_apply_apply,
    cartan_action_eq_adjoint_of_published_realization T M F hExpG realize hbijN hbijD dynkinN]
  obtain ⟨v, hv, hb⟩ := hR₀bound i n
    (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix (d n x) i.val)) (u n x i.val)
    (hlog n x hx i.val i.isLt.le) (hheight n x hx i.val i.isLt.le) (hu n x hx i)
  exact ⟨v, hv, hb.trans (hRle i n)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
