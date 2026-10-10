import OAI.Analysis.KadisonKastler.InvariantOperatorMean

namespace OAI

/-! # Fixed-point algebras and the common-action gap

The fixed algebra is an actual von Neumann algebra, defined as a commutant.
The scalar invariant mean constructed in `InvariantOperatorMean` averages
ordinary unit-ball approximants into fixed-point approximants without
increasing either their norm or their error. No existence of a scalar mean
or fixed-point averaging map is postulated here.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {G H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fixed points inside `M`, expressed as the commutant of `M'` together
with the given representation. -/
def fixedPointAlgebra (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    ((M.commutant : Set (H →L[ℂ] H)) ∪ Set.range (fun g => (U g : H →L[ℂ] H)))
  centralizer_centralizer' := by
    let S : Set (H →L[ℂ] H) := (M.commutant : Set (H →L[ℂ] H)) ∪
      Set.range (fun g => (U g : H →L[ℂ] H))
    change (S ∪ star S).centralizer.centralizer.centralizer =
      (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

theorem mem_fixedPointAlgebra_iff (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    T ∈ fixedPointAlgebra U M ↔ T ∈ M ∧ ∀ g, unitaryConj (U g) T = T := by
  change T ∈ StarSubalgebra.centralizer ℂ
    ((M.commutant : Set (H →L[ℂ] H)) ∪ Set.range (fun g => (U g : H →L[ℂ] H))) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h
    constructor
    · have hM : T ∈ M.commutant.commutant :=
        VonNeumannAlgebra.mem_commutant_iff.mpr (fun S hS => (h S (Or.inl hS)).1)
      simpa only [VonNeumannAlgebra.commutant_commutant] using hM
    · intro g
      exact (commute_unitary_iff_star_right_conjugate (U g).property).mp
        (h (U g) (Or.inr ⟨g, rfl⟩)).1
  · rintro ⟨hM, hU⟩ S (hS | ⟨g, rfl⟩)
    · exact ⟨VonNeumannAlgebra.mem_commutant_iff.mp hS T hM |>.symm,
        VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hS) T hM |>.symm⟩
    · have hc (g : G) : (U g : H →L[ℂ] H) * T = T * (U g : H →L[ℂ] H) :=
        ((commute_unitary_iff_star_right_conjugate (U g).property).mpr (hU g)).eq
      refine ⟨hc g, ?_⟩
      have he : (U (g⁻¹) : H →L[ℂ] H) = star (U g : H →L[ℂ] H) := by
        rw [map_inv]
        rfl
      simpa only [he] using hc (g⁻¹)

theorem fixedPointAlgebra_le (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : fixedPointAlgebra U M ≤ M :=
  fun T hT => ((mem_fixedPointAlgebra_iff U M T).mp hT).1

namespace ScalarInvariantMean

variable [TopologicalSpace G] [DiscreteTopology G]
variable (m : ScalarInvariantMean G) (U : G →* unitary (H →L[ℂ] H))

/-- Actual averaging takes invariant-algebra elements to its fixed algebra. -/
theorem averageConjugation_mem_fixed (M : VonNeumannAlgebra H)
    (hM : ∀ g T, T ∈ M → unitaryConj (U g) T ∈ M)
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    m.averageConjugation U T ∈ fixedPointAlgebra U M := by
  rw [mem_fixedPointAlgebra_iff]
  exact ⟨m.averageConjugation_mem U M T (fun g => hM g T hT),
    m.averageConjugation_invariant U T⟩

theorem averageConjugation_fixed_on_fixed (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hT : T ∈ fixedPointAlgebra U M) :
    m.averageConjugation U T = T :=
  m.averageConjugation_fixed U T ((mem_fixedPointAlgebra_iff U M T).mp hT).2

theorem averageConjugation_norm_le (T : H →L[ℂ] H) :
    ‖m.averageConjugation U T‖ ≤ ‖T‖ :=
  unital_completelyPositive_norm_le _ (m.averageConjugation_one U) T

include m in
theorem exists_fixedPoint_unitBall_approx
    (M N : VonNeumannAlgebra H)
    (hN : ∀ g T, T ∈ N → unitaryConj (U g) T ∈ N)
    {r : ℝ} (hr : kkDistance M N < r)
    (T : H →L[ℂ] H) (hT : T ∈ unitBall (fixedPointAlgebra U M)) :
    ∃ S ∈ unitBall (fixedPointAlgebra U N), ‖T - S‖ < r := by
  obtain ⟨S, hS, hTS⟩ := exists_unitBall_approx
    (M := M) (N := N) ⟨fixedPointAlgebra_le U M hT.1, hT.2⟩ hr
  refine ⟨m.averageConjugation U S,
    ⟨m.averageConjugation_mem_fixed U N hN hS.1,
      (m.averageConjugation_norm_le U S).trans hS.2⟩, ?_⟩
  have hfix := m.averageConjugation_fixed_on_fixed U M hT.1
  calc
    ‖T - m.averageConjugation U S‖ =
        ‖m.averageConjugation U T - m.averageConjugation U S‖ := by rw [hfix]
    _ = ‖m.averageConjugation U (T - S)‖ := by rw [map_sub]
    _ ≤ ‖T - S‖ := m.averageConjugation_norm_le U _
    _ < r := hTS

include m in
/-- A common unitary action cannot increase the ordinary Kadison--Kastler
gap upon passage to fixed points. -/
theorem kkDistance_fixedPointAlgebra_le
    (M N : VonNeumannAlgebra H)
    (hM : ∀ g T, T ∈ M → unitaryConj (U g) T ∈ M)
    (hN : ∀ g T, T ∈ N → unitaryConj (U g) T ∈ N) :
    kkDistance (fixedPointAlgebra U M) (fixedPointAlgebra U N) ≤ kkDistance M N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Metric.hausdorffDist_le_of_mem_dist
    (add_nonneg (kkDistance_nonneg M N) hε.le)
  · intro T hT
    obtain ⟨S, hS, hTS⟩ := m.exists_fixedPoint_unitBall_approx U M N hN
      (lt_add_of_pos_right _ hε) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS.le⟩
  · intro S hS
    obtain ⟨T, hT, hST⟩ := m.exists_fixedPoint_unitBall_approx U N M hM
      (by rw [kkDistance_comm]; exact lt_add_of_pos_right _ hε) S hS
    exact ⟨T, hT, by simpa only [dist_eq_norm] using hST.le⟩

end ScalarInvariantMean

end

end KadisonKastler

end OAI
