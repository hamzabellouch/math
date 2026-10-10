import OAI.Analysis.IrrationalRotation.Analysis.MultiplicationPurePoint
import OAI.Analysis.IrrationalRotation.Operators.JointEigenspaceAlgebra
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal

namespace OAI

open MeasureTheory Filter Set
open scoped Pointwise

namespace Invariant233.RegularPolarAtomicity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem isSelfAdjoint_of_real_diagonal
    {ι : Type*} [Countable ι] (f : ι → X → ℝ)
    (T : Lp (lp (fun _ : ι => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ι => ℂ) 2) 2 μ)
    (hT : ∀ (v : Lp (lp (fun _ : ι => ℂ) 2) 2 μ) i,
      ∀ᵐ x ∂μ, T v x i = (f i x : ℂ) * v x i) :
    IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  change inner ℂ (T v) w = inner ℂ v (T w)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hv : ∀ᵐ x ∂μ, ∀ i, T v x i = (f i x : ℂ) * v x i := ae_all_iff.2 (hT v)
  have hw : ∀ᵐ x ∂μ, ∀ i, T w x i = (f i x : ℂ) * w x i := ae_all_iff.2 (hT w)
  filter_upwards [hv, hw] with x hxv hxw
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [hxv i, hxw i]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem finite_orbit_family_atomic_bicommutant
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℝ) (hf : Measurable f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (T : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T j v x k = (f (σ (k - n j) x) : ℂ) * v x k)
    {q : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ}
    (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hqmem : q ∈ Set.centralizer (Set.centralizer (Set.range T))) :
    ∃ p : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
        Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ,
      IsStarProjection p ∧ p ≠ 0 ∧
      p ∈ Set.centralizer (Set.centralizer (Set.range T)) ∧ p ≤ q ∧
      ∀ r : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
          Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ,
        IsStarProjection r →
        r ∈ Set.centralizer (Set.centralizer (Set.range T)) →
        r ≤ p → r = 0 ∨ r = p := by
  obtain ⟨C, _, hdense⟩ :=
    MultiplicationPurePoint.finite_orbit_family_dense_jointEigenspaces_real
      n σ hσ f hf hcount T hT
  have hself : ∀ j, IsSelfAdjoint (T j) := fun j =>
    isSelfAdjoint_of_real_diagonal (fun k x => f (σ (k - n j) x)) (T j) (hT j)
  exact JointEigenspaceAlgebra.atomic_bicommutant_of_dense_joint_eigenspaces
    T hself (fun y : C => y.val) hdense hq hq0 hqmem

theorem isAtomicVonNeumannGenerated_of_dense_jointEigenspaces
    {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : J → I → ℝ)
    (hdense : (⨆ j, ⨅ i,
      Module.End.eigenspace (A i).toLinearMap (eig j i : ℂ)).topologicalClosure = ⊤) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range A)) := by
  have hstar : star (Set.range A) ⊆ Set.range A := by
    intro B hB
    have hB' : star B ∈ Set.range A := hB
    obtain ⟨i, hi⟩ := hB'
    refine ⟨i, ?_⟩
    simpa only [(hA i).star_eq, star_star] using congrArg star hi
  have hcarrier : (vonNeumannGenerated (Set.range A) : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (Set.range A)) := by
    rw [coe_vonNeumannGenerated, Set.union_eq_left.2 hstar]
  intro p hpmem hp hp0
  have hpmem' : p ∈ Set.centralizer (Set.centralizer (Set.range A)) := by
    rwa [← hcarrier]
  obtain ⟨q, hq, hq0, hqmem, hqle, hqmin⟩ :=
    JointEigenspaceAlgebra.atomic_bicommutant_of_dense_joint_eigenspaces
      A hA eig hdense hp hp0 hpmem'
  refine ⟨q, ⟨?_, hq, hq0, ?_⟩, (hq.le_iff_mul_eq_left hp).1 hqle⟩
  · change q ∈ (vonNeumannGenerated (Set.range A) : Set (H →L[ℂ] H))
    rwa [hcarrier]
  · intro r hrmem hr hrq
    have hrmem' : r ∈ Set.centralizer (Set.centralizer (Set.range A)) := by
      rwa [← hcarrier]
    exact hqmin r hr hrmem' ((hr.le_iff_mul_eq_left hq).2 hrq)

theorem finite_orbit_family_isAtomicVonNeumannGenerated
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℝ) (hf : Measurable f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (T : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T j v x k = (f (σ (k - n j) x) : ℂ) * v x k) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range T)) := by
  obtain ⟨C, _, hdense⟩ :=
    MultiplicationPurePoint.finite_orbit_family_dense_jointEigenspaces_real
      n σ hσ f hf hcount T hT
  have hself : ∀ j, IsSelfAdjoint (T j) := fun j =>
    isSelfAdjoint_of_real_diagonal (fun k x => f (σ (k - n j) x)) (T j) (hT j)
  exact isAtomicVonNeumannGenerated_of_dense_jointEigenspaces
    T hself (fun y : C => y.val) hdense

theorem finite_orbit_fieldDiagonal_isAtomic
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℝ) (hf : Measurable f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (a : J → X → WeightedShift.Weight) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (ha : ∀ j x, ‖a j x‖ ≤ C j)
    (hm : ∀ j k, AEStronglyMeasurable (fun x => a j x k) μ)
    (heq : ∀ j, ∀ᵐ x ∂μ, ∀ k,
      a j x k = (f (σ (k - n j) x) : ℂ)) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range (fun j =>
      WeightedShift.fieldDiagonal (a j) (C j) (hC j) (ha j) (hm j)))) := by
  apply finite_orbit_family_isAtomicVonNeumannGenerated n σ hσ f hf hcount
  intro j v k
  have hfield : WeightedShift.fieldDiagonal (a j) (C j) (hC j) (ha j) (hm j) v =ᵐ[μ]
      fun x => WeightedShift.diagonal (a j x) (v x) :=
    WeightedShift.fieldDiagonalVec_ae (a j) (C j) (hC j) (ha j) (hm j) v
  filter_upwards [hfield, heq j] with x hx hax
  have hcoord :
      WeightedShift.fieldDiagonal (a j) (C j) (hC j) (ha j) (hm j) v x k =
        a j x k * v x k := congrArg (fun u : WeightedShift.Hilbert => u k) hx
  rw [hcoord, hax k]

end Invariant233.RegularPolarAtomicity

end OAI
