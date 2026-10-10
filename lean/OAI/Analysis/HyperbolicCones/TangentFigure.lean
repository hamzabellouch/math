import OAI.Analysis.HyperbolicCones.ConstantRank
import OAI.Analysis.HyperbolicCones.TangentExpansion

namespace OAI

noncomputable section

open scoped ContDiff Matrix.Norms.L2Operator
open Set ContinuousLinearMap

universe u v

namespace Paper256

theorem exists_smooth_constant_rank_extension
    {W : Type u} {F : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (S : Set W) (hne : S.Nonempty) (A : W → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hs : ∀ u ∈ S, IsSelfAdjoint (A u)) :
    ∃ v ∈ S, ∃ (U : Set W) (P : W → F →L[ℝ] F), IsOpen U ∧ v ∈ U ∧
      ContDiffOn ℝ ∞ P U ∧
      (∀ u ∈ S, Module.finrank ℝ (A u).range ≤ Module.finrank ℝ (A v).range) ∧
      (∀ u ∈ U, u ∈ S → Module.finrank ℝ (A u).range = Module.finrank ℝ (A v).range) ∧
      ∀ u ∈ U, u ∈ S → P u = (A u).ker.starProjection := by
  obtain ⟨v, hv, U, hU, hvU, hmax, hrank⟩ := exists_constant_rank_neighborhood S hne A hA hs
  obtain ⟨w, hw, V, P, hV, hwV, hP, heq⟩ := exists_smooth_kernel_extension (S ∩ U)
    ⟨v, hv, hvU⟩ A hA (fun u hu => hs u hu.1)
  refine ⟨w, hw.1, U ∩ V, P, hU.inter hV, ⟨hw.2, hwV⟩,
    hP.mono (fun _ hu => hu.2), ?_, ?_, ?_⟩
  · intro u hu
    rw [hrank w hw.2 hw.1]
    exact hmax u hu
  · intro u hu hus
    rw [hrank w hw.2 hw.1]
    exact hrank u hu.1 hus
  · intro u hu hus
    exact heq u hu.2 ⟨hus, hu.1⟩

theorem tangentCurve_mem_span (v h : Vec 4) (s : ℝ) :
    tangentCurve v h s ∈ Submodule.span ℝ ({v, h} : Set (Vec 4)) := by
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem tangentCurve_zero (v h : Vec 4) : tangentCurve v h 0 = v := by
  simp [tangentCurve]

theorem kernelProjection_zero (c : ℕ) : kernelProjection (0 : Mat c ℝ) = 1 := by
  apply Matrix.toEuclideanLin.injective
  simp [kernelProjection, Matrix.toEuclideanLin, Submodule.starProjection_top]

theorem kernelProjection_eq_one_of_rank_zero {c : ℕ} (A : Mat c ℝ)
    (hA : Module.finrank ℝ (Matrix.toEuclideanLin A).range = 0) : kernelProjection A = 1 := by
  have hz : Matrix.toEuclideanLin A = 0 :=
    LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hA)
  have hzero : A = 0 := Matrix.toEuclideanLin.injective (by simpa using hz)
  rw [hzero, kernelProjection_zero]

theorem matrix_independent_spanning_columns {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ f : Fin A.rank → Fin n, Function.Injective f ∧
      LinearIndependent ℝ (fun i => A.col (f i)) ∧
      Submodule.span ℝ (Set.range (fun i => A.col (f i))) =
        Submodule.span ℝ (Set.range A.col) := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols]
  obtain ⟨v, hv, hspan, hlin⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.col)
  choose f hf using hv
  have heq : (fun i => A.col (f i)) = v := funext hf
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    apply hlin.injective
    rw [← hf i, ← hf j, hij]
  · simpa only [heq] using hlin
  · simpa only [heq] using hspan

theorem matrix_columns_independent_neighborhood
    {W : Type u} [TopologicalSpace W] {m n q : ℕ}
    (A : W → Matrix (Fin m) (Fin n) ℝ) (hA : Continuous A)
    (v : W) (f : Fin q → Fin n)
    (hf : LinearIndependent ℝ (fun i => (A v).col (f i))) :
    ∃ U : Set W, IsOpen U ∧ v ∈ U ∧
      ∀ u ∈ U, LinearIndependent ℝ (fun i => (A u).col (f i)) := by
  have hcol : Continuous (fun u => fun i : Fin q => (A u).col (f i)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (Matrix.entryLinearMap ℝ ℝ j (f i)).continuous_of_finiteDimensional.comp hA
  let U : Set W := {u | LinearIndependent ℝ (fun i => (A u).col (f i))}
  have hU : IsOpen U := isOpen_setOfPred_linearIndependent.preimage hcol
  exact ⟨U, hU, hf, fun _ hu => hu⟩

theorem matrix_columns_span_of_rank_le {m n q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (f : Fin q → Fin n)
    (hf : LinearIndependent ℝ (fun i => A.col (f i))) (hrank : A.rank ≤ q) :
    Submodule.span ℝ (Set.range (fun i => A.col (f i))) =
      Submodule.span ℝ (Set.range A.col) := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  · rw [finrank_span_eq_card hf, Fintype.card_fin, ← Matrix.rank_eq_finrank_span_cols]
    exact hrank

theorem matrix_fixed_columns_local_frame
    {W : Type u} [TopologicalSpace W] {m n : ℕ}
    (A : W → Matrix (Fin m) (Fin n) ℝ) (hA : Continuous A)
    (S : Set W) (v : W) (hmax : ∀ u ∈ S, (A u).rank ≤ (A v).rank) :
    ∃ (f : Fin (A v).rank → Fin n) (U : Set W), Function.Injective f ∧
      IsOpen U ∧ v ∈ U ∧ ∀ u ∈ U, u ∈ S →
        LinearIndependent ℝ (fun i => (A u).col (f i)) ∧
        Submodule.span ℝ (Set.range (fun i => (A u).col (f i))) =
          Submodule.span ℝ (Set.range (A u).col) := by
  obtain ⟨f, hf, hlin, _⟩ := matrix_independent_spanning_columns (A v)
  obtain ⟨U, hU, hvU, hlocal⟩ := matrix_columns_independent_neighborhood A hA v f hlin
  exact ⟨f, U, hf, hU, hvU, fun u hu hus =>
    ⟨hlocal u hu, matrix_columns_span_of_rank_le (A u) f (hlocal u hu) (hmax u hus)⟩⟩

end Paper256

end

end OAI
