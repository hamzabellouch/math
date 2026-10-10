import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedLargeOutput
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricTwoCoreUniform

namespace OAI

section

/-! # The actual selected kernel restricted to one origin and a compact scale window -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def originScaleRegion (s₀ η r δ M : ℝ) (N : ℕ) (k : Lattice) : Set Published.SpaceTime :=
  ⋃ (i : Label) (_h : i.lattice = k ∧ δ ≤ JetGeometry.jetScale s₀ η i.annulus/r ∧
    JetGeometry.jetScale s₀ η i.annulus/r ≤ M), mainCoreRegion s₀ η r N i

theorem originScaleRegion_measurable (s₀ η r δ M : ℝ) (N : ℕ) (k : Lattice) :
    MeasurableSet (originScaleRegion s₀ η r δ M N k) := by
  apply MeasurableSet.iUnion
  intro i
  exact MeasurableSet.iUnion (fun _ => measurableSet_mainCoreRegion s₀ η r N i)

def originScaleKernel (r s₀ η K α γ d₀ q δ M : ℝ) (N : ℕ) (k : Lattice) :
    Kernel Published.KineticPhase Velocity := by
  classical
  exact Kernel.piecewise ((originScaleRegion_measurable s₀ η r δ M N k).preimage measurable_fst)
    (selectedFreeKernel r s₀ η K α γ d₀ q N) 0

instance originScaleKernel_sFinite (r s₀ η K α γ d₀ q δ M : ℝ) (N : ℕ) (k : Lattice) :
    IsSFiniteKernel (originScaleKernel r s₀ η K α γ d₀ q δ M N k) := by
  unfold originScaleKernel
  infer_instance

theorem originScaleKernel_eq_copy {r s₀ η K α γ d₀ q δ M : ℝ} {N : ℕ} {k : Lattice}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {i : Label} {z : Published.KineticPhase} (hi : z.1 ∈ mainCoreRegion s₀ η r N i)
    (hk : i.lattice = k) (hlo : δ ≤ JetGeometry.jetScale s₀ η i.annulus/r)
    (hhi : JetGeometry.jetScale s₀ η i.annulus/r ≤ M) :
    originScaleKernel r s₀ η K α γ d₀ q δ M N k z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  classical
  have hz : z.1 ∈ originScaleRegion s₀ η r δ M N k :=
    mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨hk,hlo,hhi⟩,hi⟩⟩
  simp only [originScaleKernel,Kernel.piecewise_apply,mem_preimage,hz,ite_true]
  exact selectedFreeKernel_eq_copy hs₀ hsmax hη hηmax hi

theorem originScaleKernel_zero_or_copy {r s₀ η K α γ d₀ q δ M : ℝ} {N : ℕ} {k : Lattice}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (z : Published.KineticPhase) :
    originScaleKernel r s₀ η K α γ d₀ q δ M N k z = 0 ∨
      ∃ i : Label, z.1 ∈ mainCoreRegion s₀ η r N i ∧ i.lattice = k ∧
        δ ≤ JetGeometry.jetScale s₀ η i.annulus/r ∧
        JetGeometry.jetScale s₀ η i.annulus/r ≤ M ∧
        originScaleKernel r s₀ η K α γ d₀ q δ M N k z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  classical
  by_cases hz : z.1 ∈ originScaleRegion s₀ η r δ M N k
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨h,hi⟩ := mem_iUnion.mp hi
    exact Or.inr ⟨i,hi,h.1,h.2.1,h.2.2,
      originScaleKernel_eq_copy hs₀ hsmax hη hηmax hi h.1 h.2.1 h.2.2⟩
  · exact Or.inl (by simp [originScaleKernel,Kernel.piecewise_apply,hz])

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact finite mesh labels for the selected origin and scale window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.JetCopyDatum

def windowMesh (η δ M : ℝ) : Finset ℤ :=
  Finset.Icc (index (δ/Real.exp η) η) (index M η)

def meshLabel (s₀ η : ℝ) (r : ℕ → ℝ) {J : Finset ℤ} (n : ℕ) (j : MeshLabel J) : Label :=
  ⟨jetIndex s₀ η r j.1.val n,j.2,0⟩

def meshLabelRegion (s₀ η δ M : ℝ) (r : ℕ → ℝ) (N : ℕ) {J : Finset ℤ}
    (n : ℕ) (j : MeshLabel J) : Set Published.KineticPhase :=
  {z | jetMeshIndex s₀ η (r n) (meshLabel s₀ η r n j).annulus = j.1.val ∧
    δ ≤ meshScale s₀ η r n j/r n ∧ meshScale s₀ η r n j/r n ≤ M ∧
    z.1 ∈ mainCoreRegion s₀ η (r n) N (meshLabel s₀ η r n j)}

theorem meshLabelRegion_measurable (s₀ η δ M : ℝ) (r : ℕ → ℝ) (N : ℕ) {J : Finset ℤ}
    (n : ℕ) (j : MeshLabel J) : MeasurableSet (meshLabelRegion s₀ η δ M r N n j) := by
  unfold meshLabelRegion
  have hc (p : Prop) : MeasurableSet {_z : Published.KineticPhase | p} := by
    by_cases h : p <;> simp [h]
  exact (hc _).inter ((hc _).inter
    ((hc _).inter ((measurableSet_mainCoreRegion s₀ η (r n) N _).preimage measurable_fst)))

theorem meshLabelRegion_originScale {s₀ η δ M : ℝ} {r : ℕ → ℝ} {N : ℕ} {J : Finset ℤ}
    {n : ℕ} {j : MeshLabel J} {z : Published.KineticPhase}
    (h : z ∈ meshLabelRegion s₀ η δ M r N n j) :
    z.1 ∈ originScaleRegion s₀ η (r n) δ M N 0 :=
  mem_iUnion.mpr ⟨meshLabel s₀ η r n j,mem_iUnion.mpr ⟨⟨rfl,h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

theorem meshLabelRegion_disjoint {s₀ η δ M : ℝ} {r : ℕ → ℝ} {N : ℕ} {J : Finset ℤ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {n : ℕ} {j k : MeshLabel J} {z : Published.KineticPhase}
    (hj : z ∈ meshLabelRegion s₀ η δ M r N n j)
    (hk : z ∈ meshLabelRegion s₀ η δ M r N n k) : j = k := by
  have he := mainCoreRegion_unique hs₀ hsmax hη hηmax hj.2.2.2 hk.2.2.2
  apply Prod.ext
  · apply Subtype.ext
    exact hj.1.symm.trans ((congrArg (fun i : Label => jetMeshIndex s₀ η (r n) i.annulus) he).trans hk.1)
  · exact congrArg Label.positive he

theorem originScale_mem_meshLabel {s₀ η δ M : ℝ} {r : ℕ → ℝ} {N : ℕ} {n : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : 0 < r n) (hδ : 0 < δ)
    {z : Published.KineticPhase} (hz : z.1 ∈ originScaleRegion s₀ η (r n) δ M N 0) :
    ∃ j : MeshLabel (windowMesh η δ M), z ∈ meshLabelRegion s₀ η δ M r N n j := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨h,hi⟩ := mem_iUnion.mp hi
  have hwin : jetMeshIndex s₀ η (r n) i.annulus ∈ windowMesh η δ M := by
    have hs := h.2
    rw [jetScale_ratio_exact hs₀ hr hη] at hs
    exact Finset.mem_Icc.mpr (point_window (phase_bounds hη _).1 (phase_bounds hη _).2
      hη hδ hs.1 hs.2)
  let j : MeshLabel (windowMesh η δ M) := ⟨⟨jetMeshIndex s₀ η (r n) i.annulus,hwin⟩,i.positive⟩
  have he : meshLabel s₀ η r n j = i := by
    change Label.mk (jetIndex s₀ η r (jetMeshIndex s₀ η (r n) i.annulus) n) i.positive 0 = i
    rw [jetIndex_at_meshIndex]
    cases i
    congr
    exact h.1.symm
  have hscale : meshScale s₀ η r n j = JetGeometry.jetScale s₀ η i.annulus :=
    congrArg (fun l : Label => JetGeometry.jetScale s₀ η l.annulus) he
  refine ⟨j,?_⟩
  change jetMeshIndex s₀ η (r n) (meshLabel s₀ η r n j).annulus = j.1.val ∧ _
  rw [he,hscale]
  exact ⟨rfl,h.2.1,h.2.2,hi⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The fixed-origin selected kernel is exactly a finite sum of physical cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem copy_meshLabel_eq {s₀ η K α γ d₀ q : ℝ} {r : ℕ → ℝ}
    {J : Finset ℤ} (n : ℕ) (j : MeshLabel J) (z : Published.KineticPhase) :
    copyFreeKernel (r n) s₀ η K α γ d₀ q (meshLabel s₀ η r n j) z =
      dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
        (d₀*meshScale s₀ η r n j^10) q j.2 z := by
  have h0 : latticeVector (0 : Lattice) = 0 := by
    simp [latticeVector]
    rfl
  rw [copyFreeKernel_eq]
  simp only [meshLabel,h0,smul_zero,sub_zero]
  rfl

theorem originScale_lintegral_eq_mesh_sum {s₀ η K α γ d₀ q δ M : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ)
    (z : Published.KineticPhase) (f : Velocity → ℝ≥0∞) :
    (∫⁻ v, f v ∂originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0 z) =
      ∑ j : MeshLabel (windowMesh η δ M),
        (meshLabelRegion s₀ η δ M r N n j).indicator (fun y =>
          ∫⁻ v, f v ∂dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
            (d₀*meshScale s₀ η r n j^10) q j.2 y) z := by
  classical
  by_cases hz : z.1 ∈ originScaleRegion s₀ η (r n) δ M N 0
  · obtain ⟨j,hj⟩ := originScale_mem_meshLabel hs₀ hη hr hδ hz
    rw [Finset.sum_eq_single j]
    · rw [indicator_of_mem hj]
      have he := originScaleKernel_eq_copy (K := K) (α := α) (γ := γ) (d₀ := d₀) (q := q) hs₀ hsmax hη hηmax hj.2.2.2
        (show (meshLabel s₀ η r n j).lattice = 0 from rfl) hj.2.1 hj.2.2.1
      rw [he,copy_meshLabel_eq]
    · intro k _ hkj
      apply indicator_of_notMem
      intro hk
      exact hkj (meshLabelRegion_disjoint hs₀ hsmax hη hηmax hk hj)
    · simp
  · have hk : originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0 z = 0 := by
      simp [originScaleKernel,ProbabilityTheory.Kernel.piecewise_apply,hz]
    rw [hk,lintegral_zero_measure]
    symm
    apply Finset.sum_eq_zero
    intro j _
    exact indicator_of_notMem (fun hj => hz (meshLabelRegion_originScale hj)) _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The selected fixed-origin step equals the finite masked physical-core step -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem meshRegion_lintegral_indicator (s₀ η δ M : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} (j : MeshLabel J) (z : Published.KineticPhase)
    (μ : Measure Velocity) (f : Published.KineticPhase → ℝ≥0∞) :
    (∫⁻ v, (meshLabelRegion s₀ η δ M r N n j).indicator f (z.1,v) ∂μ) =
      (meshLabelRegion s₀ η δ M r N n j).indicator (fun _ => ∫⁻ v, f (z.1,v) ∂μ) z := by
  classical
  have hm (v : Velocity) : (z.1,v) ∈ meshLabelRegion s₀ η δ M r N n j ↔
      z ∈ meshLabelRegion s₀ η δ M r N n j := Iff.rfl
  by_cases hz : z ∈ meshLabelRegion s₀ η δ M r N n j
  · rw [indicator_of_mem hz]
    apply lintegral_congr
    intro v
    exact indicator_of_mem ((hm v).mpr hz) f
  · rw [indicator_of_notMem hz]
    have hzero : (fun v => (meshLabelRegion s₀ η δ M r N n j).indicator f (z.1,v)) = fun _ => 0 := by
      funext v
      exact indicator_of_notMem ((not_congr (hm v)).mpr hz) f
    rw [hzero,lintegral_zero]

theorem originScale_step_eq_mesh_sum {s₀ η K α γ d₀ q δ M : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ) (a : ℝ)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (z : Published.KineticPhase) :
    step a (originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0) f z =
      ∑ j : MeshLabel (windowMesh η δ M),
        step a (dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
          (d₀*meshScale s₀ η r n j^10) q j.2)
          ((meshLabelRegion s₀ η δ M r N n j).indicator f) z := by
  let F (j : MeshLabel (windowMesh η δ M)) (s : ℝ) : ℝ≥0∞ :=
    ∫⁻ v, (meshLabelRegion s₀ η δ M r N n j).indicator f ((flight z s).1,v)
      ∂dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
        (d₀*meshScale s₀ η r n j^10) q j.2 (flight z s)
  have hF (j : MeshLabel (windowMesh η δ M)) : Measurable (F j) :=
    step_inner_measurable _ (hf.indicator (meshLabelRegion_measurable s₀ η δ M r N n j)) z
  have he (s : ℝ) :
      (∫⁻ v, f ((flight z s).1,v)
        ∂originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0 (flight z s)) =
          ∑ j : MeshLabel (windowMesh η δ M), F j s := by
    rw [originScale_lintegral_eq_mesh_sum hs₀ hsmax hη hηmax n hr hδ N]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [F]
    rw [meshRegion_lintegral_indicator]
    by_cases hj : flight z s ∈ meshLabelRegion s₀ η δ M r N n j
    · simp only [indicator_of_mem hj]
    · simp only [indicator_of_notMem hj]
  unfold step
  simp_rw [he]
  exact lintegral_finsetSum _ (fun j _ => hF j)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
