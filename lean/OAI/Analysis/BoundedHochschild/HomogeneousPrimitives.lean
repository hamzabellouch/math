import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CompactAverages
import OAI.Analysis.BoundedHochschild.MatrixAlgebras
import OAI.Analysis.BoundedHochschild.SubalgebraModules
import OAI.Analysis.BoundedHochschild.CommutingExtensions

namespace OAI

/-! Bounded primitives for homogeneous type-I matrix algebras. -/

noncomputable section

namespace BoundedHochschild
open Filter Topology TopologicalSpace MeasureTheory MeasureTheory.Measure
open HochschildMatrixSystems
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
theorem primitive_of_homogeneous_typeI {d : ℕ} (E : MatrixSystem M d)
    (hcomm : ∀ a b : E.commutant, a*b=b*a)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  classical
  let A := E.matrixAlgebra
  let B := E.commutant
  let K := unitary A
  let compactUnitaryMeasurableSpace : MeasurableSpace K := borel K
  let compactUnitaryBorelSpace : BorelSpace K := ⟨rfl⟩
  let K₀ : PositiveCompacts K := ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  let μ : Measure K := haarMeasure K₀
  let compactUnitaryProbabilityMeasure : IsProbabilityMeasure μ := ⟨haarMeasure_self⟩
  let ρ : K →* unitary M := unitaryInclusion A
  have hρ : Continuous ρ := continuous_unitaryInclusion A
  let F := compactAverage ρ μ f
  have hF : ‖F‖≤‖f‖ := norm_compactAverage_le ρ μ f
  have hfix : ∀ v ∈ Set.range ρ, translateLast F v=F := by
    rintro v ⟨u,rfl⟩
    exact compactAverage_fixed ρ hρ μ f u
  let σ : unitary B →* unitary M := unitaryInclusion B
  have hσcomm (s t : unitary B) : Commute (σ s) (σ t) := by
    apply Subtype.ext
    exact congrArg (fun b : B => (b:M)) (hcomm (s:B) (t:B))
  have hcross (s : unitary B) (v : unitary M) (hv : v ∈ Set.range ρ) : Commute (σ s) v := by
    obtain ⟨t,rfl⟩ := hv
    apply Subtype.ext
    exact (E.commutant_commutes_matrix (s:B) (t:A)).eq
  have hr : ∀ v x, residualCLM x (translateLast F v)=((-1:ℂ)^(n+1)) • f x :=
    compactAverage_residual ρ hρ μ f _ (residual_translate_cocycle f hf)
  obtain ⟨G,hG,hGA,hGB,hGr⟩ := exists_commuting_extension e σ (Set.range ρ)
    (HochschildSakai.mul_hasPreadjoint e) (HochschildSakai.mul_right_hasPreadjoint e)
    hσcomm hcross F hfix _ hr
  have hA : ∀ u : unitary A, translateLast G (unitaryInclusion A u)=G :=
    fun u => hGA _ ⟨u,rfl⟩
  have hB : ∀ u : unitary B, translateLast G (unitaryInclusion B u)=G := hGB
  have hmod : ∀ (a : Fin n → M) (x : M), G (Fin.snoc a x)=G (Fin.snoc a 1)*x := by
    intro a x
    let L := G.curryRight a
    have hAm (y : A) : L (y:M)=L 1*(y:M) := by
      simpa only [one_mul,L,ContinuousMultilinearMap.curryRight_apply] using right_module_subalgebra A G hA a 1 y
    have hBm (y : M) (z : B) : L (y*(z:M))=L y*(z:M) :=
      right_module_subalgebra B G hB a y z
    change L x=L 1*x
    calc
      L x = L (∑ i,∑ j,E.entry i j*E.coefficient i j x) := congrArg L (E.reconstruct x).symm
      _ = ∑ i,∑ j,L (E.entry i j*E.coefficient i j x) := by simp only [_root_.map_sum]
      _ = ∑ i,∑ j,(L 1*E.entry i j)*E.coefficient i j x := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hBm (E.entry i j) ⟨_,E.coefficient_mem i j x⟩,
          hAm ⟨_,E.entry_mem_span i j⟩]
      _ = L 1*(∑ i,∑ j,E.entry i j*E.coefficient i j x) := by
        simp only [Finset.mul_sum,mul_assoc]
      _ = L 1*x := congrArg (fun y : M => L 1*y) (E.reconstruct x)
  apply primitive_from_average f G (hG.trans hF) ?_ hmod
  intro x
  simpa only [translateLast_one] using hGr 1 x

omit [PartialOrder M] [StarOrderedRing M] in
lemma commutant_commutative_of_abelian_diagonal {d : ℕ} (E : MatrixSystem M d)
    (i : Fin d) (hp : FinitePathMain.AbelianProjection (E.entry i i)) :
    ∀ a b : E.commutant, a*b=b*a := by
  intro a b
  have he (y : E.commutant) : E.entry i i*(y:M)*E.entry i i=E.entry i i*(y:M) := by
    rw [mul_assoc,(y.property i i).eq,← mul_assoc,hp.1.isIdempotentElem.eq]
  have hm (y z : E.commutant) :
      (E.entry i i*(y:M))*(E.entry i i*(z:M))=E.entry i i*((y:M)*(z:M)) := by
    rw [← mul_assoc,he,mul_assoc]
  have h := (hp.2 (a:M) (b:M)).eq
  rw [he,he,hm,hm] at h
  have hh := congrArg (E.coefficient i i) h
  change E.coefficient i i (E.entry i i*((a*b : E.commutant):M)) =
    E.coefficient i i (E.entry i i*((b*a : E.commutant):M)) at hh
  rw [E.coefficient_of_commutant i (a*b).property,
    E.coefficient_of_commutant i (b*a).property] at hh
  exact Subtype.ext hh

include e in
theorem primitive_of_abelian_matrix_diagonal {d : ℕ} (E : MatrixSystem M d)
    (i : Fin d) (hp : FinitePathMain.AbelianProjection (E.entry i i))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ x, differentialValue g x=f x :=
  primitive_of_homogeneous_typeI e E (commutant_commutative_of_abelian_diagonal E i hp) f hf

theorem primitive_of_homogeneous_typeI_wstar [WStarAlgebra M] {d : ℕ} (E : MatrixSystem M d)
    (hcomm : ∀ a b : E.commutant, a*b=b*a)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  obtain ⟨Y,hY,hN,hC,⟨d⟩⟩ := WStarAlgebra.exists_predual (M:=M)
  let predualNormedAddCommGroup := hY
  let predualNormedSpace := hN
  let predualCompleteSpace := hC
  exact primitive_of_homogeneous_typeI d E hcomm f hf

end BoundedHochschild

end

end OAI
