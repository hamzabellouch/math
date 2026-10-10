import Mathlib
import OAI.Analysis.Commutator.FiniteDimensionalAverage
import OAI.Analysis.Commutator.MatrixGNS
import OAI.Analysis.Commutator.MatrixTowerClosure
import OAI.Analysis.Commutator.WeakConvergence

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator Topology

open MeasureTheory Filter

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

def unitaryMap (n : ℕ) : unitary (Matrix (F n).I (F n).I ℂ) →* unitary M where
  toFun u := TracialGNS.stageUnitary (F n).hom u
  map_one' := Subtype.ext (map_one (F n).hom)
  map_mul' u v := Subtype.ext (map_mul (F n).hom (u:Matrix (F n).I (F n).I ℂ) (v:Matrix (F n).I (F n).I ℂ))

def unitaryRepresentation (n : ℕ) : unitary (Matrix (F n).I (F n).I ℂ) →* (H ≃ₗᵢ[ℂ] H) :=
  (algebraUnitaryRepresentation M).comp (unitaryMap M F n)

lemma unitaryRepresentation_continuous (n : ℕ) (x : H) :
    Continuous fun u => unitaryRepresentation M F n u x := by
  change Continuous fun u : unitary (Matrix (F n).I (F n).I ℂ) => ((F n).hom (u:_):H →L[ℂ] H) x
  have hf : Continuous ((F n).hom : Matrix (F n).I (F n).I ℂ → M) := (F n).hom.toLinearMap.continuous_of_finiteDimensional
  exact (continuous_subtype_val.comp (hf.comp continuous_subtype_val)).clm_apply continuous_const

lemma exists_stage_approximation (Y : H →L[ℂ] H) (n : ℕ) :
    ∃ Z : H →L[ℂ] H, ‖Z‖ ≤ ‖Y‖ ∧ ‖Z-Y‖ ≤ commutatorSeminorm M Y ∧
      ∀ a, Z*concreteStage M F n a=concreteStage M F n a*Z := by
  classical
  let := UnitaryHaar.compactUnitary (Matrix (F n).I (F n).I ℂ)
  let : MeasurableSpace (unitary (Matrix (F n).I (F n).I ℂ)) := borel _
  let : BorelSpace (unitary (Matrix (F n).I (F n).I ℂ)) := ⟨rfl⟩
  let U := unitaryRepresentation M F n
  let μ := UnitaryHaar.probability (unitary (Matrix (F n).I (F n).I ℂ))
  obtain ⟨Z,hZ,hcomm,hcoeff⟩ := CompactAverage.exists_average U (unitaryRepresentation_continuous M F n) Y μ
  refine ⟨Z,hZ,?_,?_⟩
  · apply WeakOperatorIntegral.difference_norm μ (CompactAverage.conjugate U Y) _ Z hcoeff Y
      (commutatorSeminorm_nonneg M Y)
    · intro u
      exact unitary_conjugate_distance M Y (unitaryMap M F n u)
    · intro x y
      exact ((CompactAverage.conjugate_continuous U (unitaryRepresentation_continuous M F n) Y x).inner
        continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · let D : Matrix (F n).I (F n).I ℂ →ₗ[ℂ] (H →L[ℂ] H) :=
      { toFun := fun a => Z*concreteStage M F n a-concreteStage M F n a*Z
        map_add' := by intro a b; simp only [map_add,mul_add,add_mul]; abel
        map_smul' := by intro z a; simp only [map_smul,mul_smul_comm,smul_mul_assoc,smul_sub]; rfl }
    have hD : D=0 := by
      apply LinearMap.ext_on (CStarAlgebra.span_unitary (Matrix (F n).I (F n).I ℂ))
      intro u hu
      exact sub_eq_zero.mpr (hcomm ⟨u,hu⟩)
    intro a
    exact sub_eq_zero.mp (congrArg (fun D => (D : Matrix (F n).I (F n).I ℂ →ₗ[ℂ] (H →L[ℂ] H)) a) hD)

theorem exists_tower_approximation (hF : Monotone (fun n => (F n).hom.range))
    (Y : H →L[ℂ] H) :
    ∃ Z : H →L[ℂ] H, ‖Z‖ ≤ ‖Y‖ ∧ ‖Z-Y‖ ≤ commutatorSeminorm M Y ∧
      ∀ a : generated M F,Z*(a:H →L[ℂ] H)=(a:H →L[ℂ] H)*Z := by
  choose T hn hd hc using exists_stage_approximation M F Y
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨Z,hZ,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T ‖Y‖ (norm_nonneg Y) hn
  have hconv : WeakOperatorLimit.Converges T Z (ω:Filter ℕ) := hlim
  refine ⟨Z,hZ,hconv.dist Y (commutatorSeminorm_nonneg M Y) (Eventually.of_forall hd),?_⟩
  have hstage (n : ℕ) (a : Matrix (F n).I (F n).I ℂ) :
      Z*concreteStage M F n a=concreteStage M F n a*Z := by
    apply hconv.commutes
    apply (Ultrafilter.of_le atTop)
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨b,hb⟩ := hF hm (show (F n).hom a∈(F n).hom.range from ⟨a,rfl⟩)
    have he : concreteStage M F m b=concreteStage M F n a := congrArg (fun c : M => (c:H →L[ℂ] H)) hb
    rw [←he]
    exact hc m b
  have hcent : Z∈Set.centralizer (stageAlgebra M F : Set (H →L[ℂ] H)) := by
    have hcomm : stageAlgebra M F≤StarSubalgebra.centralizer ℂ ({Z} : Set (H →L[ℂ] H)) := by
      apply iSup_le
      intro n
      rintro a ⟨b,rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro z hz
      have he : z=Z := Set.mem_singleton_iff.mp hz
      subst z
      constructor
      · exact hstage n b
      · have hh := congrArg star (hstage n (star b))
        simpa only [star_mul,←map_star,star_star] using! hh.symm

    intro a ha
    exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hcomm ha)) Z (Set.mem_singleton Z)).1.symm
  intro a
  exact ((mem_generated M F a).mp a.property Z hcent)

end Kadison.MatrixTower

end

end
end

end OAI
