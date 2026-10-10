import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupMatrixDimensions
import OAI.Analysis.Pureness.States.ScalarTracialUltraproductTrace
import Mathlib.Order.Filter.Ultrafilter.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupScalarProductDecidable (p : Prop) : Decidable p := Classical.propDecidable p
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder

def freeGroupCoordinateModel (m : ℕ) : FreeGroup ℕ →* unitary (FinMatrix ℂ (m+1)) :=
  if h : ∃ n, freeGroupModelCoordinate n = m then
    h.choose_spec ▸ freeGroupReplicatedMatrix h.choose
  else 1

lemma freeGroupCoordinateModel_selected (n : ℕ) :
    freeGroupCoordinateModel (freeGroupModelCoordinate n) = freeGroupReplicatedMatrix n := by
  rw [freeGroupCoordinateModel, dite_eq_left (show ∃ k, freeGroupModelCoordinate k = freeGroupModelCoordinate n from ⟨n,rfl⟩)]
  generalize_proofs h
  have he : h.choose = n := freeGroupModelCoordinate_strictMono.injective h.choose_spec
  have aux (k m : ℕ) (hk : k=m) (hp : freeGroupModelCoordinate k = freeGroupModelCoordinate m) :
      hp ▸ freeGroupReplicatedMatrix k = freeGroupReplicatedMatrix m := by
    subst m
    rfl
  exact aux _ _ he _

abbrev ScalarMatrixProduct := lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞

instance scalarMatrixProductStarMul : StarMul ScalarMatrixProduct :=
  (lp.inftyStarRing (B := fun n : ℕ => FinMatrix ℂ (n+1))).toStarMul

def freeGroupScalarProductModel : FreeGroup ℕ →* unitary ScalarMatrixProduct where
  toFun g := ⟨⟨fun n => freeGroupCoordinateModel n g, memℓp_infty_iff.mpr ⟨1,by
    rintro _ ⟨n,rfl⟩
    exact (CStarRing.norm_coe_unitary _).le⟩⟩, by
      constructor <;> apply lp.ext <;> funext n
      · change star (freeGroupCoordinateModel n g : FinMatrix ℂ (n+1))*freeGroupCoordinateModel n g=1
        exact Unitary.coe_star_mul_self _
      · change (freeGroupCoordinateModel n g : FinMatrix ℂ (n+1))*star (freeGroupCoordinateModel n g)=1
        exact Unitary.coe_mul_star_self _⟩
  map_one' := by
    apply Subtype.ext
    apply lp.ext
    funext n
    exact congrArg Subtype.val (map_one (freeGroupCoordinateModel n))
  map_mul' g h := by
    apply Subtype.ext
    apply lp.ext
    funext n
    exact congrArg Subtype.val (map_mul (freeGroupCoordinateModel n) g h)

def freeGroupScalarUltrafilter : Ultrafilter ℕ :=
  (hyperfilter ℕ).map freeGroupModelCoordinate

lemma freeGroupScalarUltrafilter_free : (freeGroupScalarUltrafilter : Filter ℕ) ≤ atTop := by
  rw [freeGroupScalarUltrafilter, Ultrafilter.coe_map]
  exact freeGroupModelCoordinate_strictMono.tendsto_atTop.comp Nat.hyperfilter_le_atTop

lemma freeGroupScalarProduct_trace_limit (g : FreeGroup ℕ) :
    Tendsto (fun n => (scalarMatrixTracialState n).functional
      ((freeGroupScalarProductModel g : ScalarMatrixProduct) n))
      (freeGroupScalarUltrafilter : Filter ℕ) (nhds (if g=1 then 1 else 0)) := by
  rw [freeGroupScalarUltrafilter, Ultrafilter.coe_map, tendsto_map'_iff]
  have he : (fun n => (scalarMatrixTracialState (freeGroupModelCoordinate n)).functional
      ((freeGroupScalarProductModel g : ScalarMatrixProduct) (freeGroupModelCoordinate n))) =ᶠ[↑(hyperfilter ℕ)]
      (fun _ => if g=1 then 1 else 0) := by
    apply Nat.hyperfilter_le_atTop
    change ∀ᶠ n in atTop, (scalarMatrixTracialState (freeGroupModelCoordinate n)).functional
      (freeGroupCoordinateModel (freeGroupModelCoordinate n) g) = if g=1 then 1 else 0
    simpa only [freeGroupCoordinateModel_selected] using freeGroupReplicatedMatrix_trace g
  exact tendsto_const_nhds.congr' he.symm

def scalarMatrixProductQuotient (U : Ultrafilter ℕ) :
    ScalarMatrixProduct →⋆ₐ[ℂ] ScalarTracialMatrixUltraproduct U :=
  filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit

def freeGroupScalarUltraUnitary : FreeGroup ℕ →*
    unitary (ScalarTracialMatrixUltraproduct freeGroupScalarUltrafilter) :=
  (Unitary.map { (scalarMatrixProductQuotient freeGroupScalarUltrafilter).toMonoidHom with
      map_star' := map_star (scalarMatrixProductQuotient freeGroupScalarUltrafilter) }).toMonoidHom.comp
    freeGroupScalarProductModel

lemma freeGroupScalarUltraUnitary_trace (g : FreeGroup ℕ) :
    (scalarMatrixUltraTracialState freeGroupScalarUltrafilter).functional
      (freeGroupScalarUltraUnitary g) = if g=1 then 1 else 0 := by
  exact tendsto_nhds_unique
    (scalarMatrixUltraValue_tendsto freeGroupScalarUltrafilter (freeGroupScalarProductModel g))
    (freeGroupScalarProduct_trace_limit g)
end CuntzPureness

end

end OAI
