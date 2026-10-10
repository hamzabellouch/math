import OAI.Probability.ClassicalON.IsingPositive

namespace OAI

universe uV

noncomputable section
open MeasureTheory
namespace ClassicalON

abbrev PlanarAngle := UnitAddCircle

def angleLaw : Measure PlanarAngle := AddCircle.haarAddCircle

instance angleLaw_isProbability : IsProbabilityMeasure angleLaw := by
  unfold angleLaw; infer_instance
instance angleLaw_isAddHaar : angleLaw.IsAddHaarMeasure := by
  unfold angleLaw; infer_instance

variable {V : Type uV} [Fintype V]

def planarReference : Measure (V → PlanarAngle) := Measure.pi (fun _ => angleLaw)

instance planarReference_isProbability : IsProbabilityMeasure (planarReference (V := V)) := by
  unfold planarReference; infer_instance
instance planarReference_isAddHaar : (planarReference (V := V)).IsAddHaarMeasure := by
  unfold planarReference; infer_instance

def torusDouble : ((V → PlanarAngle)×(V → PlanarAngle)) →+
    ((V → PlanarAngle)×(V → PlanarAngle)) where
  toFun p := (p.1+p.2,p.1-p.2)
  map_zero' := by simp
  map_add' := by intros; ext <;> simp <;> abel

omit [Fintype V] in
theorem torusDouble_continuous : Continuous (torusDouble (V := V)) := by
  change Continuous (fun p : (V → PlanarAngle)×(V → PlanarAngle) => (p.1+p.2,p.1-p.2))
  fun_prop

omit [Fintype V] in
theorem torusDouble_surjective : Function.Surjective (torusDouble (V := V)) := by
  intro p
  let v := DivisibleBy.div (p.1+p.2) (2 : ℤ)
  have hv : (2 : ℤ) • v=p.1+p.2 := DivisibleBy.div_cancel _ (by norm_num)
  refine ⟨(v,p.1-v),?_⟩
  apply Prod.ext
  · change v+(p.1-v)=p.1; abel
  · change v-(p.1-v)=p.2
    rw [show v-(p.1-v)=(2 : ℤ) • v-p.1 by simp only [two_zsmul]; abel,hv]
    abel

theorem torusDouble_preserves : MeasurePreserving (torusDouble (V := V))
    ((planarReference (V := V)).prod (planarReference (V := V)))
    ((planarReference (V := V)).prod (planarReference (V := V))) :=
  by
    classical
    let : BorelSpace (V → PlanarAngle) := Pi.borelSpace
    let : SFinite (planarReference (V := V)) := inferInstance
    let : MeasurableAdd (V → PlanarAngle) := inferInstance
    let : ((planarReference (V := V)).prod (planarReference (V := V))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure _ _
    exact AddMonoidHom.measurePreserving torusDouble_continuous torusDouble_surjective rfl

end ClassicalON

end

end OAI
