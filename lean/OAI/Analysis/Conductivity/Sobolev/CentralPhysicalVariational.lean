import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralCoercivitySmooth

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

@[instance_reducible] def centralEnergy_inner (s : Fin 3 → ℝ) : InnerProductSpace ℝ (centralEnergySpace s) :=
  Submodule.innerProductSpace (centralEnergySpace s)

def centralCoercivityConstant (s : Fin 3 → ℝ) : ℝ :=
  1+‖centralAmbientQ s‖^2*centralCoercivityBase

lemma centralCoercivityConstant_pos (s : Fin 3 → ℝ) : 0<centralCoercivityConstant s := by
  have := centralCoercivityBase_pos
  dsimp [centralCoercivityConstant]
  positivity

lemma central_graph_projected_bound (s : Fin 3 → ℝ) (u : centralEnergySpace s) :
    ‖centralAmbientQ s u.val‖^2≤
      (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s u.val := by
  have hc : IsClosed {v : CentralAmbient s | ‖centralAmbientQ s v‖^2≤
      (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s v} :=
    isClosed_le ((centralAmbientQ s).continuous.norm.pow 2)
      (continuous_const.mul (continuous_centralAmbientEnergy s))
  have hr : (LinearMap.range (centralEmbedL s) : Set (CentralAmbient s))⊆
      {v : CentralAmbient s | ‖centralAmbientQ s v‖^2≤
        (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s v} := by
    rintro v ⟨f,rfl⟩
    exact central_smooth_projected_bound s f
  exact closure_minimal hr hc u.property

lemma central_graph_coercivity (s : Fin 3 → ℝ) (u : (centralM s).ker) :
    ‖u‖^2≤centralCoercivityConstant s*(‖centralD s u.val‖^2+
      ∑ i : Fin 3,‖spectralGraphWeight (torusRate s) (centralT s i u.val)‖^2) := by
  have hm : centralAmbientM s u.val.val=0 := u.property
  have hq : centralAmbientQ s u.val.val=u.val.val := by
    rw [centralAmbientQ_apply,hm,zero_smul,sub_zero]
  have hh := central_graph_projected_bound s u.val
  rw [hq] at hh
  have hn := centralAmbientEnergy_nonneg s u.val.val
  change ‖u.val.val‖^2≤centralCoercivityConstant s*centralAmbientEnergy s u.val.val
  dsimp only [centralCoercivityConstant]
  nlinarith

theorem central_physical_variational_exists (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧
      (∀ v : centralEnergySpace s,
        inner ℝ (centralD s p) (centralD s v)+
          (∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          ∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v)) ∧
      (∀ q : centralEnergySpace s,(∀ v : centralEnergySpace s,
        inner ℝ (centralD s q) (centralD s v)+
          (∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i q))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          ∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v)) →
        q-p=centralM s q • centralOne s) := by
  have hh := @central_variational_exists_graph (centralEnergySpace s) CentralGradients
    inferInstance (centralEnergy_inner s) inferInstance inferInstance inferInstance
    TorusModes inferInstance (torusRate s) (centralD s) (centralT s) (centralM s) (centralOne s)
    (centralAmbientM_one s) (centralAmbientD_one s) (centralAmbientWeight_one s)
    (centralOne_mean s) (centralCoercivityConstant s) (centralCoercivityConstant_pos s)
    (central_graph_coercivity s) slopes hs
  exact hh

end ScalarConductivity

end

end OAI
