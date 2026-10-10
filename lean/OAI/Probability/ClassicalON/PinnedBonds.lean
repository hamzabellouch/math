import OAI.Probability.ClassicalON.PinComparison

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def pinNormalization (B : Set V) : ℝ :=
  (2:ℝ)⁻¹^Fintype.card ↥(Bᶜ)/((2:ℝ)⁻¹^Fintype.card V)

theorem pinNormalization_pos (B : Set V) : 0<pinNormalization B := by
  unfold pinNormalization
  positivity

theorem sum_prescribed_bondSignProduct (left right : E → V) (t : E → ℝ)
    (B : Set V) (p : V → Bool) (η : E → Bool) :
    (∑ τ : ↥(Bᶜ) → Bool,bondSignProduct left right t η (glueFamily B (fun v => p v) τ))=
      bondProduct t η*(Fintype.card (prescribedCompatibleSigns left right B p η):ℝ) := by
  rw [sum_glueFamily]
  simp_rw [bondSignProduct_eq]
  have he (s : V → Bool) :
      (if (fun v : B => s v)=(fun v : B => p v) then
        bondProduct t η*(if s∈compatibleSigns left right η then 1 else 0) else 0)=
      bondProduct t η*(if s∈prescribedCompatibleSigns left right B p η then 1 else 0) := by
    have h : (fun v : B => s v)=(fun v : B => p v) ↔ ∀ v∈B,s v=p v := by
      simp only [funext_iff,Subtype.forall]
    have hp : s∈prescribedCompatibleSigns left right B p η ↔
        s∈compatibleSigns left right η ∧ ∀ v∈B,s v=p v := Iff.rfl
    simp only [hp,h]
    by_cases hB : ∀ v∈B,s v=p v
    · rw [ite_eq_left hB]
      by_cases hC : s∈compatibleSigns left right η
      · rw [ite_eq_left hC,ite_eq_left ⟨hC,hB⟩]
      · rw [ite_eq_right hC,ite_eq_right (fun h => hC h.1)]
    · rw [ite_eq_right hB,ite_eq_right (fun h => hB h.2),mul_zero]
  simp_rw [he]
  rw [← Finset.mul_sum,Finset.sum_boole,← Fintype.card_subtype]

theorem integral_pole_spinBondWeight_card (left right : E → V) (b : E → ℝ)
    (B : Set V) (p : V → Bool) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η
      ∂(poleSystem left right b B (fun v => p v)).reference)=
      pinNormalization B * ∫ r,amplitudeBondPrefactor left right b (glueAmplitude B ⊤ r)*
        bondProduct (amplitudeBondParam left right b (glueAmplitude B ⊤ r)) η*
        (Fintype.card (prescribedCompatibleSigns left right B p η):ℝ)
        ∂Measure.pi (fun _ : ↥(Bᶜ) => sphericalAmplitudeLaw) := by
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      spinBondWeight left right b s η) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_spinBondWeight left right b η)
  rw [integral_poleSystem_cylinder _ _ _ _ _ _ hc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  simp_rw [cylindrical_spin_bond_weight,integral_const_mul]
  change (∫ τ,Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)*
    bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b
      (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)-1) η (glueFamily B (fun v => p v) τ)*
    planarAmplitudePartition left right b (glueAmplitude B ⊤ r) ∂isingReference)=_
  rw [integral_mul_const,integral_const_mul,integral_isingReference]
  have hh := sum_prescribed_bondSignProduct left right
    (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)-1) B p η
  convert_to Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)*
    ((2:ℝ)⁻¹^Fintype.card ↥(Bᶜ)*
      (∑ τ : ↥(Bᶜ) → Bool,bondSignProduct left right
        (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)-1) η
        (glueFamily B (fun v => p v) τ)))*
    planarAmplitudePartition left right b (glueAmplitude B ⊤ r)=_ using 1
  · congr!
  rw [hh,amplitudeBondParam_eq]
  unfold amplitudeBondPrefactor pinNormalization
  have hn : ((2:ℝ)⁻¹^Fintype.card V)≠0 := by positivity
  field_simp

omit [Fintype E] in
theorem prescribed_positive_card (left right : E → V) (B : Set V) (η : E → Bool) :
    (Fintype.card (prescribedCompatibleSigns left right B (fun _ => true) η):ℝ)=
      clusterWeight left right η*bondPinFactor left right B η :=
  positiveCompatibleSigns_card _ _ _ _

theorem integral_positive_spinBondWeight (left right : E → V) (b : E → ℝ)
    (B : Set V) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η
      ∂(poleSystem left right b B (fun _ => true)).reference)=
      pinNormalization B * ∫ r,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*
        bondPinFactor left right B η ∂Measure.pi (fun _ : ↥(Bᶜ) => sphericalAmplitudeLaw) := by
  rw [integral_pole_spinBondWeight_card left right b B (fun _ => true) η]
  simp_rw [prescribed_positive_card]
  simp only [amplitudeBondWeight,bondWeight,mul_assoc,mul_left_comm,mul_comm]

theorem integral_layer_spinBondWeight (left right : E → V) (b : E → ℝ)
    (I O : Set V) (hIO : Disjoint I O) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η
      ∂(poleSystem left right b (I∪O) (fun v => layerSigns I v)).reference)=
      pinNormalization (I∪O) * ∫ r,amplitudeBondWeight left right b (glueAmplitude (I∪O) ⊤ r) η*
        bondPinFactor left right (I∪O) η*(if bondCrossing left right I O η then 0 else 1)
        ∂Measure.pi (fun _ : ↥((I∪O)ᶜ) => sphericalAmplitudeLaw) := by
  rw [integral_pole_spinBondWeight_card]
  simp_rw [layerSigns_card _ _ _ _ hIO]
  simp only [amplitudeBondWeight,bondWeight,mul_assoc,mul_left_comm,mul_comm]
  all_goals congr!

def poleBondMean (left right : E → V) (b : E → ℝ) (B : Set V) (p : B → Bool)
    (f : (E → Bool) → ℝ) : ℝ :=
  weightedMean (poleSystem left right b B p).reference (fun s => Real.exp (freeSpinEnergy 3 left right b s))
    (fun s => ∑ η,spinBondWeight left right b s η*f η)

theorem integral_spinWeight_sum (left right : E → V) (b : E → ℝ)
    (μ : Measure (V → Spin 3)) [IsFiniteMeasure μ] :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂μ)=
      ∑ η,∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η ∂μ := by
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with s
    rw [← Finset.mul_sum,spinBondWeight_sum,mul_one]
  · intro η _
    exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul (continuous_spinBondWeight _ _ _ _))

theorem positive_Z (left right : E → V) (b : E → ℝ) (B : Set V) :
    (poleSystem left right b B (fun _ => true)).Z (fun _ => 1)=
      pinNormalization B*pinnedBondNumerator sphericalAmplitudeLaw left right b B (fun _ => 1) := by
  change (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂(poleSystem left right b B (fun _ => true)).reference)=_
  rw [integral_spinWeight_sum]
  simp_rw [integral_positive_spinBondWeight]
  rw [← Finset.mul_sum,← integral_finsetSum]
  · simp only [mul_one,pinnedBondNumerator]
  · intro η _
    exact compact_integrable (((continuous_amplitudeBondWeight _ _ _ _).comp
      ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))).mul continuous_const)

theorem layer_Z (left right : E → V) (b : E → ℝ) (I O : Set V) (hIO : Disjoint I O) :
    (poleSystem left right b (I∪O) (fun v => layerSigns I v)).Z (fun _ => 1)=
      pinNormalization (I∪O)*pinnedBondNumerator sphericalAmplitudeLaw left right b (I∪O)
        (fun η => if bondCrossing left right I O η then 0 else 1) := by
  change (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂(poleSystem left right b (I∪O) (fun v => layerSigns I v)).reference)=_
  rw [integral_spinWeight_sum]
  simp_rw [integral_layer_spinBondWeight _ _ _ _ _ hIO]
  rw [← Finset.mul_sum,← integral_finsetSum]
  · simp only [pinnedBondNumerator]
    congr!
  · intro η _
    exact compact_integrable ((((continuous_amplitudeBondWeight _ _ _ _).comp
      ((continuous_glueAmplitude (I∪O)).comp (continuous_const.prodMk continuous_id))).mul continuous_const).mul continuous_const)

theorem poleBondMean_eq_pinnedBondMean (left right : E → V) (b : E → ℝ) (B : Set V)
    (f : (E → Bool) → ℝ) :
    poleBondMean left right b B (fun _ => true) f=
      pinnedBondMean sphericalAmplitudeLaw left right b B f := by
  unfold poleBondMean weightedMean
  change _/(poleSystem left right b B (fun _ => true)).Z (fun _ => 1)=_
  rw [positive_Z]
  simp_rw [Finset.mul_sum,← mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_mul_const,integral_positive_spinBondWeight]
    simp_rw [mul_assoc (pinNormalization B)]
    rw [← Finset.mul_sum]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum]
    · exact mul_div_mul_left _ _ (ne_of_gt (pinNormalization_pos B))
    · intro η _
      exact compact_integrable ((((continuous_amplitudeBondWeight _ _ _ _).comp
        ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))).mul continuous_const).mul continuous_const)
  · intro η _
    exact (compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_spinBondWeight _ _ _ _))).mul_const _

end ClassicalON

end

end OAI
