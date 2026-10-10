import OAI.NumberTheory.DirichletL.Detector.GaussianTuple
import OAI.NumberTheory.DirichletL.Detector.Windows

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRowIndex := {I : Id // Supported I}×O

def physicalRowMonoid (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  rowCoefficient η C.Xi (primaryGenerator r.1.val)
    ((supported_span_primaryGenerator_iff r.1.val).mpr r.1.property) r.2

def physicalRowWeight (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (r : PhysicalRowIndex) : ℂ :=
  if ∀P∈C.excluded,¬P∣r.1.val then
    let a := primaryGenerator r.1.val
    let ha := supported_primaryGenerator_ne_zero r.1.val r.1.property
    let q : ℝ := Ideal.absNorm r.1.val
    (Y:ℂ)⁻¹*W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator r.1.val/
      (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
      C.residueMonoid r.2*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*q*X))
  else 0

lemma physicalRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

lemma physicalRowWeight_outer_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowWeight_inner_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex)
    (h : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowScale_pos (C : CalibrationData) (X : ℝ) (hX : 0<X)
    (s : {I : Id // Supported I}) : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := by
  have hc : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hs : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  positivity

theorem physicalRowWeight_finite_support (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    (Function.support (physicalRowWeight C W0 W1 X Y)).Finite := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply ho.subset
    rintro s ⟨r,hr,rfl⟩
    exact fun hz=>hr (physicalRowWeight_outer_zero C W0 W1 X Y r hz)
  · intro s hs
    have hm := elementWindow_finite_support W0 hW0 _ (physicalRowScale_pos C X hX s)
    apply ((Set.finite_singleton s).prod hm).subset
    intro r hr
    have he : r.1=s := hr.2
    refine ⟨he,?_⟩
    intro hz
    apply hr.1
    apply physicalRowWeight_inner_zero C W0 W1 X Y r
    simpa only [he] using hz

lemma physicalRowWeight_mul_summable (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (F : PhysicalRowIndex→ℂ) :
    Summable (fun r=>physicalRowWeight C W0 W1 X Y r*F r) := by
  apply summable_of_hasFiniteSupport
  apply (physicalRowWeight_finite_support C W0 W1 hW0 hW1 X Y hX hY).subset
  intro r hr hz
  exact hr (by dsimp only; rw [hz,zero_mul])

theorem markedPhysicalProbe_eq_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=>verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t))
  rw [hf.tsum_prod]
  unfold markedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [ite_eq_left hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [ite_eq_right hc,zero_mul,mul_zero,tsum_zero]

theorem markedPhysicalProbe_eq_gaussian_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (physicalRowMonoid η C r) gaussianCompletedProfile Z := by
  rw [markedPhysicalProbe_eq_rows η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (physicalRowMonoid_norm η C r) 4 (by norm_num) Z hZ]

end SevenEighths.ProbePhysical
end

end OAI
