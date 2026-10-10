import OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTail
import OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalScaleMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*lowPhysicalScale C (X k) (Y k)

theorem gaussianPhysicalFamily_mass_bound (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      gaussianPhysicalFamilyMass (calibrationForSet S hS) W0 W1 F a X Y W q≤
        K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q := by
  obtain ⟨K,hK,hb⟩ := physicalRowWeight_source_mass a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨K,hK,?_⟩
  intro α ι _ S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  unfold gaussianPhysicalFamilyMass gaussianPhysicalScaleMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ (‖a k‖*(∏i,‖W i (q k i)‖))*(K*lowPhysicalScale (calibrationForSet S hS) (X k) (Y k)) :=
      mul_le_mul_of_nonneg_left (hb S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 (X k) (Y k) (hX k hk) (hY k hk)) (by positivity)
    _ = _ := by ring

theorem gaussianPhysicalFamily_remote_polynomial (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ)
    (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,HasCompactSupport W0→HasCompactSupport W1→
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hremote⟩ := gaussianPhysicalFamily_remote V hV N
  obtain ⟨C1,hC1,hmass⟩ := gaussianPhysicalFamily_mass_bound a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro α ι _ η S hS W0 W1 hW0c hW1c hW0 hW1 hWB0 hWB1 F a D X Y hX hY W q Z A hZ hA
  have hh := hremote η (calibrationForSet S hS) W0 W1 hW0c hW1c F a D X Y
    (fun k hk=>lt_of_lt_of_le zero_lt_one (hX k hk)) (fun k hk=>lt_of_lt_of_le zero_lt_one (hY k hk)) W q Z A hZ hA
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := hmass S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  calc
    _ ≤ C0*(C1*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q)*Z^2/A^N := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
