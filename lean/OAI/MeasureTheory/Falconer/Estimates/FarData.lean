import OAI.MeasureTheory.Falconer.Estimates.FarRegionScales
import OAI.MeasureTheory.Falconer.Fourier.JetStateFarBand
import OAI.MeasureTheory.Falconer.Fourier.JetStateFarOriginal
import OAI.MeasureTheory.Falconer.Estimates.NoncomparableCommonBound

namespace OAI

/-! # Geometric data for the actual far branch

These are scale and descriptor conditions to be verified by the recursive
policy. They are not additional published inputs.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

noncomputable def farMinimumLength (d h : ℕ) : ℝ :=
  4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ))

structure JetStateFarData (m : ℕ) (B : ℝ) where
  Q : DyadicCube (m+3)
  unit : Q.side = 1
  ρ : Measure (Space (m+3))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  regular : Regularization.RegularizedProfileData Q ρ N s lam profile
  N_pos : 0 < N
  a : ℕ
  h : ℕ
  t : ℕ
  ah : a ≤ h
  ht : h+6 ≤ t
  tN : t ≤ N
  σ : ℝ
  J : ℕ
  i : ℕ
  q : ℕ
  policy : ℕ → ℝ
  X : List (Fin (m+3) → Bool)
  Y : List (Fin (m+3) → Bool)
  X_length : X.length = a
  Y_length : Y.length = a
  F : Finset PolicyDescriptor
  masks : PolicyDescriptor → Finset (Sphere (m+3))
  separated : ∀ b ∈ F, ∀ w ∈ masks b, ∀ z ∈ masks b, w ≠ z →
    descriptorMaskRadius N σ b/2 ≤ dist w z
  child_list : ∀ b ∈ Finset.Icc (a+9) (h+6),
    PlanarFalconer.policyDescriptorList policy N q b t ⊆ F
  Dq : ℝ
  Dmask : ℝ
  E : ℝ
  Z : ℝ
  Dq_nonneg : 0 ≤ Dq
  Dmask_one : 1 ≤ Dmask
  Z_pos : 0 < Z
  scale_one : 1 ≤ 2*(E+Dq)
  mask_scale : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask
  list_scale : (F.card:ℝ)*B*Dmask ≤ E
  κ : ℝ
  loss : ℝ
  loss_nonneg : 0 ≤ loss
  scale_upper : 2*(E+Dq) ≤ ((2:ℝ)^N)^2
  band_scale : (2*(E+Dq))^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ))
  large_scale : (2*(E+Dq))^2 ≤ (2:ℝ)^t*farMinimumLength (m+3) h
  large_frequency : ((2:ℝ)^N)^κ ≤ (2:ℝ)^t*farMinimumLength (m+3) h
  shell_one : 1 ≤ ((2:ℝ)^t/4)*farMinimumLength (m+3) h
  shell_scale : (2*(E+Dq))^2/(((2:ℝ)^t/4)*farMinimumLength (m+3) h) ≤ ((2:ℝ)^N)^(-κ)

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

noncomputable def originalMeasure (D : JetStateFarData m B) :=
  originalFourPointMeasure (D.Q.descendant D.X) (D.Q.descendant D.Y) D.ρ D.ρ

noncomputable def prefactor (D : JetStateFarData m B) : ℝ :=
  (2:ℝ)^(((m+3:ℕ):ℝ)*((D.t:ℝ)-D.a))*(profileModelMass D.profile D.N D.a)⁻¹^4

noncomputable def kernel (D : JetStateFarData m B) {K L : ℕ}
    (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)) (Ψ : ℝ → ℝ) :=
  jetStateOriginalKernel f g w₀ D.Q D.ρ (fun t => D.profile (t/D.N))
    D.N D.σ D.J D.i D.masks D.Z D.Z D.t Ψ

noncomputable def stationaryKernel (D : JetStateFarData m B) {K L : ℕ}
    (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3))
    (J : ℕ) (Ψ : ℝ → ℝ) :=
  jetStateStationaryKernel f g w₀ D.Q D.ρ (fun t => D.profile (t/D.N))
    D.N D.σ D.J D.i D.masks D.Z J ((2:ℝ)^D.t) Ψ

noncomputable def collisionTerm (D : JetStateFarData m B) (w₀ : Sphere (m+3))
    (C : ℝ) (b : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    ((2:ℝ)^D.N)^(-2*((D.profile ((b:ℝ)/D.N)-((m+3:ℕ):ℝ)/2*(b:ℝ)/D.N)-
      (D.profile ((D.a:ℝ)/D.N)-((m+3:ℕ):ℝ)/2*(D.a:ℝ)/D.N))+4*(((m+3:ℕ):ℝ)+1)*D.lam)) *
    (PlanarFalconer.binKernelConstant * farCollisionMaximum w₀ D.Q D.ρ
      (fun t => D.profile (t/D.N)) D.policy D.N D.σ D.J (D.i+1) D.q b D.t D.X D.Y (b-D.a))

theorem minimumLength_pos (D : JetStateFarData m B) : 0 < farMinimumLength (m+3) D.h := by
  unfold farMinimumLength
  positivity

theorem base_one (D : JetStateFarData m B) : 1 ≤ (2:ℝ)^D.N := one_le_pow₀ (by norm_num)

theorem prefactor_nonneg (D : JetStateFarData m B) : 0 ≤ D.prefactor := by
  unfold prefactor
  positivity

theorem list_scale_mono (D : JetStateFarData m B) {C : ℝ} (hCB : C ≤ B) :
    (D.F.card:ℝ)*C*D.Dmask ≤ D.E :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCB (Nat.cast_nonneg _))
    (zero_le_one.trans D.Dmask_one)).trans D.list_scale

theorem collisionTerm_mono (D : JetStateFarData m B) (w₀ : Sphere (m+3))
    {C C' : ℝ} (hC : C ≤ C') (b : ℕ) :
    D.collisionTerm w₀ C b ≤ D.collisionTerm w₀ C' b := by
  unfold collisionTerm
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (by positivity)

end JetStateFarData
end Falconer

end OAI
