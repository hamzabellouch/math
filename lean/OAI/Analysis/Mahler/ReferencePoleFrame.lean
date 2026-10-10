import OAI.Analysis.Mahler.ReferencePole

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def poleFrameVector (k : ℕ) : Fin 1 ⊕ WedgePowerSlots k → ComplexEuclidean (k+1) :=
  Sum.elim (fun _ => EuclideanSpace.single 0 I)
    (fun s => EuclideanSpace.single (pairSlotEquiv k s).1.succ
      (if (pairSlotEquiv k s).2 = 0 then 1 else I))

lemma poleFrameVector_tangent {k : ℕ} (s : Fin 1 ⊕ WedgePowerSlots k) :
    poleFrameVector k s ∈ sphereTangent (referencePole k) := by
  rw [referencePole_tangent_iff]
  cases s <;> simp [poleFrameVector]

noncomputable def poleTangentFrame (k : ℕ) :
    Fin 1 ⊕ WedgePowerSlots k → sphereTangent (referencePole k) :=
  fun s => ⟨poleFrameVector k s, poleFrameVector_tangent s⟩

lemma pole_covector_matrix (k : ℕ) :
    Matrix.of (fun a b : Fin 1 ⊕ WedgePowerSlots k =>
      (Sum.elim
        (fun _ : Fin 1 => (imagCoordinate (0 : Fin (k+1))).comp (sphereTangent (referencePole k)).subtype)
        (pairedCovectors (fun j : Fin k => fun i =>
          (coordinatePair j.succ i).comp (sphereTangent (referencePole k)).subtype))) b
        (poleTangentFrame k a)) = (1 : Matrix (Fin 1 ⊕ WedgePowerSlots k) (Fin 1 ⊕ WedgePowerSlots k) ℂ) := by
  ext a b
  simp only [Matrix.of_apply]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp [poleTangentFrame, poleFrameVector, Matrix.one_apply]
      exact Subsingleton.elim _ _
    | inr b =>
      obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv k b = (j,β) := ⟨_,_,rfl⟩
      fin_cases β <;> simp [pairedCovectors, hb, coordinatePair, poleTangentFrame,
        poleFrameVector]
  | inr a =>
    cases b with
    | inl b => simp [poleTangentFrame, poleFrameVector]
    | inr b =>
      obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv k a = (i,α) := ⟨_,_,rfl⟩
      obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv k b = (j,β) := ⟨_,_,rfl⟩
      have hab : a = b ↔ i = j ∧ α = β := by
        rw [← (pairSlotEquiv k).injective.eq_iff, ha, hb, Prod.mk.injEq]
      fin_cases α <;> fin_cases β <;>
        simp [pairedCovectors, poleTangentFrame, poleFrameVector, ha, hb, coordinatePair,
          PiLp.single_apply, Matrix.one_apply, hab, eq_comm] <;> split_ifs <;> simp_all

lemma referencePole_boundary_value (k : ℕ) :
    wedge (tangentForm (referencePole k)
      (oneForm (dcLinear (normEnergy (k+1))) (referencePole k)).toAlternatingMap)
      (wedgePower (tangentForm (referencePole k)
        (extDeriv (oneForm (dcLinear (normEnergy (k+1)))) (referencePole k)).toAlternatingMap) k)
      (poleTangentFrame k) = (k.factorial : ℂ)/2 := by
  rw [referencePole_boundary]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, covectorVolume_apply,
    pole_covector_matrix, Matrix.det_one, mul_one]

lemma ambientFinEquiv_real_zero (k : ℕ) :
    ambientFinEquiv k (Sum.inl 0) = 0 := by
  apply Fin.ext
  rfl

lemma ambientFinEquiv_imag_zero (k : ℕ) :
    ambientFinEquiv k (Sum.inl 1) = (boundaryFinEquiv k (Sum.inl 0)).succ := by
  apply Fin.ext
  rfl

lemma ambientFinEquiv_tail (k : ℕ) (s : WedgePowerSlots k) :
    ambientFinEquiv k (Sum.inr s) = (boundaryFinEquiv k (Sum.inr s)).succ := by
  apply Fin.ext
  change 2 + (powerFinEquiv k s).val = (1 + (powerFinEquiv k s).val) + 1
  omega

noncomputable def poleFrameFin (k : ℕ) : Fin (2*k+1) → ComplexEuclidean (k+1) :=
  poleFrameVector k ∘ (boundaryFinEquiv k).symm

lemma poleFrameFin_volume (k : ℕ) :
    sphereVolume k (Matrix.vecCons (referencePole k) (poleFrameFin k)) = 1 := by
  have he : (Matrix.vecCons (referencePole k) (poleFrameFin k)) ∘ ambientFinEquiv k =
      (interleavedBasis : WedgePowerSlots (k+1) → ComplexEuclidean (k+1)) := by
    funext s
    cases s with
    | inl j =>
      fin_cases j
      · change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inl 0)) = _
        rw [ambientFinEquiv_real_zero]
        simp [Matrix.vecCons, referencePole, interleavedBasis, pairSlotEquiv]
        rfl
      · change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inl 1)) = _
        rw [ambientFinEquiv_imag_zero]
        simp [Matrix.vecCons, poleFrameFin, interleavedBasis, pairSlotEquiv, poleFrameVector]
        rfl
    | inr s =>
      change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inr s)) = _
      rw [ambientFinEquiv_tail]
      simp [Matrix.vecCons, poleFrameFin, interleavedBasis, pairSlotEquiv, poleFrameVector]
      rfl
  simp only [sphereVolume, AlternatingMap.domDomCongr_apply, he, interleavedVolume_basis]

lemma referencePole_boundaryFin_value (k : ℕ) :
    boundaryFormFin (dcLinear (normEnergy (k+1))) (referencePole k) (poleFrameFin k) =
      (k.factorial : ℂ)/2 := by
  have h := referencePole_boundary_value k
  have he : (poleFrameFin k ∘ boundaryFinEquiv k) = poleFrameVector k := by
    ext s; simp [poleFrameFin]
  simp only [boundaryFormFin, AlternatingMap.domDomCongr_apply, he]
  simpa only [tangentForm, ← wedgePower_compLinearMap, ← wedge_compLinearMap,
    AlternatingMap.compLinearMap_apply, Submodule.subtype_apply, poleTangentFrame] using h

end Mahler

end OAI
