import OAI.Analysis.Cotype.BinaryCoordinates

namespace OAI

noncomputable section

namespace Cotype
variable {n r s : ℕ}

def binaryDualTransport (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) :
    Module.Dual (ZMod 2) (BinarySpace n) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinarySpace n) where
  toFun φ := φ.comp H.symm.toLinearMap
  invFun φ := φ.comp H.toLinearMap
  left_inv := by intro φ; ext x; simp
  right_inv := by intro φ; ext x; simp
  map_add' := by intro φ ψ; rfl
  map_smul' := by intro c φ; rfl

def binaryContragredient (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) :
    BinarySpace n ≃ₗ[ZMod 2] BinarySpace n :=
  coordinateDual.trans ((binaryDualTransport H).trans coordinateDual.symm)

theorem binaryContragredient_pairing (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n)
    (u v : BinarySpace n) :
    coordinateDual (binaryContragredient H v) (H u) = coordinateDual v u := by
  change coordinateDual (coordinateDual.symm ((coordinateDual v).comp H.symm.toLinearMap)) (H u) = _
  rw [coordinateDual.apply_symm_apply]
  simp

def walshSymmetryOfLinear (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) : WalshSymmetry n :=
  ⟨((cubeBinaryEquiv n).trans (H.toEquiv.trans (cubeBinaryEquiv n).symm),
    (cubeBinaryEquiv n).trans ((binaryContragredient H).toEquiv.trans (cubeBinaryEquiv n).symm)), by
    intro u v
    simp only [Equiv.trans_apply, character_binary_dot, Equiv.apply_symm_apply]
    exact congrArg binarySign (binaryContragredient_pairing H _ _)⟩

theorem walsh_paired_frames_orbit (U U' : Fin r → Cube n) (V V' : Fin s → Cube n)
    (hU : BinaryFrame U) (hU' : BinaryFrame U')
    (hV : BinaryFrame V) (hV' : BinaryFrame V')
    (hpair : ∀ i j, character (V j) (U i) = character (V' j) (U' i)) :
    ∃ g : WalshSymmetry n,
      (∀ i, primalSymmetry g (U i) = U' i) ∧ ∀ j, dualSymmetry g (V j) = V' j := by
  have hv : LinearIndependent (ZMod 2) (fun j => coordinateDual (cubeBinaryEquiv n (V j))) :=
    hV.map' coordinateDual.toLinearMap (LinearMap.ker_eq_bot.mpr coordinateDual.injective)
  have hv' : LinearIndependent (ZMod 2) (fun j => coordinateDual (cubeBinaryEquiv n (V' j))) :=
    hV'.map' coordinateDual.toLinearMap (LinearMap.ker_eq_bot.mpr coordinateDual.injective)
  have hp (i) (j) : coordinateDual (cubeBinaryEquiv n (V j)) (cubeBinaryEquiv n (U i)) =
      coordinateDual (cubeBinaryEquiv n (V' j)) (cubeBinaryEquiv n (U' i)) := by
    apply binarySign_injective
    simpa only [← character_binary_dot] using hpair i j
  obtain ⟨H,hHu,hHv⟩ := paired_frames_orbit
    (fun i => cubeBinaryEquiv n (U i)) (fun i => cubeBinaryEquiv n (U' i))
    (fun j => coordinateDual (cubeBinaryEquiv n (V j)))
    (fun j => coordinateDual (cubeBinaryEquiv n (V' j))) hU hU' hv hv' hp
  refine ⟨walshSymmetryOfLinear H, ?_, ?_⟩
  · intro i
    change (cubeBinaryEquiv n).symm (H (cubeBinaryEquiv n (U i))) = U' i
    rw [hHu, Equiv.symm_apply_apply]
  · intro j
    apply (cubeBinaryEquiv n).injective
    change cubeBinaryEquiv n ((cubeBinaryEquiv n).symm
      (binaryContragredient H (cubeBinaryEquiv n (V j)))) = _
    rw [Equiv.apply_symm_apply]
    apply coordinateDual.injective
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := H.surjective x
    exact (binaryContragredient_pairing H y _).trans (hHv j y).symm

end Cotype

end

end OAI
