import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackRecovery

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

abbrev StackCoordinates (M H : ℕ) :=
  (Fin (H+1) → ZMod M → Spin) × (Fin H → ZMod M → Spin) × (Fin H → ZMod M → Spin)
noncomputable def coordinatesCurrent (c : StackCoordinates M H) : Edge M →₀ ℤ :=
  stackCurrent c.1 c.2.1 c.2.2
abbrev LegalStack (M H : ℕ) [NeZero M] :=
  {c : StackCoordinates M H // ∀v∈bandSites M H,LocalIce (coordinatesCurrent c) v}
abbrev BandFlow (M H : ℕ) [NeZero M] :=
  {q : Edge M →₀ ℤ // (∀v∈bandSites M H,LocalIce q v) ∧ SupportedAt (bandSites M H) q}

noncomputable def recoverCoordinates (q : Edge M →₀ ℤ) : StackCoordinates M H :=
  (recoverVertical H q,recoverAuxiliary H q,recoverInternal H q)

theorem coordinatesCurrent_injective : Function.Injective (coordinatesCurrent (M:=M) (H:=H)) := by
  rintro ⟨v,a,k⟩ ⟨v',a',k'⟩ he
  obtain ⟨rfl,rfl,rfl⟩:=stackCurrent_injective v v' a k a' k' he
  rfl

instance : Finite (BandFlow M H) := by
  apply Finite.of_injective (fun q : BandFlow M H => recoverCoordinates (H:=H) q.val)
  intro q r h
  apply Subtype.ext
  have he:=congrArg coordinatesCurrent h
  change stackCurrent (recoverVertical H q.val) (recoverAuxiliary H q.val) (recoverInternal H q.val)=
    stackCurrent (recoverVertical H r.val) (recoverAuxiliary H r.val) (recoverInternal H r.val) at he
  simpa only [recover_stack q.val q.property.1 q.property.2,recover_stack r.val r.property.1 r.property.2] using he
noncomputable instance : Fintype (BandFlow M H) := Fintype.ofFinite _

 

noncomputable def stackFlowEquiv (hH : 0<H) : LegalStack M H ≃ BandFlow M H where
  toFun c:=⟨coordinatesCurrent c.val,c.property,stack_supported hH c.val.1 c.val.2.1 c.val.2.2⟩
  invFun q:=⟨recoverCoordinates q.val,by
    have he : coordinatesCurrent (recoverCoordinates (H:=H) q.val)=q.val :=
      recover_stack q.val q.property.1 q.property.2
    rw [he]
    exact q.property.1⟩
  left_inv c:=by
    apply Subtype.ext
    apply coordinatesCurrent_injective
    change stackCurrent (recoverVertical H (coordinatesCurrent c.val))
      (recoverAuxiliary H (coordinatesCurrent c.val)) (recoverInternal H (coordinatesCurrent c.val))= _
    exact recover_stack _ c.property (stack_supported hH c.val.1 c.val.2.1 c.val.2.2)
  right_inv q:=by
    apply Subtype.ext
    exact recover_stack q.val q.property.1 q.property.2

end PolynomialVacuumCylinder

end OAI
