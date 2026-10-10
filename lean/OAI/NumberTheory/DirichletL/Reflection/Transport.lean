import OAI.NumberTheory.DirichletL.Reflection.Independent

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Eis}
noncomputable local instance transportFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] [Fintype κ] in
theorem residualWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) :
    residualWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c R F =
      residualWithFrozen hp hg c (R.image f) (F.image f) := by
  unfold residualWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf R i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem markedWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) :
    markedWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c S F =
      markedWithFrozen hp hg c (S.image f) (F.image f) := by
  unfold markedWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf S i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem ramifiedBlock_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S : Finset κ) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock (fun i => hg (f i)) (fun i => j (f i)) S u m =
      ramifiedBlock hg j (S.image f) u m := by
  unfold ramifiedBlock
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem frozenArgument_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenArgument (fun i => hg (f i)) (fun i => j (f i)) F =
      frozenArgument hg j (F.image f) := by
  unfold frozenArgument
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceRowPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) R F u m =
      sourceRowPhase s hp hg j (R.image f) (F.image f) u m := by
  unfold sourceRowPhase
  rw [residualWithFrozen_transport hp hg c f hf R F,
    ramifiedBlock_transport hg (fun _ => 1) f hf R,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceSlotPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) S F u m =
      sourceSlotPhase s hp hg j (S.image f) (F.image f) u m := by
  unfold sourceSlotPhase
  rw [markedWithFrozen_transport hp hg c f hf S F,
    ramifiedBlock_transport hg (fun _ => 0) f hf S,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

end
end SevenEighths.InverseReflectedPhase

end OAI
