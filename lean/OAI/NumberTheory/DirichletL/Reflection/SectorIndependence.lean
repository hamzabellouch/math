import OAI.NumberTheory.DirichletL.Reflection.Functions
import OAI.NumberTheory.DirichletL.Reflection.Family

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance sectorIndependentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem frozenCore_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenCore (fun i => hp (f i)) (fun i => hg (f i)) c (fun i => j (f i)) F =
      frozenCore hp hg c j (F.image f) := by
  unfold frozenCore
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf F i,Finset.prod_image hf.injOn]

lemma frozenCore_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (c : Eis) (j j' : κ → ℕ) (F : Finset κ) (he : p=q) (hj : j=j') :
    frozenCore hp hg c j F = frozenCore hq hqg c j' F := by
  subst q; subst j'; rfl

lemma ramifiedBlock_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    ramifiedBlock hg j F u m = ramifiedBlock hqg j' F u m := by
  subst q; subst j'; rfl

def frozenColumnProduct {κ : Type*} [Fintype κ]
    {p : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) : ℂ :=
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))

theorem frozenColumnProduct_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) (n b : Ideal Eis) :
    frozenColumnProduct (fun i => hg (f i)) (fun i => j (f i)) F n b =
      frozenColumnProduct hg j (F.image f) n b := by
  unfold frozenColumnProduct
  rw [Finset.prod_image hf.injOn]

lemma frozenColumnProduct_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) (he : p=q) (hj : j=j') :
    frozenColumnProduct hg j F n b = frozenColumnProduct hqg j' F n b := by
  subst q; subst j'; rfl

theorem sourceFrozenPhase_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (hN : (9:Eis)*c ∣ N) (hr : λ₀^2 ∣ (∏ i, p i)-1) (hr₀ : λ₀^2 ∣ (∏ i, q i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hmatrix : ∀ i j, N ∣ D.matrix (fun _ => 1) i j-D₀.matrix (fun _ => 1) i j)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s hp hg j (F.image f) u m =
      sourceFrozenPhase D₀ s hq hqg j' (F.image g) u m := by
  unfold sourceFrozenPhase
  rw [controlled_fixedFactor_eq D D₀ hN hr hr₀ hbase (hmatrix 0 0) (hmatrix 0 1),
    ← frozenCore_transport hp hg c j f hf F,← frozenCore_transport hq hqg c j' g hg' F,
    ← ramifiedBlock_transport hg j f hf F,← ramifiedBlock_transport hqg j' g hg' F,
    frozenCore_congr_functions _ _ _ _ c _ _ F (funext he) (funext hj),
    ramifiedBlock_congr_functions _ _ _ _ F _ _ (funext he) (funext hj)]

theorem sourceColumn_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (hbad : CubicEisenstein.ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, q i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1-D₀.matrix (fun _ => 1) 1 1)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg j (F.image f) u m n b =
      sourceColumn D₀ s hc hqg j' (F.image g) u m n b := by
  unfold sourceColumn
  rw [controlled_static_array_eq D D₀ hc s hbad hr hd u m n b]
  congr 1
  change frozenColumnProduct hg j (F.image f) n b = frozenColumnProduct hqg j' (F.image g) n b
  rw [← frozenColumnProduct_transport hg j f hf F,← frozenColumnProduct_transport hqg j' g hg' F]
  exact frozenColumnProduct_congr_functions _ _ _ _ F n b (funext he) (funext hj)

end
end SevenEighths.InverseReflectedPhase

end OAI
