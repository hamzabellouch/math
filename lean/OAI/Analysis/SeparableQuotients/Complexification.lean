import OAI.Analysis.SeparableQuotients.NegativeReal

namespace OAI

noncomputable section

/- Complexification by real-linear maps from ℂ with the operator norm and real coordinates f(1), f(i). -/
namespace SeparableQuotient
open scoped Classical
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

def Complexify := ℂ →L[ℝ] X
namespace Complexify
def toCLM (f : Complexify X) : ℂ →L[ℝ] X := f
instance : CoeFun (Complexify X) (fun _ => ℂ → X) := ⟨fun f => toCLM X f⟩
@[ext] lemma ext {f g : Complexify X} (h : ∀ z, f z = g z) : f = g := ContinuousLinearMap.ext h

instance : NormedAddCommGroup (Complexify X) := inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] X))
instance : NormedSpace ℝ (Complexify X) := inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] X))
instance [CompleteSpace X] : CompleteSpace (Complexify X) := inferInstanceAs (CompleteSpace (ℂ →L[ℝ] X))

@[simp] lemma add_apply (f g : Complexify X) (z : ℂ) : (f+g) z = f z + g z := rfl
@[simp] lemma zero_apply (z : ℂ) : (0 : Complexify X) z = 0 := rfl
@[simp] lemma apply_zero (f : Complexify X) : f 0 = 0 := (toCLM X f).map_zero
@[simp] lemma apply_add (f : Complexify X) (z w : ℂ) : f (z+w) = f z + f w := (toCLM X f).map_add _ _
@[simp] lemma apply_smul (f : Complexify X) (r : ℝ) (z : ℂ) : f (r • z) = r • f z := (toCLM X f).map_smul _ _

def cmul (c : ℂ) (f : Complexify X) : Complexify X := (toCLM X f).comp ((ContinuousLinearMap.mul ℝ ℂ) c)
instance : SMul ℂ (Complexify X) := ⟨cmul X⟩
@[simp] lemma smul_apply (c : ℂ) (f : Complexify X) (z : ℂ) :
    (c • f : Complexify X) z = f (c*z) := rfl

instance : Module ℂ (Complexify X) where
  one_smul f := by ext z; simp
  mul_smul c d f := by ext z; simp [mul_assoc,mul_left_comm]
  smul_zero c := by ext z; rfl
  smul_add c f g := by ext z; rfl
  add_smul c d f := by ext z; simp [add_mul]
  zero_smul f := by ext z; simp

instance : NormedSpace ℂ (Complexify X) where
  norm_smul_le c f := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖f (c*z)‖ ≤ (‖c‖*‖f‖)*‖z‖
    calc
      _ ≤ ‖f‖*‖c*z‖ := (toCLM X f).le_opNorm _
      _ = _ := by rw [norm_mul]; ring

instance : IsScalarTower ℝ ℂ (Complexify X) where
  smul_assoc r c f := by
    ext z
    change f ((r • c)*z) = r • f (c*z)
    rw [smul_mul_assoc,apply_smul]

instance : SMulCommClass ℝ ℂ (Complexify X) where
  smul_comm r c f := by
    ext z
    change r • f (c*z) = (r • f : ℂ →L[ℝ] X) (c*z)
    rfl

def pairMap : Complexify X →L[ℝ] X × X :=
  (ContinuousLinearMap.apply ℝ X (1 : ℂ)).prod (ContinuousLinearMap.apply ℝ X Complex.I)

def ofPair (p : X × X) : Complexify X :=
  Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2

lemma pairMap_ofPair (p : X × X) : pairMap X (ofPair X p) = p := by
  apply Prod.ext
  · change ((Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2) (1 : ℂ)) = p.1
    simp
  · change ((Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2) Complex.I) = p.2
    simp

lemma ofPair_pairMap (f : Complexify X) : ofPair X (pairMap X f) = f := by
  ext z
  change z.re • f 1 + z.im • f Complex.I = f z
  rw [← apply_smul,← apply_smul,← apply_add]
  congr 1
  apply Complex.ext <;> simp

def pairEquiv [CompleteSpace X] : Complexify X ≃L[ℝ] (X × X) :=
  (LinearEquiv.ofBijective (pairMap X).toLinearMap
    ⟨Function.HasLeftInverse.injective ⟨ofPair X,ofPair_pairMap X⟩,
      Function.HasRightInverse.surjective ⟨ofPair X,pairMap_ofPair X⟩⟩).toContinuousLinearEquivOfContinuous
    (pairMap X).continuous

lemma infinite [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X) :
    ¬ FiniteDimensional ℂ (Complexify X) := by
  intro hh
  let := hh
  let : FiniteDimensional ℝ (Complexify X) := FiniteDimensional.trans ℝ ℂ _
  let : FiniteDimensional ℝ (X × X) := FiniteDimensional.of_injective (pairEquiv X).symm.toLinearMap (pairEquiv X).symm.injective
  exact hX (FiniteDimensional.of_injective (LinearMap.inl ℝ X X) (by intro x y h; exact Prod.mk.inj h |>.1))

end Complexify
end SeparableQuotient

end

end OAI
