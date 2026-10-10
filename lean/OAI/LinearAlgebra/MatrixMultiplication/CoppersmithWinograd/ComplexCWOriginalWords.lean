import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCoppersmithWinograd
import Mathlib.Data.Fintype.Pi

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CWOriginalWords

open scoped BigOperators

abbrev OriginalComponent :=
  {xyz : Fin 3 × Fin 3 × Fin 3 // xyz.1.val + xyz.2.1.val + xyz.2.2.val = 2}

@[simp] theorem originalComponent_card : Fintype.card OriginalComponent = 6 := by
  decide

namespace OriginalComponent

def x (g : OriginalComponent) : Fin 3 := g.val.1
def y (g : OriginalComponent) : Fin 3 := g.val.2.1
def z (g : OriginalComponent) : Fin 3 := g.val.2.2

theorem sum_eq_two (g : OriginalComponent) : g.x.val + g.y.val + g.z.val = 2 :=
  g.property

@[ext] theorem ext {g h : OriginalComponent}
    (hx : g.x = h.x) (hy : g.y = h.y) (hz : g.z = h.z) : g = h := by
  apply Subtype.ext
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_xy {g h : OriginalComponent} (hx : g.x = h.x) (hy : g.y = h.y) : g = h := by
  apply ext hx hy
  apply Fin.ext
  have hg := g.sum_eq_two
  have hh := h.sum_eq_two
  rw [hx, hy] at hg
  omega

theorem eq_of_xz {g h : OriginalComponent} (hx : g.x = h.x) (hz : g.z = h.z) : g = h := by
  apply ext hx _ hz
  apply Fin.ext
  have hg := g.sum_eq_two
  have hh := h.sum_eq_two
  rw [hx, hz] at hg
  omega

theorem eq_of_yz {g h : OriginalComponent} (hy : g.y = h.y) (hz : g.z = h.z) : g = h := by
  apply ext _ hy hz
  apply Fin.ext
  have hg := g.sum_eq_two
  have hh := h.sum_eq_two
  rw [hy, hz] at hg
  omega

@[simp] theorem coefficient (g : OriginalComponent) :
    CoppersmithWinograd.tensor g.x g.y g.z = 1 := by
  simp only [CoppersmithWinograd.tensor, g.sum_eq_two, ite_true]

def coordinate (g : OriginalComponent) : Fin 3 → Fin 3
  | 0 => g.x
  | 1 => g.y
  | 2 => g.z

theorem coordinate_sum (g : OriginalComponent) :
    (∑ side, (g.coordinate side).val) = 2 := by
  simpa [coordinate, Fin.sum_univ_succ, add_assoc] using g.sum_eq_two

theorem coordinate_injective : Function.Injective coordinate := by
  intro g h he
  exact ext (congrFun he 0) (congrFun he 1) (congrFun he 2)

def permute (σ : Equiv.Perm (Fin 3)) (g : OriginalComponent) : OriginalComponent :=
  ⟨(g.coordinate (σ 0), g.coordinate (σ 1), g.coordinate (σ 2)), by
    have h := (Equiv.sum_comp σ (fun side => (g.coordinate side).val)).trans g.coordinate_sum
    simpa [Fin.sum_univ_succ, add_assoc] using h⟩

@[simp] theorem coordinate_permute (σ : Equiv.Perm (Fin 3))
    (g : OriginalComponent) (side : Fin 3) :
    (permute σ g).coordinate side = g.coordinate (σ side) := by
  fin_cases side <;> rfl

theorem permute_injective (σ : Equiv.Perm (Fin 3)) : Function.Injective (permute σ) := by
  intro g h he
  apply coordinate_injective
  funext side
  have hs := congrArg (fun a : OriginalComponent => a.coordinate (σ.symm side)) he
  simpa only [coordinate_permute, Equiv.apply_symm_apply] using hs

end OriginalComponent

theorem tensor_ne_zero_iff (x y z : Fin 3) :
    CoppersmithWinograd.tensor x y z ≠ 0 ↔ x.val + y.val + z.val = 2 := by
  by_cases h : x.val + y.val + z.val = 2 <;> simp [CoppersmithWinograd.tensor, h]

def decodeComponent (x y z : Fin 3) : OriginalComponent :=
  if h : x.val + y.val + z.val = 2 then ⟨(x, y, z), h⟩
  else ⟨(2, 0, 0), by decide⟩

@[simp] theorem decodeComponent_coordinates (g : OriginalComponent) :
    decodeComponent g.x g.y g.z = g := by
  rw [decodeComponent, dite_eq_left g.sum_eq_two]
  apply Subtype.ext
  rfl

section Words

variable {Site : Type*}

def xWord (word : Site → OriginalComponent) : Site → Fin 3 := fun s => (word s).x
def yWord (word : Site → OriginalComponent) : Site → Fin 3 := fun s => (word s).y
def zWord (word : Site → OriginalComponent) : Site → Fin 3 := fun s => (word s).z

def originalWords (word : Site → OriginalComponent) :
    (Site → Fin 3) × (Site → Fin 3) × (Site → Fin 3) :=
  (xWord word, yWord word, zWord word)

def decodeWord (x y z : Site → Fin 3) : Site → OriginalComponent :=
  fun s => decodeComponent (x s) (y s) (z s)

@[simp] theorem decodeWord_originalWords (word : Site → OriginalComponent) :
    decodeWord (xWord word) (yWord word) (zWord word) = word := by
  funext s
  exact decodeComponent_coordinates (word s)

theorem originalWords_decodeWord_of_support (x y z : Site → Fin 3)
    (support : ∀ s, (x s).val + (y s).val + (z s).val = 2) :
    originalWords (decodeWord x y z) = (x, y, z) := by
  apply Prod.ext
  · funext s
    simp [originalWords, xWord, decodeWord, decodeComponent, support s,
      OriginalComponent.x]
  · apply Prod.ext
    · funext s
      simp [originalWords, yWord, decodeWord, decodeComponent, support s,
        OriginalComponent.y]
    · funext s
      simp [originalWords, zWord, decodeWord, decodeComponent, support s,
        OriginalComponent.z]

theorem decodeWord_eq_iff_of_support (x y z : Site → Fin 3)
    (support : ∀ s, (x s).val + (y s).val + (z s).val = 2)
    (word : Site → OriginalComponent) :
    decodeWord x y z = word ↔ x = xWord word ∧ y = yWord word ∧ z = zWord word := by
  constructor
  · intro he
    have h := originalWords_decodeWord_of_support x y z support
    rw [he] at h
    exact ⟨(congrArg Prod.fst h).symm,
      (congrArg (fun words => words.2.1) h).symm,
      (congrArg (fun words => words.2.2) h).symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact decodeWord_originalWords word

theorem originalWords_injective : Function.Injective (originalWords (Site := Site)) := by
  intro first second he
  funext s
  apply OriginalComponent.ext
  · exact congrFun (congrArg Prod.fst he) s
  · exact congrFun (congrArg (fun words => words.2.1) he) s
  · exact congrFun (congrArg (fun words => words.2.2) he) s

theorem xyWords_injective :
    Function.Injective (fun word : Site → OriginalComponent => (xWord word, yWord word)) := by
  intro first second he
  funext s
  exact OriginalComponent.eq_of_xy
    (congrFun (congrArg Prod.fst he) s) (congrFun (congrArg Prod.snd he) s)

theorem xzWords_injective :
    Function.Injective (fun word : Site → OriginalComponent => (xWord word, zWord word)) := by
  intro first second he
  funext s
  exact OriginalComponent.eq_of_xz
    (congrFun (congrArg Prod.fst he) s) (congrFun (congrArg Prod.snd he) s)

theorem yzWords_injective :
    Function.Injective (fun word : Site → OriginalComponent => (yWord word, zWord word)) := by
  intro first second he
  funext s
  exact OriginalComponent.eq_of_yz
    (congrFun (congrArg Prod.fst he) s) (congrFun (congrArg Prod.snd he) s)

def permuteWord (orientation : Site → Equiv.Perm (Fin 3))
    (word : Site → OriginalComponent) : Site → OriginalComponent :=
  fun s => OriginalComponent.permute (orientation s) (word s)

theorem permuteWord_injective (orientation : Site → Equiv.Perm (Fin 3)) :
    Function.Injective (permuteWord orientation) := by
  intro first second he
  funext s
  exact OriginalComponent.permute_injective (orientation s) (congrFun he s)

theorem oriented_originalWords_injective (orientation : Site → Equiv.Perm (Fin 3)) :
    Function.Injective (fun word => originalWords (permuteWord orientation word)) :=
  originalWords_injective.comp (permuteWord_injective orientation)

variable [Fintype Site]

def siteTensor : Tensor ℂ (Site → Fin 3) (Site → Fin 3) (Site → Fin 3) :=
  fun x y z => ∏ s, CoppersmithWinograd.tensor (x s) (y s) (z s)

@[simp] theorem siteTensor_originalWords (word : Site → OriginalComponent) :
    siteTensor (xWord word) (yWord word) (zWord word) = 1 := by
  simp only [siteTensor, xWord, yWord, zWord, OriginalComponent.coefficient,
    Finset.prod_const_one]

theorem siteTensor_originalWords_ne_zero (word : Site → OriginalComponent) :
    siteTensor (xWord word) (yWord word) (zWord word) ≠ 0 := by
  rw [siteTensor_originalWords]
  exact one_ne_zero

theorem siteTensor_oriented_originalWords (orientation : Site → Equiv.Perm (Fin 3))
    (word : Site → OriginalComponent) :
    siteTensor (xWord (permuteWord orientation word))
      (yWord (permuteWord orientation word)) (zWord (permuteWord orientation word)) = 1 :=
  siteTensor_originalWords _

theorem siteTensor_ne_zero_iff (x y z : Site → Fin 3) :
    siteTensor x y z ≠ 0 ↔ ∀ s, (x s).val + (y s).val + (z s).val = 2 := by
  simp only [siteTensor, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const,
    tensor_ne_zero_iff]

def supportedWordEquiv : (Site → OriginalComponent) ≃
    {words : (Site → Fin 3) × (Site → Fin 3) × (Site → Fin 3) //
      siteTensor words.1 words.2.1 words.2.2 ≠ 0} where
  toFun word := ⟨originalWords word, siteTensor_originalWords_ne_zero word⟩
  invFun words s := ⟨(words.val.1 s, words.val.2.1 s, words.val.2.2 s),
    (siteTensor_ne_zero_iff _ _ _).mp words.property s⟩
  left_inv word := by
    funext s
    apply Subtype.ext
    rfl
  right_inv words := by
    apply Subtype.ext
    rfl

section WordCard

local instance : DecidableEq Site := Classical.decEq Site

@[simp] theorem word_card : Fintype.card (Site → OriginalComponent) =
    6 ^ Fintype.card Site := by
  simp only [Fintype.card_pi, originalComponent_card, Finset.prod_const, Finset.card_univ]

end WordCard

theorem siteTensor_eq_power {n : ℕ} (site : Fin n ≃ Site)
    (x y z : Site → Fin 3) :
    siteTensor x y z = Tensor.power CoppersmithWinograd.tensor n
      (fun i => x (site i)) (fun i => y (site i)) (fun i => z (site i)) := by
  exact (site.prod_comp (fun s => CoppersmithWinograd.tensor (x s) (y s) (z s))).symm

end Words

@[simp] theorem power_originalWords (n : ℕ) (word : Fin n → OriginalComponent) :
    Tensor.power CoppersmithWinograd.tensor n (xWord word) (yWord word) (zWord word) = 1 :=
  siteTensor_originalWords word

theorem power_originalWords_ne_zero (n : ℕ) (word : Fin n → OriginalComponent) :
    Tensor.power CoppersmithWinograd.tensor n (xWord word) (yWord word) (zWord word) ≠ 0 :=
  siteTensor_originalWords_ne_zero word

end MatrixMultiplication.Foundation.CWOriginalWords

end

end OAI
