import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialControlledKernel

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation.InitialTargetKernel

open Tensor LocalMaps PolynomialLocalConstruction

variable {X Y Z RawLabel Label : Type*}

def Chosen (window : X → Prop) (read : X → RawLabel) (embed : Label → RawLabel)
    (label : Label) (x : X) : Prop :=
  window x ∧ read x = embed label

def Eligible (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (label : Label) : X → Y → Z → Prop :=
  fun x y z => Chosen PX lx embed label x ∧ Chosen PY ly embed label y ∧
    Chosen PZ lz embed label z

def auxiliary : Tensor ℂ Unit Unit Unit := fun _ _ _ => 1

theorem auxiliary_rank : RankAtMost auxiliary 1 := by
  have haux : auxiliary = rankOne (fun _ : Unit => (1 : ℂ))
      (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ)) := by
    funext x y z
    simp only [auxiliary, rankOne, one_mul]
  rw [haux]
  exact rankOne_rankAtMost _ _ _

def sideMap (window : X → Prop) (read : X → RawLabel) (embed : Label → RawLabel) :
    X → (Label × (Fin 1 × Fin 1)) → Unit → Polynomial ℂ := by
  classical
  exact fun x output _ => Polynomial.C (if Chosen window read embed output.1 x then 1 else 0)

theorem sideMap_degree (window : X → Prop) (read : X → RawLabel)
    (embed : Label → RawLabel) (x : X) (output : Label × (Fin 1 × Fin 1)) (input : Unit) :
    (sideMap window read embed x output input).degree ≤ (0 : ℕ) := by
  classical
  exact Polynomial.degree_C_le

def rawLeading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) :
    Tensor ℂ (X × (Label × (Fin 1 × Fin 1)))
      (Y × (Label × (Fin 1 × Fin 1))) (Z × (Label × (Fin 1 × Fin 1))) := by
  classical
  exact fun x y z => if Chosen PX lx embed x.2.1 x.1 ∧
      Chosen PY ly embed y.2.1 y.1 ∧ Chosen PZ lz embed z.2.1 z.1 then 1 else 0

def previousLeading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) :
    Tensor ℂ (X × (Label × (Fin 1 × Fin 1)))
      (Y × (Label × (Fin 1 × Fin 1))) (Z × (Label × (Fin 1 × Fin 1))) := by
  classical
  exact fun x y z => if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
    Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 then 1 else 0

theorem kernel_eq_C_rawLeading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1))) :
    kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
      x y z = Polynomial.C (rawLeading PX PY PZ lx ly lz embed x y z) := by
  classical
  by_cases hx : Chosen PX lx embed x.2.1 x.1 <;>
    by_cases hy : Chosen PY ly embed y.2.1 y.1 <;>
    by_cases hz : Chosen PZ lz embed z.2.1 z.1 <;>
    simp [kernel, fiberTransform, sideMap, auxiliary, rawLeading, hx, hy, hz]

theorem rawLeading_eq_previousLeading
    (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1)))
    (hs : support x.1 y.1 z.1) :
    rawLeading PX PY PZ lx ly lz embed x y z =
      previousLeading PX PY PZ lx ly lz embed x y z := by
  classical
  have hcondition :
      (Chosen PX lx embed x.2.1 x.1 ∧ Chosen PY ly embed y.2.1 y.1 ∧
        Chosen PZ lz embed z.2.1 z.1) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1) := by
    constructor
    · rintro ⟨hx, hy, hz⟩
      have hsync := compatible x.1 y.1 z.1 hs hx.1 hy.1 hz.1
      have hxy : x.2.1 = y.2.1 := injective (hx.2.symm.trans (hsync.1.trans hy.2))
      have hxz : x.2.1 = z.2.1 := injective (hx.2.symm.trans (hsync.2.trans hz.2))
      refine ⟨hxy, hxz, hx, ?_, ?_⟩
      · simpa only [hxy] using hy
      · simpa only [hxz] using hz
    · rintro ⟨hxy, hxz, hx, hy, hz⟩
      refine ⟨hx, ?_, ?_⟩
      · simpa only [hxy] using hy
      · simpa only [hxz] using hz
  simp only [rawLeading, previousLeading, hcondition]

theorem kernel_leading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1)))
    (hs : support x.1 y.1 z.1) :
    (kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
      x y z).coeff 0 = previousLeading PX PY PZ lx ly lz embed x y z := by
  rw [kernel_eq_C_rawLeading, Polynomial.coeff_C_zero]
  exact rawLeading_eq_previousLeading PX PY PZ lx ly lz embed injective support
    compatible x y z hs

theorem kernel_low (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1)))
    (j : ℕ) (hj : j < 0) :
    (kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
      x y z).coeff j = 0 :=
  (Nat.not_lt_zero j hj).elim

theorem previousLeading_ne_zero_iff (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1))) :
    previousLeading PX PY PZ lx ly lz embed x y z ≠ 0 ↔
      x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 := by
  classical
  by_cases h : x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 <;>
    simp [previousLeading, h]

theorem kernel_substitution (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (original : Tensor ℂ X Y Z) :
    fiberTransform (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
        (fun x y z => Polynomial.C (Tensor.product original auxiliary x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)) := by
  have h := fiberTransform_originalScale (sideMap PX lx embed)
    (sideMap PY ly embed) (sideMap PZ lz embed)
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (auxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C (Tensor.product original auxiliary x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C (auxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [hinput]
  simpa only [kernel] using h

end MatrixMultiplication.Foundation.InitialTargetKernel

end

end OAI
