import OAI.Analysis.CircleDomains.Probability.ArcNullImage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-!
# Null images of local circle-valued traces

Projection modulo one preserves real outer-null sets. A countable family
of null real branches therefore gives a null image in the circle with
its Haar measure of total mass one.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem volume_addCircle_image_eq_zero {A : Set ℝ} (hA : volume A = 0) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' A) = 0 := by
  have hpiece (a : ℝ) :
      volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1))) = 0 := by
    let e := AddCircle.measurableEquivIoc (1 : ℝ) a
    let S : Set (Ioc a (a + 1)) := Subtype.val ⁻¹' A
    have he : MeasurePreserving e volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    have hset : e ⁻¹' S = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1)) := by
      ext y
      constructor
      · intro hy
        refine ⟨(e y).val, ⟨hy, (e y).property⟩, ?_⟩
        exact AddCircle.coe_equivIoc
      · rintro ⟨x, hx, rfl⟩
        change (AddCircle.equivIoc (1 : ℝ) a (x : AddCircle (1 : ℝ))).val ∈ A
        rw [AddCircle.equivIoc_coe_eq hx.2]
        exact hx.1
    rw [← hset, he.measure_preimage_equiv S,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    apply measure_mono_null _ hA
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcover : ((↑) : ℝ → AddCircle (1 : ℝ)) '' A ⊆
      ⋃ k : ℤ, ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        (A ∩ Ioc ((k : ℝ) - 1) ((k : ℝ) - 1 + 1)) := by
    rintro y ⟨x, hx, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨⌈x⌉, x, ⟨hx, ?_⟩, rfl⟩
    have hlo := Int.ceil_lt_add_one x
    have hhi := Int.le_ceil x
    constructor <;> linarith
  apply measure_mono_null hcover
  exact measure_iUnion_null (fun k => hpiece ((k : ℝ) - 1))

/-- A circle-valued image covered by countably many null real branch
images is Haar-null, with no measurability assumption on the image. -/
theorem volume_eq_zero_of_countable_real_branches
    {X : Type*} (F : Set X) (w : X → AddCircle (1 : ℝ))
    (V : ℕ → Set X) (v : ℕ → X → ℝ)
    (hcover : F ⊆ ⋃ n, V n)
    (hbranch : ∀ n, ∀ x ∈ F ∩ V n, (v n x : AddCircle (1 : ℝ)) = w x)
    (hnull : ∀ n, volume (v n '' (F ∩ V n)) = 0) :
    volume (w '' F) = 0 := by
  have himage : w '' F ⊆ ⋃ n,
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' (v n '' (F ∩ V n)) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨n, v n x, ⟨x, ⟨hx, hn⟩, rfl⟩, hbranch n x ⟨hx, hn⟩⟩
  exact measure_mono_null himage
    (measure_iUnion_null (fun n => volume_addCircle_image_eq_zero (hnull n)))

end CircleDomainRigidity

end OAI
