import Mathlib

namespace OAI


namespace Problem355.Lattice

theorem kernel_relIndex_mul_image_index
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (H : AddSubgroup G) (f : G →+ A) (hf : Function.Surjective f) :
    (H ⊓ f.ker).relIndex f.ker * (H.map f).index = H.index := by
  rw [AddSubgroup.inf_relIndex_right, AddSubgroup.index_map,
    f.range_eq_top_of_surjective hf, AddSubgroup.index_top, mul_one]
  simpa only [AddSubgroup.relIndex_sup_left] using
    (AddSubgroup.relIndex_mul_index (show H ≤ H ⊔ f.ker from le_sup_left))

theorem kernel_relIndex_mul_image_generator
    {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (f : G →+ ℤ) (hf : Function.Surjective f)
    (g : ℤ) (himage : H.map f = AddSubgroup.zmultiples g) :
    (H ⊓ f.ker).relIndex f.ker * g.natAbs = H.index := by
  simpa only [himage, Int.index_zmultiples] using kernel_relIndex_mul_image_index H f hf

end Problem355.Lattice

end OAI
