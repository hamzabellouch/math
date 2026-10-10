import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCodeDyads

namespace OAI

/-! Exact finite partition of the chosen retained frequencies by their
supported prefix. The remaining index is the literal primary free variable. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCodeFreeSet {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) : Finset Eisenstein :=
  (T.filter (fun z => metaplecticCodePrefix z = p)).image (fun z => z.2.2.val)

lemma metaplectic_code_ext {r : Eisenstein} {x y : MetaplecticRetainedCode r}
    (hp : metaplecticCodePrefix x = metaplecticCodePrefix y)
    (hw : x.2.2.val = y.2.2.val) : x = y := by
  have hd : x.1 = y.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.1) hp
  have hs : x.2.1 = y.2.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hp
  have hf : x.2.2 = y.2.2 := Subtype.ext hw
  exact Prod.ext hd (Prod.ext hs hf)

lemma metaplectic_decode_of_prefix {r : Eisenstein} {z : MetaplecticRetainedCode r}
    {p : MetaplecticDyadPrefix r} (hp : metaplecticCodePrefix z = p) :
    metaplecticRetainedDecode r z = (metaplecticPrefixArgument r p.2 z.2.2.val,p.1) := by
  have hd : z.1 = p.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.1) hp
  have hs : z.2.1 = p.2 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hp
  simp only [metaplecticRetainedDecode,hd,hs]

lemma metaplectic_mem_codeFreeSet {r : Eisenstein} {T : Finset (MetaplecticRetainedCode r)}
    {p : MetaplecticDyadPrefix r} {w : Eisenstein} :
    w ∈ metaplecticCodeFreeSet T p ↔
      ∃ z ∈ T, metaplecticCodePrefix z = p ∧ z.2.2.val = w := by
  simp only [metaplecticCodeFreeSet,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨z,⟨hz,hp⟩,hw⟩
    exact ⟨z,hz,hp,hw⟩
  · rintro ⟨z,hz,hp,hw⟩
    exact ⟨z,⟨hz,hp⟩,hw⟩

lemma metaplectic_codeFreeSet_primary {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) {w : Eisenstein} (hw : w ∈ metaplecticCodeFreeSet T p) :
    primary w := by
  obtain ⟨z,_,_,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
  exact z.2.2.property

lemma metaplectic_code_prefix_sum {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) (F : MetaplecticDualArgument × PrimaryArgument → ℂ) :
    (∑ z ∈ T.filter (fun z => metaplecticCodePrefix z = p), F (metaplecticRetainedDecode r z)) =
      ∑ w ∈ metaplecticCodeFreeSet T p, F (metaplecticPrefixArgument r p.2 w,p.1) := by
  rw [metaplecticCodeFreeSet,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [metaplectic_decode_of_prefix (Finset.mem_filter.mp hz).2]
  · intro x hx y hy hxy
    exact metaplectic_code_ext
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy

/-- No extra multiplicity is introduced by separating the fixed support
parameters from the free primary argument. -/
theorem metaplectic_code_partition {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (F : MetaplecticDualArgument × PrimaryArgument → ℂ) :
    (∑ z ∈ T, F (metaplecticRetainedDecode r z)) =
      ∑ p ∈ T.image metaplecticCodePrefix,
        ∑ w ∈ metaplecticCodeFreeSet T p, F (metaplecticPrefixArgument r p.2 w,p.1) := by
  calc
    _ = ∑ p ∈ T.image metaplecticCodePrefix,
        ∑ z ∈ T.filter (fun z => metaplecticCodePrefix z = p),
          F (metaplecticRetainedDecode r z) :=
      (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image metaplecticCodePrefix)
        (g := metaplecticCodePrefix)
        (fun z hz => by
          simp only [Finset.mem_image]
          exact ⟨z,hz,rfl⟩)
        (fun z => F (metaplecticRetainedDecode r z))).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => metaplectic_code_prefix_sum T p F)

lemma metaplectic_codeFreeSet_dyad {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) {I : ℝ}
    (hT : ∀ z ∈ T, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
      metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) :
    ∀ w ∈ metaplecticCodeFreeSet T p,
      (I/metaplecticFreeScale p)/2 ≤ norm w ∧ norm w ≤ I/metaplecticFreeScale p := by
  intro w hw
  obtain ⟨z,hz,hp,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
  apply metaplectic_free_dyad p (primary_ne_zero z.2.2.property)
  rw [←metaplectic_decode_of_prefix hp]
  exact hT z hz

lemma metaplectic_codeFreeSet_length_one {r : Eisenstein}
    (T : Finset (MetaplecticRetainedCode r)) {p : MetaplecticDyadPrefix r}
    (hp : p ∈ T.image metaplecticCodePrefix) {I : ℝ}
    (hT : ∀ z ∈ T, metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) :
    1 ≤ I/metaplecticFreeScale p := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
  apply metaplectic_free_length_one (r := r) (metaplecticCodePrefix z) z.2.2.property
  rw [←metaplectic_decode_of_prefix (rfl : metaplecticCodePrefix z = metaplecticCodePrefix z)]
  exact hT z hz

end CubicFirstMoment

end

end OAI
