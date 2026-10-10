import OAI.Geometry.RuledCovering.HyperbolicCover

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsParallelogram P) (a : E) :
    IsParallelogram ((fun x => a + x) '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨a+c, u, v, hli, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨s, hs, t, ht, by abel_nf⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨c+s•u+t•v, ⟨s, hs, t, ht, rfl⟩, by abel_nf⟩

def rotatedPlane (u : Space) (R : Space ≃ₗᵢ[ℝ] Space) :
    ((Submodule.span ℝ ({u} : Set Space))ᗮ) ≃ₗᵢ[ℝ]
      ((Submodule.span ℝ ({R u} : Set Space))ᗮ) where
  toFun b := ⟨R b, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, R.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp b.property⟩
  invFun b := ⟨R.symm b, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [← R.inner_map_map u (R.symm b), R.apply_symm_apply]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp b.property⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp
  map_add' b c := by ext; simp
  map_smul' a b := by ext; simp
  norm_map' b := R.norm_map b

def Cylinder.rotate (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) : Cylinder where
  axis := R C.axis
  unit_axis := by rw [R.norm_map, C.unit_axis]
  base := rotatedPlane C.axis R '' C.base

lemma Cylinder.rotate_carrier (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).carrier = R '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    exact ⟨(b : Space) + t • C.axis, ⟨b, hb, t, rfl⟩, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    exact ⟨rotatedPlane C.axis R b, ⟨b, hb, rfl⟩, t, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩

lemma Cylinder.rotate_area (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).area = C.area := by
  change volume.real (rotatedPlane C.axis R '' C.base) = volume.real C.base
  have he := (rotatedPlane C.axis R).measurePreserving.setIntegral_image_emb
    (rotatedPlane C.axis R).toHomeomorph.measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.rotate_parallelogram {C : Cylinder} (hC : C.parallelogram)
    (R : Space ≃ₗᵢ[ℝ] Space) : (C.rotate R).parallelogram :=
  hC.linear_image (rotatedPlane C.axis R).toLinearMap (rotatedPlane C.axis R).injective

def Cylinder.transversePart (C : Cylinder) (q : Space) :
    ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) :=
  ⟨q - (inner ℝ C.axis q) • C.axis, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, C.unit_axis]
    simp⟩

def Cylinder.translate (C : Cylinder) (q : Space) : Cylinder where
  axis := C.axis
  unit_axis := C.unit_axis
  base := (fun b => C.transversePart q + b) '' C.base

lemma Cylinder.translate_carrier (C : Cylinder) (q : Space) :
    (C.translate q).carrier = (fun x => q + x) '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    refine ⟨(b : Space) + (t - inner ℝ C.axis q) • C.axis,
      ⟨b, hb, _, rfl⟩, ?_⟩
    change q + ((b : Space) + (t - inner ℝ C.axis q) • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + t • C.axis
    module
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    refine ⟨C.transversePart q + b, ⟨b, hb, rfl⟩, t + inner ℝ C.axis q, ?_⟩
    change q + ((b : Space) + t • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + (t + inner ℝ C.axis q) • C.axis
    module

lemma Cylinder.translate_area (C : Cylinder) (q : Space) :
    (C.translate q).area = C.area := by
  change volume.real ((fun b => C.transversePart q + b) '' C.base) = volume.real C.base
  have he := (measurePreserving_add_left volume (C.transversePart q)).setIntegral_image_emb
    (Homeomorph.addLeft (C.transversePart q)).measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.translate_parallelogram {C : Cylinder} (hC : C.parallelogram) (q : Space) :
    (C.translate q).parallelogram := hC.translate (C.transversePart q)

/-- Exact Euclidean isometry transport preserves finite covers and perpendicular area. -/
lemma HasFiniteCover.isometry {S : Set Space} {A : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (F : Space ≃ᵢ Space) :
    HasFiniteCover Cylinder.parallelogram (F '' S) A := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := hc
  let R := F.toRealLinearIsometryEquiv
  have hF (x : Space) : F x = F 0 + R x := by
    simp [R, IsometryEquiv.toRealLinearIsometryEquiv_apply]
  let D : Fin n → Cylinder := fun i => ((C i).rotate R).translate (F 0)
  refine ⟨n, D, fun i => Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram (hC i) R) (F 0), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change F x ∈ (((C i).rotate R).translate (F 0)).carrier
    rw [Cylinder.translate_carrier, Cylinder.rotate_carrier]
    exact ⟨R x, ⟨x, hi, rfl⟩, (hF x).symm⟩
  · simpa [familyArea, D, Cylinder.translate_area, Cylinder.rotate_area] using hcost

end RuledApproximation

end

end OAI
