import OAI.CategoryTheory.ThickClosure.PrincipalModules

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.BackwardStep
section ModuleMaps
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.PrincipalModules
universe u v w
variable {R : Type u} [Ring R] [IsDomain R]

lemma torsion_to_free_zero {M N : ModuleCat.{u} R} [Module.Free R N]
    (hM : IsTorsionModule R M) (f : M ⟶ N) : f = 0 := by
  ext x
  obtain ⟨a, ha, hx⟩ := hM x
  have hf : a • f x = 0 := by rw [← map_smul, hx, map_zero]
  exact (smul_eq_zero.mp hf).resolve_left ha

end ModuleMaps
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.PrincipalModules
universe u v w
variable {R : Type u} [Ring R] [IsDomain R]
variable {E : Type v} [Category.{w} E] [HasZeroObject E] [HasShift E ℤ]
  [Preadditive E] [∀ (n : ℤ), (shiftFunctor E n).Additive]
  [Pretriangulated E] [IsTriangulated E]

theorem homology_backward_step (H : E ⥤ ModuleCat.{u} R) [H.IsHomological]
    {Y F P₁ P₂ V L : E} (f : F ⟶ P₁) (u₁₂ : P₁ ⟶ P₂)
    (w₁₂ : P₂ ⟶ F⟦(1 : ℤ)⟧)
    (h₁₂ : Triangle.mk f u₁₂ w₁₂ ∈ distTriang E)
    (l : L ⟶ P₂) (v : P₂ ⟶ V) (w₂₃ : V ⟶ L⟦(1 : ℤ)⟧)
    (h₂₃ : Triangle.mk l v w₂₃ ∈ distTriang E)
    (r : P₂ ⟶ L) (hlr : l ≫ r = 𝟙 L)
    (hY : IsTorsionModule R (H.obj Y))
    (hL : IsTorsionModule R (H.obj (L⟦(-1 : ℤ)⟧)))
    [Module.Free R (H.obj F)]
    (g : Y ⟶ P₁) (hg : H.map (g ≫ u₁₂) = 0)
    (hgv : g ≫ u₁₂ ≫ v = 0) : H.map g = 0 := by
  obtain ⟨Z, z, w₁₃, h₁₃⟩ := distinguished_cocone_triangle₁ (u₁₂ ≫ v)
  let o := Triangulated.someOctahedron' (rfl : u₁₂ ≫ v = u₁₂ ≫ v) h₁₂ h₂₃ h₁₃
  have hLift : ∃ k : Y ⟶ Z, g = k ≫ z :=
    (Triangle.mk z (u₁₂ ≫ v) w₁₃).coyoneda_exact₂ h₁₃ g hgv
  obtain ⟨k, hk'⟩ := hLift
  have hk : k ≫ z = g := hk'.symm
  have hi : Mono (H.map o.m₁) := by
    let S := (shortComplexOfDistTriangle (Triangle.mk o.m₁ o.m₃ (l ≫ w₁₂)).invRotate
      (inv_rot_of_distTriang _ o.mem)).map H
    have hex : S.Exact := H.map_distinguished_exact _ (inv_rot_of_distTriang _ o.mem)
    let : Module.Free R S.X₂ := inferInstanceAs (Module.Free R (H.obj F))
    have hz : S.f = 0 := torsion_to_free_zero hL S.f
    exact (S.exact_iff_mono hz).mp hex
  have hl : Mono (H.map l) := by
    have hid : H.map l ≫ H.map r = 𝟙 _ := by rw [← H.map_comp, hlr, H.map_id]
    exact @mono_of_mono _ _ _ _ _ (H.map l) (H.map r) (by rw [hid]; infer_instance)
  have hkl : H.map k ≫ H.map o.m₃ = 0 := by
    apply (cancel_mono (H.map l)).mp
    rw [CategoryTheory.Limits.zero_comp, Category.assoc, ← H.map_comp, o.comm₄,
      H.map_comp, ← Category.assoc, ← H.map_comp, hk, ← H.map_comp, hg]
  let S := (shortComplexOfDistTriangle (Triangle.mk o.m₁ o.m₃ (l ≫ w₁₂)) o.mem).map H
  have hex : S.Exact := H.map_distinguished_exact _ o.mem
  let : Mono S.f := hi
  let : Module.Free R S.X₁ := inferInstanceAs (Module.Free R (H.obj F))
  obtain ⟨a, ha⟩ := hex.lift' (H.map k) hkl
  change a ≫ H.map o.m₁ = H.map k at ha
  have ha0 : a = 0 := torsion_to_free_zero hY a
  have hk0 : H.map k = 0 := by
    calc
      H.map k = a ≫ H.map o.m₁ := ha.symm
      _ = (0 : H.obj Y ⟶ H.obj F) ≫ H.map o.m₁ := by rw [ha0]; rfl
      _ = 0 := CategoryTheory.Limits.zero_comp
  rw [← hk, H.map_comp, hk0, CategoryTheory.Limits.zero_comp]

end HahnWilson.BackwardStep

end

end OAI
