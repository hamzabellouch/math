import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalTensorDetection

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D E F : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

lemma additiveTensorFiltration_antitone (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B) :
    Antitone (additiveTensorFiltration P Q) := by
  intro u v h
  apply Submodule.span_mono
  rintro x ⟨a,b,f,g,hab,hf,hg,rfl⟩
  exact ⟨a,b,f,g,le_trans h hab,hf,hg,rfl⟩

lemma tensor_map_mem_filtration (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (f : A →ₗ[K] C) (g : B →ₗ[K] D)
    (hf : ∀ w x,x∈P w → f x∈R w) (hg : ∀ w y,y∈Q w → g y∈S w)
    (W : ℤ) (x : A⊗[K]B) (hx : x∈additiveTensorFiltration P Q W) :
    TensorProduct.map f g x∈additiveTensorFiltration R S W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,a,b,hw,ha,hb,rfl⟩:=hx
    rw [TensorProduct.map_tmul]
    exact tmul_mem_additiveTensorFiltration R S hw (hf u a ha) (hg v b hb)
  | zero => rw [map_zero]; exact (additiveTensorFiltration R S W).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (additiveTensorFiltration R S W).add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact (additiveTensorFiltration R S W).smul_mem r hx

lemma interchange_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (U V : ℤ) (x : A⊗[K]B) (y : C⊗[K]D)
    (hx : x∈additiveTensorFiltration P Q U) (hy : y∈additiveTensorFiltration R S V) :
    TensorProduct.tensorTensorTensorComm K A B C D (x⊗ₜ[K]y)∈
    additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (U+V)
  let τ:=TensorProduct.tensorTensorTensorComm K A B C D
  change τ (x⊗ₜ[K]y)∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,a,b,hu,ha,hb,rfl⟩:=hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,z,c,d,hv,hc,hd,rfl⟩:=hy
      change (a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d)∈J
      exact tmul_mem_additiveTensorFiltration _ _ (show U+V≤(u+w)+(v+z) by omega)
        (tmul_mem_additiveTensorFiltration P R (le_refl _) ha hc)
        (tmul_mem_additiveTensorFiltration Q S (le_refl _) hb hd)
    | zero => rw [TensorProduct.tmul_zero,τ.map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add,τ.map_add]; exact J.add_mem hy hz
    | smul r y _ hy => rw [TensorProduct.tmul_smul,τ.map_smul]; exact J.smul_mem r hy
  | zero => rw [TensorProduct.zero_tmul,τ.map_zero]; exact J.zero_mem
  | add x z _ _ hx hz => rw [TensorProduct.add_tmul,τ.map_add]; exact J.add_mem hx hz
  | smul r x _ hx => rw [←TensorProduct.smul_tmul',τ.map_smul]; exact J.smul_mem r hx

lemma lift_mem_filtration (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (hR : Antitone R) (f : A →ₗ[K] B →ₗ[K] C)
    (hf : ∀ u v x y,x∈P u → y∈Q v → f x y∈R (u+v))
    (W : ℤ) (x : A⊗[K]B) (hx : x∈additiveTensorFiltration P Q W) :
    TensorProduct.lift f x∈R W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,a,b,hw,ha,hb,rfl⟩:=hx
    rw [TensorProduct.lift.tmul]
    exact hR hw (hf u v a b ha hb)
  | zero => rw [map_zero]; exact (R W).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (R W).add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact (R W).smul_mem r hx
end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearFiltration
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
noncomputable def next (F G : Submodule ℚ M) : Submodule ℚ F := G.comap F.subtype
def Grade (F G : Submodule ℚ M) := F ⧸ next F G
noncomputable instance (F G : Submodule ℚ M) : AddCommGroup (Grade F G) :=
  inferInstanceAs (AddCommGroup (F ⧸ next F G))
noncomputable instance (F G : Submodule ℚ M) : Module ℚ (Grade F G) :=
  inferInstanceAs (Module ℚ (F ⧸ next F G))
noncomputable def mk (F G : Submodule ℚ M) : F →ₗ[ℚ] Grade F G := (next F G).mkQ
noncomputable def restrict (F : Submodule ℚ M) (G : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) : F →ₗ[ℚ] G :=
  (f.comp F.subtype).codRestrict G (fun x=>h x.val x.property)
noncomputable def map (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) (h' : ∀ x∈F',f x∈G') :
    Grade F F' →ₗ[ℚ] Grade G G' :=
  (next F F').liftQ ((next G G').mkQ.comp (restrict F G f h)) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h' x.val hx))
lemma map_mk (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) (h' : ∀ x∈F',f x∈G') (x : F) :
    map F F' G G' f h h' (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (restrict F G f h x) := rfl
lemma map_eq_zero (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) (h' : ∀ x∈F',f x∈G')
    (hz : ∀ x∈F,f x∈G') : map F F' G G' f h h'=0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk (restrict F G f h x) = (0 : G ⧸ next G G')
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hz x.val x.property)
end ElementaryPositivity.LinearFiltration

end
section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

lemma assoc_mem_tensorFiltration (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (W : ℤ) (x : (A⊗[K]B)⊗[K]C)
    (hx : x∈additiveTensorFiltration (additiveTensorFiltration F G) H W) :
    TensorProduct.assoc K A B C x∈additiveTensorFiltration F (additiveTensorFiltration G H) W := by
  let J:=additiveTensorFiltration F (additiveTensorFiltration G H) W
  let τ:=TensorProduct.assoc K A B C
  change τ x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨u,v,x,z,huv,hx,hz,rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨r,s,x,y,hrs,hx,hy,rfl⟩
      change x⊗ₜ[K](y⊗ₜ[K]z)∈J
      exact tmul_mem_additiveTensorFiltration _ _ (show W≤r+(s+v) by omega) hx
        (tmul_mem_additiveTensorFiltration _ _ (le_refl _) hy hz)
    | zero => rw [TensorProduct.zero_tmul,τ.map_zero]; exact J.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul,τ.map_add]; exact J.add_mem hx hy
    | smul r x _ hx => rw [←TensorProduct.smul_tmul',τ.map_smul]; exact J.smul_mem r hx
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

lemma unassoc_mem_tensorFiltration (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (W : ℤ) (x : A⊗[K](B⊗[K]C))
    (hx : x∈additiveTensorFiltration F (additiveTensorFiltration G H) W) :
    (TensorProduct.assoc K A B C).symm x∈additiveTensorFiltration (additiveTensorFiltration F G) H W := by
  let J:=additiveTensorFiltration (additiveTensorFiltration F G) H W
  let τ:=(TensorProduct.assoc K A B C).symm
  change τ x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨u,v,x,z,huv,hx,hz,rfl⟩
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨r,s,y,z,hrs,hy,hz,rfl⟩
      change (x⊗ₜ[K]y)⊗ₜ[K]z∈J
      exact tmul_mem_additiveTensorFiltration _ _ (show W≤(u+r)+s by omega)
        (tmul_mem_additiveTensorFiltration _ _ (le_refl _) hx hy) hz
    | zero => rw [TensorProduct.tmul_zero,τ.map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add,τ.map_add]; exact J.add_mem hy hz
    | smul r z _ hz => rw [TensorProduct.tmul_smul,τ.map_smul]; exact J.smul_mem r hz
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

end ElementaryPositivity.LinearDetection

end

end OAI
