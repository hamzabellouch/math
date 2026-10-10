import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

noncomputable def middleInsert (a : A) (d : D) :
    C⊗[K]B →ₗ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  TensorProduct.map (TensorProduct.mk K A C a) ((TensorProduct.mk K B D).flip d)

lemma middleInsert_tmul (a : A) (d : D) (c : C) (b : B) :
    middleInsert a d (c⊗ₜ[K]b)=(a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d) := rfl

lemma middleInsert_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (u z W : ℤ) (a : A) (d : D) (ha : a∈P u) (hd : d∈S z)
    (x : C⊗[K]B) (hx : x∈additiveTensorFiltration R Q W) :
    middleInsert a d x∈
      additiveTensorFiltration (additiveTensorFiltration P R)
        (additiveTensorFiltration Q S) (u+W+z) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (u+W+z)
  change middleInsert a d x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,w,c,b,hw,hc,hb,rfl⟩:=hx
    rw [middleInsert_tmul]
    exact tmul_mem_additiveTensorFiltration _ _ (show u+W+z≤(u+v)+(w+z) by omega)
      (tmul_mem_additiveTensorFiltration P R (le_refl _) ha hc)
      (tmul_mem_additiveTensorFiltration Q S (le_refl _) hb hd)
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D : Type*} [Field K]
  [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]

noncomputable def middleEmbedding : C⊗[K]B →ₐ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeLeft

lemma middleEmbedding_mul (r : C⊗[K]B) (a : A) (c : C) (b : B) (d : D) :
    middleEmbedding r*((a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d))=
      middleInsert a d (r*(c⊗ₜ[K]b)) := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => rw [map_add,add_mul,add_mul,map_add,hr,hs]
  | tmul x y =>
    change ((1⊗ₜ[K]x)⊗ₜ[K](y⊗ₜ[K]1))*((a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d))=_
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,middleInsert_tmul]

lemma middleAction_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (δ : ℤ) (r : C⊗[K]B)
    (hr : ∀ v w c b,c∈R v → b∈Q w → r*(c⊗ₜ[K]b)∈additiveTensorFiltration R Q (v+w+δ))
    (W : ℤ) (x : (A⊗[K]C)⊗[K](B⊗[K]D))
    (hx : x∈additiveTensorFiltration (additiveTensorFiltration P R)
      (additiveTensorFiltration Q S) W) :
    middleEmbedding r*x∈additiveTensorFiltration (additiveTensorFiltration P R)
      (additiveTensorFiltration Q S) (W+δ) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (W+δ)
  let L : (A⊗[K]C)⊗[K](B⊗[K]D) →ₗ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
    LinearMap.mulLeft K (middleEmbedding r)
  change L x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,z,f,g,hw,hf,hg,rfl⟩:=hx
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨p,v,a,c,hpv,ha,hc,rfl⟩:=hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨w,t,b,d,hwt,hb,hd,rfl⟩:=hg
        change middleEmbedding r*((a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d))∈J
        rw [middleEmbedding_mul]
        exact additiveTensorFiltration_antitone _ _ (show W+δ≤p+(v+w+δ)+t by omega)
          (middleInsert_mem_filtration P Q R S p t (v+w+δ) a d ha hd _ (hr v w c b hc hb))
      | zero => rw [TensorProduct.tmul_zero,L.map_zero]; exact J.zero_mem
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add,L.map_add]; exact J.add_mem hx hy
      | smul s x _ hx => rw [TensorProduct.tmul_smul,L.map_smul]; exact J.smul_mem s hx
    | zero => rw [TensorProduct.zero_tmul,L.map_zero]; exact J.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul,L.map_add]; exact J.add_mem hx hy
    | smul s x _ hx => rw [←TensorProduct.smul_tmul',L.map_smul]; exact J.smul_mem s hx
  | zero => rw [L.map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [L.map_add]; exact J.add_mem hx hy
  | smul s x _ hx => rw [L.map_smul]; exact J.smul_mem s hx

end ElementaryPositivity.LinearDetection

end

end OAI
