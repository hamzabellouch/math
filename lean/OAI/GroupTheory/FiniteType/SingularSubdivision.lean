import Mathlib
import OAI.GroupTheory.FiniteType.AffineSimplex

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
section
open CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization

abbrev sd (n : ℕ) := AffineChains.subdiv (@center n) n

def simplexChain (n : ℕ) : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains (Std n)).X n :=
  AffineChains.generator (basis n) ≫ sd n

def prismChain (n : ℕ) : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains (Std n)).X (n+1) :=
  AffineChains.generator (basis n) ≫ AffineChains.prism (@center n) n

@[reassoc] lemma simplexChain_affine {m n : ℕ} (v : Fin (m+1) → Std n) :
    simplexChain m ≫ (AffineChains.map (affine v)).f m =
      AffineChains.generator v ≫ AffineChains.subdiv (@center n) m := by
  rw [simplexChain,Category.assoc,AffineChains.subdiv_map (@center m) (@center n)
    (affine v) (fun w => affine_center v w),← Category.assoc,
    AffineChains.generator_map,basis_map_affine]

@[reassoc] lemma prismChain_affine {m n : ℕ} (v : Fin (m+1) → Std n) :
    prismChain m ≫ (AffineChains.map (affine v)).f (m+1) =
      AffineChains.generator v ≫ AffineChains.prism (@center n) m := by
  rw [prismChain,Category.assoc,AffineChains.prism_map (@center m) (@center n)
    (affine v) (fun w => affine_center v w),← Category.assoc,
    AffineChains.generator_map,basis_map_affine]

@[reassoc] lemma simplexChain_face {n : ℕ} (i : Fin (n+2)) :
    simplexChain n ≫ (AffineChains.map (SingularChains.face i)).f n =
      AffineChains.generator (basis (n+1) ∘ i.succAbove) ≫ AffineChains.subdiv (@center (n+1)) n := by
  rw [face_affine]
  exact simplexChain_affine _

@[reassoc] lemma prismChain_face {n : ℕ} (i : Fin (n+2)) :
    prismChain n ≫ (AffineChains.map (SingularChains.face i)).f (n+1) =
      AffineChains.generator (basis (n+1) ∘ i.succAbove) ≫ AffineChains.prism (@center (n+1)) n := by
  rw [face_affine]
  exact prismChain_affine _

@[reassoc] lemma simplexChain_boundary (n : ℕ) :
    simplexChain (n+1) ≫ (AffineChains.chains (Std (n+1))).d (n+1) n =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val •
        (simplexChain n ≫ (AffineChains.map (SingularChains.face i)).f n) := by
  rw [simplexChain,Category.assoc,AffineChains.subdiv_comm,
    ← Category.assoc,AffineChains.generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,simplexChain_face]

@[reassoc] lemma prismChain_boundary (n : ℕ) :
    prismChain (n+1) ≫ (AffineChains.chains (Std (n+1))).d (n+2) (n+1) =
      AffineChains.generator (basis (n+1)) - simplexChain (n+1) -
        ∑ i : Fin (n+2), (-1:ℤ)^i.val •
          (prismChain n ≫ (AffineChains.map (SingularChains.face i)).f (n+1)) := by
  rw [prismChain,Category.assoc,AffineChains.prism_boundary]
  simp only [Preadditive.comp_sub,Category.comp_id]
  rw [← Category.assoc,AffineChains.generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,prismChain_face]
  rfl

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def subdiv (n : ℕ) : (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X n :=
  SingularChains.desc (fun f => simplexChain n ≫ (realize n).f n ≫ (SingularChains.map f).f n)

@[reassoc (attr := simp)] lemma generator_subdiv {n : ℕ} (f : C(Std n,X)) :
    SingularChains.generator f ≫ subdiv n =
      simplexChain n ≫ (realize n).f n ≫ (SingularChains.map f).f n :=
  SingularChains.generator_desc _ _

@[reassoc] lemma generator_affine_subdiv {m n : ℕ} (v : Fin (m+1) → Std n) :
    SingularChains.generator (affine v) ≫ subdiv m =
      AffineChains.generator v ≫ AffineChains.subdiv (@center n) m ≫ (realize n).f m := by
  rw [generator_subdiv,← realize_affine,← Category.assoc,simplexChain_affine,Category.assoc]

lemma subdiv_comm (n : ℕ) :
    subdiv (X := X) (n+1) ≫ (SingularChains.chains X).d (n+1) n =
      (SingularChains.chains X).d (n+1) n ≫ subdiv n := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_subdiv_assoc, (SingularChains.map f).comm]
  rw [← Category.assoc ((realize (n+1)).f (n+1)),(realize (n+1)).comm]
  simp only [Category.assoc]
  rw [simplexChain_boundary_assoc,SingularChains.generator_boundary_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_subdiv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Category.assoc]
  rw [realize_face_assoc]
  congr 2
  rw [SingularChains.map_comp,HomologicalComplex.comp_f]

def subdivision : SingularChains.chains X ⟶ SingularChains.chains X :=
  ChainComplex.ofHom subdiv subdiv_comm

end

open CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def prism (n : ℕ) : (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X (n+1) :=
  SingularChains.desc (fun f => prismChain n ≫ (realize n).f (n+1) ≫ (SingularChains.map f).f (n+1))

@[reassoc (attr := simp)] lemma generator_prism {n : ℕ} (f : C(Std n,X)) :
    SingularChains.generator f ≫ prism n =
      prismChain n ≫ (realize n).f (n+1) ≫ (SingularChains.map f).f (n+1) :=
  SingularChains.generator_desc _ _

@[simp] lemma subdiv_zero : subdiv (X := X) 0 = 𝟙 _ := by
  apply SingularChains.hom_ext
  intro f
  simp only [generator_subdiv,simplexChain,sd,AffineChains.subdiv_zero,Category.comp_id,
    generator_realize_assoc,basis_affine,SingularChains.generator_map,ContinuousMap.comp_id]

@[simp] lemma prism_zero : prism (X := X) 0 = 0 := by
  apply SingularChains.hom_ext
  intro f
  simp [generator_prism,prismChain]

lemma prism_boundary (n : ℕ) :
    prism (X := X) (n+1) ≫ (SingularChains.chains X).d (n+2) (n+1) =
      𝟙 _ - subdiv (n+1) - (SingularChains.chains X).d (n+1) n ≫ prism n := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_prism_assoc,(SingularChains.map f).comm]
  rw [← Category.assoc ((realize (n+1)).f (n+2)),(realize (n+1)).comm]
  simp only [Category.assoc]
  rw [prismChain_boundary_assoc]
  simp only [Preadditive.sub_comp,Preadditive.comp_sub,Category.comp_id,
    Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc]
  rw [generator_realize_assoc,basis_affine,SingularChains.generator_map,ContinuousMap.comp_id,
    generator_subdiv,SingularChains.generator_boundary_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_prism]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [realize_face_assoc]
  rw [SingularChains.map_comp,HomologicalComplex.comp_f]

lemma subdiv_map (f : C(X,Y)) (n : ℕ) :
    subdiv n ≫ (SingularChains.map f).f n = (SingularChains.map f).f n ≫ subdiv n := by
  apply SingularChains.hom_ext
  intro s
  simp only [generator_subdiv_assoc,SingularChains.generator_map_assoc,generator_subdiv,
    SingularChains.map_comp,HomologicalComplex.comp_f]

lemma prism_map (f : C(X,Y)) (n : ℕ) :
    prism n ≫ (SingularChains.map f).f (n+1) = (SingularChains.map f).f n ≫ prism n := by
  apply SingularChains.hom_ext
  intro s
  simp only [generator_prism_assoc,SingularChains.generator_map_assoc,generator_prism,
    SingularChains.map_comp,HomologicalComplex.comp_f]

def homComponent (n m : ℕ) : (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X m :=
  if h : n+1 = m then prism n ≫ eqToHom (congrArg (SingularChains.chains X).X h) else 0

@[simp] lemma homComponent_succ (n : ℕ) : homComponent (X := X) n (n+1) = prism n := by
  simp [homComponent]

def chainHomotopy : Homotopy (𝟙 (SingularChains.chains X)) subdivision where
  hom := homComponent
  zero i j h := by simp only [ComplexShape.down_Rel] at h; simp [homComponent,h]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,zero_add,
        homComponent_succ]
      change 𝟙 _ = prism 0 ≫ _ + subdiv 0
      simp
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,
        homComponent_succ,homComponent_succ]
      change 𝟙 _ = _ + prism (n+1) ≫ _ + subdiv (n+1)
      rw [prism_boundary]
      abel

end SingularSubdivision

namespace AffineSupport
open CategoryTheory AlgebraicTopology Limits
variable {V W : Type} {n m : ℕ}

abbrev gen (v : Fin (n+1) → V) : (AffineChains.chains V).X n := AffineChains.generator v 1

def span (P : (Fin (n+1) → V) → Prop) : Submodule ℤ ((AffineChains.chains V).X n) :=
  Submodule.span ℤ {x | ∃ v, P v ∧ x = gen v}

lemma gen_mem {P : (Fin (n+1) → V) → Prop} (v : Fin (n+1) → V) (hv : P v) : gen v ∈ span P :=
  Submodule.subset_span ⟨v,hv,rfl⟩

lemma span_mono {P Q : (Fin (n+1) → V) → Prop} (h : ∀ v, P v → Q v) : span P ≤ span Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v,hv,rfl⟩
  exact gen_mem v (h v hv)

lemma map_mem {P : (Fin (n+1) → V) → Prop}
    {A : ModuleCat ℤ} {S : Submodule ℤ A}
    (f : (AffineChains.chains V).X n ⟶ A)
    (hf : ∀ v, P v → f (gen v) ∈ S) {c : (AffineChains.chains V).X n} (hc : c ∈ span P) : f c ∈ S := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨v,hv,rfl⟩ := hx; exact hf v hv
  | zero => simp
  | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
  | smul a x hx ih => simpa using S.smul_mem a ih

lemma induction_on (S : Submodule ℤ ((AffineChains.chains V).X n))
    (hS : ∀ v : Fin (n+1) → V, gen v ∈ S) (c : (AffineChains.chains V).X n) : c ∈ S := by
  let : Module ℤ (((AffineChains.chains V).X n) ⧸ S) := Submodule.Quotient.module S
  let q : (AffineChains.chains V).X n ⟶ ModuleCat.of ℤ (((AffineChains.chains V).X n) ⧸ S) :=
    ModuleCat.ofHom S.mkQ
  have hq : q = 0 := by
    apply AffineChains.hom_ext
    intro v
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.mkQ (gen v) = 0
    change gen v ∈ LinearMap.ker S.mkQ
    rw [Submodule.ker_mkQ]
    exact hS v
  have hc := congrArg (fun h => h c) hq
  change S.mkQ c = 0 at hc
  have hc' : c ∈ LinearMap.ker S.mkQ := hc
  simpa only [Submodule.ker_mkQ] using hc'

@[simp] lemma map_gen (v : Fin (n+1) → V) (f : V → W) :
    (AffineChains.map f).f n (gen v) = gen (f ∘ v) := by
  exact congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains W).X n => h 1)
    (AffineChains.generator_map v f)

@[simp] lemma cone_gen (v : Fin (n+1) → V) (x : V) :
    AffineChains.cone x n (gen v) = gen (Fin.cons x v) := by
  exact congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains V).X (n+1) => h 1)
    (AffineChains.generator_cone v x)

lemma boundary_gen (v : Fin (n+2) → V) :
    (AffineChains.chains V).d (n+1) n (gen v) =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val • gen (v ∘ i.succAbove) := by
  have h := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains V).X n => h 1)
    (AffineChains.generator_boundary v)
  simpa using h

lemma subdiv_gen (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V) (v : Fin (n+2) → V) :
    AffineChains.subdiv b (n+1) (gen v) =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val •
        AffineChains.cone (b v) n (AffineChains.subdiv b n (gen (v ∘ i.succAbove))) := by
  have h := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains V).X (n+1) => h 1)
    (AffineChains.generator_subdiv_succ b v)
  change AffineChains.subdiv b (n+1) (gen v) =
    AffineChains.cone (b v) n (AffineChains.subdiv b n ((AffineChains.chains V).d (n+1) n (gen v))) at h
  rw [h,boundary_gen]
  simp

end AffineSupport

end

end OAI
