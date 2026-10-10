import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ModelAssembly

namespace OAI

section

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalProjection

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
abbrev c := ComplexShape.down ℕ
variable (K : HomologicalComplex₂ C c c)

noncomputable def projection (p q n : ℕ) : (K.total c).X n ⟶ (K.X p).X q :=
  K.totalDesc (fun i j _ => if hi : i=p then if hj : j=q then
    eqToHom (by subst i; subst j; rfl) else 0 else 0)

@[reassoc (attr := simp)] lemma inclusion_projection (p q n : ℕ) (h : p+q=n) :
    K.ιTotal c p q n h ≫ projection K p q n = 𝟙 _ := by
  simp [projection]

@[reassoc] lemma inclusion_projection_of_ne (i j p q n : ℕ) (h : i+j=n)
    (hne : (i,j) ≠ (p,q)) :
    K.ιTotal c i j n h ≫ projection K p q n = 0 := by
  simp only [projection,ι_totalDesc]
  split_ifs with hi hj
  · exact False.elim (hne (Prod.ext hi hj))
  all_goals rfl

abbrev Index (n : ℕ) := ↥(Finset.HasAntidiagonal.antidiagonal n)
noncomputable abbrev inclusion (n : ℕ) (i : Index n) :=
  K.ιTotal c i.val.1 i.val.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp i.property)
noncomputable abbrev proj (n : ℕ) (i : Index n) := projection K i.val.1 i.val.2 n

lemma sum_projection_inclusion (n : ℕ) :
    (∑ i : Index n,proj K n i ≫ inclusion K n i) = 𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  let j : Index n := ⟨(p,q),Finset.HasAntidiagonal.mem_antidiagonal.mpr hpq⟩
  rw [Preadditive.comp_sum]
  rw [Finset.sum_eq_single j]
  · change K.ιTotal c p q n hpq ≫ (proj K n j ≫ inclusion K n j) = _
    simp [j,←Category.assoc]
  · intro i _ hij
    rw [←Category.assoc,inclusion_projection_of_ne]
    · simp
    · exact fun h => hij (Subtype.ext h.symm)
  · simp

lemma hom_ext {A : C} {n : ℕ} {f g : A ⟶ (K.total c).X n}
    (h : ∀ i : Index n,f ≫ proj K n i = g ≫ proj K n i) : f=g := by
  rw [←Category.comp_id f,←Category.comp_id g,←sum_projection_inclusion K n]
  simp only [Preadditive.comp_sum,←Category.assoc,h]

@[reassoc] lemma D₁_projection (p q : ℕ) :
    K.D₁ c (p+q+1) (p+q) ≫ projection K p q (p+q) =
      projection K (p+1) q (p+q+1) ≫ (K.d (p+1) p).f q := by
  apply total.hom_ext
  intro i j hij
  change i+j=p+q+1 at hij
  cases i with
  | zero =>
    have hj : j=p+q+1 := by omega
    subst j
    rw [←Category.assoc,TotalHomotopy.ι_d₁_zero,zero_comp,
      inclusion_projection_of_ne_assoc K 0 (p+q+1) (p+1) q _ _ (by intro h; have := congrArg Prod.fst h; omega),zero_comp]
  | succ i =>
    rw [←Category.assoc,TotalHomotopy.ι_d₁_succ i j (p+q) (by omega),Category.assoc]
    by_cases hi : i=p
    · subst i
      have : j=q := by omega
      subst j
      simp
    · rw [inclusion_projection_of_ne K i j p q _ _ (by intro h; exact hi (congrArg Prod.fst h)),comp_zero,
        inclusion_projection_of_ne_assoc K (i+1) j (p+1) q _ _ (by intro h; have := congrArg Prod.fst h; omega),zero_comp]

@[reassoc] lemma D₂_projection (p q : ℕ) :
    K.D₂ c (p+q+1) (p+q) ≫ projection K p q (p+q) =
      ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+q+1) ≫ (K.X p).d (q+1) q) := by
  apply total.hom_ext
  intro i j hij
  change i+j=p+q+1 at hij
  cases j with
  | zero =>
    have hi : i=p+q+1 := by omega
    subst i
    rw [←Category.assoc,TotalHomotopy.ι_d₂_zero,zero_comp,Linear.comp_units_smul,←Category.assoc,
      inclusion_projection_of_ne K (p+q+1) 0 p (q+1) _ _ (by intro h; have := congrArg Prod.snd h; omega),zero_comp,smul_zero]
  | succ j =>
    rw [←Category.assoc,TotalHomotopy.ι_d₂_succ i j (p+q) (by omega)]
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,Category.assoc]
    by_cases hi : i=p
    · subst i
      have : j=q := by omega
      subst j
      simp
    · rw [inclusion_projection_of_ne K i j p q _ _ (by intro h; exact hi (congrArg Prod.fst h)),comp_zero,smul_zero,
        inclusion_projection_of_ne_assoc K i (j+1) p (q+1) _ _ (by intro h; exact hi (congrArg Prod.fst h)),zero_comp,smul_zero]

@[reassoc] lemma d_projection (p q : ℕ) :
    (K.total c).d (p+q+1) (p+q) ≫ projection K p q (p+q) =
      projection K (p+1) q (p+q+1) ≫ (K.d (p+1) p).f q +
      ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+q+1) ≫ (K.X p).d (q+1) q) := by
  change (K.D₁ _ _ _ + K.D₂ _ _ _) ≫ _ = _
  rw [Preadditive.add_comp,D₁_projection,D₂_projection]

end TotalProjection

end

section

namespace FilteredFiniteness

universe u
variable {R : Type u} [CommRing R]
variable {A B C E : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]

lemma finite_of_ker_le [IsNoetherianRing R] (f : A →ₗ[R] B) (g : A →ₗ[R] E)
    (hf : Function.Surjective f) (hker : LinearMap.ker g ≤ LinearMap.ker f)
    [Module.Finite R E] : Module.Finite R B := by
  have : Module.Finite R (LinearMap.range g) :=
    Module.Finite.of_injective (LinearMap.range g).subtype Subtype.val_injective
  have : Module.Finite R (A ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  let φ := (LinearMap.ker g).liftQ f hker
  exact Module.Finite.of_surjective φ (by
    intro b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨(LinearMap.ker g).mkQ a,rfl⟩)

structure Data where
  d : A →ₗ[R] B
  e : B →ₗ[R] C
  de : e.comp d=0
  FA : ℤ → Submodule R A
  FB : ℤ → Submodule R B
  FC : ℤ → Submodule R C
  monoB : Monotone FB

namespace Data
variable (K : Data (R:=R) (A:=A) (B:=B) (C:=C))

def dCycles : A →ₗ[R] LinearMap.ker K.e :=
  K.d.codRestrict _ (fun x => by
    change K.e (K.d x)=0
    exact congrArg (fun f : A →ₗ[R] C => f x) K.de)

abbrev H := LinearMap.ker K.e ⧸ LinearMap.range K.dCycles

def π : LinearMap.ker K.e →ₗ[R] K.H := (LinearMap.range K.dCycles).mkQ

def cycles (p : ℤ) : Submodule R (LinearMap.ker K.e) :=
  (K.FB p).comap (LinearMap.ker K.e).subtype

def πp (p : ℤ) : K.cycles p →ₗ[R] K.H := K.π.comp (K.cycles p).subtype

def filtration (p : ℤ) : Submodule R K.H := LinearMap.range (K.πp p)

lemma filtration_mono : Monotone K.filtration := by
  intro p q hpq y hy
  obtain ⟨x,rfl⟩ := hy
  exact ⟨⟨x.val,K.monoB hpq x.property⟩,rfl⟩

def Z₂ (p : ℤ) : Submodule R B := K.FB p ⊓ (K.FC (p-2)).comap K.e

def B₂ (p : ℤ) : Submodule R B :=
  (K.FB (p-1) ⊓ (K.FC (p-2)).comap K.e) ⊔ ((K.FA (p+1)).map K.d ⊓ K.FB p)

lemma B₂_le_Z₂ (p : ℤ) : K.B₂ p ≤ K.Z₂ p := by
  apply sup_le
  · exact inf_le_inf (K.monoB (by omega)) le_rfl
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1
    refine ⟨hx.2,?_⟩
    change K.e (K.d y) ∈ K.FC (p-2)
    have he : K.e (K.d y)=0 := congrArg (fun f : A →ₗ[R] C => f y) K.de
    rw [he]
    exact (K.FC _).zero_mem

abbrev E₂ (p : ℤ) := K.Z₂ p ⧸ (K.B₂ p).comap (K.Z₂ p).subtype

def lead (p : ℤ) : K.cycles p →ₗ[R] K.E₂ p :=
  ((K.B₂ p).comap (K.Z₂ p).subtype).mkQ.comp
    (((LinearMap.ker K.e).subtype.comp (K.cycles p).subtype).codRestrict _ (fun x => by
      refine ⟨x.property,?_⟩
      change K.e x.val.val∈K.FC (p-2)
      rw [x.val.property]
      exact (K.FC _).zero_mem))

lemma lead_eq_zero {p : ℤ} (x : K.cycles p) :
    K.lead p x=0 ↔ x.val.val∈K.B₂ p := by
  exact Submodule.Quotient.mk_eq_zero ((K.B₂ p).comap (K.Z₂ p).subtype)

lemma lower_of_lead_zero {p : ℤ} (x : K.cycles p) (hx : K.lead p x=0) :
    K.πp p x∈K.filtration (p-1) := by
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp ((K.lead_eq_zero x).mp hx)
  obtain ⟨a,ha,haz⟩ := hz.1
  have hza : K.e z=0 := by
    rw [←haz]
    exact congrArg (fun f : A →ₗ[R] C => f a) K.de
  have hey : K.e y=0 := by
    have he := congrArg K.e hyz
    rw [map_add,hza,add_zero,x.val.property] at he
    exact he
  let y' : K.cycles (p-1) := ⟨⟨y,hey⟩,hy.1⟩
  refine ⟨y',?_⟩
  change K.π ⟨y,hey⟩=K.π x.val
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-a,?_⟩
  apply Subtype.ext
  change K.d (-a)=y-x.val.val
  rw [map_neg,haz,←hyz]
  abel

variable [IsNoetherianRing R]

lemma finite_step (p : ℤ) [Module.Finite R (K.filtration (p-1))]
    [Module.Finite R (K.E₂ p)] : Module.Finite R (K.filtration p) := by
  let S : Submodule R (K.filtration p) :=
    (K.filtration (p-1)).submoduleOf (K.filtration p)
  have : Module.Finite R S := Module.Finite.equiv
    (Submodule.submoduleOfEquivOfLe (K.filtration_mono (by omega : p-1≤p))).symm
  let f : K.cycles p →ₗ[R] (K.filtration p ⧸ S) := S.mkQ.comp (K.πp p).rangeRestrict
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
  have hk : LinearMap.ker (K.lead p) ≤ LinearMap.ker f := by
    intro x hx
    change f x=0
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    exact K.lower_of_lead_zero x hx
  have : Module.Finite R (K.filtration p ⧸ S) := finite_of_ker_le f (K.lead p) hf hk
  exact Module.Finite.of_submodule_quotient S

lemma finite_H (N : ℕ) (hzero : K.FB 0=⊥) (htop : K.FB (N+1)=⊤)
    (hfinite : ∀ p : ℕ, p≤N → Module.Finite R (K.E₂ (p+1))) : Module.Finite R K.H := by
  have hz : K.filtration 0=⊥ := by
    apply le_antisymm _ bot_le
    rintro y ⟨x,rfl⟩
    have hx : x=0 := by
      apply Subtype.ext; apply Subtype.ext
      exact (Submodule.mem_bot R).mp (hzero ▸ x.property)
    rw [hx,map_zero]
    exact Submodule.zero_mem _
  have hfg : ∀ p : ℕ, p≤N+1 → Module.Finite R (K.filtration p) := by
    intro p hp
    induction p with
    | zero => rw [Nat.cast_zero,hz]; infer_instance
    | succ p ih =>
      have := ih (by omega)
      have := hfinite p (by omega)
      have he : (p:ℤ)+1-1=(p:ℤ) := by omega
      have : Module.Finite R (K.filtration ((p:ℤ)+1-1)) := by rw [he]; infer_instance
      exact K.finite_step (p+1)
  have hh : K.filtration (N+1)=⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.dCycles) y
    exact ⟨⟨z,by change z.val∈K.FB (N+1); rw [htop]; trivial⟩,rfl⟩
  have := hfg (N+1) le_rfl
  exact Module.Finite.of_surjective (K.filtration ((N+1:ℕ):ℤ)).subtype (by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    have he : ((N+1:ℕ):ℤ)=(N:ℤ)+1 := by omega
    rw [he,hh]
    trivial)

end Data
end FilteredFiniteness

end

end

end OAI
