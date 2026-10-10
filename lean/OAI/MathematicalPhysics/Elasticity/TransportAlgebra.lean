import OAI.MathematicalPhysics.Elasticity.Carleman

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section CGO
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
def normal (θ : Fin 3 → ℂ) (u : Fin 3 → A) : A := ∑ i, θ i • u i
def direction (θ : Fin 3 → ℂ) (a : A) : A := ∑ i, θ i • D i a
def leadingR (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A) (i : Fin 3) : A :=
  2*m*direction D θ (u i)+direction D θ m*u i+
    θ i • ((lam+m)*b+∑ j, D j m*u j)
def leadingS (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A) : A :=
  2*(lam+m+m)*direction D θ b+2*direction D θ (lam+m)*b+
    4*(∑ i, D i m*direction D θ (u i))+2*(∑ i, direction D θ (D i m)*u i)
def leadingP (θ : Fin 3 → ℂ) (m f : A) : A :=
  2*m*direction D θ f+direction D θ m*f

lemma shifted_lap_expansion (z : Fin 3 → ℂ) (f : A) :
    lapT (shifted D z) f=lap D f+2*direction D z f+(∑ i, z i*z i) • f := by
  simp only [lapT,lap,direction,shifted_apply,map_add,Derivation.map_smul,Fin.sum_univ_three]
  simp only [Algebra.smul_def,map_add,map_mul]
  ring

lemma leading_normal (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (lam m : A) (u : Fin 3 → A) (b : A) :
    normal θ (leadingR D θ lam m u b)=leadingP D θ m (normal θ u) := by
  have hz : ∑ i, algebraMap ℂ A (θ i)*algebraMap ℂ A (θ i)=0 := by
    simpa only [map_sum,map_mul,map_zero] using congrArg (algebraMap ℂ A) hθ
  simp only [Fin.sum_univ_three] at hz
  simp only [normal,leadingR,leadingP,direction,Fin.sum_univ_three,map_add,Derivation.map_smul]
  simp only [Algebra.smul_def]
  linear_combination ((lam+m)*b+(D 0 m*u 0+D 1 m*u 1+D 2 m*u 2))*hz

lemma RT_phase_polynomial (θ : Fin 3 → ℂ) (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A) :
    RT D (shifted D (τ • θ)) lam m u b =
      (fun i => R D lam m u b i+τ • leadingR D θ lam m u b i+
        (τ*τ*(∑ j, θ j*θ j)) • (m*u i)) := by
  funext i
  simp only [RT,R,cmT,cm,lapT,lap,shifted_apply,direction,leadingR,
    Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,map_add,Derivation.map_smul,smul_add]
  simp only [Algebra.smul_def,map_add,map_mul]
  ring

lemma ST_phase_polynomial (θ : Fin 3 → ℂ) (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hD : ∀ i j f, D i (D j f)=D j (D i f)) :
    ST D (shifted D (τ • θ)) lam m u b = S D lam m u b+τ • leadingS D θ lam m u b+
      (τ*τ*(∑ j, θ j*θ j)) • ((lam+m+m)*b+2*∑ i, D i m*u i) := by
  simp only [ST,S,lapT,lap,shifted_apply,direction,leadingS,
    Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,map_add,Derivation.map_smul,smul_add]
  simp only [Algebra.smul_def,map_add,map_mul]
  rw [hD 1 0 m,hD 2 0 m,hD 2 1 m]
  ring

lemma RT_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A) (i : Fin 3) :
    RT D (shifted D (τ • θ)) lam m u b i=R D lam m u b i+τ • leadingR D θ lam m u b i := by
  have hh := congrFun (RT_phase_polynomial D θ τ lam m u b) i
  simpa only [hθ,mul_zero,zero_smul,add_zero] using hh

lemma ST_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hD : ∀ i j f, D i (D j f)=D j (D i f)) :
    ST D (shifted D (τ • θ)) lam m u b=S D lam m u b+τ • leadingS D θ lam m u b := by
  simpa only [hθ,mul_zero,zero_smul,add_zero] using ST_phase_polynomial D θ τ lam m u b hD
/-- The exact first-order compatibility identity used by the physical recursion. -/
lemma transport_compatibility (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hD : ∀ i j f, D i (D j f)=D j (D i f)) :
    div D (leadingR D θ lam m u b)+normal θ (R D lam m u b)-leadingS D θ lam m u b =
      P D m (normal θ u)+leadingP D θ m (div D u-b) := by
  have htwo (i : Fin 3) : D i (2 : A)=0 := (D i).map_natCast 2
  simp only [div,normal,leadingR,leadingS,leadingP,direction,R,P,cm,lap,
    Fin.sum_univ_three,map_add,map_sub,Derivation.map_smul,partial_mul,htwo,zero_mul,zero_add]
  simp only [hD 1 0,hD 2 0,hD 2 1,Algebra.smul_def]
  ring
end CGO
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section FiniteExpansion
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def truncation (h : ℂ) (N : ℕ) (a : ℕ → V) : V := ∑ j ∈ Finset.range (N+1), h^j • a j
lemma truncation_zero (h : ℂ) (a : ℕ → V) : truncation h 0 a=a 0 := by simp [truncation]
lemma truncation_succ (h : ℂ) (N : ℕ) (a : ℕ → V) :
    truncation h (N+1) a=truncation h N a+h^(N+1) • a (N+1) := by
  exact Finset.sum_range_succ _ _

/-- Exact finite telescoping, not an asymptotic formal series. -/
lemma truncated_transport (L T : V →ₗ[ℂ] W) (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → V)
    (h₀ : T (a 0)=0) (hrec : ∀ j<N, T (a (j+1))=-L (a j)) :
    L (truncation h N a)+h⁻¹ • T (truncation h N a)=h^N • L (a N) := by
  induction N with
  | zero => simp only [truncation_zero,h₀,smul_zero,add_zero,pow_zero,one_smul]
  | succ N ih =>
    have hn := ih (fun j hj => hrec j (hj.trans (Nat.lt_succ_self N)))
    have hp : h⁻¹*h^(N+1)=h^N := by rw [pow_succ]; field_simp
    simp only [truncation_succ,map_add,map_smul,smul_add,smul_smul,hp,hrec N (Nat.lt_succ_self N),smul_neg]
    rw [← hn]
    abel
end FiniteExpansion
section PhysicalRecursion
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
abbrev Amplitude (A : Type*) := (Fin 3 → A) × A

def Rpair (lam m : A) : Amplitude A →ₗ[ℂ] (Fin 3 → A) where
  toFun a := R D lam m a.1 a.2
  map_add' a b := by
    funext i
    simp only [R,lap,cm,Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,Finset.sum_add_distrib,mul_add,add_mul]
    ring
  map_smul' c a := by
    funext i
    simp only [R,lap,cm,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Derivation.map_smul]
    simp only [Algebra.smul_def,Fin.sum_univ_three,RingHom.id_apply]
    ring

def leadingRpair (θ : Fin 3 → ℂ) (lam m : A) : Amplitude A →ₗ[ℂ] (Fin 3 → A) where
  toFun a := leadingR D θ lam m a.1 a.2
  map_add' a b := by
    funext i
    simp only [leadingR,direction,Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,smul_add,
      Finset.sum_add_distrib,mul_add,add_mul]
    ring
  map_smul' c a := by
    funext i
    simp only [leadingR,direction,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Derivation.map_smul]
    simp only [Algebra.smul_def,Fin.sum_univ_three,RingHom.id_apply]
    ring

def divergenceDefect : Amplitude A →ₗ[ℂ] A where
  toFun a := div D a.1-a.2
  map_add' a b := by
    simp only [div,Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,Finset.sum_add_distrib]
    abel
  map_smul' c a := by
    simp only [div,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Derivation.map_smul,Finset.smul_sum,smul_sub,
      RingHom.id_apply]

def normalPair (θ : Fin 3 → ℂ) : Amplitude A →ₗ[ℂ] A where
  toFun a := normal θ a.1
  map_add' a b := by
    simp only [normal,Prod.fst_add,Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [normal,Prod.smul_fst,Pi.smul_apply,smul_comm (θ _) c,Finset.smul_sum,RingHom.id_apply]

lemma truncated_R (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (lam m : A)
    (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → Amplitude A)
    (h₀ : leadingR D θ lam m (a 0).1 (a 0).2=0)
    (hrec : ∀ j<N, leadingR D θ lam m (a (j+1)).1 (a (j+1)).2=-R D lam m (a j).1 (a j).2) (i : Fin 3) :
    RT D (shifted D (h⁻¹ • θ)) lam m (truncation h N a).1 (truncation h N a).2 i=
      h^N • R D lam m (a N).1 (a N).2 i := by
  rw [RT_null_expansion D θ hθ]
  exact congrFun (truncated_transport (Rpair D lam m) (leadingRpair D θ lam m) h hh N a h₀ hrec) i

lemma divT_expansion (θ : Fin 3 → ℂ) (h : ℂ) (u : Fin 3 → A) :
    divT (shifted D (h • θ)) u=div D u+h • normal θ u := by
  simp only [divT,div,normal,shifted_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib,smul_smul,Finset.smul_sum]

/-- The physical divergence constraint telescopes independently. -/
lemma truncated_divergence (θ : Fin 3 → ℂ) (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → Amplitude A)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N, normal θ (a (j+1)).1=-(div D (a j).1-(a j).2)) :
    divT (shifted D (h⁻¹ • θ)) (truncation h N a).1 =
      (truncation h N a).2+h^N • (div D (a N).1-(a N).2) := by
  rw [divT_expansion]
  have ht := truncated_transport (divergenceDefect D) (normalPair θ) h hh N a h₀ hrec
  change div D (truncation h N a).1-(truncation h N a).2+h⁻¹ • normal θ (truncation h N a).1=h^N • (div D (a N).1-(a N).2) at ht
  linear_combination ht
end PhysicalRecursion
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma RT_scalar_add (T : Fin 3 → A →ₗ[ℂ] A) (lam m : A) (u : Fin 3 → A) (b d : A) (i : Fin 3) :
    RT D T lam m u (b+d) i=RT D T lam m u b i+(lam+m)*T i d+D i lam*d := by
  simp only [RT,map_add,mul_add]
  ring

theorem truncated_physical_residual (hD : ∀ i j f, D i (D j f)=D j (D i f))
    (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (lam m : A)
    (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → Amplitude A)
    (hR₀ : leadingR D θ lam m (a 0).1 (a 0).2=0)
    (hRrec : ∀ j<N, leadingR D θ lam m (a (j+1)).1 (a (j+1)).2=-R D lam m (a j).1 (a j).2)
    (hn₀ : normal θ (a 0).1=0)
    (hnrec : ∀ j<N, normal θ (a (j+1)).1=-(div D (a j).1-(a j).2)) (i : Fin 3) :
    LT (shifted D (h⁻¹ • θ)) lam m (truncation h N a).1 i =
      h^N • (R D lam m (a N).1 (a N).2 i +
        (lam+m)*D i (div D (a N).1-(a N).2)+D i lam*(div D (a N).1-(a N).2)+
        (h⁻¹*θ i) • ((lam+m)*(div D (a N).1-(a N).2))) := by
  rw [shifted_physical_expansion D _ _ _ _ hD i,
    truncated_divergence D θ h hh N a hn₀ hnrec,RT_scalar_add,
    truncated_R D θ hθ lam m h hh N a hR₀ hRrec i]
  simp only [shifted_apply,Pi.smul_apply,smul_eq_mul,Derivation.map_smul]
  simp only [Algebra.smul_def]
  ring

lemma P_neg (m f : A) : P D m (-f)=-P D m f := by
  simp only [P,lap,map_neg,mul_neg,Finset.sum_neg_distrib,neg_add_rev,add_comm]

/-- Compatibility at every recursive stage follows from both augmented rows
and the preceding physical constraint. No extra compatibility is assumed. -/
theorem recursive_normal_compatibility (hD : ∀ i j f, D i (D j f)=D j (D i f))
    (θ : Fin 3 → ℂ) (lam m : A) (u v : Fin 3 → A) (b c : A)
    (hR : leadingR D θ lam m u b=-R D lam m v c)
    (hS : leadingS D θ lam m u b=-S D lam m v c)
    (hn : normal θ u=-(div D v-c)) :
    normal θ (R D lam m u b)=leadingP D θ m (div D u-b) := by
  have hc := transport_compatibility D θ lam m u b hD
  rw [hR,hS,hn,P_neg] at hc
  have hd : div D (-R D lam m v c)= -div D (R D lam m v c) := by
    simp only [div,Pi.neg_apply,map_neg,Finset.sum_neg_distrib]
  rw [hd] at hc
  have hp := augmented_identity D hD lam m v c
  linear_combination hc+hp

lemma leading_stage_compatibility (hD : ∀ i j f, D i (D j f)=D j (D i f))
    (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hR : leadingR D θ lam m u b=0) (hS : leadingS D θ lam m u b=0)
    (hn : normal θ u=0) :
    normal θ (R D lam m u b)=leadingP D θ m (div D u-b) := by
  have hc := transport_compatibility D θ lam m u b hD
  simpa only [hR,hS,hn,div,P,lap,Pi.zero_apply,map_zero,mul_zero,Finset.sum_const_zero,
    zero_add,add_zero,sub_zero] using hc
end ElasticityAugmented

end
end
section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

def restriction (U : Set X) : Smooth →ₐ[ℂ] (U → ℂ) where
  toFun f x := (f : X → ℂ) x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
abbrev LocalSmooth (U : Set X) := (restriction U).range
def restrictSmooth (U : Set X) : Smooth →ₐ[ℂ] LocalSmooth U := (restriction U).rangeRestrict
lemma restrictSmooth_surjective (U : Set X) : Function.Surjective (restrictSmooth U) :=
  (restriction U).rangeRestrict_surjective
lemma restrictSmooth_eq_iff (U : Set X) (f g : Smooth) :
    restrictSmooth U f=restrictSmooth U g ↔ EqOn (f : X → ℂ) (g : X → ℂ) U := by
  constructor
  · intro h x hx
    exact congrArg (fun v : LocalSmooth U => (v : U → ℂ) ⟨x,hx⟩) h
  · intro h
    apply Subtype.ext
    funext x
    exact h x.property
lemma restrictSmooth_zero_iff (U : Set X) (f : Smooth) :
    restrictSmooth U f=0 ↔ ∀ x∈U,(f : X → ℂ) x=0 := by
  rw [← map_zero (restrictSmooth U),restrictSmooth_eq_iff]
  rfl
lemma restrict_coord_zero {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth)
    (hf : restrictSmooth U f=0) : restrictSmooth U (coord i f)=0 := by
  apply (restrictSmooth_zero_iff U _).mpr
  intro x hx
  have he : (f : X → ℂ)=ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (restrictSmooth_zero_iff U f).mp hf y hy
  rw [coord_apply,he.fderiv_eq]
  simp

def localCoord {U : Set X} (hU : IsOpen U) (i : Fin 3) :
    Derivation ℂ (LocalSmooth U) (LocalSmooth U) :=
  Derivation.liftOfSurjective (restrictSmooth_surjective U) (restrict_coord_zero hU i)
lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
lemma localCoord_commute {U : Set X} (hU : IsOpen U) (i j : Fin 3) (f : LocalSmooth U) :
    localCoord hU i (localCoord hU j f)=localCoord hU j (localCoord hU i f) := by
  obtain ⟨f,rfl⟩ := restrictSmooth_surjective U f
  simp only [localCoord_restrict,coord_commute i j]

lemma restrict_div {U : Set X} (hU : IsOpen U) (a : Fin 3 → Smooth) :
    restrictSmooth U (div coord a)=div (localCoord hU) (fun i => restrictSmooth U (a i)) := by
  simp only [div,map_sum,localCoord_restrict]
lemma restrict_normal (U : Set X) (θ : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (normal θ a)=normal θ (fun i => restrictSmooth U (a i)) := by
  simp only [normal,map_sum,map_smul]
lemma restrict_direction {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (f : Smooth) :
    restrictSmooth U (direction coord θ f)=direction (localCoord hU) θ (restrictSmooth U f) := by
  simp only [direction,map_sum,map_smul,localCoord_restrict]
lemma restrict_R {U : Set X} (hU : IsOpen U) (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    restrictSmooth U (R coord lam mu a b i)=
      R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) i := by
  simp only [R,cm,lap,map_add,map_mul,map_sum,localCoord_restrict]
lemma restrict_S {U : Set X} (hU : IsOpen U) (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) :
    restrictSmooth U (S coord lam mu a b)=
      S (localCoord hU) (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) := by
  simp only [S,lap,map_add,map_mul,map_ofNat,map_sum,localCoord_restrict]
lemma restrict_leadingR {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ)
    (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    restrictSmooth U (leadingR coord θ lam mu a b i)=
      leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) i := by
  simp only [leadingR,map_add,map_mul,map_ofNat,map_sum,map_smul,localCoord_restrict,restrict_direction hU]
lemma restrict_leadingS {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ)
    (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) :
    restrictSmooth U (leadingS coord θ lam mu a b)=
      leadingS (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) := by
  simp only [leadingS,map_add,map_mul,map_ofNat,map_sum,localCoord_restrict,restrict_direction hU]
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented

lemma restrict_coeffA {B : Set X} (hB : IsOpen B) (lam m n o : Smooth)
    (k : Fin 3) (i j : Fin 4) :
    restrictSmooth B (coeffA coord lam m n o k i j)=
      coeffA (localCoord hB) (restrictSmooth B lam) (restrictSmooth B m)
        (restrictSmooth B n) (restrictSmooth B o) k i j := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffA,Fin.cons_zero,Fin.cons_succ,map_mul,map_add,map_sub,map_ofNat,
      localCoord_restrict,map_zero,apply_ite] <;> split_ifs <;> rfl

lemma restrict_coeffV {B : Set X} (hB : IsOpen B) (lam m n o : Smooth)
    (i j : Fin 4) :
    restrictSmooth B (coeffV coord lam m n o i j)=
      coeffV (localCoord hB) (restrictSmooth B lam) (restrictSmooth B m)
        (restrictSmooth B n) (restrictSmooth B o) i j := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffV,Fin.cons_zero,Fin.cons_succ,lap,map_mul,map_sub,map_ofNat,
      map_sum,localCoord_restrict,map_zero]

lemma inverse_eqOn {B : Set X} (m₁ m₂ n₁ n₂ : Smooth)
    (hn₁ : n₁*m₁=1) (hn₂ : n₂*m₂=1) (he : EqOn (m₁ : X → ℂ) m₂ B) :
    EqOn (n₁ : X → ℂ) n₂ B := by
  intro x hx
  have h1 := congrArg (fun f : Smooth => (f : X → ℂ) x) hn₁
  have h2 := congrArg (fun f : Smooth => (f : X → ℂ) x) hn₂
  change (n₁ : X → ℂ) x*(m₁ : X → ℂ) x=1 at h1
  change (n₂ : X → ℂ) x*(m₂ : X → ℂ) x=1 at h2
  rw [he hx] at h1
  linear_combination (n₂ : X → ℂ) x*h1-(n₁ : X → ℂ) x*h2

/-- Equality of the original coefficients on an open set gives equality of
both actual normalized matrices there. Reciprocals are not extra exterior
identifications: they follow from their defining inverse identities. -/
theorem normalized_coefficients_eqOn {B : Set X} (hB : IsOpen B)
    (l₁ m₁ n₁ o₁ l₂ m₂ n₂ o₂ : Smooth)
    (hn₁ : n₁*m₁=1) (hn₂ : n₂*m₂=1)
    (ho₁ : o₁*(l₁+m₁+m₁)=1) (ho₂ : o₂*(l₂+m₂+m₂)=1)
    (hel : EqOn (l₁ : X → ℂ) l₂ B) (hem : EqOn (m₁ : X → ℂ) m₂ B) :
    (∀ k i j,EqOn ((coeffA coord l₁ m₁ n₁ o₁ k i j : Smooth) : X → ℂ)
      ((coeffA coord l₂ m₂ n₂ o₂ k i j : Smooth) : X → ℂ) B) ∧
    (∀ i j,EqOn ((coeffV coord l₁ m₁ n₁ o₁ i j : Smooth) : X → ℂ)
      ((coeffV coord l₂ m₂ n₂ o₂ i j : Smooth) : X → ℂ) B) := by
  have hen := inverse_eqOn m₁ m₂ n₁ n₂ hn₁ hn₂ hem
  have heo : EqOn (o₁ : X → ℂ) o₂ B :=
    inverse_eqOn _ _ o₁ o₂ ho₁ ho₂ (by
      intro x hx
      change (l₁ : X → ℂ) x+(m₁ : X → ℂ) x+(m₁ : X → ℂ) x =
        (l₂ : X → ℂ) x+(m₂ : X → ℂ) x+(m₂ : X → ℂ) x
      rw [hel hx,hem hx])
  have hl := (restrictSmooth_eq_iff B _ _).mpr hel
  have hm := (restrictSmooth_eq_iff B _ _).mpr hem
  have hn := (restrictSmooth_eq_iff B _ _).mpr hen
  have ho := (restrictSmooth_eq_iff B _ _).mpr heo
  constructor
  · intro k i j
    apply (restrictSmooth_eq_iff B _ _).mp
    rw [restrict_coeffA hB,restrict_coeffA hB,hl,hm,hn,ho]
  · intro i j
    apply (restrictSmooth_eq_iff B _ _).mp
    rw [restrict_coeffV hB,restrict_coeffV hB,hl,hm,hn,ho]
end ElasticityAugmented

end
end

end OAI
