import OAI.NumberTheory.PiExponent.Cohomology.CechOne
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

def intersection {n : ℕ} (t : Fin n → J) : Opens X := ⨅ i, U (t i)

theorem intersectionLE {m n : ℕ} (t : Fin n → J) (f : Fin m → Fin n) :
    intersection U t ≤ intersection U (t ∘ f) :=
  le_iInf fun i => iInf_le (fun j => U (t j)) (f i)

theorem faceLE {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    intersection U t ≤ intersection U (t ∘ k.succAbove) :=
  intersectionLE U t k.succAbove

abbrev Cochain (q : ℕ) :=
  ∀ t : Fin (q + 1) → J, freeOpen R (intersection U t) ⟶ M

def differential {q : ℕ} (c : Cochain R U M q) : Cochain R U M (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
    restrictHom R (faceLE U t k) (c (t ∘ k.succAbove))

def HasPrimitives (q : ℕ) : Prop :=
  ∀ c : Cochain R U M (q + 1), differential R U M c = 0 →
    ∃ b : Cochain R U M q, differential R U M b = c

@[simp] theorem restrictHom_refl {W : Opens X} (f : freeOpen R W ⟶ M) :
    restrictHom R le_rfl f = f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (𝟙 W) ≫ f = f
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp f

@[simp] theorem restrictHom_sum {W V : Opens X} (h : W ≤ V)
    {T : Type*} (s : Finset T) (f : T → (freeOpen R V ⟶ M)) :
    restrictHom R h (∑ i ∈ s, f i) = ∑ i ∈ s, restrictHom R h (f i) := by
  simp only [restrictHom, Preadditive.comp_sum]

@[simp] theorem restrictHom_zsmul {W V : Opens X} (h : W ≤ V)
    (z : ℤ) (f : freeOpen R V ⟶ M) :
    restrictHom R h (z • f) = z • restrictHom R h f := by
  simp only [restrictHom, Preadditive.comp_zsmul]

def evaluate {L : Type*} (W : Opens X) (f : L → J)
    (hf : ∀ l, W ≤ U (f l)) {q : ℕ} (c : Cochain R U M q) :
    ProjectiveMonomialCechHigher.Cochain L (freeOpen R W ⟶ M) q :=
  fun t => restrictHom R (le_iInf fun i => hf (t i)) (c (f ∘ t))

theorem evaluate_differential {L : Type*} (W : Opens X) (f : L → J)
    (hf : ∀ l, W ≤ U (f l)) {q : ℕ} (c : Cochain R U M q) :
    evaluate R U M W f hf (differential R U M c) =
      ProjectiveMonomialCechHigher.differential (evaluate R U M W f hf c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential]
  erw [restrictHom_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [restrictHom_zsmul, restrictHom_restrictHom]
  rfl

theorem differential_squared {q : ℕ} (c : Cochain R U M q) :
    differential R U M (differential R U M c) = 0 := by
  funext t
  let W := intersection U t
  have hf : ∀ i, W ≤ U (t i) := fun i => iInf_le (fun j => U (t j)) i
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate R U M W t hf c)) id
  rw [← evaluate_differential, ← evaluate_differential] at h
  change restrictHom R le_rfl (differential R U M (differential R U M c) t) = 0 at h
  simpa only [restrictHom_refl, Pi.zero_apply] using h

def map {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c : Cochain R U M q) : Cochain R U N q := fun t => c t ≫ g

theorem map_differential {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c : Cochain R U M q) :
    map R U M g (differential R U M c) = differential R U N (map R U M g c) := by
  funext t
  simp only [map, differential, Preadditive.sum_comp, Preadditive.zsmul_comp,
    restrictHom_comp]

@[simp] theorem differential_zero {q : ℕ} :
    differential R U M (0 : Cochain R U M q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, restrictHom, comp_zero, smul_zero,
    Finset.sum_const_zero]

theorem differential_sub {q : ℕ} (c e : Cochain R U M q) :
    differential R U M (c - e) = differential R U M c - differential R U M e := by
  funext t
  simp only [differential, Pi.sub_apply, restrictHom_sub, smul_sub, Finset.sum_sub_distrib]

@[simp] theorem map_zero {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ} :
    map R U M g (0 : Cochain R U M q) = 0 := by
  funext t
  exact zero_comp

theorem map_sub {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c e : Cochain R U M q) :
    map R U M g (c - e) = map R U M g c - map R U M g e := by
  funext t
  exact Preadditive.sub_comp _ _ _

theorem map_injective {N : SheafOfModules.{u} R} (g : M ⟶ N) [Mono g] {q : ℕ} :
    Function.Injective (map R U M g (q := q)) := by
  intro c e h
  funext t
  exact (cancel_mono g).mp (congrFun h t)

theorem lift_cochain (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (q : ℕ)
    (hzero : ∀ (t : Fin (q + 1) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (c : Cochain R U S.X₃ q) :
    ∃ b : Cochain R U S.X₂ q, map R U S.X₂ S.g b = c := by
  classical
  choose b hb using fun t =>
    lift_of_ext_one_zero R S hS (intersection U t) (hzero t) (c t)
  exact ⟨b, funext hb⟩

theorem lift_kernel_cochain (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) {q : ℕ} (c : Cochain R U S.X₂ q)
    (hc : map R U S.X₂ S.g c = 0) :
    ∃ b : Cochain R U S.X₁ q, map R U S.X₁ S.f b = c := by
  let : Mono S.f := hS.mono_f
  have hz (t : Fin (q + 1) → J) : c t ≫ S.g = 0 := congrFun hc t
  exact ⟨fun t => hS.exact.lift (c t) (hz t),
    funext (fun t => hS.exact.lift_f (c t) (hz t))⟩

theorem connecting_cocycle (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) {q : ℕ}
    (hzero : ∀ (t : Fin (q + 1) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (c : Cochain R U S.X₃ q) (hc : differential R U S.X₃ c = 0) :
    ∃ (b : Cochain R U S.X₂ q) (a : Cochain R U S.X₁ (q + 1)),
      map R U S.X₂ S.g b = c ∧
      map R U S.X₁ S.f a = differential R U S.X₂ b ∧
      differential R U S.X₁ a = 0 := by
  let : Mono S.f := hS.mono_f
  obtain ⟨b, hb⟩ := lift_cochain R U S hS q hzero c
  have hdb : map R U S.X₂ S.g (differential R U S.X₂ b) = 0 := by
    rw [map_differential, hb, hc]
  obtain ⟨a, ha⟩ := lift_kernel_cochain R U S hS _ hdb
  refine ⟨b, a, hb, ha, ?_⟩
  apply map_injective R U S.X₁ S.f
  rw [map_differential, ha, differential_squared, map_zero]

theorem primitives_of_shortExact (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (q : ℕ)
    (hzero : ∀ (t : Fin (q + 2) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hkernel : HasPrimitives R U S.X₁ (q + 1))
    (hmiddle : HasPrimitives R U S.X₂ q) : HasPrimitives R U S.X₃ q := by
  intro c hc
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c hc
  obtain ⟨e, he⟩ := hkernel a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨v, hv⟩ := hmiddle _ hcorrected
  refine ⟨map R U S.X₂ S.g v, ?_⟩
  rw [← map_differential, hv, map_sub, hb]
  have hz : map R U S.X₂ S.g (map R U S.X₁ S.f e) = 0 := by
    funext t
    change (e t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  rw [hz, sub_zero]

theorem insertLE (p : J) (hp : ∀ i, U i ≤ U p) {q : ℕ} (t : Fin (q + 1) → J) :
    intersection U t ≤ intersection U (Fin.cons p t) := by
  apply le_iInf
  intro i
  cases i using Fin.cases with
  | zero => exact (iInf_le (fun j => U (t j)) 0).trans (hp (t 0))
  | succ i => exact iInf_le (fun j => U (t j)) i

def contraction (p : J) (hp : ∀ i, U i ≤ U p) {q : ℕ}
    (c : Cochain R U M (q + 1)) : Cochain R U M q :=
  fun t => restrictHom R (insertLE U p hp t) (c (Fin.cons p t))

theorem restrict_cochain_congr {q : ℕ} (c : Cochain R U M q)
    {t t' : Fin (q + 1) → J} (ht : t = t') {W : Opens X}
    (h : W ≤ intersection U t) (h' : W ≤ intersection U t') :
    restrictHom R h (c t) = restrictHom R h' (c t') := by
  subst t'
  rfl

theorem contraction_differential (p : J) (hp : ∀ i, U i ≤ U p) {q : ℕ}
    (c : Cochain R U M (q + 1)) :
    contraction R U M p hp (differential R U M c) =
      c - differential R U M (contraction R U M p hp c) := by
  funext t
  simp only [contraction, differential, Pi.sub_apply]
  rw [Fin.sum_univ_succ]
  erw [restrictHom_add, restrictHom_sum]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, Fin.succAbove_zero]
  erw [restrictHom_restrictHom, restrictHom_refl]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  erw [restrictHom_zsmul, restrictHom_restrictHom]
  rw [pow_succ, mul_neg_one, neg_zsmul]
  exact congrArg (fun f : freeOpen R (intersection U t) ⟶ M => -((-1 : ℤ) ^ k.val • f))
    ((restrict_cochain_congr R U M c (Fin.cons_comp_succ_succAbove p t k)
      ((insertLE U p hp t).trans (faceLE U (Fin.cons p t) k.succ))
      ((faceLE U t k).trans (insertLE U p hp (t ∘ k.succAbove)))).trans
        (restrictHom_restrictHom R (faceLE U t k) (insertLE U p hp (t ∘ k.succAbove))
          (c (Fin.cons p (t ∘ k.succAbove)))).symm)

theorem hasPrimitives_of_containing_member (p : J) (hp : ∀ i, U i ≤ U p)
    (q : ℕ) : HasPrimitives R U M q := by
  intro c hc
  refine ⟨contraction R U M p hp c, ?_⟩
  have h := contraction_differential R U M p hp c
  rw [hc] at h
  have hz : contraction R U M p hp (0 : Cochain R U M (q + 2)) = 0 := by
    funext t
    exact comp_zero
  rw [hz] at h
  exact (sub_eq_zero.mp h.symm).symm

theorem hasPrimitives_on_chart (p : J) (q : ℕ) :
    HasPrimitives R (fun i => U i ⊓ U p) M q := by
  apply hasPrimitives_of_containing_member R (fun i => U i ⊓ U p) M p
  intro i
  exact le_inf inf_le_right inf_le_right

def sectionZero (c : Cochain R U M 0) (i : J) : freeOpen R (U i) ⟶ M :=
  restrictHom R (le_iInf fun _ => le_rfl) (c (fun _ => i))

private theorem scalar_differential_zero_degree {B I : Type*} [AddCommGroup B]
    (c : ProjectiveMonomialCechHigher.Cochain I B 0) (i j : I) :
    ProjectiveMonomialCechHigher.differential c (Fin.cons i (fun _ => j)) =
      c (fun _ => j) - c (fun _ => i) := by
  have hsingleton (f : Fin 1 → I) : f = fun _ => f 0 := by
    funext k
    exact congrArg f (Subsingleton.elim k 0)
  simp only [ProjectiveMonomialCechHigher.differential]
  simp only [hsingleton, Function.comp_apply]
  simp [Fin.succAbove, sub_eq_add_neg]

theorem sectionZero_compatible (c : Cochain R U M 0)
    (hc : differential R U M c = 0) (i j : J) :
    restrictHom R inf_le_left (sectionZero R U M c i) =
      restrictHom R inf_le_right (sectionZero R U M c j) := by
  let W := U i ⊓ U j
  let f : Fin 2 → J := Fin.cons i (fun _ => j)
  have hf : ∀ l, W ≤ U (f l) := by
    intro l
    cases l using Fin.cases with
    | zero => exact inf_le_left
    | succ l => exact inf_le_right
  have h := evaluate_differential R U M W f hf c
  rw [hc] at h
  have h' := congrFun h (Fin.cons 0 (fun _ => 1))
  have hz : evaluate R U M W f hf (0 : Cochain R U M 1)
      (Fin.cons 0 (fun _ => 1)) = 0 := comp_zero
  rw [hz, scalar_differential_zero_degree] at h'
  have he := (sub_eq_zero.mp h'.symm).symm
  have h0 : f ∘ (fun _ : Fin 1 => (0 : Fin 2)) = (fun _ => i) := by
    funext k
    rfl
  have h1 : f ∘ (fun _ : Fin 1 => (1 : Fin 2)) = (fun _ => j) := by
    funext k
    rfl
  calc
    restrictHom R inf_le_left (sectionZero R U M c i) =
        evaluate R U M W f hf c (fun _ => 0) := by
      simp only [sectionZero, evaluate]
      erw [restrictHom_restrictHom]
      exact (restrict_cochain_congr R U M c h0 _ _).symm
    _ = evaluate R U M W f hf c (fun _ => 1) := he
    _ = restrictHom R inf_le_right (sectionZero R U M c j) := by
      simp only [sectionZero, evaluate]
      erw [restrictHom_restrictHom]
      exact restrict_cochain_congr R U M c h1 _ _

theorem glue_zero_cocycle (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : Cochain R U M 0)
    (hc : differential R U M c = 0) :
    ∃ g : freeOpen R V ⟶ M,
      ∀ i, restrictHom R (hUV i) g = sectionZero R U M c i := by
  exact hom_glue R U V hUV hcover M (sectionZero R U M c)
    (sectionZero_compatible R U M c hc)

def augmentation (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) : Cochain R U M 0 :=
  fun t => restrictHom R ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))) f

@[simp] theorem augmentation_closed (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) : differential R U M (augmentation R U M V hUV f) = 0 := by
  funext t
  simp only [differential, augmentation, Pi.zero_apply]
  calc
    _ = ∑ k : Fin 2, (-1 : ℤ) ^ k.val •
        restrictHom R ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))) f := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun g : freeOpen R (intersection U t) ⟶ M => (-1 : ℤ) ^ k.val • g)
        (restrictHom_restrictHom R _ _ f)
    _ = 0 := by rw [Fin.sum_univ_two]; simp

@[simp] theorem sectionZero_augmentation (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) (i : J) :
    sectionZero R U M (augmentation R U M V hUV f) i = restrictHom R (hUV i) f := by
  simp only [sectionZero, augmentation]
  exact restrictHom_restrictHom R _ _ f

theorem shortExact_global_lift (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hprimitive : HasPrimitives R U S.X₁ 0) (f : freeOpen R V ⟶ S.X₃) :
    ∃ g : freeOpen R V ⟶ S.X₂, g ≫ S.g = f := by
  let c := augmentation R U S.X₃ V hUV f
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c
    (augmentation_closed R U S.X₃ V hUV f)
  obtain ⟨e, he⟩ := hprimitive a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨g, hg⟩ := glue_zero_cocycle R U S.X₂ V hUV hcover _ hcorrected
  refine ⟨g, ?_⟩
  apply hom_ext R U V hUV hcover S.X₃
  intro i
  rw [restrictHom_comp, hg i]
  change (restrictHom R _ (b (fun _ => i) - e (fun _ => i) ≫ S.f)) ≫ S.g = _
  erw [restrictHom_sub, Preadditive.sub_comp, ← restrictHom_comp,
    ← restrictHom_comp, Category.assoc, S.zero, comp_zero]
  simp only [restrictHom, comp_zero, sub_zero]
  have hi := congrFun hb (fun _ => i)
  change b (fun _ => i) ≫ S.g = c (fun _ => i) at hi
  rw [hi]
  exact sectionZero_augmentation R U S.X₃ V hUV f i

theorem ext_one_eq_zero (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M 1), x = 0)
    (hprimitive : HasPrimitives R U M 0)
    (x : Ext.{u+1} (freeOpen R V) M 1) : x = 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  obtain ⟨g, rfl⟩ := shortExact_global_lift R U V hUV hcover S hS hzero hprimitive f
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero] at hy
  exact hy.symm

theorem ext_succ_eq_zero_of_injective_cech
    (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hinjective : ∀ (I : SheafOfModules.{u} R) [Injective I] (q : ℕ),
      HasPrimitives R U I q)
    (n : ℕ)
    (hlocal : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M (k + 1)), x = 0)
    (hprimitive : HasPrimitives R U M n)
    (x : Ext.{u+1} (freeOpen R V) M (n + 1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
      exact ext_one_eq_zero R U M V hUV hcover (fun t x => hlocal 0 t 0 x) hprimitive x
  | succ n ih =>
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hlocal' : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
          (y : Ext.{u+1} (freeOpen R (intersection U t)) S.X₃ (k + 1)), y = 0 := by
        intro q t k y
        obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
          (freeOpen R (intersection U t)) hS y (n₁ := k + 2) rfl (hlocal q t (k + 1) _)
        rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
        exact hz.symm
      have hprimitive' : HasPrimitives R U S.X₃ n :=
        primitives_of_shortExact R U S hS n
          (fun t y => hlocal (n + 1) t 0 y) hprimitive (hinjective S.X₂ n)
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
        (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
      rw [ih S.X₃ hlocal' hprimitive' y, Ext.zero_comp] at hy
      exact hy.symm

private abbrev schemeFreeOpen (Y : Scheme.{u}) (V : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero_of_injective_cech
    (Y : Scheme.{u}) [IsNoetherian Y] (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J), IsAffineOpen (intersection W t))
    (hinjective : ∀ (I : Y.Modules) [Injective I] (q : ℕ),
      HasPrimitives Y.ringCatSheaf W I q)
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact ext_succ_eq_zero_of_injective_cech Y.ringCatSheaf W A V hWV hcover
    hinjective n (fun q t k y =>
      PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
        (intersection W t) (haffine q t) A k y) hprimitive x

end
end PiExponent.GeometrySupport.CechHigher

end OAI
