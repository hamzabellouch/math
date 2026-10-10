import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
namespace SquareZero
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (δ : V →ₗ[k] V) (hδ : ∀ x, δ (δ x) = 0)

abbrev Cycles := LinearMap.ker δ

def boundaryMap : V →ₗ[k] Cycles δ :=
  δ.codRestrict (Cycles δ) (fun x => hδ x)

def boundaries : Submodule k (Cycles δ) := (boundaryMap δ hδ).range

abbrev Cohomology := (Cycles δ) ⧸ boundaries δ hδ

def classMap : Cycles δ →ₗ[k] Cohomology δ hδ := (boundaries δ hδ).mkQ

@[simp] theorem class_boundary (x : V) :
    classMap δ hδ (boundaryMap δ hδ x) = 0 := by
  change (Submodule.Quotient.mk (boundaryMap δ hδ x) : Cohomology δ hδ) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

theorem class_eq_zero (x : Cycles δ) : classMap δ hδ x = 0 ↔ ∃ y, δ y = x := by
  change (Submodule.Quotient.mk x : Cohomology δ hδ) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

theorem classMap_surjective : Function.Surjective (classMap δ hδ) :=
  Submodule.mkQ_surjective _

                                                                               
                                                                    
def cycleMap (f g : V →ₗ[k] V) (hfg : ∀ x, δ (f x) = g (δ x)) :
    Cycles δ →ₗ[k] Cycles δ :=
  (f.comp (Cycles δ).subtype).codRestrict (Cycles δ) (fun x => by
    change δ (f (x : V)) = 0
    rw [hfg, x.property, map_zero])

@[simp] theorem cycleMap_val (f g : V →ₗ[k] V) (hfg : ∀ x, δ (f x) = g (δ x))
    (x : Cycles δ) : (cycleMap δ f g hfg x : V) = f x := rfl

def induced (f g j : V →ₗ[k] V)
    (hfg : ∀ x, δ (f x) = g (δ x)) (hfj : ∀ x, f (δ x) = δ (j x)) :
    Cohomology δ hδ →ₗ[k] Cohomology δ hδ :=
  (boundaries δ hδ).mapQ (boundaries δ hδ) (cycleMap δ f g hfg) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨j x, Subtype.ext (hfj x).symm⟩)

@[simp] theorem induced_class (f g j : V →ₗ[k] V)
    (hfg : ∀ x, δ (f x) = g (δ x)) (hfj : ∀ x, f (δ x) = δ (j x))
    (x : Cycles δ) :
    induced δ hδ f g j hfg hfj (classMap δ hδ x) =
      classMap δ hδ (cycleMap δ f g hfg x) := rfl

                                                                            
theorem induced_ext (f g : Cohomology δ hδ →ₗ[k] Cohomology δ hδ)
    (h : ∀ z : Cycles δ, f (classMap δ hδ z) = g (classMap δ hδ z)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := classMap_surjective δ hδ x
  exact h z

theorem induced_square_zero (f g j : V →ₗ[k] V)
    (hfg : ∀ x, δ (f x) = g (δ x)) (hfj : ∀ x, f (δ x) = δ (j x))
    (hf : ∀ x, f (f x) = 0) (x : Cohomology δ hδ) :
    induced δ hδ f g j hfg hfj (induced δ hδ f g j hfg hfj x) = 0 := by
  obtain ⟨z, rfl⟩ := classMap_surjective δ hδ x
  rw [induced_class, induced_class]
  have hz : cycleMap δ f g hfg (cycleMap δ f g hfg z) = 0 := Subtype.ext (hf z)
  rw [hz, map_zero]

                                                                        
                                                              
def oddInduced (D : V →ₗ[k] V) (hD : ∀ x, δ (D x) = -D (δ x)) :
    Cohomology δ hδ →ₗ[k] Cohomology δ hδ :=
  induced δ hδ D (-D) (-D) hD (fun x => by
    change D (δ x) = δ (-D x)
    rw [map_neg, hD, neg_neg])

@[simp] theorem oddInduced_class (D : V →ₗ[k] V) (hD : ∀ x, δ (D x) = -D (δ x))
    (z : Cycles δ) :
    oddInduced δ hδ D hD (classMap δ hδ z) =
      classMap δ hδ (cycleMap δ D (-D) hD z) := rfl

theorem oddInduced_square_zero (D : V →ₗ[k] V) (hD : ∀ x, δ (D x) = -D (δ x))
    (hDD : ∀ x, D (D x) = 0) (x : Cohomology δ hδ) :
    oddInduced δ hδ D hD (oddInduced δ hδ D hD x) = 0 :=
  induced_square_zero δ hδ _ _ _ _ _ hDD x

                                                                                   
def evenInduced (S : V →ₗ[k] V) (hS : ∀ x, δ (S x) = S (δ x)) :
    Cohomology δ hδ →ₗ[k] Cohomology δ hδ :=
  induced δ hδ S S S hS (fun x => (hS x).symm)

@[simp] theorem evenInduced_class (S : V →ₗ[k] V) (hS : ∀ x, δ (S x) = S (δ x))
    (z : Cycles δ) :
    evenInduced δ hδ S hS (classMap δ hδ z) =
      classMap δ hδ (cycleMap δ S S hS z) := rfl

                                                                            
                                
theorem correction_of_kernel (D S T : V →ₗ[k] V)
    (hD : ∀ x, δ (D x) = -D (δ x))
    (hS : ∀ x, δ (S x) = S (δ x))
    (_ : ∀ x, δ (T x) = -T (δ x))
    (hDS : ∀ x, D (S x) - S (D x) = T x)
    (x : Cycles δ)
    (hSx : evenInduced δ hδ S hS (classMap δ hδ x) = 0)
    (hSDx : evenInduced δ hδ S hS
      (oddInduced δ hδ D hD (classMap δ hδ x)) = 0) :
    ∃ y : V, δ y = -T x := by
  rw [evenInduced_class] at hSx
  obtain ⟨u, hu⟩ := (class_eq_zero δ hδ _).mp hSx
  rw [oddInduced_class, evenInduced_class] at hSDx
  obtain ⟨v, hv⟩ := (class_eq_zero δ hδ _).mp hSDx
  change δ u = S x at hu
  change δ v = S (D x) at hv
  refine ⟨D u + v, ?_⟩
  rw [map_add, hD, hu, hv, ← hDS]
  abel

end SquareZero
end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.SquareZero
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

private theorem generalized_inverse (S : V →ₗ[k] V) :
    ∃ L : V →ₗ[k] V, ∀ x, S (L (S x)) = S x := by
  obtain ⟨g,hg⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  obtain ⟨h,hh⟩ := S.range.subtype.exists_leftInverse_of_injective S.range.ker_subtype
  refine ⟨g.comp h, fun x => ?_⟩
  have hx : h (S x) = S.rangeRestrict x := LinearMap.congr_fun hh (S.rangeRestrict x)
  change S (g (h (S x))) = S x
  rw [hx]
  exact congrArg Subtype.val (LinearMap.congr_fun hg (S.rangeRestrict x))

                                                                          
                                                                               
theorem cohomology_contraction (δ : V →ₗ[k] V) (hδ : ∀ x, δ (δ x) = 0) :
    ∃ (i : Cohomology δ hδ →ₗ[k] V) (p : V →ₗ[k] Cohomology δ hδ) (h : V →ₗ[k] V),
      (∀ x, δ (i x) = 0) ∧ (∀ x, p (δ x) = 0) ∧
      (∀ x, p (i x) = x) ∧
      (∀ z : Cycles δ, p z = classMap δ hδ z) ∧
      (∀ x, x - i (p x) = δ (h x) + h (δ x)) := by
  obtain ⟨g, hg⟩ := generalized_inverse δ
  let q := LinearMap.id - δ.comp g - g.comp δ
  have hq (x : V) : q x = x - δ (g x) - g (δ x) := rfl
  have hδq (x : V) : δ (q x) = 0 := by
    rw [hq, map_sub, map_sub, hδ, sub_zero, hg, sub_self]
  have hqδ (x : V) : q (δ x) = 0 := by
    rw [hq, hg, sub_self, hδ, map_zero, sub_zero]
  let qz := q.codRestrict (Cycles δ) hδq
  have hqz (z : Cycles δ) :
      qz z = z - boundaryMap δ hδ (g z) := by
    apply Subtype.ext
    change q z = (z : V) - δ (g z)
    rw [hq, z.property, map_zero, sub_zero]
  obtain ⟨j, hj⟩ := (classMap δ hδ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (classMap_surjective δ hδ))
  have hj' (x : Cohomology δ hδ) : classMap δ hδ (j x) = x :=
    LinearMap.congr_fun hj x
  let i := (Cycles δ).subtype.comp j
  let p := (classMap δ hδ).comp qz
  have hpz (z : Cycles δ) : p z = classMap δ hδ z := by
    change classMap δ hδ (qz z) = _
    rw [hqz, map_sub, class_boundary, sub_zero]
  have hpδ (x : V) : p (δ x) = 0 := by
    change classMap δ hδ (qz (δ x)) = 0
    have hz : qz (δ x) = 0 := Subtype.ext (hqδ x)
    rw [hz, map_zero]
  let K : V →ₗ[k] boundaries δ hδ :=
    (qz - j.comp p).codRestrict (boundaries δ hδ) (fun x => by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change classMap δ hδ (qz x - j (p x)) = 0
      rw [map_sub, hj']
      exact sub_self _)
  obtain ⟨b, hb⟩ := (boundaryMap δ hδ).rangeRestrict.exists_rightInverse_of_surjective
    (boundaryMap δ hδ).range_rangeRestrict
  let b' : boundaries δ hδ →ₗ[k] V := b
  let h₁ := b'.comp K
  have hh₁ (x : V) : δ (h₁ x) = q x - i (p x) :=
    congrArg (fun z : boundaries δ hδ => ((z : Cycles δ) : V))
      (LinearMap.congr_fun hb (K x))
  have hKδ (x : V) : K (δ x) = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    change q (δ x) - i (p (δ x)) = 0
    rw [hqδ, hpδ, map_zero, sub_zero]
  refine ⟨i, p, g + h₁, ?_, hpδ, ?_, hpz, ?_⟩
  · intro x; exact (j x).property
  · intro x; exact (hpz (j x)).trans (hj' x)
  · intro x
    have hz : h₁ (δ x) = 0 := by change b' (K (δ x)) = 0; rw [hKδ, map_zero]
    simp only [LinearMap.add_apply, map_add, hh₁, hz, add_zero]
    rw [hq]
    abel

end BoundaryOnly.FormalObstruction.SquareZero

namespace BoundaryOnly.FormalObstruction.SquareZero
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

                                                                               
theorem odd_generalized_inverse (htwo : (2 : k) ≠ 0)
    (δ P : V →ₗ[k] V) (hPP : ∀ x, P (P x) = x)
    (hDP : ∀ x, δ (P x) = -P (δ x)) :
    ∃ g : V →ₗ[k] V, (∀ x, δ (g (δ x)) = δ x) ∧
      (∀ x, g (P x) = -P (g x)) := by
  obtain ⟨g,hg⟩ := generalized_inverse δ
  let c : k := (2 : k)⁻¹
  have hc : c+c = 1 := by dsimp [c]; field_simp; ring
  let g' : V →ₗ[k] V := c • (g - P.comp (g.comp P))
  have hg' (x : V) : g' x = c • (g x - P (g (P x))) := rfl
  refine ⟨g', ?_, ?_⟩
  · intro x
    have hpd : P (δ x) = -δ (P x) := by rw [hDP, neg_neg]
    rw [hg', map_smul, map_sub, hg, hDP (g (P (δ x))), hpd]
    simp only [map_neg]
    rw [hg, hDP]
    simp only [map_neg, hPP, neg_neg, sub_neg_eq_add]
    rw [smul_add, ← add_smul, hc, one_smul]
  · intro x
    simp only [hg', map_smul, map_sub, hPP]
    module

                                                                
theorem odd_homotopy (htwo : (2 : k) ≠ 0)
    (δ P r h : V →ₗ[k] V) (hPP : ∀ x, P (P x) = x)
    (hDP : ∀ x, δ (P x) = -P (δ x))
    (hrP : ∀ x, r (P x) = P (r x))
    (hrh : ∀ x, x - r x = δ (h x) + h (δ x)) :
    ∃ h' : V →ₗ[k] V,
      (∀ x, h' (P x) = -P (h' x)) ∧
      (∀ x, x - r x = δ (h' x) + h' (δ x)) := by
  let c : k := (2 : k)⁻¹
  have hc : c+c = 1 := by dsimp [c]; field_simp; ring
  let h' : V →ₗ[k] V := c • (h - P.comp (h.comp P))
  have hh' (x : V) : h' x = c • (h x - P (h (P x))) := rfl
  have hPD (x : V) : P (δ x) = -δ (P x) := by rw [hDP, neg_neg]
  refine ⟨h', ?_, ?_⟩
  · intro x
    simp only [hh', map_smul, map_sub, hPP]
    module
  · intro x
    have h₂ := congrArg P (hrh (P x))
    simp only [map_sub, map_add, hrP, hPP] at h₂
    rw [hPD (h (P x)), hDP x, map_neg, map_neg] at h₂
    rw [hh', hh']
    simp only [map_smul, map_sub]
    calc
      x - r x = c • (x - r x) + c • (x - r x) := by
        rw [← add_smul, hc, one_smul]
      _ = c • (δ (h x) + h (δ x)) +
          c • (-δ (P (h (P x))) - P (h (P (δ x)))) := by
        conv_lhs => arg 1; rw [hrh]
        congr 1
        exact congrArg (c • ·) (by simpa only [sub_eq_add_neg] using h₂)
      _ = _ := by module

end BoundaryOnly.FormalObstruction.SquareZero

namespace BoundaryOnly.FormalObstruction.SquareZero
variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

private theorem equivariant_section (htwo : (2 : k) ≠ 0)
    (f : V →ₗ[k] W) (hf : Function.Surjective f)
    (P : V →ₗ[k] V) (Q : W →ₗ[k] W)
    (hPP : ∀ x, P (P x) = x) (hQQ : ∀ x, Q (Q x) = x)
    (hfP : ∀ x, f (P x) = Q (f x)) :
    ∃ j : W →ₗ[k] V, (∀ x, f (j x) = x) ∧ (∀ x, j (Q x) = P (j x)) := by
  obtain ⟨j,hj⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hj' (x : W) : f (j x) = x := LinearMap.congr_fun hj x
  let c : k := (2 : k)⁻¹
  have hc : c+c = 1 := by dsimp [c]; field_simp; ring
  let j' : W →ₗ[k] V := c • (j + P.comp (j.comp Q))
  have hj'val (x : W) : j' x = c • (j x + P (j (Q x))) := rfl
  refine ⟨j', ?_, ?_⟩
  · intro x
    simp only [hj'val, map_smul, map_add, hfP, hj', hQQ]
    rw [smul_add, ← add_smul, hc, one_smul]
  · intro x
    simp only [hj'val, map_smul, map_add, hPP, hQQ]
    module

                                                                              
                                                                             
theorem parity_cohomology_contraction (htwo : (2 : k) ≠ 0)
    (δ P : V →ₗ[k] V) (hδ : ∀ x, δ (δ x) = 0)
    (hPP : ∀ x, P (P x) = x) (hDP : ∀ x, δ (P x) = -P (δ x)) :
    ∃ (i : Cohomology δ hδ →ₗ[k] V) (p : V →ₗ[k] Cohomology δ hδ)
      (h : V →ₗ[k] V),
      (∀ x, δ (i x) = 0) ∧ (∀ x, p (δ x) = 0) ∧
      (∀ x, p (i x) = x) ∧
      (∀ z : Cycles δ, p z = classMap δ hδ z) ∧
      (∀ x, i (oddInduced δ hδ P hDP x) = P (i x)) ∧
      (∀ x, p (P x) = oddInduced δ hδ P hDP (p x)) ∧
      (∀ x, h (P x) = -P (h x)) ∧
      (∀ x, x - i (p x) = δ (h x) + h (δ x)) := by
  let PZ := cycleMap δ P (-P) hDP
  let PH := oddInduced δ hδ P hDP
  have hPZ (x : Cycles δ) : PZ (PZ x) = x := Subtype.ext (hPP x)
  have hclP (z : Cycles δ) : classMap δ hδ (PZ z) = PH (classMap δ hδ z) := rfl
  have hPH (x : Cohomology δ hδ) : PH (PH x) = x := by
    obtain ⟨z, rfl⟩ := classMap_surjective δ hδ x
    rw [← hclP, ← hclP, hPZ]
  obtain ⟨j,hj',hjP⟩ := equivariant_section htwo (classMap δ hδ)
    (classMap_surjective δ hδ) PZ PH hPZ hPH hclP
  obtain ⟨g,hg,hgP⟩ := odd_generalized_inverse htwo δ P hPP hDP
  let q := LinearMap.id - δ.comp g - g.comp δ
  have hq (x : V) : q x = x - δ (g x) - g (δ x) := rfl
  have hδq (x : V) : δ (q x) = 0 := by
    rw [hq, map_sub, map_sub, hδ, sub_zero, hg, sub_self]
  have hqδ (x : V) : q (δ x) = 0 := by
    rw [hq, hg, sub_self, hδ, map_zero, sub_zero]
  have hqP (x : V) : q (P x) = P (q x) := by
    simp only [hq, hgP, hDP, map_sub, map_neg, neg_neg]
  let qz := q.codRestrict (Cycles δ) hδq
  have hqz (z : Cycles δ) : qz z = z - boundaryMap δ hδ (g z) := by
    apply Subtype.ext
    change q z = (z : V) - δ (g z)
    rw [hq, z.property, map_zero, sub_zero]
  let i := (Cycles δ).subtype.comp j
  let p := (classMap δ hδ).comp qz
  have hpz (z : Cycles δ) : p z = classMap δ hδ z := by
    change classMap δ hδ (qz z) = _
    rw [hqz, map_sub, class_boundary, sub_zero]
  have hpδ (x : V) : p (δ x) = 0 := by
    change classMap δ hδ (qz (δ x)) = 0
    have hz : qz (δ x) = 0 := Subtype.ext (hqδ x)
    rw [hz, map_zero]
  have hiP (x : Cohomology δ hδ) : i (PH x) = P (i x) :=
    congrArg Subtype.val (hjP x)
  have hpP (x : V) : p (P x) = PH (p x) := by
    change classMap δ hδ (qz (P x)) = PH (classMap δ hδ (qz x))
    rw [← hclP]
    exact congrArg (classMap δ hδ) (Subtype.ext (hqP x))
  let K : V →ₗ[k] boundaries δ hδ :=
    (qz - j.comp p).codRestrict (boundaries δ hδ) (fun x => by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change classMap δ hδ (qz x - j (p x)) = 0
      rw [map_sub, hj']
      exact sub_self _)
  obtain ⟨b, hb⟩ := (boundaryMap δ hδ).rangeRestrict.exists_rightInverse_of_surjective
    (boundaryMap δ hδ).range_rangeRestrict
  let b' : boundaries δ hδ →ₗ[k] V := b
  let h₁ := b'.comp K
  have hh₁ (x : V) : δ (h₁ x) = q x - i (p x) :=
    congrArg (fun z : boundaries δ hδ => ((z : Cycles δ) : V))
      (LinearMap.congr_fun hb (K x))
  have hKδ (x : V) : K (δ x) = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    change q (δ x) - i (p (δ x)) = 0
    rw [hqδ, hpδ, map_zero, sub_zero]
  have hraw (x : V) : x - i (p x) = δ ((g+h₁) x) + (g+h₁) (δ x) := by
    have hz : h₁ (δ x) = 0 := by change b' (K (δ x)) = 0; rw [hKδ, map_zero]
    simp only [LinearMap.add_apply, map_add, hh₁, hz, add_zero]
    rw [hq]
    abel
  have hrP (x : V) : (i.comp p) (P x) = P ((i.comp p) x) := by
    change i (p (P x)) = P (i (p x))
    rw [hpP, hiP]
  obtain ⟨h,hhP,hhh⟩ := odd_homotopy htwo δ P (i.comp p) (g+h₁) hPP hDP hrP hraw
  refine ⟨i,p,h,?_,hpδ,?_,hpz,hiP,hpP,hhP,hhh⟩
  · intro x; exact (j x).property
  · intro x; exact (hpz (j x)).trans (hj' x)

end BoundaryOnly.FormalObstruction.SquareZero

end

end OAI
