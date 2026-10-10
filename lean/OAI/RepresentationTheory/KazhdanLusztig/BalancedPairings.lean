import OAI.RepresentationTheory.KazhdanLusztig.IntegralPairings

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/

section

namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPairing_dualToSupport (l : List I) (x : W)
    (lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (m : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l (bottStalkDualToSupport cs l x lam).val m =
      lam (bottStalkProjection cs l x m) := by
  change bottSamelsonDuality cs l
    ((bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam)) m = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem bottStalkDuality_apply_projection (l : List I) (x : W)
    (s : bottWeightSupported cs l x) (m : BottSamelsonModule cs l) :
    bottStalkDuality cs l x s (bottStalkProjection cs l x m) =
      bottSamelsonDuality cs l s.val m := by
  have he : bottStalkDualToSupport cs l x (bottStalkDuality cs l x s)=s :=
    (LinearEquiv.ofBijective (bottStalkDualToSupport cs l x)
      (bottStalkDualToSupport_bijective cs l x)).apply_symm_apply s
  calc
    _ = bottSamelsonDuality cs l
        (bottStalkDualToSupport cs l x (bottStalkDuality cs l x s)).val m :=
      (bottPairing_dualToSupport cs l x _ m).symm
    _ = _ := by rw [he]

 theorem bottStalkDuality_homogeneous (l : List I) (x : W) (n : ℤ)
    (s : bottWeightSupported cs l x) (hs : s ∈ bottSupportPiece cs basis l x n)
    (j : ℤ) (v : bottStalk cs l x) (hv : v ∈ bottStalkPiece cs basis l x j) :
    bottStalkDuality cs l x s v ∈ symmetricGrading basis (n+j-l.length) := by
  obtain ⟨m,hm,rfl⟩ := bottStalk_homogeneous_lift cs basis l x j v hv
  rw [bottStalkDuality_apply_projection]
  exact bottDuality_homogeneous cs basis l hs hm

 theorem bottDualToSupport_homogeneous (l : List I) (x : W) (r : ℤ)
    (lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (hlam : ∀ j v, v ∈ bottStalkPiece cs basis l x j →
      lam v ∈ symmetricGrading basis (j+r)) :
    bottStalkDualToSupport cs l x lam ∈ bottSupportPiece cs basis l x (r+l.length) := by
  change (bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam) ∈
    bottPiece cs basis l (r+l.length)
  apply perfect_inverse_of_homogeneous_functional (symmetricGrading basis) (bottPiece cs basis l)
    (bottSamelsonDuality cs l) l.length
    (fun _ _ _ _ hm hn => bottDuality_homogeneous cs basis l hm hn) r
  intro j m hm
  exact hlam j _ (bottStalkProjection_homogeneous cs basis l x j m hm)

 theorem bottStalkDuality_homogeneous_iff (l : List I) (x : W) (n : ℤ)
    (s : bottWeightSupported cs l x) :
    (∀ j v, v ∈ bottStalkPiece cs basis l x j →
      bottStalkDuality cs l x s v ∈ symmetricGrading basis (n+j-l.length)) ↔
        s ∈ bottSupportPiece cs basis l x n := by
  constructor
  · intro h
    have hh := bottDualToSupport_homogeneous cs basis l x (n-l.length)
      (bottStalkDuality cs l x s) (by
        intro j v hv
        have he : n+j-(l.length:ℤ) = j+(n-l.length) := by omega
        rw [← he]
        exact h j v hv)
    have he : bottStalkDualToSupport cs l x (bottStalkDuality cs l x s)=s :=
      (LinearEquiv.ofBijective (bottStalkDualToSupport cs l x)
        (bottStalkDualToSupport_bijective cs l x)).apply_symm_apply s
    simpa only [he,sub_add_cancel] using hh
  · intro h
    exact bottStalkDuality_homogeneous cs basis l x n s h

end
end KLInvariance.TitsSpace

end


section

/-! The actual word adjoint preserves homogeneity. Projection kernels are
annihilators of the actual supported lattices, integrally, with no localization
or freeness assumption on the projection lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bott_projection_zero_iff_annihilates_support (l : List I) (x : W)
    (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x m=0 ↔ ∀ s : bottWeightSupported cs l x,
      bottSamelsonDuality cs l s.val m=0 := by
  constructor
  · intro hm s
    exact bott_supported_annihilates cs l x s.property m
      ((bottStalkProjection_eq_zero cs l x m).mp hm)
  · intro h
    apply Subtype.ext
    funext e
    let lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
      (LinearMap.proj e).comp (bottStalk cs l x).subtype
    have he := h (bottStalkDualToSupport cs l x lam)
    rw [bottPairing_dualToSupport] at he
    exact he

 def bottAdjoint (l : List I) (f : End (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l)) := PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f

 theorem bottAdjoint_preserves_kernel (l : List I) (x : W)
    (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ s, s ∈ bottWeightSupported cs l x → f s ∈ bottWeightSupported cs l x)
    (m : BottSamelsonModule cs l) (hm : bottStalkProjection cs l x m=0) :
    bottStalkProjection cs l x (bottAdjoint cs l f m)=0 := by
  apply (bott_projection_zero_iff_annihilates_support cs l x _).mpr
  intro s
  change bottSamelsonDuality cs l s.val (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f m)=0
  rw [PerfectAdjoint.symmetric_pairing (bottSamelsonDuality cs l)
    (bottSamelson_symmetric cs l)]
  exact (bott_projection_zero_iff_annihilates_support cs l x m).mp hm ⟨f s.val,hf s.val s.property⟩

 theorem bottAdjoint_preserves_support (l : List I) (x : W)
    (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ m, bottStalkProjection cs l x m=0 → bottStalkProjection cs l x (f m)=0)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottWeightSupported cs l x) :
    bottAdjoint cs l f m ∈ bottWeightSupported cs l x := by
  apply bott_annihilates_supported cs l x
  intro n hn
  change bottSamelsonDuality cs l (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f m) n=0
  rw [PerfectAdjoint.pairing]
  apply bott_supported_annihilates cs l x hm
  exact (bottStalkProjection_eq_zero cs l x (f n)).mp
    (hf n ((bottStalkProjection_eq_zero cs l x n).mpr hn))

 theorem bottAdjoint_homogeneous
    {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
    (l : List I) (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ n m, m ∈ bottPiece cs basis l n → f m ∈ bottPiece cs basis l n)
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottAdjoint cs l f m ∈ bottPiece cs basis l n :=
  adjoint_homogeneous (symmetricGrading basis) (bottPiece cs basis l)
    (bottSamelsonDuality cs l) l.length
    (fun _ _ _ _ h1 h2 => bottDuality_homogeneous cs basis l h1 h2) f hf n m hm

end
end KLInvariance.TitsSpace

end


section

/-! Integral realization of tensor words as ALL sections of their actual
pair-projection sheaf. This assertion alone is not a BMP summand theorem,
flabbiness/standard-filtration theorem, or EW character theorem. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottVertexProjection (l : List I) (u b : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    (∀ x : Interval cs u b, bottStalk cs l x.val) :=
  LinearMap.pi (fun x => bottStalkProjection cs l x.val)

 theorem bottVertexProjection_injective (l : List I) (hl : cs.IsReduced l) :
    Function.Injective (bottVertexProjection cs l 1 (cs.wordProd l)) := by
  intro m n h
  apply bottSection_injective cs l hl
  exact Subtype.ext h

 theorem bottVertexProjection_stable (l : List I) (u b : W)
    (a : SymmetricCoefficient (M := M)) :
    (fun x : Interval cs u b => coefficientAction cs x.val a) ∈
      stabilizer (LinearMap.range (bottVertexProjection cs l u b)) := by
  rintro z ⟨m,rfl⟩
  refine ⟨bottSamelsonRight cs l a m,?_⟩
  funext x
  exact bottStalkProjection_right cs l x.val a m

 theorem bottVertexProjection_scaled (l : List I) (hl : cs.IsReduced l)
    (z : ∀ x : Interval cs 1 (cs.wordProd l), bottStalk cs l x.val) :
    bottCoordinateDenominator cs l • z ∈
      LinearMap.range (bottVertexProjection cs l 1 (cs.wordProd l)) := by
  let c (e : BottIndex l) : SymmetricCoefficient (M := M) :=
    (z ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩).val ⟨e,rfl⟩
  obtain ⟨m,hm⟩ := bottEvaluation_contains_scaled_coordinates cs l c
  refine ⟨m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  exact hm e


 theorem bottSection_pair_lift (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (x y : Interval cs u b) (t : W) (ht : cs.IsReflection t) (he : t*x.val=y.val) :
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x.val m=s.val x ∧ bottStalkProjection cs l y.val m=s.val y := by
  have he' : t*y.val=x.val := by
    rw [← he,← mul_assoc,ht.mul_self,one_mul]
  have hne : cs.length y.val ≠ cs.length x.val := by
    rw [← he]
    exact ht.length_mul_right_ne x.val
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let e : Edge cs u b := ⟨(y,x),hlt,⟨t,ht,he'.symm⟩⟩
    have hs := s.property e (Set.mem_univ _) (Set.mem_univ _)
    obtain ⟨m,hm,hn⟩ := (PairProjection.compatible_iff _ _ _ _).mp hs
    exact ⟨m,hn,hm⟩
  · let e : Edge cs u b := ⟨(x,y),hlt,⟨t,ht,he.symm⟩⟩
    have hs := s.property e (Set.mem_univ _) (Set.mem_univ _)
    exact (PairProjection.compatible_iff _ _ _ _).mp hs

 theorem bottSection_prime_lift (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) (x : Interval cs u b) :
    ∃ m : BottSamelsonModule cs l, ∀ y : Interval cs u b,
      (∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a) →
      bottStalkProjection cs l y.val m=s.val y := by
  classical
  by_cases hx : ∃ y : Interval cs u b, x ≠ y ∧
      ∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a
  · obtain ⟨y,hxy,hcon⟩ := hx
    obtain ⟨t,ht,he,hclass⟩ := prime_character_class cs p hp
      (fun h => hxy (Subtype.ext h)) hcon
    obtain ⟨m,hm,hn⟩ := bottSection_pair_lift cs l u b s x y t ht he.symm
    refine ⟨m,?_⟩
    intro z hz
    rcases (hclass z.val).mp hz with hxz | hzy
    · have h : z=x := Subtype.ext hxz.symm
      subst z
      exact hm
    · have h : z=y := Subtype.ext (hzy.trans he.symm)
      subst z
      exact hn
  · obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val (s.val x)
    refine ⟨m,?_⟩
    intro y hy
    have h : y=x := by
      by_contra h
      exact hx ⟨y,Ne.symm h,hy⟩
    subst y
    exact hm

 theorem bottSection_local_denominator (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) :
    ∃ a : SymmetricCoefficient (M := M), ¬ p ∣ a ∧ a • s.val ∈
      LinearMap.range (bottVertexProjection cs l u b) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  apply character_local_denominator (E := fun x : Interval cs u b => bottStalk cs l x.val)
    (LinearMap.range (bottVertexProjection cs l u b)) p hp
    (fun a x => coefficientAction cs x.val a) (fun a => bottVertexProjection_stable cs l u b a) s.val
  intro x
  obtain ⟨m,hm⟩ := bottSection_prime_lift cs l u b s p hp x
  exact ⟨bottVertexProjection cs l u b m,⟨m,rfl⟩,hm⟩

 theorem bottSection_surjective (l : List I) (hl : cs.IsReduced l) :
    Function.Surjective (bottSection cs l 1 (cs.wordProd l)) := by
  intro s
  let L := LinearMap.range (bottVertexProjection cs l 1 (cs.wordProd l))
  let : Module.Free (SymmetricCoefficient (M := M)) L :=
    Module.Free.of_equiv (LinearEquiv.ofInjective _ (bottVertexProjection_injective cs l hl))
  let : UniqueFactorizationMonoid (SymmetricCoefficient (M := M)) :=
    (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis ℝ (Extended M))).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have h : s.val ∈ L := EdgeLattice.mem_of_prime_local_membership L s.val
    ⟨bottCoordinateDenominator cs l,bottCoordinateDenominator_ne_zero cs l,
      bottVertexProjection_scaled cs l hl s.val⟩
    (fun p hp => bottSection_local_denominator cs l 1 (cs.wordProd l) s p hp)
  obtain ⟨m,hm⟩ := h
  exact ⟨m,Subtype.ext hm⟩

 def bottSectionEquiv (l : List I) (hl : cs.IsReduced l) :
    BottSamelsonModule cs l ≃ₗ[SymmetricCoefficient (M := M)]
      (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ :=
  LinearEquiv.ofBijective (bottSection cs l 1 (cs.wordProd l))
    ⟨bottSection_injective cs l hl,bottSection_surjective cs l hl⟩

end
end KLInvariance.TitsSpace

end


section

namespace TransportPerfectPairing
open Module
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

theorem balanced (e : M ≃ₗ[A] N) (D : M ≃ₗ[A] Dual A M) (a : End A M)
    (h : ∀ x y, D (a x) y = D x (a y)) (s z : N) :
    (e.symm.trans (D.trans e.symm.dualMap))
      ((e.toLinearMap.comp (a.comp e.symm.toLinearMap)) s) z =
    (e.symm.trans (D.trans e.symm.dualMap)) s
      ((e.toLinearMap.comp (a.comp e.symm.toLinearMap)) z) := by
  change D (e.symm (e (a (e.symm s)))) (e.symm z) =
    D (e.symm s) (e.symm (e (a (e.symm z))))
  simp only [LinearEquiv.symm_apply_apply]
  exact h _ _

theorem symmetric (e : M ≃ₗ[A] N) (D : M ≃ₗ[A] Dual A M)
    (h : ∀ x y, D x y = D y x) (s z : N) :
    (e.symm.trans (D.trans e.symm.dualMap)) s z =
    (e.symm.trans (D.trans e.symm.dualMap)) z s :=
  h (e.symm s) (e.symm z)

end TransportPerfectPairing

end


section

/-! Integral perfect balanced self-duality on all sections of the genuine
word projection sheaf. This is the word object, NOT the indecomposable BMP
object. Selection of a BMP summand with the required normalization is not
made or assumed here. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSectionDuality (l : List I) (hl : cs.IsReduced l) :
    (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M))
        ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :=
  (bottSectionEquiv cs l hl).symm.trans
    ((bottSamelsonDuality cs l).trans (bottSectionEquiv cs l hl).symm.dualMap)

 theorem bottSectionDuality_apply (l : List I) (hl : cs.IsReduced l)
    (m n : BottSamelsonModule cs l) :
    bottSectionDuality cs l hl (bottSection cs l 1 (cs.wordProd l) m)
      (bottSection cs l 1 (cs.wordProd l) n) = bottSamelsonDuality cs l m n := by
  change bottSamelsonDuality cs l
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) m))
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) n))= _
  simp only [LinearEquiv.symm_apply_apply]

 def bottSectionRight (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M)) :
    End (SymmetricCoefficient (M := M))
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :=
  (bottSectionEquiv cs l hl).toLinearMap.comp
    ((bottSamelsonRight cs l a).comp (bottSectionEquiv cs l hl).symm.toLinearMap)

 theorem bottSectionRight_apply (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottSectionRight cs l hl a (bottSection cs l 1 (cs.wordProd l) m) =
      bottSection cs l 1 (cs.wordProd l) (bottSamelsonRight cs l a m) := by
  change (bottSectionEquiv cs l hl) (bottSamelsonRight cs l a
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) m))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

 theorem bottSectionRight_coordinates (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M))
    (s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    (bottSectionRight cs l hl a s).val x=coefficientAction cs x.val a • s.val x := by
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  rw [bottSectionRight_apply]
  exact bottStalkProjection_right cs l x.val a m

 theorem bottSection_balanced (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M))
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl (bottSectionRight cs l hl a s) z =
      bottSectionDuality cs l hl s (bottSectionRight cs l hl a z) := by
  exact TransportPerfectPairing.balanced (bottSectionEquiv cs l hl)
    (bottSamelsonDuality cs l) (bottSamelsonRight cs l a)
    (bottSamelson_balanced cs l a) s z

 theorem bottSection_symmetric (l : List I) (hl : cs.IsReduced l)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl s z=bottSectionDuality cs l hl z s := by
  exact TransportPerfectPairing.symmetric (bottSectionEquiv cs l hl)
    (bottSamelsonDuality cs l) (bottSamelson_symmetric cs l) s z

end
end KLInvariance.TitsSpace

end


section

/-! The word SECTION pairing has precisely the word-length shift in the
actual coordinatewise sheaf grading. It is not an asserted pairing on the
indecomposable BMP boundary sheaf. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPiece_iff_stalks (l : List I) (hl : cs.IsReduced l) (n : ℤ)
    (m : BottSamelsonModule cs l) : m ∈ bottPiece cs basis l n ↔
      ∀ x : Interval cs 1 (cs.wordProd l),
        bottStalkProjection cs l x.val m ∈ bottStalkPiece cs basis l x.val n := by
  constructor
  · intro hm x
    exact bottStalkProjection_homogeneous cs basis l x.val n m hm
  · intro hm
    have he : component (bottPiece cs basis l) n m=m := by
      apply bottVertexProjection_injective cs l hl
      funext x
      have hh := map_component (bottPiece cs basis l) (bottStalkPiece cs basis l x.val)
        (bottStalkProjection cs l x.val) 0 (by
          simpa only [add_zero] using bottStalkProjection_homogeneous cs basis l x.val) n m
      rw [sub_zero,show component (bottStalkPiece cs basis l x.val) n
        (bottStalkProjection cs l x.val m)=bottStalkProjection cs l x.val m from
        DirectSum.decompose_of_mem_same _ (hm x)] at hh
      exact hh.symm
    rw [← he]
    exact (DirectSum.decompose (bottPiece cs basis l) m n).property

 theorem bottSectionDuality_homogeneous (l : List I) (hl : cs.IsReduced l)
    (i j : ℤ)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hs : ∀ x, s.val x ∈ bottStalkPiece cs basis l x.val i)
    (hz : ∀ x, z.val x ∈ bottStalkPiece cs basis l x.val j) :
    bottSectionDuality cs l hl s z ∈ symmetricGrading basis (i+j-l.length) := by
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  obtain ⟨n,rfl⟩ := bottSection_surjective cs l hl z
  rw [bottSectionDuality_apply]
  exact bottDuality_homogeneous cs basis l ((bottPiece_iff_stalks cs basis l hl i m).mpr hs)
    ((bottPiece_iff_stalks cs basis l hl j n).mpr hz)

end
end KLInvariance.TitsSpace

end


section

/-! Section maps for the actual graded sheaf morphisms. A sheaf splitting
really gives an integral graded section splitting; it is not replaced by a
generic-fibre splitting. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def Hom.assignmentMap (h : Hom B C) : B.forget.Assignment →ₗ[A] C.forget.Assignment where
  toFun f x := (h.vertex x).map (f x)
  map_add' f g := by funext x; exact map_add (h.vertex x).map (f x) (g x)
  map_smul' r f := by funext x; exact map_smul (h.vertex x).map r (f x)

 theorem Hom.assignmentMap_compatible (h : Hom B C) (Ω : Set V)
    (f : B.forget.Assignment) (hf : B.forget.CompatibleOn Ω f) :
    C.forget.CompatibleOn Ω (h.assignmentMap f) := by
  intro e hs ht
  change (C.lower e).map ((h.vertex _).map (f _)) =
    (C.upper e).map ((h.vertex _).map (f _))
  exact (h.lower e (f (G.source e))).symm.trans
    ((congrArg (h.edge e).map (hf e hs ht)).trans (h.upper e (f (G.target e))))

 def Hom.sectionMap (h : Hom B C) (Ω : Set V) :
    B.forget.sections Ω →ₗ[A] C.forget.sections Ω :=
  (h.assignmentMap.domRestrict (B.forget.sections Ω)).codRestrict (C.forget.sections Ω)
    (fun f => h.assignmentMap_compatible Ω f.val f.property)

 theorem Hom.sectionMap_apply (h : Hom B C) (Ω : Set V)
    (f : B.forget.sections Ω) (x : V) :
    (h.sectionMap Ω f).val x=(h.vertex x).map (f.val x) := rfl

 variable [Fintype V] [Fintype E] [IsNoetherianRing A]

 def Hom.gradedSectionMap (h : Hom B C) (Ω : Set V) :
    ModuleData.Hom (B.sections Ω) (C.sections Ω) where
  map := h.sectionMap Ω
  graded := by
    intro n f hf x hx
    exact (h.vertex x).graded n (f.val x) (hf x hx)

omit [Fintype V] [Fintype E] [IsNoetherianRing A] in
 theorem SplitIn.sections_split (s : SplitIn B C) (Ω : Set V)
    (f : B.forget.sections Ω) :
    s.projection.sectionMap Ω (s.inclusion.sectionMap Ω f)=f := by
  apply Subtype.ext
  funext x
  exact s.vertex_split x (f.val x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Endomorphisms of the ACTUAL graded word sheaf act on its integral tensor
module and preserve every stalk kernel and single-weight support lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 def bottEndOfSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSectionEquiv cs l hl).symm.toLinearMap.comp
    ((h.sectionMap Set.univ).comp (bottSectionEquiv cs l hl).toLinearMap)

 theorem bottEndOfSheaf_coordinates (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (m : BottSamelsonModule cs l) (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottEndOfSheaf cs basis l hl h m)=
      (h.vertex x).map (bottStalkProjection cs l x.val m) := by
  have he := congrArg (fun s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    s.val x) ((bottSectionEquiv cs l hl).apply_symm_apply
      (h.sectionMap Set.univ ((bottSectionEquiv cs l hl) m)))
  exact he

 theorem bottEndOfSheaf_homogeneous (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottEndOfSheaf cs basis l hl h m ∈ bottPiece cs basis l n := by
  apply (bottPiece_iff_stalks cs basis l hl n _).mpr
  intro x
  rw [bottEndOfSheaf_coordinates]
  exact (h.vertex x).graded n _ (bottStalkProjection_homogeneous cs basis l x.val n m hm)

 theorem bottEndOfSheaf_preserves_kernel (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x.val m=0) :
    bottStalkProjection cs l x.val (bottEndOfSheaf cs basis l hl h m)=0 := by
  rw [bottEndOfSheaf_coordinates,hm]
  exact (h.vertex x).map.map_zero

 theorem bottEndOfSheaf_preserves_support (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : m ∈ bottWeightSupported cs l x.val) :
    bottEndOfSheaf cs basis l hl h m ∈ bottWeightSupported cs l x.val := by
  intro e he
  let y : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hmy : bottStalkProjection cs l y.val m=0 := by
    apply Subtype.ext
    funext f
    exact hm f.val (fun hx => he (f.property.symm.trans hx))
  have hfy := bottEndOfSheaf_preserves_kernel cs basis l hl h y m hmy
  exact congrFun (congrArg Subtype.val hfy) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace

end


section

namespace LinearDescent
universe ur um ux
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {X : Type ux} [AddCommGroup X] [Module R X]
  (f : M →ₗ[R] X) (hf : Function.Surjective f) (e : Module.End R M)
  (he : ∀ m, f m=0 → f (e m)=0)
noncomputable section

 def descend : Module.End R X :=
  ((LinearMap.ker f).liftQ (f.comp e) he).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (m : M) : descend f hf e he (f m)=f (e m) := by
  change (LinearMap.ker f).liftQ (f.comp e) he
    ((f.quotKerEquivOfSurjective hf).symm (f m))=f (e m)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

 theorem descend_idempotent (hee : ∀ m, e (e m)=e m) (x : X) :
    descend f hf e he (descend f hf e he x)=descend f hf e he x := by
  obtain ⟨m,rfl⟩ := hf x
  rw [descend_apply,descend_apply,hee]

end
end LinearDescent

end


section

namespace KLInvariance.Graded.ModuleData
open PairProjection LinearDescent
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (e : Hom M M) (f : Hom M X) (g : Hom M Y)
  (hf : Function.Surjective f.map) (hg : Function.Surjective g.map)
  (hef : ∀ m, f.map m=0 → f.map (e.map m)=0)
  (heg : ∀ m, g.map m=0 → g.map (e.map m)=0)
noncomputable section

 def descended : Hom X X where
  map := descend f.map hf e.map hef
  graded := by
    intro n x hx
    obtain ⟨m,hm,rfl⟩ := f.homogeneous_lift hf n x hx
    rw [descend_apply]
    exact f.graded n _ (e.graded n m hm)

include heg in
 theorem lower_kernel_preserved (x : X) (hx : lower f.map g.map x=0) :
    lower f.map g.map ((descended e f hf hef).map x)=0 := by
  obtain ⟨m,hm,hn⟩ := (kernel_lower f.map g.map x).mp hx
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨e.map m,?_,heg m hn⟩
  rw [← hm]
  exact (descend_apply f.map hf e.map hef m).symm

 def descendedEdge : Hom (pairEdge f g hg) (pairEdge f g hg) where
  map := descend (lower f.map g.map) (lower_surjective f.map g.map hg)
    (descended e f hf hef).map (lower_kernel_preserved e f g hf hef heg)
  graded := by
    intro n z hz
    obtain ⟨x,hx,rfl⟩ := hz
    refine ⟨(descended e f hf hef).map x,(descended e f hf hef).graded n x hx,?_⟩
    exact (descend_apply (lower f.map g.map) (lower_surjective f.map g.map hg)
      (descended e f hf hef).map (lower_kernel_preserved e f g hf hef heg) x).symm

 theorem descendedEdge_lower (x : X) :
    (descendedEdge e f g hf hg hef heg).map (lower f.map g.map x)=
      lower f.map g.map ((descended e f hf hef).map x) :=
  descend_apply _ _ _ _ x

 theorem descendedEdge_upper (y : Y) :
    (descendedEdge e f g hf hg hef heg).map (upper f.map g.map y)=
      upper f.map g.map ((descended e g hg heg).map y) := by
  obtain ⟨m,rfl⟩ := hg y
  rw [← compatible f.map g.map m,descendedEdge_lower]
  change lower f.map g.map (descend f.map hf e.map hef (f.map m)) =
    upper f.map g.map (descend g.map hg e.map heg (g.map m))
  rw [descend_apply,descend_apply]
  exact compatible f.map g.map (e.map m)

end
end KLInvariance.Graded.ModuleData

end


section

/-! The adjoint of an actual graded word-sheaf endomorphism is again an
integral graded word-sheaf endomorphism. No stalk freeness or BMP character
is used or asserted. This supplies the correct adjoint route for a future
BMP summand, instead of restricting a form to an arbitrary summand. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 def bottAdjointWordHom (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    ModuleData.Hom (bottWordData cs basis l) (bottWordData cs basis l) where
  map := bottAdjoint cs l (bottEndOfSheaf cs basis l hl h)
  graded := bottAdjoint_homogeneous cs basis l _
    (bottEndOfSheaf_homogeneous cs basis l hl h)

 theorem bottAdjointWordHom_kernel (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x.val m=0) :
    bottStalkProjection cs l x.val ((bottAdjointWordHom cs basis l hl h).map m)=0 :=
  bottAdjoint_preserves_kernel cs l x.val _
    (bottEndOfSheaf_preserves_support cs basis l hl h x) m hm

 def bottAdjointSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)) where
  vertex x := ModuleData.descended (bottAdjointWordHom cs basis l hl h)
    (bottStalkHom cs basis l x.val) (bottStalkHom_surjective cs basis l x.val)
    (bottAdjointWordHom_kernel cs basis l hl h x)
  edge e := ModuleData.descendedEdge (bottAdjointWordHom cs basis l hl h)
    (bottStalkHom cs basis l (source cs 1 (cs.wordProd l) e).val)
    (bottStalkHom cs basis l (target cs 1 (cs.wordProd l) e).val)
    (bottStalkHom_surjective cs basis l _)
    (bottStalkHom_surjective cs basis l _)
    (bottAdjointWordHom_kernel cs basis l hl h _)
    (bottAdjointWordHom_kernel cs basis l hl h _)
  lower _ x := ModuleData.descendedEdge_lower _ _ _ _ _ _ _ x
  upper _ y := ModuleData.descendedEdge_upper _ _ _ _ _ _ _ y

 theorem bottAdjointSheaf_vertex (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map (bottStalkProjection cs l x.val m)=
      bottStalkProjection cs l x.val (bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) m) :=
  LinearDescent.descend_apply _ _ _ _ m

 theorem bottEndOfAdjointSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottEndOfSheaf cs basis l hl (bottAdjointSheaf cs basis l hl h)=
      bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  exact (bottEndOfSheaf_coordinates cs basis l hl _ m x).trans
    (bottAdjointSheaf_vertex cs basis l hl h x m)

end
end KLInvariance.TitsSpace

end


section

/-! Integral graded adjoint WORD projectors. The assumption below is only
that the GIVEN endomorphism is a projector; no existence of a BMP projector
or identification of its image with its adjoint is asserted. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottEndOfSheaf_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : BottSamelsonModule cs l) :
    bottEndOfSheaf cs basis l hl h (bottEndOfSheaf cs basis l hl h m)=
      bottEndOfSheaf cs basis l hl h m := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  simp only [bottEndOfSheaf_coordinates]
  exact hh x _

 theorem bottAdjointSheaf_vertex_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (x : Interval cs 1 (cs.wordProd l))
    (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map
      (((bottAdjointSheaf cs basis l hl h).vertex x).map v)=
      ((bottAdjointSheaf cs basis l hl h).vertex x).map v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  simp only [bottAdjointSheaf_vertex]
  exact congrArg (bottStalkProjection cs l x.val)
    (PerfectAdjoint.adjoint_idempotent (bottSamelsonDuality cs l) _
      (bottEndOfSheaf_idempotent cs basis l hl h hh) m)

 theorem bottAdjointSheaf_edge_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (e : Edge cs 1 (cs.wordProd l))
    (v : (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).edge e) :
    ((bottAdjointSheaf cs basis l hl h).edge e).map
      (((bottAdjointSheaf cs basis l hl h).edge e).map v)=
      ((bottAdjointSheaf cs basis l hl h).edge e).map v := by
  have hs : Function.Surjective
      ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).lower e).map :=
    bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  obtain ⟨m,rfl⟩ := hs v
  simp only [(bottAdjointSheaf cs basis l hl h).lower]
  exact congrArg ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).lower e).map
    (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh _ m)

 theorem bottAdjointSheaf_twice_vertex (x : Interval cs 1 (cs.wordProd l))
    (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl (bottAdjointSheaf cs basis l hl h)).vertex x).map v=
      (h.vertex x).map v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  rw [bottAdjointSheaf_vertex,bottEndOfAdjointSheaf]
  change bottStalkProjection cs l x.val
    (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl h)) m)=_
  rw [PerfectAdjoint.adjoint_adjoint _ (bottSamelson_symmetric cs l)]
  exact bottEndOfSheaf_coordinates cs basis l hl h m x

end
end KLInvariance.TitsSpace

end


section

/-! The literal integral image sheaf of a graded projector, with its actual
splitting. Used for word-adjoint projectors; no BMP summand is assumed. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {M N : ModuleData.{uk,ua,um} 𝓐}
noncomputable section

 def rangeMap (e : Hom M M) (f : Hom N N) (g : Hom M N)
    (h : ∀ m, f.map (g.map m)=g.map (e.map m)) : Hom (range e) (range f) where
  map := (g.map.domRestrict e.map.range).codRestrict f.map.range (by
    rintro ⟨_,m,rfl⟩
    exact ⟨g.map m,h m⟩)
  graded n m hm := g.graded n m.val hm

 def rangeInclusion (e : Hom M M) : Hom (range e) M where
  map := e.map.range.subtype
  graded _ _ hm := hm

 def rangeProjection (e : Hom M M) : Hom M (range e) where
  map := e.map.rangeRestrict
  graded n m hm := e.graded n m hm

end
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def Hom.image (h : Hom B B) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.range (h.vertex x)
  edge e := ModuleData.range (h.edge e)
  lower e := ModuleData.rangeMap (h.vertex (G.source e)) (h.edge e) (B.lower e) (h.lower e)
  upper e := ModuleData.rangeMap (h.vertex (G.target e)) (h.edge e) (B.upper e) (h.upper e)

 def Hom.imageInclusion (h : Hom B B) : Hom h.image B where
  vertex x := ModuleData.rangeInclusion (h.vertex x)
  edge e := ModuleData.rangeInclusion (h.edge e)
  lower _ _ := rfl
  upper _ _ := rfl

 def Hom.imageProjection (h : Hom B B) : Hom B h.image where
  vertex x := ModuleData.rangeProjection (h.vertex x)
  edge e := ModuleData.rangeProjection (h.edge e)
  lower e v := Subtype.ext (h.lower e v)
  upper e v := Subtype.ext (h.upper e v)

 def Hom.imageSplit (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (he : ∀ e v, (h.edge e).map ((h.edge e).map v)=(h.edge e).map v) : SplitIn h.image B where
  inclusion := h.imageInclusion
  projection := h.imageProjection
  vertex_split x v := by
    obtain ⟨m,hm⟩ := v.property
    apply Subtype.ext
    change (h.vertex x).map v.val=v.val
    rw [← hm,hv]
  edge_split e v := by
    obtain ⟨m,hm⟩ := v.property
    apply Subtype.ext
    change (h.edge e).map v.val=v.val
    rw [← hm,he]

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! All integral sections of an idempotent image sheaf are the image of the
actual section projector; this is stronger than equality over the fraction
field and requires the actual idempotence, not merely pointwise surjectivity. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem Hom.imageSection_fixed (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) (f : h.image.forget.sections Ω) :
    h.sectionMap Ω (h.imageInclusion.sectionMap Ω f)=h.imageInclusion.sectionMap Ω f := by
  apply Subtype.ext
  funext x
  obtain ⟨v,hv'⟩ := (f.val x).property
  change (h.vertex x).map (f.val x).val=(f.val x).val
  rw [← hv',hv]

 def Hom.imageSectionMap (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : h.image.forget.sections Ω →ₗ[A] LinearMap.range (h.sectionMap Ω) :=
  (h.imageInclusion.sectionMap Ω).codRestrict _ (fun f =>
    ⟨h.imageInclusion.sectionMap Ω f,h.imageSection_fixed hv Ω f⟩)

 theorem Hom.imageSectionMap_bijective (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : Function.Bijective (h.imageSectionMap hv Ω) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val (congrArg Subtype.val hfg)) x
  · rintro ⟨s,m,rfl⟩
    refine ⟨h.imageProjection.sectionMap Ω m,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

 def Hom.imageSectionEquiv (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : h.image.forget.sections Ω ≃ₗ[A] LinearMap.range (h.sectionMap Ω) :=
  LinearEquiv.ofBijective (h.imageSectionMap hv Ω) (h.imageSectionMap_bijective hv Ω)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace ConjugateRange
open Module
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (e : M ≃ₗ[R] N) (f : End R N)
noncomputable section

 def conjugate : End R M := e.symm.toLinearMap.comp (f.comp e.toLinearMap)

 def map : LinearMap.range f →ₗ[R] LinearMap.range (conjugate e f) :=
  (e.symm.toLinearMap.domRestrict f.range).codRestrict _ (by
    rintro ⟨_,n,rfl⟩
    refine ⟨e.symm n,?_⟩
    change e.symm (f (e (e.symm n)))=e.symm (f n)
    rw [LinearEquiv.apply_symm_apply])

 theorem map_bijective : Function.Bijective (map e f) := by
  constructor
  · intro m n h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val h
  · rintro ⟨_,m,rfl⟩
    refine ⟨⟨f (e m),e m,rfl⟩,?_⟩
    rfl

 def equiv : LinearMap.range f ≃ₗ[R] LinearMap.range (conjugate e f) :=
  LinearEquiv.ofBijective (map e f) (map_bijective e f)

 theorem equiv_apply (n : LinearMap.range f) : (equiv e f n).val=e.symm n.val := rfl

end
end ConjugateRange

end


section

/-! The correct integral summand duality. A chosen summand of a perfectly
paired module is paired with its ADJOINT summand, not with itself by fiat.
This is the algebraic connector for the unresolved BMP summand recognition.
No existence of a BMP summand, or isomorphism with its adjoint, is asserted. -/
namespace AdjointSummandDuality
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (d : M ≃ₗ[R] Module.Dual R M) (i : N →ₗ[R] M) (p : M →ₗ[R] N)
  (hpi : ∀ n, p (i n)=n)
noncomputable section

 def dualSection : Module.Dual R N →ₗ[R] M :=
  d.symm.toLinearMap.comp p.dualMap

 def dualProjection : M →ₗ[R] Module.Dual R N := i.dualMap.comp d.toLinearMap

include hpi in
 theorem projection_section (lam : Module.Dual R N) :
    dualProjection d i (dualSection d p lam)=lam := by
  apply LinearMap.ext
  intro n
  change d (d.symm (p.dualMap lam)) (i n)=lam n
  rw [LinearEquiv.apply_symm_apply]
  change lam (p (i n))=lam n
  rw [hpi]

 def adjointProjector : Module.End R M := (dualSection d p).comp (dualProjection d i)

include hpi in
 theorem adjointProjector_idempotent (m : M) :
    adjointProjector d i p (adjointProjector d i p m)=adjointProjector d i p m := by
  change dualSection d p (dualProjection d i (dualSection d p (dualProjection d i m))) = _
  rw [projection_section d i p hpi]
  rfl

 def adjointSummand : Submodule R M := LinearMap.range (dualSection d p)

include hpi in
 theorem dualProjection_injective_on_adjoint :
    Function.Injective ((dualProjection d i).domRestrict (adjointSummand d p)) := by
  rintro ⟨m,lam,rfl⟩ ⟨n,mu,rfl⟩ h
  apply Subtype.ext
  change dualSection d p lam=dualSection d p mu
  change dualProjection d i (dualSection d p lam)=dualProjection d i (dualSection d p mu) at h
  rw [projection_section d i p hpi,projection_section d i p hpi] at h
  rw [h]

include hpi in
 theorem dualProjection_surjective_on_adjoint :
    Function.Surjective ((dualProjection d i).domRestrict (adjointSummand d p)) := by
  intro lam
  exact ⟨⟨dualSection d p lam,lam,rfl⟩,projection_section d i p hpi lam⟩

 def adjointEquivDual : adjointSummand d p ≃ₗ[R] Module.Dual R N :=
  LinearEquiv.ofBijective ((dualProjection d i).domRestrict (adjointSummand d p))
    ⟨dualProjection_injective_on_adjoint d i p hpi,dualProjection_surjective_on_adjoint d i p hpi⟩

 theorem adjointEquivDual_apply (m : adjointSummand d p) (n : N) :
    adjointEquivDual d i p hpi m n=d m.val (i n) := rfl

include hpi in
 theorem adjointProjector_range :
    LinearMap.range (adjointProjector d i p)=adjointSummand d p := by
  apply le_antisymm
  · rintro m ⟨n,rfl⟩
    exact ⟨dualProjection d i n,rfl⟩
  · rintro m ⟨lam,rfl⟩
    refine ⟨dualSection d p lam,?_⟩
    change dualSection d p (dualProjection d i (dualSection d p lam))=dualSection d p lam
    rw [projection_section d i p hpi]

variable (f : Module.End R M) (g : Module.End R N)
  (hbal : ∀ m n, d (f m) n=d m (f n))
  (hi : ∀ n, f (i n)=i (g n)) (hp : ∀ m, p (f m)=g (p m))

include hbal hi in
 theorem projection_intertwines (m : M) :
    dualProjection d i (f m)=g.dualMap (dualProjection d i m) := by
  apply LinearMap.ext
  intro n
  change d (f m) (i n)=d m (i (g n))
  rw [hbal,hi]

include hbal hp in
 theorem section_intertwines (lam : Module.Dual R N) :
    f (dualSection d p lam)=dualSection d p (g.dualMap lam) := by
  apply d.injective
  apply LinearMap.ext
  intro n
  change d (f (d.symm (p.dualMap lam))) n=
    d (d.symm (p.dualMap (g.dualMap lam))) n
  rw [hbal,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change lam (p (f n))=lam (g (p n))
  rw [hp]

include hbal hi hp in
 theorem adjointProjector_commutes (m : M) :
    f (adjointProjector d i p m)=adjointProjector d i p (f m) := by
  change f (dualSection d p (dualProjection d i m)) =
    dualSection d p (dualProjection d i (f m))
  rw [section_intertwines d p f g hbal hp,projection_intertwines d i f g hbal hi]

end
end AdjointSummandDuality

end


section

/-! The range of the genuine adjoint projector is integrally the dual of
the original summand, with no assumed self-duality of that summand. -/
namespace PerfectAdjoint
open Module
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (d : M ≃ₗ[R] Dual R M) (i : N →ₗ[R] M) (p : M →ₗ[R] N)
  (hpi : ∀ n, p (i n)=n)
noncomputable section

 theorem adjoint_projector_eq : adjoint d (i.comp p)=
    AdjointSummandDuality.adjointProjector d i p := by
  apply LinearMap.ext
  intro m
  rfl

 def rangeAdjointEquivDual : LinearMap.range (adjoint d (i.comp p)) ≃ₗ[R] Dual R N :=
  (LinearEquiv.ofEq _ _ (by
    rw [adjoint_projector_eq,AdjointSummandDuality.adjointProjector_range d i p hpi])).trans
    (AdjointSummandDuality.adjointEquivDual d i p hpi)

 theorem rangeAdjointEquivDual_apply (m : LinearMap.range (adjoint d (i.comp p))) (n : N) :
    rangeAdjointEquivDual d i p hpi m n=d m.val (i n) := rfl

end
end PerfectAdjoint

end


section

namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M) (f : End R M) (hf : ∀ m, f (f m)=f m)
noncomputable section

include hf in
 theorem range_projector_split (m : f.range) : f.rangeRestrict (f.range.subtype m)=m := by
  apply Subtype.ext
  obtain ⟨n,hn⟩ := m.property
  change f m.val=m.val
  rw [← hn,hf]

 def rangeAdjointEquivDualRange : LinearMap.range (adjoint d f) ≃ₗ[R] Dual R f.range :=
  rangeAdjointEquivDual d f.range.subtype f.rangeRestrict (range_projector_split f hf)

 theorem rangeAdjointEquivDualRange_apply (m : LinearMap.range (adjoint d f)) (n : f.range) :
    rangeAdjointEquivDualRange d f hf m n=d m.val n.val := rfl

end
end PerfectAdjoint

end


section

namespace KLInvariance.TitsSpace
open Module
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))

include basis in
 theorem symmetricCoefficientNoetherian : IsNoetherianRing (SymmetricCoefficient (M := M)) :=
  isNoetherianRing_of_surjective (MvPolynomial σ ℝ) (SymmetricCoefficient (M := M))
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).symm.surjective

end KLInvariance.TitsSpace

end


section

/-! The actual adjoint IMAGE sheaf has all integral sections dual to those
of the original projector image. This does not identify those two image
sheaves or assert that the word sheaf satisfies the BMP axioms. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottImageSheaf : GradedSheaf (𝓐 := symmetricGrading basis)
    (graph cs 1 (cs.wordProd l)) := by
  letI := symmetricCoefficientNoetherian basis
  exact h.image

 def bottImageSectionWordEquiv
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v) :
    (bottImageSheaf cs basis l h).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)] LinearMap.range (bottEndOfSheaf cs basis l hl h) := by
  letI := symmetricCoefficientNoetherian basis
  exact (h.imageSectionEquiv hh Set.univ).trans
    (ConjugateRange.equiv (bottSectionEquiv cs l hl) (h.sectionMap Set.univ))

 def bottAdjointImageEquivDual
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v) :
    (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M))
        ((bottImageSheaf cs basis l h).forget.sections Set.univ) :=
  (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl h)
      (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh)).trans
    ((LinearEquiv.ofEq _ _ (congrArg LinearMap.range
        (bottEndOfAdjointSheaf cs basis l hl h))).trans
      ((PerfectAdjoint.rangeAdjointEquivDualRange (bottSamelsonDuality cs l)
          (bottEndOfSheaf cs basis l hl h)
          (bottEndOfSheaf_idempotent cs basis l hl h hh)).trans
        (bottImageSectionWordEquiv cs basis l hl h hh).dualMap))

 theorem bottImageSectionWordEquiv_coordinates
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val ((bottImageSectionWordEquiv cs basis l hl h hh m).val)=
      (m.val x).val := by
  let := symmetricCoefficientNoetherian basis
  exact congrArg (fun s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    s.val x) ((bottSectionEquiv cs l hl).apply_symm_apply
      (h.imageInclusion.sectionMap Set.univ m))

 theorem bottImageSectionWordEquiv_homogeneous
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (n : ℤ) (m : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈ ((bottImageSheaf cs basis l h).vertex x).piece n) :
    (bottImageSectionWordEquiv cs basis l hl h hh m).val ∈ bottPiece cs basis l n := by
  apply (bottPiece_iff_stalks cs basis l hl n _).mpr
  intro x
  rw [bottImageSectionWordEquiv_coordinates]
  exact hm x

 theorem bottAdjointImageEquivDual_apply
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ)
    (n : (bottImageSheaf cs basis l h).forget.sections Set.univ) :
    bottAdjointImageEquivDual cs basis l hl h hh m n=bottSamelsonDuality cs l
      (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl h)
        (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh) m).val
      (bottImageSectionWordEquiv cs basis l hl h hh n).val := rfl

 theorem bottAdjointImagePairing_homogeneous
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (i j : ℤ)
    (m : (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ)
    (n : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈
      ((bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).vertex x).piece i)
    (hn : ∀ x, n.val x ∈ ((bottImageSheaf cs basis l h).vertex x).piece j) :
    bottAdjointImageEquivDual cs basis l hl h hh m n ∈ symmetricGrading basis (i+j-(l.length : ℤ)) := by
  rw [bottAdjointImageEquivDual_apply]
  exact bottDuality_homogeneous cs basis l
    (bottImageSectionWordEquiv_homogeneous cs basis l hl _
      (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh) i m hm)
    (bottImageSectionWordEquiv_homogeneous cs basis l hl h hh j n hn)

end
end KLInvariance.TitsSpace

end


section

/-! A specified integral graded sheaf splitting identifies its source with
its literal projector image. No existence of a word/BMP splitting is assumed
outside each explicitly parametric helper. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 def SplitIn.projector : Hom C C := s.inclusion.comp s.projection

omit [IsNoetherianRing A] in
 theorem SplitIn.projector_vertex (x : V) (v : C.vertex x) :
    (s.projector.vertex x).map ((s.projector.vertex x).map v)=(s.projector.vertex x).map v := by
  change (s.inclusion.vertex x).map ((s.projection.vertex x).map
    ((s.inclusion.vertex x).map ((s.projection.vertex x).map v)))=_
  rw [s.vertex_split]
  rfl

omit [IsNoetherianRing A] in
 theorem SplitIn.projector_edge (e : E) (v : C.edge e) :
    (s.projector.edge e).map ((s.projector.edge e).map v)=(s.projector.edge e).map v := by
  change (s.inclusion.edge e).map ((s.projection.edge e).map
    ((s.inclusion.edge e).map ((s.projection.edge e).map v)))=_
  rw [s.edge_split]
  rfl

 def SplitIn.imageTo : Hom s.projector.image B := s.projection.comp s.projector.imageInclusion
 def SplitIn.toImage : Hom B s.projector.image := s.projector.imageProjection.comp s.inclusion

 theorem SplitIn.imageTo_toImage_vertex (x : V) (v : B.vertex x) :
    (s.imageTo.vertex x).map ((s.toImage.vertex x).map v)=v := by
  change (s.projection.vertex x).map ((s.inclusion.vertex x).map
    ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))=v
  rw [s.vertex_split,s.vertex_split]

 theorem SplitIn.toImage_imageTo_vertex (x : V) (v : s.projector.image.vertex x) :
    (s.toImage.vertex x).map ((s.imageTo.vertex x).map v)=v := by
  apply Subtype.ext
  obtain ⟨m,hm⟩ := v.property
  change (s.projector.vertex x).map ((s.projector.vertex x).map v.val)=v.val
  rw [s.projector_vertex,← hm,s.projector_vertex]

 theorem SplitIn.imageTo_toImage_edge (e : E) (v : B.edge e) :
    (s.imageTo.edge e).map ((s.toImage.edge e).map v)=v := by
  change (s.projection.edge e).map ((s.inclusion.edge e).map
    ((s.projection.edge e).map ((s.inclusion.edge e).map v)))=v
  rw [s.edge_split,s.edge_split]

 theorem SplitIn.toImage_imageTo_edge (e : E) (v : s.projector.image.edge e) :
    (s.toImage.edge e).map ((s.imageTo.edge e).map v)=v := by
  apply Subtype.ext
  obtain ⟨m,hm⟩ := v.property
  change (s.projector.edge e).map ((s.projector.edge e).map v.val)=v.val
  rw [s.projector_edge,← hm,s.projector_edge]

 theorem SplitIn.imageSection_bijective (Ω : Set V) :
    Function.Bijective (s.imageTo.sectionMap Ω) := by
  constructor
  · intro m n he
    apply Subtype.ext
    funext x
    have hx := congrFun (congrArg Subtype.val he) x
    have hy := congrArg (s.toImage.vertex x).map hx
    exact (s.toImage_imageTo_vertex x (m.val x)).symm.trans
      (hy.trans (s.toImage_imageTo_vertex x (n.val x)))
  · intro m
    refine ⟨s.toImage.sectionMap Ω m,?_⟩
    apply Subtype.ext
    funext x
    exact s.imageTo_toImage_vertex x (m.val x)

 def SplitIn.imageSectionEquiv (Ω : Set V) :
    s.projector.image.forget.sections Ω ≃ₗ[A] B.forget.sections Ω :=
  LinearEquiv.ofBijective (s.imageTo.sectionMap Ω) (s.imageSection_bijective Ω)

 theorem SplitIn.imageSectionEquiv_symm_apply (Ω : Set V) (m : B.forget.sections Ω) :
    (s.imageSectionEquiv Ω).symm m=s.toImage.sectionMap Ω m := by
  apply (s.imageSectionEquiv Ω).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  exact (s.imageTo_toImage_vertex x (m.val x)).symm

 theorem SplitIn.imageSectionEquiv_symm_homogeneous (Ω : Set V) (n : ℤ)
    (m : B.forget.sections Ω) (hm : ∀ x, m.val x ∈ (B.vertex x).piece n) (x : V) :
    ((s.imageSectionEquiv Ω).symm m).val x ∈ (s.projector.image.vertex x).piece n := by
  rw [s.imageSectionEquiv_symm_apply]
  exact (s.toImage.vertex x).graded n (m.val x) (hm x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Correct integral graded duality for a GIVEN word-sheaf summand: the dual
is realized by its ADJOINT image, not identified with the original summand.
The existence and BMP recognition of that summand remain separate. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitAdjointSheaf : GradedSheaf (𝓐 := symmetricGrading basis)
    (graph cs 1 (cs.wordProd l)) :=
  bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl s.projector)

 def bottSplitAdjointEquivDual :
    (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M)) (B.forget.sections Set.univ) := by
  letI := symmetricCoefficientNoetherian basis
  exact (bottAdjointImageEquivDual cs basis l hl s.projector s.projector_vertex).trans
    (s.imageSectionEquiv Set.univ).symm.dualMap

 theorem bottSplitAdjointPairing_homogeneous
    (i j : ℤ)
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (n : B.forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈ ((bottSplitAdjointSheaf cs basis l hl B s).vertex x).piece i)
    (hn : ∀ x, n.val x ∈ (B.vertex x).piece j) :
    bottSplitAdjointEquivDual cs basis l hl B s m n ∈
      symmetricGrading basis (i+j-(l.length : ℤ)) := by
  let := symmetricCoefficientNoetherian basis
  exact bottAdjointImagePairing_homogeneous cs basis l hl s.projector s.projector_vertex i j m
    ((s.imageSectionEquiv Set.univ).symm n) hm
    (s.imageSectionEquiv_symm_homogeneous Set.univ j n hn)

end
end KLInvariance.TitsSpace

end


section

/-! An actual word-sheaf endomorphism that is the identity at one stalk has
adjoint equal to the identity at that same stalk. In particular, an identity
TOP projector stays normalized on taking the adjoint. This alone does not
supply free stalks, flabbiness, or the BMP character. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottEndOfSheaf_fixed_support (x : Interval cs 1 (cs.wordProd l))
    (hx : ∀ v, (h.vertex x).map v=v)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottWeightSupported cs l x.val) :
    bottEndOfSheaf cs basis l hl h m=m := by
  apply bottEvaluation_injective cs l
  funext e
  by_cases he : bottWeight cs l e=x.val
  · have ho := bottEndOfSheaf_coordinates cs basis l hl h m x
    exact congrFun (congrArg Subtype.val (ho.trans (hx _))) ⟨e,he⟩
  · exact (bottEndOfSheaf_preserves_support cs basis l hl h x m hm e he).trans
      (hm e he).symm

 theorem bottAdjointSheaf_fixed_stalk (x : Interval cs 1 (cs.wordProd l))
    (hx : ∀ v, (h.vertex x).map v=v) (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map v=v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  rw [bottAdjointSheaf_vertex]
  have hz : bottStalkProjection cs l x.val
      (bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) m-m)=0 := by
    apply (bott_projection_zero_iff_annihilates_support cs l x.val _).mpr
    intro z
    change bottSamelsonDuality cs l z.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
        (bottEndOfSheaf cs basis l hl h) m-m)=0
    rw [map_sub,PerfectAdjoint.symmetric_pairing _ (bottSamelson_symmetric cs l)]
    rw [bottEndOfSheaf_fixed_support cs basis l hl h x hx z.val z.property,sub_self]
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

 theorem bottAdjointSheaf_fixed_stalk_iff (x : Interval cs 1 (cs.wordProd l)) :
    (∀ v, ((bottAdjointSheaf cs basis l hl h).vertex x).map v=v) ↔
      (∀ v, (h.vertex x).map v=v) := by
  constructor
  · intro hx v
    have h' := bottAdjointSheaf_fixed_stalk cs basis l hl
      (bottAdjointSheaf cs basis l hl h) x hx v
    exact (bottAdjointSheaf_twice_vertex cs basis l hl h x v).symm.trans h'
  · exact fun hx v => bottAdjointSheaf_fixed_stalk cs basis l hl h x hx v

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M N : ModuleData.{uk,ua,um} 𝓐}
 theorem Hom.eq_of_map_eq (f g : Hom M N) (h : f.map=g.map) : f=g := by
  cases f
  cases g
  cases h
  rfl
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 theorem Hom.eq_of_maps (f g : Hom B C)
    (hv : ∀ x v, (f.vertex x).map v=(g.vertex x).map v)
    (he : ∀ e v, (f.edge e).map v=(g.edge e).map v) : f=g := by
  have hv' : f.vertex=g.vertex := funext (fun x =>
    ModuleData.Hom.eq_of_map_eq _ _ (LinearMap.ext (hv x)))
  have he' : f.edge=g.edge := funext (fun e =>
    ModuleData.Hom.eq_of_map_eq _ _ (LinearMap.ext (he e)))
  cases f
  cases g
  cases hv'
  cases he'
  rfl

 theorem Hom.eq_of_vertex (f g : Hom B C)
    (hs : ∀ e, Function.Surjective (B.lower e).map)
    (hv : ∀ x v, (f.vertex x).map v=(g.vertex x).map v) : f=g := by
  apply f.eq_of_maps g hv
  intro e v
  obtain ⟨w,rfl⟩ := hs e v
  rw [f.lower,g.lower,hv]

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Integral anti-involution on the actual graded word-sheaf endomorphisms.
This is the algebra required to compare an indecomposable BMP summand to
its adjoint, not an assertion that such a summand is already recognized. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottEndOfSheaf_comp
    (h g : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottEndOfSheaf cs basis l hl (h.comp g)=
      (bottEndOfSheaf cs basis l hl h).comp (bottEndOfSheaf cs basis l hl g) := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  exact (bottEndOfSheaf_coordinates cs basis l hl (h.comp g) m x).trans
    ((congrArg (h.vertex x).map (bottEndOfSheaf_coordinates cs basis l hl g m x)).symm.trans
      (bottEndOfSheaf_coordinates cs basis l hl h (bottEndOfSheaf cs basis l hl g m) x).symm)

 theorem bottAdjointSheaf_comp
    (h g : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottAdjointSheaf cs basis l hl (h.comp g)=
      (bottAdjointSheaf cs basis l hl g).comp (bottAdjointSheaf cs basis l hl h) := by
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · intro x v
    have hs : Function.Surjective (bottStalkProjection cs l x.val) :=
      bottStalkProjection_surjective cs l x.val
    obtain ⟨m,rfl⟩ := hs v
    change ((bottAdjointSheaf cs basis l hl (h.comp g)).vertex x).map
      (bottStalkProjection cs l x.val m)=
        ((bottAdjointSheaf cs basis l hl g).vertex x).map
          (((bottAdjointSheaf cs basis l hl h).vertex x).map (bottStalkProjection cs l x.val m))
    simp only [bottAdjointSheaf_vertex]
    change bottStalkProjection cs l x.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl (h.comp g)) m)=
      bottStalkProjection cs l x.val
        (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl g)
          (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl h) m))
    rw [bottEndOfSheaf_comp,PerfectAdjoint.adjoint_comp]
    rfl

 theorem bottAdjointSheaf_involutive : Function.Involutive (bottAdjointSheaf cs basis l hl) := by
  intro h
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · exact bottAdjointSheaf_twice_vertex cs basis l hl h

 theorem bottAdjointSheaf_injective : Function.Injective (bottAdjointSheaf cs basis l hl) :=
  (bottAdjointSheaf_involutive cs basis l hl).injective

end
end KLInvariance.TitsSpace

end


section

/-! The endomorphism-corner formulation of a primitive graded sheaf
projector. This is a criterion, not an assertion of a BMP splitting. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 def Hom.zero : Hom B C where
  vertex x := ⟨0,fun n _ _ => (C.vertex x).piece n |>.zero_mem⟩
  edge e := ⟨0,fun n _ _ => (C.edge e).piece n |>.zero_mem⟩
  lower e v := by simp
  upper e v := by simp

 def Hom.id (B : GradedSheaf (𝓐 := 𝓐) G) : Hom B B where
  vertex x := ModuleData.Hom.id (B.vertex x)
  edge e := ModuleData.Hom.id (B.edge e)
  lower _ _ := rfl
  upper _ _ := rfl

 def Hom.PrimitiveProjector (p : Hom B B) : Prop :=
  p.comp p=p ∧ ∀ f : Hom B B, f.comp f=f → f.comp p=f → p.comp f=f →
    f=Hom.zero ∨ f=p

 theorem Hom.primitive_of_antiInvolution
    (a : Hom B B → Hom B B)
    (ha : Function.Involutive a)
    (hac : ∀ f g, a (f.comp g)=(a g).comp (a f))
    (haz : a Hom.zero=Hom.zero)
    (p : Hom B B) (hp : p.PrimitiveProjector) :
    (a p).PrimitiveProjector := by
  constructor
  · exact (hac p p).symm.trans (congrArg a hp.1)
  · intro f hf hfp hpf
    have hi : (a f).comp (a f)=a f := (hac f f).symm.trans (congrArg a hf)
    have hleft : (a f).comp p=a f := by
      have hh := congrArg a hpf
      rw [hac,ha] at hh
      exact hh
    have hright : p.comp (a f)=a f := by
      have hh := congrArg a hfp
      rw [hac,ha] at hh
      exact hh
    rcases hp.2 (a f) hi hleft hright with hz | he
    · left
      have hh := congrArg a hz
      rw [ha,haz] at hh
      exact hh
    · right
      exact (ha f).symm.trans (congrArg a he)

end KLInvariance.MomentGraph.GradedSheaf

end


section


namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R] {N : Type um} [AddCommGroup N] [Module R N]
 theorem adjoint_zero (d : N ≃ₗ[R] Dual R N) : adjoint d (0 : End R N)=0 := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing]
  simp
end PerfectAdjoint

namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottEndOfSheaf_zero :
    bottEndOfSheaf cs basis l hl GradedSheaf.Hom.zero=0 := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val 0
  rw [map_zero]
  exact bottEndOfSheaf_coordinates cs basis l hl GradedSheaf.Hom.zero m x

 theorem bottAdjointSheaf_zero :
    bottAdjointSheaf cs basis l hl GradedSheaf.Hom.zero=GradedSheaf.Hom.zero := by
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · intro x v
    have hs : Function.Surjective (bottStalkProjection cs l x.val) :=
      bottStalkProjection_surjective cs l x.val
    obtain ⟨m,rfl⟩ := hs v
    change ((bottAdjointSheaf cs basis l hl GradedSheaf.Hom.zero).vertex x).map
      (bottStalkProjection cs l x.val m)=0
    rw [bottAdjointSheaf_vertex,bottEndOfSheaf_zero]
    change bottStalkProjection cs l x.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) 0 m)=0
    rw [PerfectAdjoint.adjoint_zero]
    exact map_zero _

 theorem bottAdjointSheaf_primitive
    (p : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (hp : p.PrimitiveProjector) :
    (bottAdjointSheaf cs basis l hl p).PrimitiveProjector :=
  GradedSheaf.Hom.primitive_of_antiInvolution _
    (bottAdjointSheaf_involutive cs basis l hl)
    (bottAdjointSheaf_comp cs basis l hl)
    (bottAdjointSheaf_zero cs basis l hl) p hp

 theorem bottAdjointSheaf_primitive_iff
    (p : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    (bottAdjointSheaf cs basis l hl p).PrimitiveProjector ↔ p.PrimitiveProjector := by
  constructor
  · intro hp
    have hh := bottAdjointSheaf_primitive cs basis l hl _ hp
    rw [bottAdjointSheaf_involutive cs basis l hl p] at hh
    exact hh
  · exact bottAdjointSheaf_primitive cs basis l hl p

end
end KLInvariance.TitsSpace

end


section

/-! Primitive-corner recognition for genuine graded sheaf splittings.
This supplies the algebraic recognition step for a prospective BMP summand;
it neither postulates the splitting nor the word/BMP character. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def SplitIn.liftEnd (s : SplitIn B C) (f : Hom B B) : Hom C C :=
  s.inclusion.comp (f.comp s.projection)

 theorem SplitIn.liftEnd_injective (s : SplitIn B C) : Function.Injective s.liftEnd := by
  intro f g h
  apply Hom.eq_of_maps
  · intro x v
    have hh := congrArg (fun q : Hom C C => (s.projection.vertex x).map
      ((q.vertex x).map ((s.inclusion.vertex x).map v))) h
    change (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((f.vertex x).map ((s.projection.vertex x).map ((s.inclusion.vertex x).map v))))=
      (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((g.vertex x).map ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))) at hh
    simpa only [s.vertex_split] using hh
  · intro e v
    have hh := congrArg (fun q : Hom C C => (s.projection.edge e).map
      ((q.edge e).map ((s.inclusion.edge e).map v))) h
    change (s.projection.edge e).map ((s.inclusion.edge e).map
      ((f.edge e).map ((s.projection.edge e).map ((s.inclusion.edge e).map v))))=
      (s.projection.edge e).map ((s.inclusion.edge e).map
      ((g.edge e).map ((s.projection.edge e).map ((s.inclusion.edge e).map v)))) at hh
    simpa only [s.edge_split] using hh

 theorem SplitIn.liftEnd_comp (s : SplitIn B C) (f g : Hom B B) :
    s.liftEnd (f.comp g)=(s.liftEnd f).comp (s.liftEnd g) := by
  apply Hom.eq_of_maps
  · intro x v
    change (s.inclusion.vertex x).map ((f.vertex x).map ((g.vertex x).map
      ((s.projection.vertex x).map v)))=
      (s.inclusion.vertex x).map ((f.vertex x).map ((s.projection.vertex x).map
      ((s.inclusion.vertex x).map ((g.vertex x).map ((s.projection.vertex x).map v)))))
    rw [s.vertex_split]
  · intro e v
    change (s.inclusion.edge e).map ((f.edge e).map ((g.edge e).map
      ((s.projection.edge e).map v)))=
      (s.inclusion.edge e).map ((f.edge e).map ((s.projection.edge e).map
      ((s.inclusion.edge e).map ((g.edge e).map ((s.projection.edge e).map v)))))
    rw [s.edge_split]

 theorem SplitIn.liftEnd_zero (s : SplitIn B C) : s.liftEnd Hom.zero=Hom.zero := by
  apply Hom.eq_of_maps
  · intro x v
    change (s.inclusion.vertex x).map 0=0
    exact map_zero _
  · intro e v
    change (s.inclusion.edge e).map 0=0
    exact map_zero _

 theorem SplitIn.primitive_id_of_projector (s : SplitIn B C)
    (h : s.projector.PrimitiveProjector) : (Hom.id B).PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    have hc : (s.liftEnd f).comp (s.liftEnd f)=s.liftEnd f :=
      (s.liftEnd_comp f f).symm.trans (congrArg s.liftEnd hf)
    have hi : s.liftEnd (Hom.id B)=s.projector := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    have hleft : (s.liftEnd f).comp s.projector=s.liftEnd f := by
      rw [← hi,← s.liftEnd_comp]
      congr 1
    have hright : s.projector.comp (s.liftEnd f)=s.liftEnd f := by
      rw [← hi,← s.liftEnd_comp]
      congr 1
    rcases h.2 (s.liftEnd f) hc hleft hright with hz | he
    · exact Or.inl (s.liftEnd_injective (hz.trans s.liftEnd_zero.symm))
    · exact Or.inr (s.liftEnd_injective (he.trans hi.symm))

 theorem SplitIn.projector_eq_id_of_primitive (s : SplitIn B C)
    (h : (Hom.id C).PrimitiveProjector)
    (x : V) [Nontrivial (B.vertex x)] : s.projector=Hom.id C := by
  have hi : s.projector.comp s.projector=s.projector := by
    apply Hom.eq_of_maps
    · exact s.projector_vertex
    · exact s.projector_edge
  have hl : s.projector.comp (Hom.id C)=s.projector := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  have hr : (Hom.id C).comp s.projector=s.projector := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rcases h.2 s.projector hi hl hr with hz | he
  · obtain ⟨v,hv⟩ := exists_ne (0 : B.vertex x)
    exfalso
    apply hv
    have hh := congrArg (fun q : Hom C C => (s.projection.vertex x).map
      ((q.vertex x).map ((s.inclusion.vertex x).map v))) hz
    change (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))=
      (s.projection.vertex x).map 0 at hh
    simpa only [s.vertex_split,map_zero] using hh
  · exact he

 def SplitIn.isoOfProjectorEqId (s : SplitIn B C) (h : s.projector=Hom.id C) : Iso B C where
  vertex x :=
    { toLinearMap := (s.inclusion.vertex x).map
      invFun := (s.projection.vertex x).map
      left_inv := s.vertex_split x
      right_inv := fun v => congrArg (fun q : Hom C C => (q.vertex x).map v) h }
  edge e :=
    { toLinearMap := (s.inclusion.edge e).map
      invFun := (s.projection.edge e).map
      left_inv := s.edge_split e
      right_inv := fun v => congrArg (fun q : Hom C C => (q.edge e).map v) h }
  lower e v := s.inclusion.lower e v
  upper e v := s.inclusion.upper e v
  vertex_graded x := (s.inclusion.vertex x).graded
  edge_graded e := (s.inclusion.edge e).graded

 def SplitIn.isoOfPrimitive (s : SplitIn B C)
    (h : (Hom.id C).PrimitiveProjector)
    (x : V) [Nontrivial (B.vertex x)] : Iso B C :=
  s.isoOfProjectorEqId (s.projector_eq_id_of_primitive h x)

 variable [IsNoetherianRing A]

 theorem Hom.primitive_image (p : Hom B B) (hp : p.PrimitiveProjector) :
    (Hom.id p.image).PrimitiveProjector := by
  have hv : ∀ x v, (p.vertex x).map ((p.vertex x).map v)=(p.vertex x).map v := by
    intro x v
    exact congrArg (fun q : Hom B B => (q.vertex x).map v) hp.1
  have he : ∀ e v, (p.edge e).map ((p.edge e).map v)=(p.edge e).map v := by
    intro e v
    exact congrArg (fun q : Hom B B => (q.edge e).map v) hp.1
  let s := p.imageSplit hv he
  have hs : s.projector=p := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  apply s.primitive_id_of_projector
  rw [hs]
  exact hp

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! A normalized minimal boundary sheaf is primitive, and that property
passes to its projector in every ACTUAL graded splitting. No word splitting
is asserted here. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def SplitIn.downEnd (s : SplitIn B C) (f : Hom C C) : Hom B B :=
  s.projection.comp (f.comp s.inclusion)

 theorem SplitIn.lift_down (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp s.projector=f) (hf' : s.projector.comp f=f) :
    s.liftEnd (s.downEnd f)=f := by
  have heq : s.liftEnd (s.downEnd f)=s.projector.comp (f.comp s.projector) := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rw [heq,hf,hf']

 theorem SplitIn.downEnd_idempotent (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp f=f) (hf' : s.projector.comp f=f) :
    (s.downEnd f).comp (s.downEnd f)=s.downEnd f := by
  have heq : (s.downEnd f).comp (s.downEnd f)=s.downEnd (f.comp (s.projector.comp f)) := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rw [heq,hf',hf]

 theorem SplitIn.primitive_projector_of_id (s : SplitIn B C)
    (h : (Hom.id B).PrimitiveProjector) : s.projector.PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps
    · exact s.projector_vertex
    · exact s.projector_edge
  · intro f hf hfp hpf
    have hg := s.downEnd_idempotent f hf hpf
    have hl : (s.downEnd f).comp (Hom.id B)=s.downEnd f := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    have hr : (Hom.id B).comp (s.downEnd f)=s.downEnd f := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    rcases h.2 (s.downEnd f) hg hl hr with hz | he
    · left
      exact (s.lift_down f hfp hpf).symm.trans ((congrArg s.liftEnd hz).trans s.liftEnd_zero)
    · right
      have hi : s.liftEnd (Hom.id B)=s.projector := by
        apply Hom.eq_of_maps <;> intros <;> rfl
      exact (s.lift_down f hfp hpf).symm.trans ((congrArg s.liftEnd he).trans hi)

end
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n=⊥} {V E : Type um} [PartialOrder V] [Finite V]
  {G : OrderedGraph V E} {α : E → A} {b : V} [IsDomain A]
  (B : BoundarySheaf hneg G α b)

 theorem primitive_identity : (GradedSheaf.Hom.id B.sheaf).PrimitiveProjector := by
  constructor
  · apply GradedSheaf.Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    have hi : ∀ x v, (f.toEndomorphism.vertex x).map ((f.toEndomorphism.vertex x).map v)=
        (f.toEndomorphism.vertex x).map v := by
      intro x v
      exact congrArg (fun q : GradedSheaf.Hom B.sheaf B.sheaf => (q.vertex x).map v) hf
    rcases B.idempotent_trivial f.toEndomorphism hi with hz | hi
    · left
      apply GradedSheaf.Hom.eq_of_maps
      · intro x v
        exact LinearMap.congr_fun (hz.1 x) v
      · intro e v
        exact LinearMap.congr_fun (hz.2 e) v
    · right
      apply GradedSheaf.Hom.eq_of_maps
      · intro x v
        exact LinearMap.congr_fun (hi.1 x) v
      · intro e v
        exact LinearMap.congr_fun (hi.2 e) v

 theorem split_projector_primitive
    {C : GradedSheaf (𝓐 := 𝓐) G} (s : GradedSheaf.SplitIn B.sheaf C) :
    s.projector.PrimitiveProjector :=
  s.primitive_projector_of_id B.primitive_identity

end KLInvariance.MomentGraph.BoundarySheaf

end


section

/-! For a supplied normalized boundary sheaf and an ACTUAL word splitting,
the adjoint image is primitively indecomposable. The splitting's existence
and the BMP axioms on that image still require word recognition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (α : Edge cs 1 (cs.wordProd l) → SymmetricCoefficient (M := M))
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) α
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottBoundarySplitAdjoint_primitive :
    (GradedSheaf.Hom.id (bottSplitAdjointSheaf cs basis l hl B.sheaf s)).PrimitiveProjector := by
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  exact GradedSheaf.Hom.primitive_image _ (bottAdjointSheaf_primitive cs basis l hl
    s.projector (B.split_projector_primitive s))

end
end KLInvariance.TitsSpace

end


section

/-! The actual reduced word's top stalk is A in degree zero, integrally and
in BOTH grading directions. This is the normalization needed to start a BMP
summand construction, not a claim about the other stalks. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous_iff (n : ℤ)
    (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro hs e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact hs
  · intro hs
    exact hs ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

 def bottTopHom : ModuleData.Hom (bottStalkData cs basis l (cs.wordProd l))
    (ModuleData.unit (symmetricGrading_negative basis)) where
  map := LinearMap.pi (fun _ => (bottTopStalkEquiv cs l hl).toLinearMap)
  graded := by
    intro n s hs j
    change bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis (n-0)
    simpa only [sub_zero] using
      (bottTopStalkEquiv_homogeneous_iff cs basis l hl n s).mpr hs

 def bottTopInvHom : ModuleData.Hom (ModuleData.unit (symmetricGrading_negative basis))
    (bottStalkData cs basis l (cs.wordProd l)) where
  map := (bottTopStalkEquiv cs l hl).symm.toLinearMap.comp (LinearMap.proj PUnit.unit)
  graded := by
    intro n a ha
    apply (bottTopStalkEquiv_homogeneous_iff cs basis l hl n _).mp
    change bottTopStalkEquiv cs l hl ((bottTopStalkEquiv cs l hl).symm (a PUnit.unit)) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    have h := ha PUnit.unit
    change a PUnit.unit ∈ symmetricGrading basis (n-0) at h
    simpa only [sub_zero] using h

 theorem bottTopHom_inv (a : ModuleData.unit (symmetricGrading_negative basis)) :
    (bottTopHom cs basis l hl).map ((bottTopInvHom cs basis l hl).map a)=a := by
  funext j
  change bottTopStalkEquiv cs l hl ((bottTopStalkEquiv cs l hl).symm (a PUnit.unit))=a j
  rw [LinearEquiv.apply_symm_apply]

 theorem bottTopInvHom_top (s : bottStalk cs l (cs.wordProd l)) :
    (bottTopInvHom cs basis l hl).map ((bottTopHom cs basis l hl).map s)=s :=
  (bottTopStalkEquiv cs l hl).symm_apply_apply s

end
end KLInvariance.TitsSpace

end


section

/-! A split pair between rank-one normalized degree-zero modules reverses.
This uses commutativity of the genuine coefficient ring, not finite-dimensional
vector-space reasoning or a restricted perfect form. -/

end

end OAI
