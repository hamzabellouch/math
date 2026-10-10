import Mathlib
import OAI.GroupTheory.FiniteType.CubeDisk

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
namespace HomotopyFunctor
variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {x : X} {y : Y} {z : Z}

def loopMap (f : C(X,Y)) (hf : f x = y) (a : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp a.1, fun w hw => (congrArg f (a.2 w hw)).trans hf⟩

@[simp] theorem loopMap_apply (f : C(X,Y)) (hf : f x = y) (a : GenLoop N X x)
    (w : N → unitInterval) : loopMap f hf a w = f (a w) := rfl

theorem loopMap_homotopic (f : C(X,Y)) (hf : f x = y) {a b : GenLoop N X x}
    (h : GenLoop.Homotopic a b) : GenLoop.Homotopic (loopMap f hf a) (loopMap f hf b) :=
  h.comp_continuousMap f

def map (f : C(X,Y)) (hf : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (loopMap f hf) (fun _ _ => loopMap_homotopic f hf)

@[simp] theorem map_mk (f : C(X,Y)) (hf : f x = y) (a : GenLoop N X x) :
    map f hf (⟦a⟧ : HomotopyGroup N X x) = ⟦loopMap f hf a⟧ := rfl

@[simp] theorem map_id (a : HomotopyGroup N X x) : map (.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h a => rfl

@[simp] theorem map_comp (f : C(X,Y)) (hf : f x = y) (g : C(Y,Z)) (hg : g y = z)
    (a : HomotopyGroup N X x) :
    map (g.comp f) ((congrArg g hf).trans hg) a = map g hg (map f hf a) := by
  induction a using Quotient.inductionOn with
  | h a => rfl

variable [DecidableEq N]

theorem loopMap_transAt (f : C(X,Y)) (hf : f x = y) (i : N) (a b : GenLoop N X x) :
    loopMap f hf (GenLoop.transAt i a b) =
      GenLoop.transAt i (loopMap f hf a) (loopMap f hf b) := by
  apply GenLoop.ext
  intro w
  simp only [loopMap_apply,GenLoop.transAt,GenLoop.coe_copy]
  split_ifs <;> rfl

variable [Nonempty N]

def mapHom (f : C(X,Y)) (hf : f x = y) : HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    rw [HomotopyGroup.one_def,HomotopyGroup.one_def,map_mk]
    apply congrArg Quotient.mk''
    apply GenLoop.ext
    intro w
    exact hf
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        simp only [HomotopyGroup.mul_spec (i := Classical.choice ‹Nonempty N›),map_mk,
          loopMap_transAt]
        rfl

theorem mapHom_eq_of_homotopy {f g : C(X,Y)} (hf : f x = y) (hg : g x = y)
    (H : f.HomotopyRel g {x}) : mapHom (N := N) f hf = mapHom g hg := by
  apply MonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    refine ⟨{ toFun := fun w => H (w.1,a w.2)
              continuous_toFun := H.continuous.comp
                (continuous_fst.prodMk (a.1.continuous.comp continuous_snd))
              map_zero_left := fun w => H.apply_zero (a w)
              map_one_left := fun w => H.apply_one (a w)
              prop' := ?_ }⟩
    intro t w hw
    change H (t,a w) = f (a w)
    have ha : a w = x := a.2 w hw
    rw [ha]
    exact H.eq_fst t rfl

def equiv (e : X ≃ₜ Y) (he : e x = y) : HomotopyGroup N X x ≃* HomotopyGroup N Y y :=
  { mapHom ⟨e,e.continuous⟩ he with
    invFun := map ⟨e.symm,e.symm.continuous⟩ (by change e.symm y = x; rw [← he,e.symm_apply_apply])
    left_inv := by
      intro a
      induction a using Quotient.inductionOn with
      | h a =>
        apply congrArg Quotient.mk''
        apply GenLoop.ext
        intro w
        exact e.symm_apply_apply (a w)
    right_inv := by
      intro a
      induction a using Quotient.inductionOn with
      | h a =>
        apply congrArg Quotient.mk''
        apply GenLoop.ext
        intro w
        exact e.apply_symm_apply (a w) }

end HomotopyFunctor

namespace HurewiczConstruction
open Set Topology Metric CategoryTheory AlgebraicTopology
open scoped unitInterval
open SphereQuotient
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def sphereData {n : ℕ} (a : GenLoop (Fin n) X x) : C(Disk n ⊕ Unit,X) :=
  ⟨Sum.elim (a.1.comp (CubeDisk.toCube n)) (fun _ => x),
    continuous_sum_dom.mpr ⟨(a.1.comp (CubeDisk.toCube n)).continuous,continuous_const⟩⟩

theorem sphereData_boundary {n : ℕ} (a : GenLoop (Fin n) X x) (v : Disk n)
    (hv : ‖v.1‖ = 1) : a (CubeDisk.toCube n v) = x :=
  a.2 _ (CubeDisk.boundary_of_norm_eq_one v hv)

theorem sphereData_factors {n : ℕ} (a : GenLoop (Fin n) X x) :
    Function.FactorsThrough (sphereData a) (sphereQuot n) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases quotient_eq h with h | ⟨hv,hw⟩
      · exact congrArg (a ∘ CubeDisk.toCube n) h
      · exact (sphereData_boundary a v hv).trans (sphereData_boundary a w hw).symm
    | inr w => exact sphereData_boundary a v (quotient_eq_pole h)
  | inr v =>
    cases w with
    | inl w => exact (sphereData_boundary a w (quotient_eq_pole h.symm)).symm
    | inr w => rfl

def sphereMap {n : ℕ} (a : GenLoop (Fin n) X x) : C(Boundary (n+1),X) :=
  (sphereQuot_isQuotientMap n).lift (sphereData a) (sphereData_factors a)

@[simp] theorem sphereMap_apply_quot {n : ℕ} (a : GenLoop (Fin n) X x) (v : Disk n ⊕ Unit) :
    sphereMap a (sphereQuot n v) = sphereData a v :=
  DFunLike.congr_fun ((sphereQuot_isQuotientMap n).lift_comp (sphereData a) (sphereData_factors a)) v

@[simp] theorem sphereMap_pole {n : ℕ} (a : GenLoop (Fin n) X x) : sphereMap a (pole n) = x :=
  sphereMap_apply_quot a (Sum.inr ())

def homotopyData {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) : C(Disk n ⊕ Unit,C(I,X)) :=
  ⟨Sum.elim ((H.toHomotopy.toContinuousMap.comp
      ⟨fun z : Disk n × I => (z.2,CubeDisk.toCube n z.1),
        continuous_snd.prodMk ((CubeDisk.toCube n).continuous.comp continuous_fst)⟩).curry)
      (fun _ => .const I x),
    continuous_sum_dom.mpr ⟨(ContinuousMap.curry _).continuous,continuous_const⟩⟩

theorem homotopyData_boundary {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) (v : Disk n) (hv : ‖v.1‖ = 1) :
    homotopyData H (.inl v) = .const I x := by
  ext t
  exact (H.eq_fst t (CubeDisk.boundary_of_norm_eq_one v hv)).trans (sphereData_boundary a v hv)

theorem homotopyData_factors {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) :
    Function.FactorsThrough (homotopyData H) (sphereQuot n) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases quotient_eq h with h | ⟨hv,hw⟩
      · exact congrArg (fun v => homotopyData H (.inl v)) h
      · exact (homotopyData_boundary H v hv).trans (homotopyData_boundary H w hw).symm
    | inr w => exact homotopyData_boundary H v (quotient_eq_pole h)
  | inr v =>
    cases w with
    | inl w => exact (homotopyData_boundary H w (quotient_eq_pole h.symm)).symm
    | inr w => rfl

def sphereHomotopy {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) : (sphereMap a).Homotopy (sphereMap b) := by
  let K := (sphereQuot_isQuotientMap n).lift (homotopyData H) (homotopyData_factors H)
  have hK (v : Disk n ⊕ Unit) : K (sphereQuot n v) = homotopyData H v :=
    DFunLike.congr_fun ((sphereQuot_isQuotientMap n).lift_comp (homotopyData H) (homotopyData_factors H)) v
  refine { toFun := fun z => K z.2 z.1
           continuous_toFun := (K.continuous.comp continuous_snd).eval continuous_fst
           map_zero_left := ?_
           map_one_left := ?_ }
  · intro z
    obtain ⟨v,rfl⟩ := sphereQuot_surjective n z
    rw [hK,sphereMap_apply_quot]
    cases v with
    | inl v => exact H.apply_zero (CubeDisk.toCube n v)
    | inr v => rfl
  · intro z
    obtain ⟨v,rfl⟩ := sphereQuot_surjective n z
    rw [hK,sphereMap_apply_quot]
    cases v with
    | inl v => exact H.apply_one (CubeDisk.toCube n v)
    | inr v => rfl

abbrev integralHomology (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

def pushforward (n : ℕ) (f : C(X,Y)) : integralHomology n X →ₗ[ℤ] integralHomology n Y :=
  (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).hom

theorem pushforward_homotopic (n : ℕ) {f g : C(X,Y)} (H : f.Homotopy g) :
    pushforward n f = pushforward n g := by
  have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℤ ℤ) n
  exact congrArg ModuleCat.Hom.hom h

def map (n : ℕ) (z : integralHomology n (Boundary (n+1))) :
    HomotopyGroup (Fin n) X x → integralHomology n X :=
  Quotient.lift (fun a => pushforward n (sphereMap a) z) (by
    rintro a b ⟨H⟩
    rw [pushforward_homotopic n (sphereHomotopy H)])

@[simp] theorem map_mk (n : ℕ) (z : integralHomology n (Boundary (n+1)))
    (a : GenLoop (Fin n) X x) : map n z ⟦a⟧ = pushforward n (sphereMap a) z := rfl

@[simp] theorem pushforward_comp (n : ℕ) {Z : Type} [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z)) :
    pushforward n (g.comp f) = (pushforward n g).comp (pushforward n f) := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  exact congrArg ModuleCat.Hom.hom (F.map_comp (TopCat.ofHom f) (TopCat.ofHom g))

@[simp] theorem sphereMap_natural {n : ℕ} (f : C(X,Y)) (hf : f x = y)
    (a : GenLoop (Fin n) X x) :
    sphereMap (HomotopyFunctor.loopMap f hf a) = f.comp (sphereMap a) := by
  apply ContinuousMap.ext
  intro v
  obtain ⟨w,rfl⟩ := sphereQuot_surjective n v
  simp only [ContinuousMap.comp_apply,sphereMap_apply_quot]
  cases w with
  | inl v => rfl
  | inr v => exact hf.symm

theorem map_natural (n : ℕ) (z : integralHomology n (Boundary (n+1)))
    (f : C(X,Y)) (hf : f x = y) (a : HomotopyGroup (Fin n) X x) :
    map n z (HomotopyFunctor.map f hf a) = pushforward n f (map n z a) := by
  induction a using Quotient.inductionOn with
  | h a => simp only [HomotopyFunctor.map_mk,map_mk,sphereMap_natural,pushforward_comp,
      LinearMap.comp_apply]

theorem pushforward_const (n : ℕ) (hn : n ≠ 0) (y : Y) :
    pushforward n (.const X y) = 0 := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have hz : CategoryTheory.Limits.IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hn
  have he : (.const X y : C(X,Y)) =
      (ContinuousMap.const PUnit y).comp (ContinuousMap.const X (PUnit.unit)) := rfl
  rw [he,pushforward_comp]
  have hzero : pushforward n (.const PUnit y) = 0 := by
    exact congrArg ModuleCat.Hom.hom (hz.eq_of_src (F.map (TopCat.ofHom (.const PUnit y))) 0)
  rw [hzero,LinearMap.zero_comp]

@[simp] theorem sphereMap_const (n : ℕ) :
    sphereMap (GenLoop.const (N := Fin n) (x := x)) = .const _ x := by
  ext v
  obtain ⟨w,rfl⟩ := sphereQuot_surjective n v
  rw [sphereMap_apply_quot]
  cases w <;> rfl

@[simp] theorem map_one (n : ℕ) (hn : n ≠ 0)
    (z : integralHomology n (Boundary (n+1))) [Nonempty (Fin n)] :
    map (X := X) (x := x) n z 1 = 0 := by
  rw [HomotopyGroup.one_def,map_mk,sphereMap_const,pushforward_const n hn]
  rfl

end HurewiczConstruction

end

end OAI
