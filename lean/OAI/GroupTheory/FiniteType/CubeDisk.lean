import Mathlib
import OAI.GroupTheory.FiniteType.SphereQuotient

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
namespace CubeDisk
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1

def toDisk (n : ℕ) : C((Fin n → I),Disk n) :=
  ⟨fun w => ⟨fun i => 2*(w i:ℝ)-1,by
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
      intro i
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [(w i).2.1,(w i).2.2]⟩,
    (continuous_pi (fun i => by fun_prop)).subtype_mk _⟩

def toCube (n : ℕ) : C(Disk n,(Fin n → I)) :=
  ⟨fun v i => ⟨(v.1 i+1)/2,by
      have h : |v.1 i| ≤ 1 := by
        apply le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v.1 i)
        simpa only [mem_closedBall,dist_zero_right] using v.2
      obtain ⟨hl,hu⟩ := abs_le.mp h
      constructor <;> linarith⟩,
    continuous_pi (fun i => Continuous.subtype_mk (by
      exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2) _)⟩

@[simp] theorem toCube_toDisk (n : ℕ) (w : Fin n → I) : toCube n (toDisk n w) = w := by
  funext i
  apply Subtype.ext
  change (2*(w i:ℝ)-1+1)/2 = _
  ring

@[simp] theorem toDisk_toCube (n : ℕ) (v : Disk n) : toDisk n (toCube n v) = v := by
  apply Subtype.ext
  funext i
  change 2*((v.1 i+1)/2)-1 = _
  ring

def homeomorph (n : ℕ) : (Fin n → I) ≃ₜ Disk n where
  toFun := toDisk n
  invFun := toCube n
  left_inv := toCube_toDisk n
  right_inv := toDisk_toCube n
  continuous_toFun := (toDisk n).continuous
  continuous_invFun := (toCube n).continuous

theorem norm_eq_one_of_boundary {n : ℕ} (w : Fin n → I) (h : w ∈ Cube.boundary (Fin n)) :
    ‖(toDisk n w).1‖ = 1 := by
  apply le_antisymm
  · simpa only [mem_closedBall,dist_zero_right] using (toDisk n w).2
  · obtain ⟨i,hi⟩ := h
    have hl := norm_le_pi_norm (toDisk n w).1 i
    rcases hi with hi | hi
    · norm_num [toDisk,hi] at hl ⊢
      exact hl
    · norm_num [toDisk,hi] at hl ⊢
      exact hl

theorem boundary_of_norm_eq_one {n : ℕ} (v : Disk n) (hv : ‖v.1‖ = 1) :
    toCube n v ∈ Cube.boundary (Fin n) := by
  by_contra hh
  have hl : ‖v.1‖ < 1 := by
    rw [pi_norm_lt_iff (by norm_num : (0:ℝ) < 1)]
    intro i
    have hn0 : toCube n v i ≠ 0 := fun h => hh ⟨i,Or.inl h⟩
    have hn1 : toCube n v i ≠ 1 := fun h => hh ⟨i,Or.inr h⟩
    have hb := (toCube n v i).2
    have h0 : (toCube n v i:ℝ) ≠ 0 := fun h => hn0 (Subtype.ext h)
    have h1 : (toCube n v i:ℝ) ≠ 1 := fun h => hn1 (Subtype.ext h)
    have hc0 : 0 < (toCube n v i:ℝ) := lt_of_le_of_ne hb.1 (Ne.symm h0)
    have hc1 : (toCube n v i:ℝ) < 1 := lt_of_le_of_ne hb.2 h1
    change 0 < (v.1 i+1)/2 at hc0
    change (v.1 i+1)/2 < 1 at hc1
    rw [Real.norm_eq_abs,abs_lt]
    constructor <;> linarith
  linarith

end CubeDisk

namespace WeakSphere
open Set Topology Metric
open scoped unitInterval
universe u
variable {Y : Type u} [TopologicalSpace Y]
open SphereQuotient

def loop {n : ℕ} (f : C(Boundary (n+1),Y)) : GenLoop (Fin n) Y (f (pole n)) :=
  ⟨(f.comp (quotient n)).comp (CubeDisk.toDisk n),by
    intro w hw
    change f (quotient n (CubeDisk.toDisk n w)) = f (pole n)
    rw [quotient_boundary _ (CubeDisk.norm_eq_one_of_boundary w hw)]⟩

theorem exists_disk_path {n : ℕ} (f : C(Boundary (n+1),Y))
    [Subsingleton (HomotopyGroup (Fin n) Y (f (pole n)))] :
    ∃ P : C(Disk n,C(I,Y)),
      (∀ v,P v 0 = f (quotient n v)) ∧
      (∀ v,P v 1 = f (pole n)) ∧
      ∀ v : Disk n, ‖v.1‖ = 1 → P v = .const I (f (pole n)) := by
  have he : (⟦loop f⟧ : HomotopyGroup (Fin n) Y (f (pole n))) = ⟦GenLoop.const⟧ :=
    @Subsingleton.elim (HomotopyGroup (Fin n) Y (f (pole n))) ‹Subsingleton _› _ _
  obtain ⟨H⟩ := Quotient.exact he
  let P : C(Disk n,C(I,Y)) := (H.toHomotopy.toContinuousMap.comp
    ⟨fun z : Disk n × I => (z.2,CubeDisk.toCube n z.1),
      continuous_snd.prodMk ((CubeDisk.toCube n).continuous.comp continuous_fst)⟩).curry
  refine ⟨P,?_,?_,?_⟩
  · intro v
    change H (0,CubeDisk.toCube n v) = _
    refine (H.map_zero_left (CubeDisk.toCube n v)).trans ?_
    change f (quotient n (CubeDisk.toDisk n (CubeDisk.toCube n v))) = _
    rw [CubeDisk.toDisk_toCube]
  · intro v
    exact H.map_one_left (CubeDisk.toCube n v)
  · intro v hv
    ext t
    exact H.eq_snd t (CubeDisk.boundary_of_norm_eq_one v hv)

def pathData {n : ℕ} (y : Y) (P : C(Disk n,C(I,Y))) : C(Disk n ⊕ Unit,C(I,Y)) :=
  ⟨Sum.elim P (fun _ => .const I y),continuous_sum_dom.mpr ⟨P.continuous,continuous_const⟩⟩

theorem pathData_factors {n : ℕ} (y : Y) (P : C(Disk n,C(I,Y)))
    (hP : ∀ v : Disk n,‖v.1‖ = 1 → P v = .const I y) :
    Function.FactorsThrough (pathData y P) (sphereQuot n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      rcases quotient_eq hab with h | ⟨ha,hb⟩
      · exact congrArg P h
      · exact (hP a ha).trans (hP b hb).symm
    | inr b => exact hP a (quotient_eq_pole hab)
  | inr a =>
    cases b with
    | inl b => exact (hP b (quotient_eq_pole hab.symm)).symm
    | inr b => rfl

theorem sphere_nullhomotopic (n : ℕ) (f : C(Boundary (n+1),Y))
    [Subsingleton (HomotopyGroup (Fin n) Y (f (pole n)))] : f.Nullhomotopic := by
  obtain ⟨P,hP₀,hP₁,hPb⟩ := exists_disk_path f
  let K : C(Boundary (n+1),C(I,Y)) :=
    (sphereQuot_isQuotientMap n).lift (pathData (f (pole n)) P) (pathData_factors (f (pole n)) P hPb)
  have hK (a : Disk n ⊕ Unit) : K (sphereQuot n a) = pathData (f (pole n)) P a :=
    DFunLike.congr_fun ((sphereQuot_isQuotientMap n).lift_comp
      (pathData (f (pole n)) P) (pathData_factors (f (pole n)) P hPb)) a
  have h₀ : ∀ z,K z 0 = f z := by
    intro z
    obtain ⟨a,rfl⟩ := sphereQuot_surjective n z
    rw [hK]
    rcases a with v | a
    · exact hP₀ v
    · rfl
  have h₁ : ∀ z,K z 1 = f (pole n) := by
    intro z
    obtain ⟨a,rfl⟩ := sphereQuot_surjective n z
    rw [hK]
    rcases a with v | a
    · exact hP₁ v
    · rfl
  refine ⟨f (pole n),⟨?_⟩⟩
  exact { toFun := fun z => K z.2 z.1
          continuous_toFun := (K.continuous.comp continuous_snd).eval continuous_fst
          map_zero_left := h₀
          map_one_left := h₁ }

end WeakSphere

open Set Topology Metric
open scoped unitInterval
namespace SphereExtension
universe u
variable {Y : Type u} [TopologicalSpace Y]
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def radial (n : ℕ) : C(I × Boundary n,Disk n) :=
  ⟨fun z => ⟨(z.1:ℝ) • z.2.1,by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg z.1.2.1]
      have hn : ‖z.2.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2.2
      simpa only [hn,mul_one] using z.1.2.2⟩,
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

def zeroDisk (n : ℕ) : Disk n := ⟨0,by simp⟩

abbrev ConeData (n : ℕ) := (I × Boundary n) ⊕ Unit

def coneQuot (n : ℕ) : C(ConeData n,Disk n) :=
  ⟨Sum.elim (radial n) (fun _ => zeroDisk n),
    continuous_sum_dom.mpr ⟨(radial n).continuous,continuous_const⟩⟩

@[simp] theorem norm_radial {n : ℕ} (z : I × Boundary n) :
    ‖(radial n z).1‖ = (z.1:ℝ) := by
  change ‖(z.1:ℝ) • z.2.1‖ = _
  rw [norm_smul,Real.norm_of_nonneg z.1.2.1]
  have hn : ‖z.2.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2.2
  rw [hn,mul_one]

theorem coneQuot_surjective (n : ℕ) : Function.Surjective (coneQuot n) := by
  intro v
  by_cases hv : v.1 = 0
  · exact ⟨Sum.inr (),Subtype.ext hv.symm⟩
  have hn : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let t : I := ⟨‖v.1‖,norm_nonneg _,by simpa only [mem_closedBall,dist_zero_right] using v.2⟩
  let s : Boundary n := ⟨‖v.1‖⁻¹ • v.1,by
    rw [mem_sphere,dist_zero_right,norm_smul,norm_inv,Real.norm_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hn⟩
  refine ⟨Sum.inl (t,s),?_⟩
  apply Subtype.ext
  change ‖v.1‖ • (‖v.1‖⁻¹ • v.1) = v.1
  rw [smul_smul,mul_inv_cancel₀ hn,one_smul]

theorem coneQuot_isQuotientMap (n : ℕ) : IsQuotientMap (coneQuot n) :=
  IsQuotientMap.of_surjective_continuous (coneQuot_surjective n) (coneQuot n).continuous

def coneMap {n : ℕ} {f : C(Boundary n,Y)} {y : Y}
    (H : f.Homotopy (.const (Boundary n) y)) : C(ConeData n,Y) :=
  ⟨Sum.elim (fun z => H (unitInterval.symm z.1,z.2)) (fun _ => y),
    continuous_sum_dom.mpr ⟨H.continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd),continuous_const⟩⟩

theorem radial_eq {n : ℕ} {a b : I × Boundary n} (hab : radial n a = radial n b) :
    a.1 = b.1 ∧ ((a.1:ℝ) = 0 ∨ a.2 = b.2) := by
  have htime : (a.1:ℝ) = (b.1:ℝ) := by
    simpa only [norm_radial] using congrArg (fun v : Disk n => ‖v.1‖) hab
  refine ⟨Subtype.ext htime,?_⟩
  by_cases hz : (a.1:ℝ) = 0
  · exact Or.inl hz
  · apply Or.inr
    apply Subtype.ext
    have he : (a.1:ℝ) • a.2.1 = (a.1:ℝ) • b.2.1 := by
      simpa only [radial,ContinuousMap.coe_mk,← htime] using congrArg Subtype.val hab
    exact (smul_right_injective _ hz) he

theorem coneMap_factors {n : ℕ} {f : C(Boundary n,Y)} {y : Y}
    (H : f.Homotopy (.const (Boundary n) y)) :
    Function.FactorsThrough (coneMap H) (coneQuot n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨ht,hs⟩ := radial_eq hab
      rcases hs with hz | hs
      · have ha : a.1 = 0 := Subtype.ext hz
        have hb : b.1 = 0 := ht.symm.trans ha
        simp [coneMap,ha,hb]
      · have he : a = b := Prod.ext ht hs
        exact congrArg (coneMap H ∘ Sum.inl) he
    | inr b =>
      have hz : (a.1:ℝ) = 0 := by
        have he := congrArg (fun v : Disk n => ‖v.1‖) hab
        simpa only [coneQuot,ContinuousMap.coe_mk,Sum.elim_inl,Sum.elim_inr,zeroDisk,norm_zero,norm_radial] using he
      have ha : a.1 = 0 := Subtype.ext hz
      simp [coneMap,ha]
  | inr a =>
    cases b with
    | inl b =>
      have hz : (b.1:ℝ) = 0 := by
        have he := congrArg (fun v : Disk n => ‖v.1‖) hab.symm
        simpa only [coneQuot,ContinuousMap.coe_mk,Sum.elim_inl,Sum.elim_inr,zeroDisk,norm_zero,norm_radial] using he
      have hb : b.1 = 0 := Subtype.ext hz
      simp [coneMap,hb]
    | inr b => rfl

theorem exists_extension {n : ℕ} (f : C(Boundary n,Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(Disk n,Y),∀ v : Boundary n,g ⟨v,sphere_subset_closedBall v.2⟩ = f v := by
  obtain ⟨y,⟨H⟩⟩ := hf
  let g := (coneQuot_isQuotientMap n).lift (coneMap H) (coneMap_factors H)
  refine ⟨g,?_⟩
  intro v
  have he := DFunLike.congr_fun ((coneQuot_isQuotientMap n).lift_comp (coneMap H) (coneMap_factors H)) (Sum.inl (1,v))
  change g (coneQuot n (Sum.inl (1,v))) = coneMap H (Sum.inl (1,v)) at he
  have hp : coneQuot n (Sum.inl (1,v)) = ⟨v,sphere_subset_closedBall v.2⟩ := by
    apply Subtype.ext
    simp [coneQuot,radial]
  rw [hp] at he
  exact he.trans (by simp [coneMap])

end SphereExtension

end

end OAI
