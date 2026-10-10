import Mathlib
import OAI.GroupTheory.FiniteType.OrderChains

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
open OrderListChains
variable (P : Type*) [Preorder P]
theorem exactIn_of_top (t : P) (ht : ∀ x, x ≤ t) (n : ℕ) : ExactIn P n := by
  intro c hc hn hd ha
  have hct : c ∈ carrier P t := fun _ hs => ⟨hc hs,fun v _ => ht v⟩
  refine ⟨cone P t c,carrier_le_module P t (cone_carrier P t hct),
    cone_mem_degreeModule P t hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]
end OrderChains

namespace OrderBasedComplex
section
variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (point : B → M) (fill : B → ℕ → M → M)

private noncomputable def chosenBasis (b : B) : M :=
  if C.degree b = 0 then point b else
    fill b (C.degree b - 1) (∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • chosenBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

noncomputable def chosenExtend : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (chosenBasis C point fill)

lemma chosen_vertex {b : B} (hb : C.degree b = 0) :
    chosenExtend C point fill (Finsupp.single b 1) = point b := by
  simp only [chosenExtend,Finsupp.linearCombination_single,one_smul]
  rw [chosenBasis,ite_eq_left hb]
lemma chosen_positive {b : B} (hb : C.degree b ≠ 0) :
    chosenExtend C point fill (Finsupp.single b 1) =
      fill b (C.degree b-1) (chosenExtend C point fill (C.d (Finsupp.single b 1))) := by
  simp only [chosenExtend,Finsupp.linearCombination_single,one_smul]
  rw [chosenBasis,ite_eq_right hb]
  congr 1
  simp only [Finsupp.linearCombination_apply,Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => C.d (Finsupp.single b 1) t • chosenBasis C point fill t)

variable (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ)
  (D : ℕ → Submodule ℤ M) (P : B → Prop) (K : B → Submodule ℤ M) (N : ℕ)
  (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
  (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
  (hpoint : ∀ b, P b → point b ∈ K b ∧ point b ∈ D 0 ∧ d (point b) = 0 ∧ aug (point b) = 1)
  (hfill : ∀ b, P b → ∀ n ≤ N, ∀ z : M, z ∈ K b → z ∈ D n → d z = 0 → aug z = 0 →
    fill b n z ∈ K b ∧ fill b n z ∈ D (n+1) ∧ d (fill b n z) = z ∧ aug (fill b n z) = 0)

include hP hface hpoint hfill in
lemma chosen_spec (b : B) (hb : P b) (hbn : C.degree b ≤ N+1) :
    chosenExtend C point fill (Finsupp.single b 1) ∈ K b ∧
    chosenExtend C point fill (Finsupp.single b 1) ∈ D (C.degree b) ∧
    d (chosenExtend C point fill (Finsupp.single b 1)) =
      chosenExtend C point fill (C.d (Finsupp.single b 1)) ∧
    aug (chosenExtend C point fill (Finsupp.single b 1)) = C.aug (Finsupp.single b 1) := by
  suffices ∀ m b, C.degree b = m → P b → m ≤ N+1 →
      chosenExtend C point fill (Finsupp.single b 1) ∈ K b ∧
      chosenExtend C point fill (Finsupp.single b 1) ∈ D (C.degree b) ∧
      d (chosenExtend C point fill (Finsupp.single b 1)) =
        chosenExtend C point fill (C.d (Finsupp.single b 1)) ∧
      aug (chosenExtend C point fill (Finsupp.single b 1)) = C.aug (Finsupp.single b 1) by
    exact this _ b rfl hb hbn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro b hm hb hbn
    by_cases hz : C.degree b = 0
    · rw [chosen_vertex C point fill hz,hz,d_vertex C hz,map_zero,C.aug_single,ite_eq_left hz]
      exact hpoint b hb
    · have hs (t : B) (ht : t ∈ (C.d (Finsupp.single b 1)).support) :=
        ih (C.degree t) (by have hh := C.lowers b t ht; omega) t rfl
          (hP b t hb ht) (by have hh := C.lowers b t ht; omega)
      let z := chosenExtend C point fill (C.d (Finsupp.single b 1))
      have hzK : z ∈ K b := by
        apply map_mem_of_support
        intro t ht
        exact hface b t hb ht (hs t ht).1
      have hzD : z ∈ D (C.degree b-1) := by
        apply map_mem_of_support
        intro t ht
        have hh := C.lowers b t ht
        have he : C.degree b - 1 = C.degree t := by omega
        rw [he]
        exact (hs t ht).2.1
      have hzd : d z = 0 := by
        have he := linear_eq_on_support (d.comp (chosenExtend C point fill))
          ((chosenExtend C point fill).comp C.d) (C.d (Finsupp.single b 1))
          (fun t ht => (hs t ht).2.2.1)
        change d z = _ at he
        simpa only [LinearMap.comp_apply,C.d_squared,map_zero] using he
      have hza : aug z = 0 := by
        have he := linear_eq_on_support (aug.comp (chosenExtend C point fill)) C.aug
          (C.d (Finsupp.single b 1)) (fun t ht => (hs t ht).2.2.2)
        change aug z = _ at he
        simpa only [C.aug_d] using he
      obtain ⟨hK,hD,hd,ha⟩ := hfill b hb (C.degree b-1) (by omega) z hzK hzD hzd hza
      rw [chosen_positive C point fill hz]
      refine ⟨hK,?_,hd,?_⟩
      · have he : C.degree b - 1 + 1 = C.degree b := by omega
        simpa only [he] using hD
      · rw [C.aug_single,ite_eq_right hz]
        exact ha

end

variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (fill : B → ℕ → M → M) (F G : (B →₀ ℤ) →ₗ[ℤ] M)

private noncomputable def chosenHomotopyBasis (b : B) : M :=
  fill b (C.degree b) (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
    ∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • chosenHomotopyBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega
noncomputable def chosenHomotopy : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (chosenHomotopyBasis C fill F G)
lemma chosenHomotopy_equation (b : B) :
    chosenHomotopy C fill F G (Finsupp.single b 1) =
      fill b (C.degree b) (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
        chosenHomotopy C fill F G (C.d (Finsupp.single b 1))) := by
  simp only [chosenHomotopy,Finsupp.linearCombination_single,one_smul]
  rw [chosenHomotopyBasis]
  congr 2
  simp only [Finsupp.linearCombination_apply,Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => C.d (Finsupp.single b 1) t • chosenHomotopyBasis C fill F G t)

variable (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ)
  (D : ℕ → Submodule ℤ M) (P : B → Prop) (K : B → Submodule ℤ M) (N : ℕ)
  (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
  (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
  (hF : ∀ b, P b → C.degree b ≤ N → F (Finsupp.single b 1) ∈ K b ∧
    F (Finsupp.single b 1) ∈ D (C.degree b) ∧ d (F (Finsupp.single b 1)) = F (C.d (Finsupp.single b 1)) ∧
    aug (F (Finsupp.single b 1)) = C.aug (Finsupp.single b 1))
  (hG : ∀ b, P b → C.degree b ≤ N → G (Finsupp.single b 1) ∈ K b ∧
    G (Finsupp.single b 1) ∈ D (C.degree b) ∧ d (G (Finsupp.single b 1)) = G (C.d (Finsupp.single b 1)) ∧
    aug (G (Finsupp.single b 1)) = C.aug (Finsupp.single b 1))
  (hfill : ∀ b, P b → ∀ n ≤ N, ∀ z : M, z ∈ K b → z ∈ D n → d z = 0 → aug z = 0 →
    fill b n z ∈ K b ∧ fill b n z ∈ D (n+1) ∧ d (fill b n z) = z ∧ aug (fill b n z) = 0)

include hP hface hF hG hfill in
lemma chosenHomotopy_spec (b : B) (hb : P b) (hbn : C.degree b ≤ N) :
    chosenHomotopy C fill F G (Finsupp.single b 1) ∈ K b ∧
    chosenHomotopy C fill F G (Finsupp.single b 1) ∈ D (C.degree b+1) ∧
    d (chosenHomotopy C fill F G (Finsupp.single b 1)) +
      chosenHomotopy C fill F G (C.d (Finsupp.single b 1)) =
      F (Finsupp.single b 1) - G (Finsupp.single b 1) ∧
    aug (chosenHomotopy C fill F G (Finsupp.single b 1)) = 0 := by
  suffices ∀ m b, C.degree b = m → P b → m ≤ N →
      chosenHomotopy C fill F G (Finsupp.single b 1) ∈ K b ∧
      chosenHomotopy C fill F G (Finsupp.single b 1) ∈ D (C.degree b+1) ∧
      d (chosenHomotopy C fill F G (Finsupp.single b 1)) +
        chosenHomotopy C fill F G (C.d (Finsupp.single b 1)) =
        F (Finsupp.single b 1) - G (Finsupp.single b 1) ∧
      aug (chosenHomotopy C fill F G (Finsupp.single b 1)) = 0 by
    exact this _ b rfl hb hbn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro b hm hb hbn
    have hbn' : C.degree b ≤ N := by omega
    have hfs := hF b hb hbn'
    have hgs := hG b hb hbn'
    have hs (t : B) (ht : t ∈ (C.d (Finsupp.single b 1)).support) :=
      ih (C.degree t) (by have hh := C.lowers b t ht; omega) t rfl
        (hP b t hb ht) (by have hh := C.lowers b t ht; omega)
    let H := chosenHomotopy C fill F G
    let z := F (Finsupp.single b 1) - G (Finsupp.single b 1) - H (C.d (Finsupp.single b 1))
    have hzK : z ∈ K b := by
      apply (K b).sub_mem ((K b).sub_mem hfs.1 hgs.1)
      apply map_mem_of_support
      intro t ht
      exact hface b t hb ht (hs t ht).1
    have hzD : z ∈ D (C.degree b) := by
      apply (D _).sub_mem ((D _).sub_mem hfs.2.1 hgs.2.1)
      apply map_mem_of_support
      intro t ht
      rw [← C.lowers b t ht]
      exact (hs t ht).2.1
    have hzd : d z = 0 := by
      have he := linear_eq_on_support (d.comp H) (F-G-H.comp C.d)
        (C.d (Finsupp.single b 1)) (fun t ht => by
          have hh := (hs t ht).2.2.1
          change d (H (Finsupp.single t 1)) = _
          simpa only [LinearMap.sub_apply,LinearMap.comp_apply] using eq_sub_of_add_eq hh)
      simp only [LinearMap.sub_apply,LinearMap.comp_apply,C.d_squared,map_zero,sub_zero] at he
      dsimp only [z]
      rw [map_sub,map_sub,hfs.2.2.1,hgs.2.2.1,he,sub_self]
    have hza : aug z = 0 := by
      have he := linear_eq_on_support (aug.comp H) 0 (C.d (Finsupp.single b 1))
        (fun t ht => (hs t ht).2.2.2)
      dsimp only [z]
      rw [map_sub,map_sub,hfs.2.2.2,hgs.2.2.2,sub_self]
      change 0 - (aug.comp H) (C.d (Finsupp.single b 1)) = 0
      rw [he,LinearMap.zero_apply,sub_zero]
    obtain ⟨hK,hD,hd,ha⟩ := hfill b hb (C.degree b) hbn' z hzK hzD hzd hza
    rw [chosenHomotopy_equation]
    refine ⟨hK,hD,?_,ha⟩
    rw [hd]
    dsimp only [z,H]
    abel
end OrderBasedComplex

namespace OrderListChains
variable (P : Type*)
lemma augmentation_of_positive {n : ℕ} (hn : 0 < n) {c : Chain P}
    (hc : Homogeneous P n c) : augmentation P c = 0 := by
  have he := OrderBasedComplex.linear_eq_on_support (augmentation P) 0 c (fun s hs => by
    rw [augmentation_single,ite_eq_right,LinearMap.zero_apply]
    intro h
    have hh := hc s hs
    simp only [degree,h,List.length_nil] at hh
    omega)
  exact he
lemma mapChain_eq_on {Q : Type*} (f g : P → Q) {c : Chain P}
    (h : ∀ s ∈ c.support, ∀ x ∈ vertices P s, f x = g x) :
    mapChain P f c = mapChain P g c := by
  apply OrderBasedComplex.linear_eq_on_support
  intro s hs
  rw [mapChain_single,mapChain_single]
  congr 2
  · exact h s hs _ (head_mem_vertices P s)
  · apply List.map_congr_left
    intro x hx
    exact h s hs x (Or.inr hx)
end OrderListChains

end

end OAI
